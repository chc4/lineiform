use crate::tracer::{self, Tracer};

use cranelift::prelude::*;
use cranelift_jit::{JITBuilder, JITModule};
use cranelift_module::{DataContext, Linkage, Module};
use crate::block::{Function};
use cranelift_codegen::ir::types::Type;
use cranelift_codegen::ir::condcodes::CondCode;

use yaxpeax_x86::long_mode::{Operand, Instruction, RegSpec, Opcode};
use yaxpeax_arch::LengthedInstruction;

use bitvec::vec::BitVec;
use bitvec::slice::BitSlice;

use core::marker::PhantomData;
use std::collections::HashMap;
use std::convert::{TryInto, TryFrom};
use core::num::Wrapping;
use rangemap::RangeMap;

use thiserror::Error;
#[derive(Error, Debug)]
pub enum LiftError {
    #[error("unable to lift function")]
    Lifting,
    #[error("unsupported target")]
    Unsupported,
    #[error("unsupported cranelift builder backend")]
    Lookup(#[from] cranelift_codegen::isa::LookupError),
    #[error("unknown register {0}")]
    UnknownRegister(&'static str),
    #[error("error setting compilation option")]
    Setting(#[from] settings::SetError),
    #[error("lifting unimplemented for inst {0}")]
    UnimplementedInst(Instruction),
    #[error("error creating cranelift module {0}")]
    Module(#[from] cranelift_module::ModuleError),
    #[error("disassembling call target {0}")]
    Block(#[from] crate::block::BlockError),
    #[error("tracer error {0}")]
    Tracer(#[from] crate::tracer::TracerError),
    #[error("we hit a return to {0:x}")]
    FunctionEnded(usize),
    #[error("we didn't return to the callsite in our lifted function")]
    TranslateOut(()),
}

const HOST_WIDTH: u8 = std::mem::size_of::<usize>() as u8;
const STACK_TOP: usize = 0xFFFF_FFFF_FFFF_FFF0;
const STACK: RegSpec = RegSpec::rsp();
// we need to map eax -> rax here, so the registers alias in storage
use lazy_static::lazy_static;
lazy_static! {
    static ref REGMAP: HashMap<RegSpec, RegSpec> = [
        (RegSpec::al(), RegSpec::rax()),
        (RegSpec::ah(), RegSpec::rax()),
        (RegSpec::ax(), RegSpec::rax()),
        (RegSpec::eax(), RegSpec::rax()),

        (RegSpec::bl(), RegSpec::rbx()),
        (RegSpec::bh(), RegSpec::rbx()),
        (RegSpec::bx(), RegSpec::rbx()),
        (RegSpec::ebx(), RegSpec::rbx()),

        (RegSpec::cl(), RegSpec::rcx()), // no cx() in real_mode
        (RegSpec::ch(), RegSpec::rcx()), // no cx() in real_mode
        (RegSpec::cx(), RegSpec::rcx()), // no cx() in real_mode
        (RegSpec::ecx(), RegSpec::rcx()),

        (RegSpec::dl(), RegSpec::rdx()),
        (RegSpec::dh(), RegSpec::rdx()),
        (RegSpec::dx(), RegSpec::rdx()),
        (RegSpec::edx(), RegSpec::rdx()),

        (RegSpec::sil(), RegSpec::rsi()), // esi is not public
        (RegSpec::esi(), RegSpec::rsi()), // esi is not public

        (RegSpec::dil(), RegSpec::rdi()), // edi is not public
        (RegSpec::edi(), RegSpec::rdi()), // edi is not public

        (RegSpec::bpl(), RegSpec::rbp()), // there's only a bp() helper in real_mode
        (RegSpec::bp(), RegSpec::rbp()), // there's only a bp() helper in real_mode
        (RegSpec::ebp(), RegSpec::rbp()), // no ebp() helper
    ].iter().cloned().collect();
}

/// We use these locations essentially as the keys of an x86 operand -> Cranelift
/// SSA variable map. When we create a function, we enter all the calling convention's
/// inputs into a store, and when we decode x86 and lift it we try and fetch the
/// "variable" that operand corrosponds to.
use std::fmt::Display;
#[derive(Clone, Hash, PartialEq, Eq, Debug, Display)]
pub enum Location {
    /// A register value
    Reg(RegSpec),
    /// A stack slot value. The `usize` is the "stack address" of it:
    /// `push rax` will create a new Stack(STACK_TOP) entry if it's the first
    /// stack operation, for example.
    Stack(usize),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum JitVariable {
    Variable(Variable),
    Known(JitValue),
}
impl JitVariable {
    pub fn val(&mut self, builder: &mut FunctionBuilder, width: u8) -> JitValue {
        match self {
            JitVariable::Variable(var) => {
                let mut val = builder.use_var(*var);
                if width != HOST_WIDTH {
                    // we want a memory or stack value as a certain width:
                    // get a use of the variable backing it, and mask to the correct
                    // size.
                    let width_mask: usize = (1 << ((width*8)+1)) - 1;
                    let mask = builder.ins()
                        .iconst(types::I64, width_mask as isize as i64);
                    val = builder.ins().band(val, mask);
                }
                JitValue::Value(val)
            },
            JitVariable::Known(val) => {
                if width == HOST_WIDTH {
                    val.clone()
                } else {
                    let width_mask = Wrapping((1 << ((width*8)+1)) - 1);
                    match val {
                        JitValue::Const(c) => JitValue::Const(*c & width_mask),
                        _ => unimplemented!(),
                    }
                }
            },
        }
    }
}

use std::rc::Rc;
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum JitValue {
    /// An SSA value
    Value(Value),
    /// A reference to a value, plus an offset into it
    Ref(Rc<JitValue>,usize),
    /// A memory region we use to represent the stack: `sub rsp, 0x8` becomes
    /// manipulating a Ref to this, and load/stores can be concretized.
    Stack,
    /// A frozen memory region. We can inline values from it safely.
    Frozen { addr: *const u8, size: usize },
    /// A statically known value.
    Const(Wrapping<usize>),
}

impl JitValue {
    /// Get a Cranelift SSA Value for this JitValue. Don't use this if you can
    /// help it, since it erases statically known values and harms optimizations.
    pub fn into_ssa(&self, int: Type, builder: &mut FunctionBuilder) -> Value {
        use JitValue::*;
        match self {
            Value(val) => val.clone(),
            Const(c) => {
                builder.ins().iconst(int, i64::try_from(c.0 as isize).unwrap())
            },
            Frozen { .. } => unimplemented!("into_ssa for frozen"),
            Ref(base, offset) => {
                match **base {
                    Value(_) => unimplemented!("ref to unsupported"),
                    Const(c) => unimplemented!("ref to const"), // XXX: constant pool
                    Frozen { addr, size } => {
                        builder.ins().iconst(int, i64::try_from(
                            ((addr as usize) + offset) as isize).unwrap()
                        )
                    },
                    Ref(_, _) => unimplemented!("ref to ref unsupported"),
                    Stack => unimplemented!("stack val"),
                }
            },
            Stack => unimplemented!("raw stack value? how did you get here"),
        }
    }
}

#[derive(Hash, PartialEq, Clone, Copy, Display, Debug)]
enum Flag {
    CF = 0,
    PF = 2,
    AF = 4,
    ZF = 6,
    SF = 7,
    TF = 8,
    IF = 9,
    DF = 10,
    OF = 11,
    FINAL = 12,
}
use Flag::*;

/// A macro that allows for saving of `eflags` values to a Context after
/// operations. Care should be taken that the last operation of `e` is the
/// operation you want to collect flags from - you should probably only
/// call this with some inline assembly expression to prevent the compiler
/// from turning your a + b into a lea, for example.
/// TODO: CPUID checks for if we have lahf
macro_rules! getflags {
    ($ctx:expr, $e:expr, $bits:expr) => {
        $e;
        let mut flags: u64;
        asm!("
            pushfq;
            pop {0};
        ", out(reg) flags);
        println!("flags are 0b{:b}", flags);
        $ctx.set_flags_const($bits, flags);
    }
}


/// A conditional bool for our JIT. These are used for lazily computing branch
/// conditions: we can store Known(true|false) for constant computed adds, while
/// setting Unknown(ssa_values) to the *result* of our add - and only do the icmp
/// and bz when we need the flag value for a conditional jump instruction, to avoid
/// generating a billion SSA values and instructions that would be pruned the
/// majority of the time.
#[derive(Clone, Debug, PartialEq)]
enum JitFlag {
    Known(u64),
    Unknown(Value, Value, Value), // left <op> right = <result>
}

#[derive(Clone)]
struct Context {
    /// Our currently known execution environment. This holds values like `rax`
    /// and stored stack values, mapping them to either constant propagated
    /// values, or Cranelift SSA variables if they are unknown at compilation
    /// time.
    bound: HashMap<Location, JitVariable>,
    flags: Vec<JitFlag>,
    int: Type,
    /// This is a bitvec for keeping track of instructions that we have seen and
    /// emitted, so that we can track backwards jumps to know when to emit loops.
    /// Technically this should be updated at each instruction emission - we can
    /// optimize it a bit by only updating it when we exit a block, however, and
    /// mark (start..end) all at once.
    seen: HashMap<*const (), Vec<bool>>,
}

impl Context {
    pub fn stack(&self) -> usize {
        let sp = self.bound.get(&Location::Reg(RegSpec::rsp()));
        match sp {
            Some(JitVariable::Known(JitValue::Ref(base, offset)))
                if let JitValue::Stack = **base =>
            {
                //println!("current stack @ 0x{:x}", offset);
                assert!(offset <= &STACK_TOP);
                assert_eq!(offset % 4, 0);
                *offset
            },
            _ => unimplemented!("non-concrete stack??"),
        }
    }

    #[inline]
    pub fn set_flags(&mut self, flags: Vec<Flag>, val: (Value, Value, Value)) -> JitValue {
        for flag in flags {
            self.flags[flag as usize] = JitFlag::Unknown(val.0, val.1, val.2);
        }
        JitValue::Value(val.2)
    }

    #[inline]
    pub fn set_flags_const(&mut self, flags: Vec<Flag>, c: u64) {
        for flag in flags {
            self.flags[flag as usize] = JitFlag::Known(c);
        }
    }

    pub fn check_flag(&mut self, flag: Flag, set: bool, builder: &mut FunctionBuilder) -> JitValue {
        let val = &self.flags[flag as usize];
        println!("eflag {} is {:?}", flag, val);
        let flag_mask = (1 << (flag as usize));
        match val {
            JitFlag::Known(b) => {
                println!("{:b} & {:b}", b, flag_mask);
                if set {
                    JitValue::Const(Wrapping((*b as usize & flag_mask == flag_mask) as usize))
                } else {
                    JitValue::Const(Wrapping((*b as usize & flag_mask == 0) as usize))
                }
            },
            JitFlag::Unknown(left, right, result) => JitValue::Value({
                let flag = match flag {
                    Flag::ZF => builder.ins().icmp_imm(if set { IntCC::Equal } else { IntCC::NotEqual }, *result, 0),
                    Flag::CF => {
                        // our carry flag is set if (left + right) < result
                        let res = builder.ins().iadd(*left, *right);
                        builder.ins().icmp(if set { IntCC::UnsignedLessThan } else { IntCC::UnsignedGreaterThanOrEqual }, res, *result)
                    },
                    _ => unimplemented!(),
                };
                builder.ins().bint(self.int, flag)
            }),
        }
    }

    pub fn dump(&self) {
        println!("STACK @ 0x{:x}", self.stack());
        for (key, val) in &self.bound {
            match key {
                Location::Stack(s) => {
                    println!("0x{:x} = {:?}", s, val)
                },
                _ => println!("{} = {:?}", key, val)
            }
        }
    }
}

pub struct Jit<'a, A, O> {
    builder_context: FunctionBuilderContext,
    ctx: codegen::Context,
    data_ctx: DataContext,
    module: JITModule,
    argument_layout: Vec<Type>,
    return_layout: Vec<Type>,
    tracer: &'a mut Tracer<'static>,
    _phantom: PhantomData<(A, O)>,
}

enum EmitEffect {
    Advance,
    Jmp(usize),
    Branch(IntCC, Value, usize),
    Ret,
}

use cranelift_codegen::ir::ArgumentLoc;
use isa::RegInfo;
use target_lexicon::{Architecture, CallingConvention, Triple};
struct Target {
    triple: Triple,
    target_isa: Box<dyn isa::TargetIsa + 'static>,
    arguments: Vec<Location>,
    outputs: Vec<Location>,
}

lazy_static! {
    static ref HOST: Target = Target::for_target(Triple::host()).unwrap();
}

impl Target {
    pub fn for_target(targ: Triple) -> Result<Self, LiftError> {
        let isa = Target::isa(targ.clone())?;
        let mut arch = Self {
            target_isa: isa,
            triple: targ,
            arguments: vec![],
            outputs: vec![],
        };
        if let Ok(CallingConvention::SystemV) = arch.triple.default_calling_convention() {
            arch.fill_in_out()?;
            Ok(arch)
        } else {
            Err(LiftError::Unsupported)
        }
    }

    fn isa(trip: Triple) -> Result<Box<dyn isa::TargetIsa + 'static>, LiftError> {
        let builder = isa::lookup(trip)?;
        let mut settings = settings::builder();
        // Configure Cranelift compilation options
        settings.set("opt_level", "speed_and_size")?;
        let flags = settings::Flags::new(settings);
        Ok(builder.finish(flags))
    }

    fn fill_in_out(&mut self) -> Result<(), LiftError> {
        match self.triple.architecture {
            Architecture::X86_64 => {
                self.arguments.append(&mut vec![
                    Location::Reg(RegSpec::rdi()),
                    Location::Reg(RegSpec::rsi()),
                    Location::Reg(RegSpec::rdx()),
                ]);
                self.outputs.append(&mut vec![
                    Location::Reg(RegSpec::rax()),
                    Location::Reg(RegSpec::rdx()),
                ]);
                Ok(())
            },
            Architecture::X86_32(_) => {
                unimplemented!()
            },
            _ => Err(LiftError::Unsupported)
        }
    }
}

pub struct JitPath<A, O>(Function<A,O>, Block, Context);

impl<'a, A, O> Jit<'a, A, O> {
    pub fn new(tracer: &'a mut Tracer<'static>) -> Jit<'a, A, O> {
        let builder = JITBuilder::new(cranelift_module::default_libcall_names());
        let module = JITModule::new(builder);

        let int = module.target_config().pointer_type();
        let ptr = Type::triple_pointer_type(&HOST.triple);

        let mut ctx = module.make_context();
        ctx.func.signature.call_conv = isa::CallConv::SystemV;
        let argument_layout = vec![ptr, ptr, int]; // hardcode self, int argument first
        //let argument_layout = vec![int, int]; // hardcode self, int argument first
        for arg in argument_layout.clone() {
            ctx.func.signature.params.push(AbiParam::new(arg));
        }

        let return_layout = vec![int]; // hardcode int return type
        for ret in return_layout.clone() {
            ctx.func.signature.returns.push(AbiParam::new(ret));
        }

        Self {
            builder_context: FunctionBuilderContext::new(),
            ctx: ctx,
            data_ctx: DataContext::new(),
            module,
            argument_layout,
            return_layout,
            tracer,
            _phantom: PhantomData,
        }
    }

    /// Translate a Function into Cranelift IR.
    /// Calling conventions here are a bit weird: essentially we only ever build
    ///
    fn translate(&mut self, f: Function<A, O>) -> Result<(), LiftError> {
        let int = self.module.target_config().pointer_type();
        // We are translating extern "C" fn(A) -> O;
        // Create the builder to build a function.
        let mut builder = FunctionBuilder::new(&mut self.ctx.func, &mut self.builder_context);

        // Create the entry block, to start emitting code in.
        let entry_block = builder.create_block();

        // Since this is the entry block, add block parameters corresponding to
        // the function's parameters.
        builder.append_block_params_for_function_params(entry_block);

        // Tell the builder to emit code in this block.
        builder.switch_to_block(entry_block);

        // And, tell the builder that this block will have no further
        // predecessors. Since it's the entry block, it won't have any
        // predecessors.

        let mut idx = 0; // Why do we need to do this instead of asking cranelift for
        // a fresh variable??
        let mut variables = Self::make_variables(&mut builder, &mut idx, entry_block, int, &self.argument_layout, &f.pinned);

        let mut function_translator = FunctionTranslator {
            depth: 0,
            int,
            builder: &mut builder,
            context: variables.clone(),
            module: &mut self.module,
            idx: &mut idx,
            return_layout: &mut self.return_layout,
            tracer: &mut self.tracer,
            changed: RangeMap::new(),
        };
        // We step forward all paths through the function until we are done
        // I think we can do something clever here: we can advance the branches
        // with *the lowest f.offset.0* each time, and coallesce when we have
        // identical jump targets.
        // pred
        // if cond {
        //  body { block } body2
        // } else {
        //  shorter_body
        // }
        // merge
        //
        // We have two paths after the cond, [pred] and [pred], shorter_body > body,
        // so we'd step the first branch until it's [pred, body],
        // and then we'd see that the jump target for both blocks is merge and
        // can union the states together.
        // This doesn't properly handle detours through blocks that are towards
        // the end of the function and then jump back, since we'd advance the
        // frontier all the way to the end before we reach them even though they
        // are short. We can probably have some heuristic to inline path length
        // too, so that it's advanced until it returns and hopefully merges at some
        // other branch - but we'd have to be careful not to break merging of
        // our example.
        // TODO: think about how this interacts with loops?
        let mut need = vec![JitPath(f, entry_block, variables)];
        while let Some(next) = need.pop() {
            let mut new = function_translator.translate(next)?;
            need.append(&mut new);
        }
        function_translator.builder.seal_block(entry_block);
        println!("jit output: \n{}", function_translator.builder.display(None));
        function_translator.builder.finalize();
        Ok(())
    }


    fn make_variables<'b>(builder: &mut FunctionBuilder<'b>, idx: &mut usize, entry_block: Block,
        int: Type, arg_vars: &Vec<Type>, pinned_values: &Vec<(Location, JitValue)>) -> Context
    {
        // First, we make a variable for all of our pinned locations containing
        // the fed-in value.
        let mut ctx: HashMap<Location, JitVariable> = HashMap::new();
        for pinned in pinned_values.iter() {
            println!("adding pinned value {} = {:?}", pinned.0, pinned.1);
            ctx.insert(pinned.0.clone(),
                JitVariable::Known(pinned.1.clone()));
        }
        // Then, for all the arguments to the function, we create a variable for
        // the ABI register *unless* it has already been pinned.
        // If we pin argument 0 = 1234 in SystemV for example, we want to compile
        // a function with RDI *always* set to 1234, and throw away the actual
        // argument.
        for (i, arg_ty) in arg_vars.iter().enumerate() {
            let arg_slot = &HOST.arguments[i];
            ctx.entry(arg_slot.clone()).or_insert_with(|| {
                println!("adding argument {}", arg_slot);
                let val = builder.block_params(entry_block)[i];
                let var = Variable::new(*idx);
                *idx = *idx + 1;
                builder.declare_var(var, *arg_ty);
                builder.def_var(var, val);
                JitVariable::Variable(var)
            });
        }
        // We add a "concrete" stack pointer as well - this means that manipulating
        // the stack by a constant value is tracked, and we can constant fold
        // load/stores.
        ctx.insert(Location::Reg(STACK),
            JitVariable::Known(JitValue::Ref(
                Rc::new(JitValue::Stack),
                STACK_TOP
            ))
        );
        Context {
            int,
            bound: ctx,
            // XXX: set this to the real default flags
            flags: vec![JitFlag::Known(0); Flag::FINAL as usize],
            seen: HashMap::new(),
        }
    }

    pub fn lower(&mut self, f: Function<A, O>) -> Result<(*const u8, u32),LiftError> {
        let translate_result = self.translate(f)?;

        let id = self.module.declare_function(
            "test function",
            Linkage::Export,
            &self.ctx.func.signature)?;
        // Define the function to jit. This finishes compilation, although
        // there may be outstanding relocations to perform. Currently, jit
        // cannot finish relocations until all functions to be called are
        // defined. For this toy demo for now, we'll just finalize the
        // function below.
        let def = self.module.define_function(
            id,
            &mut self.ctx,
            &mut codegen::binemit::NullTrapSink {},
            &mut codegen::binemit::NullStackMapSink {})?;

        // Now that compilation is finished, we can clear out the context state.
        self.module.clear_context(&mut self.ctx);

        // Finalize the functions which we just defined, which resolves any
        // outstanding relocations (patching in addresses, now that they're
        // available).
        self.module.finalize_definitions();

        // We can now retrieve a pointer to the machine code.
        let code = self.module.get_finalized_function(id);
        Ok((code, def.size))
    }

    pub fn format(&self) {
        //println!("{:?}", self.module);
    }

}

// We can't hold a FunctionBuilder and the FunctionBuilderCtx in the same struct,
// so we need this helper struct for the Jit.
struct FunctionTranslator<'a> {
    depth: usize,
    int: Type,
    builder: &'a mut FunctionBuilder<'a>,
    context: Context,
    module: &'a mut dyn Module,
    idx: &'a mut usize,
    return_layout: &'a mut Vec<Type>,
    tracer: &'a mut Tracer<'static>,
    ///// This is a list of blocks that we visited: each pointer is the address of
    ///// the start (aka the jump target).
    //flow: Vec<*const ()>,
    /// a = 1
    /// b = 5
    /// c = 3
    /// do {
    ///     a += 1;
    ///     b -= 1;
    /// } while (b > 0);
    /// a + c
    ///
    /// We pair a snapshot of the context with every entry to a basic block.
    /// This means that on a backwards jump we can find the difference between
    /// the start of block containing the loop and the end we're currently at, so
    /// we have a set of changed registers + stack values. We can then pass these
    /// values in as opaque block parameters in the recompiled loop body, and have
    /// them become parameters for the loop exit block.
    ///
    /// We can also diff the bound set at the start and end of the recompiled loop
    /// to find values that were modified in the loop's *block*, but not the actual
    /// loop body: in our example it would allow us to recover `c = 3`.
    ///
    /// There's a small snag due to multiple loop exits: we can handle this by simply
    /// emitting branches breadth-first in our high-level emit loop, and delay
    /// building the loop body until we have seen all entries, and use the union
    /// of the bound set of all the entries to find the path invariant over all
    /// possibly paths through the loop.
    changed: RangeMap<usize, HashMap<Location, JitVariable>>,
}

impl<'a> FunctionTranslator<'a> {
    fn translate<A, O>(&mut self, JitPath(f, bl, ctx): JitPath<A,O>)
            -> Result<Vec<JitPath<A,O>>, LiftError> {
        self.context = ctx;
        let mut base = (f.base as usize) + f.offset.0;
        let mut ip = base;
        println!("starting emitting @ 0x{:x}", ip);
        let mut stream = f.instructions.clone();
        let mut start_i = f.offset.1;
        let mut i = f.offset.1;
        let mut snap = self.context.bound.clone();
        self.builder.switch_to_block(bl);
        // First, we check if we've already visited the entrypoint of this block
        // before.
        {
            let this_f = self.context.seen.entry(f.base);
            if let std::collections::hash_map::Entry::Occupied(emitted) = this_f {
                if let Some(true) = emitted.get().get(start_i) {
                    unimplemented!("looping @ {}, set {:?}", start_i, emitted.get());
                }
            }
        }

        // Otherwise, we emit all the instructions in our block and handle effects
        'emit: loop {
            let inst = stream.get(i);
            if let None = inst {
                // we ran out of inputs but didn't hit a ret!
                println!("hit translate out @ 0x{:x}", ip);
                return Err(LiftError::TranslateOut(()));
            }
            let inst = inst.unwrap();
            ip += inst.len().to_const() as usize;
            let mut eff = self.emit(ip, inst)?;
            let mut seal = |function_translator: &mut FunctionTranslator| {
                // Mark the entire basic block as visited
                let this_f = function_translator.context.seen.entry(f.base);
                let entry = this_f.or_insert(Vec::with_capacity(i));
                // if we don't have enough slots to mark all our data, we
                // need to grow it so it fits.
                println!("basic block range is {}-{}", start_i, i);
                if entry.len() <= i {
                    entry.resize(i, false);
                }
                for inst in
                    &mut entry[start_i..i] {
                        *inst = true;
                }
                // And then we set the context snapshot we made at the start of the
                // jump to cover the entire range of this block
                // TODO: should this not snapshot if we already have one?
                function_translator.changed.insert(start_i..i, (&snap).clone());
                snap = function_translator.context.bound.clone();
            };
            'handle: loop { match eff {
                EmitEffect::Advance => i += 1,
                EmitEffect::Jmp(target) => {
                    seal(self);
                    // XXX: make sure this only works for *internal* jumps?
                    // tailcalls need to become just a jmp to the target and stop
                    let jump_target = Function::<A, O>::new(self.tracer, target as *const ())?;
                    //self.tracer.format(&jump_target.instructions)?;
                    //self.inline(jump_target)?;
                    println!("jmp to 0x{:x}", target);
                    return Ok(vec![JitPath(jump_target, bl, self.context.clone())]);
                },
                EmitEffect::Branch(cond, flags, target) => {
                    seal(self);
                    // if cond isn't false, then we branch to target, otherwise we
                    // fallthrough.
                    // handling branchs is a bit tricky: we snapshot our context,
                    // because we need to isolate effects from one control flow path
                    // from the other. we also give the branches different "version" -
                    // i think there's a way to use (version, addr) tuples for
                    // better block compilation or something idk
                    //
                    // we probably dont ever want to *merge* control flow path,
                    // unfortunately - it's pretty unlikely that both sides of a
                    // branch end up with identical contexts when they merge, and
                    // doing eta nodes or erasing their values back to SSA is hairy
                    // because we lose constant value knowledge, which is our bread
                    // and butter. we can probably have some heuristic idk
                    let jump_target = self.builder.create_block();
                    let continue_target = self.builder.create_block();
                    self.builder.ins().brif(cond, flags,
                        jump_target, &[]);
                    self.builder.ins().jump(continue_target, &[]);
                    self.builder.seal_block(jump_target);
                    self.builder.seal_block(continue_target);

                    let target = Function::<A, O>::new(self.tracer, target as *const ())?;
                    // Our continuation is from here
                    let mut cont = f;
                    cont.offset = (ip - base, i+1);
                    return Ok(vec![
                        // The branch path
                        JitPath(target, jump_target, self.context.clone()),
                        // The fallthrough
                        JitPath(cont, continue_target, self.context.clone())
                    ]);
                },
                // The actual end of our function - 
                EmitEffect::Ret => {
                    seal(self);
                    break 'emit;
                },
            }; break 'handle; }
        };
        Ok(vec![])
    }

    fn emit(&mut self, ip: usize, inst: &Instruction) -> Result<EmitEffect, LiftError> {

        println!("emitting for {}", inst);
        let ms = inst.mem_size().and_then(|m| m.bytes_size());
        match inst.opcode() {
            Opcode::MOV => {
                // we need to support mov dword [eax+4], rcx and vice versa, so
                // both the load and store need a mem_size for memory width.
                let val = self.value(ip, inst.operand(1), ms);
                self.store(inst.operand(0), val, ms);
            },
            Opcode::INC => {
                // TODO: set flags
                let val = self.value(ip, inst.operand(0), ms);
                let inced = self.add::<false>(val, JitValue::Const(Wrapping(1)));
                self.store(inst.operand(0), inced, ms);
            },
            Opcode::ADD => {
                let left = self.value(ip, inst.operand(0), ms);
                let right = self.value(ip, inst.operand(1), ms);
                let added = self.add::<true>(left, right);
                self.store(inst.operand(0), added, ms);
            },
            op @ (Opcode::SUB | Opcode::CMP) => {
                let left = self.value(ip, inst.operand(0), ms);
                let right = self.value(ip, inst.operand(1), inst.operand(0).width());
                let subbed = self.sub::<true>(left.clone(), right.clone());
                if let Opcode::SUB = op {
                    self.store(inst.operand(0), subbed, ms);
                }
            },
            op @ (Opcode::AND | Opcode::TEST) => {
                let left = self.value(ip, inst.operand(0), ms);
                let right = self.value(ip, inst.operand(1), ms);
                let anded = self.band(left.clone(), right.clone());
                if let Opcode::AND = op {
                    self.store(inst.operand(0), anded, ms);
                }
            },
            Opcode::NOP => (),
            Opcode::XOR => {
                if inst.operand(0) == inst.operand(1) {
                    self.store(inst.operand(0), JitValue::Const(Wrapping(0)), ms);
                }
                let left = self.value(ip, inst.operand(0), ms);
                let right = self.value(ip, inst.operand(1), ms);
                let xored = self.bxor(left.clone(), right.clone());
                self.store(inst.operand(0), xored, ms);
            },
            setcc @ (Opcode::SETA | Opcode::SETAE) => {
                // get what condition they corrospond to
                let cond = self.cond_from_opcode(setcc);
                // and then get the either constant or dynamic flag for whether
                // to branch or not from the condition
                let take = self.check_cond(cond);
                if let JitValue::Const(c) = take {
                    println!("SETcc conditional is {}", c.0);
                    self.store(inst.operand(0), JitValue::Const(Wrapping(
                        if c.0 == 1 {
                            1
                        } else {
                            0
                        })), Some(1));
                } else if let JitValue::Value(flags) = take {
                    let one = self.builder.ins().iconst(self.int, 1);
                    let zero = self.builder.ins().iconst(self.int, 0);
                    let store = self.builder.ins().selectif(self.int, cond,
                        flags, one, zero);

                    self.store(inst.operand(0),
                        JitValue::Value(store), Some(1));
                } else {
                    unimplemented!();
                }
            },
            jcc @ (Opcode::JZ | Opcode::JA | Opcode::JB | Opcode::JNA) => {
                let _target = self.jump_target(inst.operand(0), ip, ms);

                let target;
                if let JitValue::Const(c) = _target {
                    println!("known conditional jump location: 0x{:x}", c.0);
                    target = c.0;
                } else {
                    unimplemented!("dynamic call");
                }

                let cond = self.cond_from_opcode(jcc);
                let take = self.check_cond(cond);
                match take {
                    JitValue::Const(Wrapping(const { false as usize })) => {
                        // we know statically we aren't taking this branch - we
                        // can just go to the next instruction
                        ()
                    },
                    JitValue::Const(Wrapping(_)) => {
                        // we know statically we are taking this branch - just
                        // jump
                        return Ok(EmitEffect::Jmp(target))
                    },
                    JitValue::Value(flags) => {
                        // we don't know until runtime if we're taking this branch
                        // or not - we return Brnz(cond, target) as an effect,
                        // so our emit loop can emit both sides of the branch.
                        return Ok(EmitEffect::Branch(cond, flags, target));
                    },
                    _ => {
                        unimplemented!();
                    },
                }
            },
            Opcode::LEA => {
                let val = self.effective_address(inst.operand(1))?;
                self.store(inst.operand(0), val, Some(HOST_WIDTH));
            },
            Opcode::PUSH => {
                // push eax
                let val = self.value(ip, inst.operand(0), Some(HOST_WIDTH)); // get rax
                self.shift_stack(-1); // rsp -= 8
                self.store(Operand::RegDeref(STACK), val, Some(HOST_WIDTH)); // [rsp] = rax
            },
            Opcode::POP => {
                // pop rax
                let sp = self.value(ip, Operand::RegDeref(STACK), Some(HOST_WIDTH)); // [rsp]
                self.shift_stack(1); // rsp += 8
                self.store(inst.operand(0), sp, Some(HOST_WIDTH)); // rax = [rsp]
            },
            Opcode::JMP => {
                let target = self.jump_target(inst.operand(0), ip, ms);
                // If we know where the jump is going, we can try to inline
                if let JitValue::Const(c) = target {
                    println!("known jump location: 0x{:x}", c.0);
                    return Ok(EmitEffect::Jmp(c.0));
                } else {
                    unimplemented!("dynamic call");
                }
            },
            Opcode::CALL => {
                // Resolve the call target (either absolute or relative)
                let target = self.jump_target(inst.operand(0), ip, ms);
                if let JitValue::Const(c) = target {
                    // we're inlining the call body into this function:
                    let body = Function::<(),()>::new(self.tracer, c.0 as *const ())?;
                    self.tracer.format(&body.instructions[body.offset.0..].to_vec())?;
                    // `push rip`
                    println!("putting return address in {:x}", self.context.stack());
                    self.shift_stack(-1); // rsp -= 8
                    self.store(Operand::RegDeref(STACK),
                        JitValue::Const(Wrapping(ip)), Some(HOST_WIDTH));
                    // and then we just jump to the call target
                    return Ok(EmitEffect::Jmp(c.0));
                } else {
                    unimplemented!("call to {} ({:?})", inst.operand(0), target)
                }
            },
            Opcode::RETURN => {
                if inst.operand_present(0) {
                    unimplemented!("return with stack pops");
                }
                // if we were trying to return to the value past the top of the
                // stack, then we were returning out of our emitted function:
                // we're all done jitting, and can tell cranelift to stop.
                if self.context.stack() == STACK_TOP {
                    let r_layout = self.return_layout.clone();
                    let return_values: Vec<Value> = r_layout.iter().enumerate()
                        .map(|(i, r_ty)| {
                            let r_val = &HOST.outputs[i];
                            let mut var = self.get(r_val.clone());
                            var.val(self.builder, HOST_WIDTH).into_ssa(self.int, self.builder)
                        }).collect();
                    self.builder.ins().return_(&return_values[..]);
                    return Ok(EmitEffect::Ret);
                }
                // inlined calls are just jumps - if we see a ret, we just
                // jump back to the IP they pushed on the stack.
                let new_rip = self.value(ip, Operand::RegDeref(STACK), Some(HOST_WIDTH));
                if let JitValue::Const(c) = new_rip {
                    self.shift_stack(1);
                    return Ok(EmitEffect::Jmp(c.0));
                } else {
                    self.context.dump();
                    unimplemented!("return to unknown location {:?}", new_rip);
                }
            },
            _ => {
                return Err(LiftError::UnimplementedInst(inst.clone()))
            }
        }
        Ok(EmitEffect::Advance)
    }

    pub fn cond_from_opcode(&mut self, op: Opcode) -> IntCC {
        match op {
            Opcode::JA | Opcode::SETA => IntCC::UnsignedGreaterThan,
            Opcode::SETAE => IntCC::UnsignedGreaterThanOrEqual,
            Opcode::JB | Opcode::SETB => IntCC::UnsignedLessThan,
            Opcode::JNA => IntCC::UnsignedGreaterThan.inverse(),
            _ => unimplemented!(),
        }
    }

    fn jump_target(&mut self, op: Operand, ip: usize, ms: Option<u8>) -> JitValue {
        // Resolve the jump target (either absolute or relative)
        let target: JitValue = match op {
            absolute @ (
                Operand::Register(_) |
                Operand::RegDeref(_) |
                Operand::RegDisp(_, _)
            ) => {
                self.value(ip, absolute, ms)
            },
            relative @ (
                Operand::ImmediateI8(_)  |
                Operand::ImmediateI16(_) |
                Operand::ImmediateI32(_)
            )=> {
                let val = match relative {
                    Operand::ImmediateI8(i) => i as isize as usize,
                    Operand::ImmediateI16(i) => i as isize as usize,
                    Operand::ImmediateI32(i) => i as isize as usize,
                    _ => unreachable!(),
                };
                JitValue::Const(Wrapping(ip) + Wrapping(val))
            },
            _ => unimplemented!("jump target operand {}", op),
        };
        target
    }


    fn effective_address(&mut self, loc: Operand) -> Result<JitValue, LiftError> {
        match loc {
            Operand::RegDeref(r) => {
                unimplemented!();
            },
            Operand::RegDisp(r, disp) => {
                let reg = self.get(Location::Reg(r)).val(self.builder, r.width());
                Ok(self.add::<false>(reg, JitValue::Const(Wrapping(disp as u8 as usize))))
            }
            _ => unimplemented!()
        }
    }

    /// Move the stack either up or down N slots. -1 becomes a -4 or -8
    pub fn shift_stack(&mut self, slots: isize) {
        let stack_reg = self.value(0, Operand::Register(STACK), Some(HOST_WIDTH));
        match stack_reg {
            JitValue::Ref(ref base, offset)
                if let JitValue::Stack = **base =>
            {
                assert_eq!(offset % 4, 0);
                //println!("shifting stack 0x{:x}", offset);
                let new_stack = self.add::<false>(stack_reg,
                    JitValue::Const(Wrapping((slots * 8) as usize)));
                self.store(Operand::Register(STACK), new_stack, Some(HOST_WIDTH));
            }
            _ => unimplemented!("non-concrete stack!!"),
        }
    }

    pub fn get(&mut self, loc: Location) -> JitVariable {
        // If we didn't already have the register bound to a variable,
        // create a fresh one and return it.
        let idx = &mut self.idx;
        let builder = &mut self.builder;
        let int = self.int;
        let key = match loc {
            Location::Reg(r) if r.width() != HOST_WIDTH => Location::Reg(*REGMAP.get(&r).unwrap_or(&r)),
            _ => loc
        };
        self.context.bound.entry(key).or_insert_with(|| {
            let fresh = Variable::new(**idx);
            **idx = **idx + 1;
            // FIXME: registers should be the correct width
            builder.declare_var(fresh, int);
            JitVariable::Variable(fresh)
        }).clone()
    }

    /// Resolve an instruction operand into JitValue.
    /// If we have `mov eax, ecx`, we want to resolve ecx to either a use of the
    /// existing ecx variable in our context, or create a new one and use that.
    /// This has to handle *all* operand types, however: if there's an `[ecx]` we need
    /// to emit a deref instruction and return the value result of that as well.
    ///
    /// If the location is a load, `width` is the memory operation size in bytes.
    /// It is ignored for other operand types, so that e.g. `mov dword [rax+4], rcx`
    /// doesn't mistakenly truncate rcx.
    pub fn value(&mut self, ip: usize, loc: Operand, width: Option<u8>) -> JitValue {
        match loc {
            Operand::Register(const { RegSpec::rip() }) => {
                JitValue::Const(Wrapping(ip))
            },
            Operand::RegDisp(const { RegSpec::rip() }, o) => {
                JitValue::Const(Wrapping(ip) + Wrapping(o as isize as usize))
            },
            Operand::Register(r) if r.width() == 1 => {
                unimplemented!("ah al etc unimplemented")
            },
            Operand::Register(r) => {
                // if we're told to get a register at any width, we actually return
                // the register's width
                self.get(Location::Reg(r)).val(self.builder, r.width())
            },
            Operand::Register(const { RegSpec::eip() } | const { RegSpec::esp() }) => {
                unimplemented!("non-native registers")
            },
            Operand::RegDeref(STACK) => {
                let sp = self.context.stack();
                self.get(Location::Stack(sp)).val(self.builder, width.unwrap())
            },
            // XXX: this doesn't allow for unaligned reads - but whatever
            Operand::RegDisp(STACK, o) => {
                // [rsp-8] becomes Stack(self.stack() + 1)
                assert_eq!(o % 4, 0);
                let slot = Wrapping(self.context.stack()) + Wrapping(o as isize as usize);
                self.get(Location::Stack(slot.0 as usize)).val(self.builder, width.unwrap())
            },
            Operand::RegDeref(r) => {
                let reg_val = self.get(Location::Reg(r)).val(self.builder, r.width());
                match reg_val {
                    JitValue::Ref(base, offset) => {
                        // we are dereferencing a ref - we just get the data
                        // it's pointing to!
                        match &*base {
                            JitValue::Frozen { addr, size } => {
                                // we are dereferencing a pointer inside our
                                // frozen region: we return the constant data
                                if offset >= *size {
                                    unimplemented!("read outside frozen memory region");
                                }
                                // XXX: self.load(width, jitvalue)?
                                unsafe {
                                    let val = Wrapping(std::ptr::read::<usize>(
                                        addr.offset(offset.try_into().unwrap()) as *const usize));
                                    JitValue::Const(val & Wrapping((1<<(width.unwrap()*8+1))-1))
                                }
                            },
                            JitValue::Stack => {
                                assert_eq!(offset % 8, 0);
                                self.get(Location::Stack(offset)).val(self.builder, width.unwrap())
                            },
                            val @ _ => unimplemented!("value for ref to {:?}", val),
                        }
                    },
                    _ => unimplemented!("deref to {:?}", reg_val),
                }
            },
            Operand::ImmediateI8(c) => {
                JitValue::Const(Wrapping(c as isize as usize))
            },
            Operand::ImmediateI32(c) => {
                JitValue::Const(Wrapping(c as isize as usize))
            },
            Operand::ImmediateI64(c) => {
                JitValue::Const(Wrapping(c as usize))
            },
            _ => unimplemented!("value for {:?}", loc)
        }
    }

    /// Store a JitValue at a specified location.
    /// If the location is a store, it will truncate the value to `width` bytes.
    /// Other location types ignore width, so that `mov rcx, dword [rax+4]` works
    /// properly.
    pub fn store(&mut self, loc: Operand, mut val: JitValue, width: Option<u8>) {
        // The key to look up for the operand in our context.
        let key = match loc {
            Operand::Register(STACK) => {
                // sub rsp, 0x8 gets the stack as the value of rsp,
                // which means it becomes e.g. STACK_TOP-8 after a push.
                // we just get the offset from STACK_TOP, and move stack
                match val {
                    JitValue::Ref(ref base,offset) if let JitValue::Stack = **base => {
                        assert!(offset <= STACK_TOP);
                        assert_eq!(offset % 4, 0);
                        Location::Reg(STACK)
                    }
                    _ => unimplemented!("non-concrete stack! {:?}", val),
                }
            },
            Operand::Register(r) if r.width() != HOST_WIDTH => {
                match width {
                    Some(1) => {
                        let mask = match r {
                            // mov al, 1 is actually mov rax, rax[64:8]:0x1
                            // there's no bl() helper, and b(3) isn't const :(
                            const { RegSpec::al() } | const { RegSpec::bl() } |
                            const { RegSpec::cl() } | const { RegSpec::dl() } => {
                                let parent = *REGMAP.get(&r).unwrap();
                                let parent = self.get(Location::Reg(parent))
                                    .val(self.builder, HOST_WIDTH);
                                println!("before on reg = {:?}, val = {:?}", parent, val);
                                let select_mask = JitValue::Const(Wrapping(0xFF));
                                val = self.bitselect(select_mask, val, parent);
                                println!("set lower on reg = {:?}", val);
                            },
                            _ => unimplemented!(),
                        };
                    },
                    Some(2) => unimplemented!(),
                    Some(4) => {
                        // e.g. `mov eax, rcx` means we mask and load only the low
                        // 4 bytes.
                        val = self.band(val, JitValue::Const(Wrapping(0xFFFF_FFFF)));
                        ()
                    },
                    Some(8) => (),
                    Some(_) => unimplemented!(),
                    None => (),
                };
                Location::Reg(*REGMAP.get(&r).unwrap())
            },
            Operand::Register(r) => {
                // if our register is a different width, we need to resize the
                // value we set it to:
                Location::Reg(r)
            },
            Operand::RegDeref(STACK) => {
                Location::Stack(self.context.stack())
            },
            Operand::RegDisp(STACK, o) => {
                // We turn [rsp-8] into Stack(stack - 1) - we count
                // stack slots up from 0.
                assert_eq!(o % 4, 0); // XXX: there's a few of these - we need to
                // handle unaligned access to stack values correct
                let sp = Wrapping(self.context.stack()) + Wrapping(o as isize as usize);
                println!("stack {} = {:x}", loc, sp.0 as usize);
                Location::Stack(sp.0 as usize)
            },
            //Operand::RegDeref(r) => Location::Reg(r),
            //Operand::RegDisp(r, o) => Location::Reg(r),
            _ => unimplemented!("unimplemented key for {:?}", loc),
        };
        match val {
            // If we're just setting a variable to a known value, we copy the
            // value in.
            JitValue::Frozen { .. } | JitValue::Const(_) | JitValue::Ref(_,_) => {
                // XXX: this can't just do this. [rax+8] = frozen needs to
                // freeze some constant memory map we keep as well.
                //unimplemented!("fix this");
                self.context.bound.entry(key).insert(JitVariable::Known(val));
            },
            // If we're setting to an SSA value...
            JitValue::Value(val) => {
                match loc {
                    // rax = val becomes a redefine for the register
                    Operand::Register(_)
                    // [rsp] = val becomes a redefine for the current stack
                    | Operand::RegDeref(STACK)
                    // [rsp-8] = val becomes a redefine for the stack slot
                    | Operand::RegDisp(STACK, _) => {
                        println!("set symbolic");
                        let var = Variable::new(*self.idx);
                        *self.idx = *self.idx + 1;
                        self.builder.declare_var(var, self.int);
                        self.builder.def_var(var, val);
                        self.context.bound.insert(key,
                            JitVariable::Variable(var));
                    },
                    Operand::RegDeref(const { RegSpec::esp() } | const { RegSpec::sp() })
                    | Operand::RegDisp(const { RegSpec::esp() } | const { RegSpec::sp()}, _) => {
                        unimplemented!("non-native stack size");
                    },
                    Operand::RegDeref(r) => {
                        unimplemented!();
                        // [rax] = val becomes a store to the contents of register
                        let reg_val = self.get(key)
                            .val(self.builder, r.width()).into_ssa(self.int, self.builder);
                        let ins = self.builder.ins();
                        match width {
                            Some(1) => ins.istore8(MemFlags::new(), val, reg_val, 0),
                            Some(2) => ins.istore16(MemFlags::new(), val, reg_val, 0),
                            Some(4) => ins.istore32(MemFlags::new(), val, reg_val, 0),
                            _ => ins.store(MemFlags::new(), val, reg_val, 0), // ??
                        };
                    },
                    Operand::RegDisp(r, o) => {
                        unimplemented!();
                        let reg_val = self.get(key)
                            .val(self.builder, r.width()).into_ssa(self.int, self.builder);
                        let ins = self.builder.ins();
                        match width {
                            Some(1) => ins.istore8(MemFlags::new(), val, reg_val, o),
                            Some(2) => ins.istore16(MemFlags::new(), val, reg_val, o),
                            Some(4) => ins.istore32(MemFlags::new(), val, reg_val, o),
                            _ => ins.store(MemFlags::new(), val, reg_val, o), // ??
                        };
                    },
                    _ => unimplemented!("store for {} ({:?}) = {:?}", loc, loc, val)
                }
            },
            _ => unimplemented!("unknown store for {:?}", val),
        }
    }

    pub fn check_cond(&mut self, cond: IntCC) -> JitValue {
        let flags = match cond {
            IntCC::UnsignedGreaterThan => {
                vec![Flag::CF, Flag::ZF]
            },
            IntCC::UnsignedGreaterThanOrEqual => {
                vec![Flag::CF]
            },
            IntCC::UnsignedLessThan => {
                vec![Flag::CF]
            },
            IntCC::UnsignedLessThanOrEqual => {
                vec![Flag::CF, Flag::ZF]
            },
            _ => unimplemented!("unimplemented check_cond for {}", cond),
        };
        let mut val = None;
        let mut same = true;
        for flag in flags {
            let flag_cond = &self.context.flags[flag as usize];
            if let Some(set_val) = val {
                if set_val != flag_cond {
                    same = false;
                    break;
                }
            } else {
                val = Some(flag_cond);
            }
        }
        if !same {
            unimplemented!();
        }
        if let Some(JitFlag::Unknown(left, right, res)) = val {
            JitValue::Value(self.builder.ins().ifcmp(*left, *right))
        } else if let Some(JitFlag::Known(c)) = val {
            println!("constant eflags {:?} with cond {}", c, cond);
            match cond {
                IntCC::UnsignedGreaterThan => {
                    // CF=0 and ZF=0
                    let cf = self.context.check_flag(Flag::CF, false, self.builder);
                    let zf = self.context.check_flag(Flag::ZF, false, self.builder);
                    self.band(cf, zf)
                },
                IntCC::UnsignedGreaterThanOrEqual => {
                    // CF=0
                    self.context.check_flag(Flag::CF, false, self.builder)
                },
                IntCC::UnsignedLessThan => {
                    // CF=1
                    self.context.check_flag(Flag::CF, true, self.builder)
                },
                IntCC::UnsignedLessThanOrEqual => {
                    // CF=1 or ZF=1
                    let cf = self.context.check_flag(Flag::CF, true, self.builder);
                    let zf = self.context.check_flag(Flag::ZF, true, self.builder);
                    self.bor(cf, zf)
                },
                _ => unimplemented!(),
            }
        } else {
            unimplemented!()
        }
    }

    /// Get left+right for JitValues.
    /// if FLAG is true, then self.context.flags are updated with eflags
    pub fn add<const FLAG:bool>(&mut self, left: JitValue, right: JitValue) -> JitValue {
        // XXX: set flags
        use JitValue::*;
        use Flag::*;
        let flags = vec![OF, SF, ZF, AF, PF, CF];
        match (left, right) {
            (Value(val_left), Value(val_right)) => {
                self.context.set_flags(flags, (val_left, val_right,
                    self.builder.ins().iadd(val_left, val_right)))
            },
            (other @ _ , Value(ssa))
            | (Value(ssa), other @ _) => {
                let other = other.into_ssa(self.int, self.builder);
                self.context.set_flags(flags, (other, ssa,
                    self.builder.ins().iadd(other, ssa)))
            },
            (Ref(base, offset), Const(c))
            | (Const(c), Ref(base, offset)) => {
                if FLAG {
                    let mut val = offset;
                    unsafe {
                        getflags!(self.context, asm!("
                            add {}, {}
                        ", inout(reg) val, in(reg) c.0),
                        vec![OF, SF, ZF, AF, PF]);
                    }
                    Ref(base, val)
                } else {
                    Ref(base, (Wrapping(offset) + c).0)
                }
            },
            (Const(left_c), Const(right_c)) => {
                if FLAG {
                    let mut val = left_c.0;
                    unsafe {
                        getflags!(self.context, asm!("
                            add {}, {}
                        ", inout(reg) val, in(reg) right_c.0),
                        vec![OF, SF, ZF, AF, PF]);
                    }
                    Const(Wrapping(val))
                } else {
                    Const(left_c + right_c)
                }
            },
            (left, right) => unimplemented!("unimplemented add {:?} {:?}", left, right)
        }
    }

    pub fn sub<const FLAG:bool>(&mut self, left: JitValue, right: JitValue) -> JitValue {
        // XXX: set flags
        use JitValue::*;
        let flags = vec![OF, SF, ZF, AF, PF, CF];
        match (left, right) {
            // add rsp, 0x8 becomes a redefine of rsp with offset -= 1
            (Value(val_left), Value(val_right)) => {
                let res = self.builder.ins().isub(val_left, val_right);
                self.context.set_flags(flags, (val_left, val_right, res));
                Value(res)
            },
            (left @ _ , right @ Value(_))
            | (left @ Value(_), right @ _) => {
                let left = left.into_ssa(self.int, self.builder);
                let right = right.into_ssa(self.int, self.builder);
                let res = self.builder.ins().isub(left, right);
                self.context.set_flags(flags, (left, right, res));
                Value(res)
            },
            (Ref(base, offset), Const(Wrapping(c)))
            | (Const(Wrapping(offset)), Ref(base, c)) => {
                if FLAG {
                    let mut val = offset;
                    unsafe {
                        getflags!(self.context, asm!("
                            sub {}, {}
                        ", inout(reg) val, in(reg) c),
                        flags);
                    }
                    Ref(base, val)
                } else {
                    Ref(base, (Wrapping(offset) - Wrapping(c)).0)
                }
            },
            (Const(left_c), Const(right_c)) => {
                if FLAG {
                    let mut val = left_c.0;
                    unsafe {
                        getflags!(self.context, asm!("
                            sub {}, {}
                        ", inout(reg) val, in(reg) right_c.0),
                        flags);
                    }
                    Const(Wrapping(val))
                } else {
                    Const(left_c - right_c)
                }
            },
            (left, right) => unimplemented!("unimplemented sub {:?} {:?}", left, right)
        }
    }

    pub fn band(&mut self, left: JitValue, right: JitValue) -> JitValue {
        // XXX: set flags
        use JitValue::*;
        match (left, right) {
            //0 & val or val & 0 = 0
            (Const(Wrapping(0)), _) | (_, Const(Wrapping(0))) => Const(Wrapping(0)),
            // add rsp, 0x8 becomes a redefine of rsp with offset -= 1
            (Value(val_left), Value(val_right)) => {
                Value(self.builder.ins().band(val_left, val_right))
            },
            (val @ _, Value(ssa))
            | (Value(ssa), val @ _) => {
                let ssa_val = val.into_ssa(self.int, self.builder);
                Value(self.builder.ins().band(ssa_val, ssa))
            },
            (Ref(base, offset), Const(c))
            | (Const(c), Ref(base, offset)) => {
                unimplemented!("band pointer")
            },
            (Const(left_c), Const(right_c)) => {
                Const(left_c & right_c)
            },
            (left, right) => unimplemented!("unimplemented band {:?} {:?}", left, right)
        }
    }

    pub fn bor(&mut self, left: JitValue, right: JitValue) -> JitValue {
        // XXX: set flags
        use JitValue::*;
        match (left, right) {
            //0 | val or val | 0 = val
            (Const(Wrapping(0)), val @ _) | (val @ _, Const(Wrapping(0))) => val,
            // add rsp, 0x8 becomes a redefine of rsp with offset -= 1
            (Value(val_left), Value(val_right)) => {
                Value(self.builder.ins().bor(val_left, val_right))
            },
            (val @ _, Value(ssa))
            | (Value(ssa), val @ _) => {
                let ssa_val = val.into_ssa(self.int, self.builder);
                Value(self.builder.ins().bor(ssa_val, ssa))
            },
            (Ref(base, offset), Const(c))
            | (Const(c), Ref(base, offset)) => {
                unimplemented!("bor pointer")
            },
            (Const(left_c), Const(right_c)) => {
                Const(left_c | right_c)
            },
            (left, right) => unimplemented!("unimplemented bor {:?} {:?}", left, right)
        }
    }

    pub fn bxor(&mut self, left: JitValue, right: JitValue) -> JitValue {
        // XXX: set flags
        use JitValue::*;
        match (left, right) {
            // add rsp, 0x8 becomes a redefine of rsp with offset -= 1
            (Value(val_left), Value(val_right)) => {
                Value(self.builder.ins().bxor(val_left, val_right))
            },
            (val @ _, Value(ssa))
            | (Value(ssa), val @ _) => {
                let ssa_val = val.into_ssa(self.int, self.builder);
                Value(self.builder.ins().bxor(ssa_val, ssa))
            },
            (Ref(base, offset), Const(c))
            | (Const(c), Ref(base, offset)) => {
                unimplemented!("bxor pointer")
            },
            (Const(left_c), Const(right_c)) => {
                Const(left_c ^ right_c)
            },
            (left, right) => unimplemented!("unimplemented bxor {:?} {:?}", left, right)
        }
    }

    pub fn bitselect(&mut self, control: JitValue, left: JitValue, right: JitValue) -> JitValue {
        // XXX: set flags
        use JitValue::*;
        match (control, left, right) {
            //bitselect(0, left, right) => right
            (Const(Wrapping(0)), t @ _, f @ _) => f,
            //bitselect(!0, left, right) => left
            (Const(Wrapping(const { !(0 as usize) })), t @ _, f @ _) => t,
            //bitselect(control, 0, right) => !control & right
            //bitselect(control, left, 0) => control & left
            (control @ _, left @ _, Const(Wrapping(0))) => {
                self.band(control, left)
            },
            (control @ _, Value(val_left), Value(val_right)) => {
                let control = control.into_ssa(self.int, self.builder);
                Value(self.builder.ins().bitselect(control, val_left, val_right))
            },
            (control, left, right) =>
                unimplemented!("unimplemented bitselect {:?} {:?} {:?}", control, left, right)
        }
    }
}
