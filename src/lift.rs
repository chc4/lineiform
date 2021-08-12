use crate::tracer::{self, Tracer};

use cranelift::prelude::*;
use cranelift_jit::{JITBuilder, JITModule};
use cranelift_module::{DataContext, Linkage, Module};
use crate::block::{Function};
use cranelift_codegen::ir::types::Type;

use yaxpeax_x86::long_mode::{Operand, Instruction, RegSpec, Opcode};
use yaxpeax_arch::LengthedInstruction;

use std::collections::HashMap;
use std::convert::{TryInto, TryFrom};
use core::num::Wrapping;

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

const STACK_TOP: usize = 0xFFFF_FFFF_FFFF_FFF0;
const STACK: RegSpec = RegSpec::rsp();

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

#[derive(Clone)]
pub enum JitVariable {
    Variable(Variable),
    Known(JitValue),
}
impl JitVariable {
    pub fn val(&mut self, builder: &mut FunctionBuilder) -> JitValue {
        match self {
            JitVariable::Variable(var) => JitValue::Value(builder.use_var(*var)),
            JitVariable::Known(val) => val.clone(),
        }
    }
}

use std::rc::Rc;
#[derive(Debug, Clone)]
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

struct Context {
    /// Our currently known execution environment. This holds values like `rax`
    /// and stored stack values, mapping them to either constant propagated
    /// values, or Cranelift SSA variables if they are unknown at compilation
    /// time.
    bound: HashMap<Location, JitVariable>,
}

pub struct Jit<'a, A, O> {
    f: Function<A, O>,
    builder_context: FunctionBuilderContext,
    ctx: codegen::Context,
    data_ctx: DataContext,
    module: JITModule,
    argument_layout: Vec<Type>,
    return_layout: Vec<Type>,
    tracer: &'a mut Tracer<'static>,
}

enum EmitEffect {
    Advance,
    Jmp(usize),
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

use lazy_static::lazy_static;
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

impl<'a, A, O> Jit<'a, A, O> {
    pub fn lift(tracer: &'a mut Tracer<'static>, f: Function<A, O>) -> Jit<'a, A, O> {
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
            f: f,
            builder_context: FunctionBuilderContext::new(),
            ctx: ctx,
            data_ctx: DataContext::new(),
            module,
            argument_layout,
            return_layout,
            tracer,
        }
    }

    /// Translate a Function into Cranelift IR.
    /// Calling conventions here are a bit weird: essentially we only ever build
    ///
    fn translate(&mut self) -> Result<(), LiftError> {
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
        let mut variables = Self::make_variables(&mut builder, &mut idx, entry_block, int, &self.argument_layout, &self.f.pinned);

        let mut function_translator = FunctionTranslator {
            depth: 0,
            f: (self.f.base, self.f.size),
            int,
            builder: &mut builder,
            context: variables,
            module: &mut self.module,
            idx: &mut idx,
            return_layout: &mut self.return_layout,
            tracer: &mut self.tracer,
        };

        let mut ip = self.f.base as usize;
        let mut stream = self.f.instructions.clone();
        let mut i = 0;
        'emit: loop {
            let inst = stream.get(i);
            if let None = inst {
                // we ran out of inputs but didn't hit a ret!
                return Err(LiftError::TranslateOut(()));
            }
            let inst = inst.unwrap();
            ip += inst.len().to_const() as usize;
            i += 1;
            let eff = function_translator.emit(ip, inst)?;
            match eff {
                EmitEffect::Advance => (),
                EmitEffect::Jmp(target) => {
                    // XXX: make sure this only works for *internal* jumps?
                    // tailcalls need to become just a jmp to the target and stop
                    let jump_target = Function::<A, O>::new(function_translator.tracer, target as *const ())?;
                    //self.tracer.format(&jump_target.instructions)?;
                    //self.inline(jump_target)?;
                    println!("emitting inlined jmp target");
                    stream = jump_target.instructions.clone();
                    i = 0;
                    ip = target;
                },
                // The actual end of our function - 
                EmitEffect::Ret => {
                    break 'emit;
                },
            };
        };
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
            bound: ctx,
        }
    }

    pub fn lower(&mut self) -> Result<(*const u8, u32),LiftError> {
        let translate_result = self.translate()?;

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
    f: (*const (), usize),
    int: Type,
    builder: &'a mut FunctionBuilder<'a>,
    context: Context,
    module: &'a mut Module,
    idx: &'a mut usize,
    return_layout: &'a mut Vec<Type>,
    tracer: &'a mut Tracer<'static>,
}

impl<'a> FunctionTranslator<'a> {
    fn emit(&mut self, ip: usize, inst: &Instruction) -> Result<EmitEffect, LiftError> {
        println!("emitting for {}", inst);
        match inst.opcode() {
            Opcode::MOV => {
                let val = self.value(ip, inst.operand(1));
                self.store(inst.operand(0), val);
            },
            Opcode::INC => {
                // TODO: set flags
                let val = self.value(ip, inst.operand(0));
                let inced = self.add(val, JitValue::Const(Wrapping(1)));
                self.store(inst.operand(0), inced);
            },
            Opcode::ADD => {
                // TODO: set flags
                let left = self.value(ip, inst.operand(0));
                let right = self.value(ip, inst.operand(1));
                let added = self.add(left, right);
                self.store(inst.operand(0), added);
            },
            Opcode::SUB => {
                // TODO: set flags
                let left = self.value(ip, inst.operand(0));
                let right = self.value(ip, inst.operand(1));
                let added = self.sub(left, right);
                self.store(inst.operand(0), added);
            },
            Opcode::LEA => {
                let val = self.effective_address(inst.operand(1))?;
                self.store(inst.operand(0), val);
            },
            Opcode::PUSH => {
                // push eax
                let val = self.value(ip, inst.operand(0)); // get rax
                self.store(Operand::RegDeref(STACK), val); // [rsp] = rax
                self.shift_stack(-1); // rsp -= 8
            },
            Opcode::POP => {
                // pop rax
                let sp = self.value(ip, Operand::RegDeref(STACK)); // [rsp]
                self.store(inst.operand(0), sp); // rax = [rsp]
                self.shift_stack(1); // rsp += 8
            },
            Opcode::JMP => {
                // Resolve the jump target (either absolute or relative)
                let target: JitValue = match inst.operand(0) {
                    absolute @ (Operand::Register(_) | Operand::RegDisp(_, _)) => {
                        self.value(ip, absolute)
                    },
                    relative @ Operand::ImmediateI8(_) => {
                        let target_val = self.value(ip, relative);
                        self.add(JitValue::Const(Wrapping(ip)), target_val)
                    },
                    _ => unimplemented!("jump target operand {}", inst.operand(0)),
                };
                // If we know where the jump is going, we can try to inline
                if let JitValue::Const(c) = target {
                    println!("known jump location: 0x{:x}", c.0);
                    // If it's within our own function, it's an internal branch:
                    // don't handle this for now.
                    if c.0 >= (self.f.0 as usize) && c.0 <= (self.f.0 as usize) + self.f.1 {
                        unimplemented!("internal jump");
                    }
                    return Ok(EmitEffect::Jmp(c.0));
                } else {
                    unimplemented!("dynamic call");
                }
            },
            Opcode::CALL => {
                // Resolve the call target (either absolute or relative)
                let target: JitValue = match inst.operand(0) {
                    absolute @ (Operand::Register(_) | Operand::RegDisp(_, _)) => {
                        self.value(ip, absolute)
                    },
                    relative @ (Operand::ImmediateI8(_)
                        | Operand::ImmediateI16(_)
                        | Operand::ImmediateI32(_)
                    )=> {
                        let target_val = self.value(ip, relative);
                        self.add(JitValue::Const(Wrapping(ip)), target_val)
                    },
                    _ => unimplemented!("call target operand {}", inst.operand(0)),
                };
                if let JitValue::Const(c) = target {
                    // we're inlining the call body into this function:
                    let body = Function::<(),()>::new(self.tracer, c.0 as *const ())?;
                    self.tracer.format(&body.instructions)?;
                    // `push rip`
                    self.store(Operand::RegDeref(STACK),
                        JitValue::Const(Wrapping(ip)));
                    self.shift_stack(-1); // rsp -= 8
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
                if self.stack() == STACK_TOP {
                    let r_layout = self.return_layout.clone();
                    let return_values: Vec<Value> = r_layout.iter().enumerate()
                        .map(|(i, r_ty)| {
                            let r_val = &HOST.outputs[i];
                            let mut var = self.get(r_val.clone());
                            var.val(self.builder).into_ssa(self.int, self.builder)
                        }).collect();
                    self.builder.ins().return_(&return_values[..]);
                    return Ok(EmitEffect::Ret);
                }
                // inlined calls are just jumps - if we see a ret, we just
                // jump back to the IP they pushed on the stack.
                let new_rip = self.value(ip, Operand::RegDeref(STACK));
                if let JitValue::Const(c) = new_rip {
                    self.shift_stack(1);
                    return Ok(EmitEffect::Jmp(c.0));
                } else {
                    unimplemented!("return to unknown location {:?}", new_rip);
                }
            },
            _ => {
                return Err(LiftError::UnimplementedInst(inst.clone()))
            }
        }
        Ok(EmitEffect::Advance)
    }

    fn effective_address(&mut self, loc: Operand) -> Result<JitValue, LiftError> {
        match loc {
            Operand::RegDeref(r) => {
                unimplemented!();
            },
            Operand::RegDisp(r, disp) => {
                let reg = self.get(Location::Reg(r)).val(self.builder);
                Ok(self.add(reg, JitValue::Const(Wrapping(disp as u8 as usize))))
            }
            _ => unimplemented!()
        }
    }

    /// Move the stack either up or down N slots. -1 becomes a -4 or -8
    pub fn shift_stack(&mut self, slots: isize) {
        let stack_reg = self.value(0, Operand::Register(STACK));
        match stack_reg {
            JitValue::Ref(ref base, offset)
                if let JitValue::Stack = **base =>
            {
                assert_eq!(offset % 8, 0);
                //println!("shifting stack 0x{:x}", offset);
                let new_stack = self.add(stack_reg,
                    JitValue::Const(Wrapping((slots * 8) as usize)));
                self.store(Operand::Register(STACK), new_stack);
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
        self.context.bound.entry(loc).or_insert_with(|| {
            let fresh = Variable::new(**idx);
            **idx = **idx + 1;
            // FIXME: registers should be the correct width
            builder.declare_var(fresh, int);
            JitVariable::Variable(fresh)
        }).clone()
    }

    pub fn stack(&mut self) -> usize {
        let sp = self.get(Location::Reg(STACK));
        match sp {
            JitVariable::Known(JitValue::Ref(base, offset))
                if let JitValue::Stack = *base =>
            {
                //println!("current stack @ 0x{:x}", offset);
                assert!(offset <= STACK_TOP);
                assert_eq!(offset % 8, 0);
                offset
            },
            _ => unimplemented!("non-concrete stack??"),
        }
    }

    /// Resolve an instruction operand into JitValue.
    /// If we have `mov eax, ecx`, we want to resolve ecx to either a use of the
    /// existing ecx variable in our context, or create a new one and use that.
    /// This has to handle *all* operand types, however: if there's an `[ecx]` we need
    /// to emit a deref instruction and return the value result of that as well.
    /// XXX: add `width` and `extension_mode` parameters?
    pub fn value(&mut self, ip: usize, loc: Operand) -> JitValue {
        match loc {
            Operand::Register(const { RegSpec::rip() }) => {
                JitValue::Const(Wrapping(ip))
            },
            Operand::RegDisp(const { RegSpec::rip() }, o) => {
                JitValue::Const(Wrapping(ip) + Wrapping(o as isize as usize))
            },
            Operand::Register(r) => {
                self.get(Location::Reg(r)).val(self.builder)
            },
            Operand::RegDeref(STACK) => {
                let sp = self.stack();
                self.get(Location::Stack(sp)).val(self.builder)
            },
            Operand::RegDisp(STACK, o) => {
                // [rsp-8] becomes Stack(self.stack() + 1)
                assert_eq!(o % 8, 0);
                let slot = Wrapping(self.stack() as isize) + Wrapping(o as isize);
                self.get(Location::Stack(slot.0 as usize)).val(self.builder)
            },
            Operand::RegDeref(r) => {
                let reg_val = self.get(Location::Reg(r)).val(self.builder);
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
                                    JitValue::Const(Wrapping(std::ptr::read::<usize>(
                                        addr.offset(offset.try_into().unwrap()) as *const usize)))
                                }
                            },
                            val @ _ => unimplemented!("value for ref to {:?}", val),
                        }
                    },
                    _ => unimplemented!("deref to {:?}", reg_val),
                }
            },
            Operand::ImmediateI8(c) => {
                JitValue::Const(Wrapping(c as u8 as usize))
            },
            Operand::ImmediateI32(c) => {
                JitValue::Const(Wrapping(c as isize as usize))
            },
            _ => unimplemented!("value for {:?}", loc)
        }
    }

    pub fn store(&mut self, loc: Operand, val: JitValue) {
        // The key to look up for the operand in our context.
        let key = match loc {
            Operand::Register(STACK) => {
                // sub rsp, 0x8 gets the stack as the value of rsp,
                // which means it becomes e.g. STACK_TOP-8 after a push.
                // we just get the offset from STACK_TOP, and move stack
                match val {
                    JitValue::Ref(ref base,offset) if let JitValue::Stack = **base => {
                        assert!(offset <= STACK_TOP);
                        assert_eq!(offset % 8, 0);
                        Location::Reg(STACK)
                    }
                    _ => unimplemented!("non-concrete stack! {:?}", val),
                }
            },
            Operand::Register(r) => Location::Reg(r),
            Operand::RegDeref(STACK) => {
                Location::Stack(self.stack())
            },
            Operand::RegDisp(STACK, o) => {
                // We turn [rsp-8] into Stack(stack - 1) - we count
                // stack slots up from 0.
                assert_eq!(o % 8, 0);
                let sp = Wrapping(self.stack() as isize) + Wrapping(o as isize);
                println!("stack {} = {:x}", loc, sp.0 as usize);
                Location::Stack(sp.0 as usize)
            },
            Operand::RegDeref(r) => Location::Reg(r),
            Operand::RegDisp(r, o) => Location::Reg(r),
            _ => unimplemented!("unimplemented key for {:?}", loc),
        };
        match val {
            // If we're just setting a variable to a value, we copy the value in
            JitValue::Frozen { .. } | JitValue::Const(_) | JitValue::Ref(_,_) => {
                // XXX: this can't just do this. [rax+8] = frozen needs to
                // freeze some constant memory map we keep as well.
                //unimplemented!("fix this");
                self.context.bound.entry(key).insert(JitVariable::Known(val));
            },
            // If we're setting a v
            JitValue::Value(val) => {
                match loc {
                    // rax = val becomes a redefine for the register
                    Operand::Register(_)
                    // [rsp] = val becomes a redefine for the current stack
                    | Operand::RegDeref(STACK)
                    // [rsp-8] = val becomes a redefine for the stack slot
                    | Operand::RegDisp(STACK, _) => {
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
                        // [rax] = val becomes a store to the contents of register
                        let reg_val = self.get(key)
                            .val(self.builder).into_ssa(self.int, self.builder);
                        self.builder.ins().store(MemFlags::new(), val, reg_val, 0);
                    },
                    Operand::RegDisp(r, o) => {
                        let reg_val = self.get(key)
                            .val(self.builder).into_ssa(self.int, self.builder);
                        self.builder.ins().store(MemFlags::new(), val, reg_val, o);
                    },
                    _ => unimplemented!("store for {} ({:?}) = {:?}", loc, loc, val)
                }
            },
            _ => unimplemented!("unknown store for {:?}", val),
        }
    }

    /// Get left+right for JitValues. Treats `left` as a distinct memory region
    /// if it is frozen: `left+8` gives back a 
    pub fn add(&mut self, left: JitValue, right: JitValue) -> JitValue {
        // XXX: set flags
        use JitValue::*;
        match (left, right) {
            // add rsp, 0x8 becomes a redefine of rsp with offset -= 1
            (Value(val_left), Value(val_right)) => {
                Value(self.builder.ins().iadd(val_left, val_right))
            },
            (ref_val @ Ref(_,_), Value(ssa))
            | (Value(ssa), ref_val @ Ref(_,_)) => {
                let v_ptr = ref_val.into_ssa(self.int, self.builder);
                Value(self.builder.ins().iadd(v_ptr, ssa))
            },
            (Ref(base, offset), Const(c))
            | (Const(c), Ref(base, offset)) => {
                Ref(base, (Wrapping(offset) + c).0)
            },
            (Const(left_c), Const(right_c)) => {
                Const(left_c + right_c)
            },
            (left, right) => unimplemented!("unimplemented add {:?} {:?}", left, right)
        }
    }

    pub fn sub(&mut self, left: JitValue, right: JitValue) -> JitValue {
        // XXX: set flags
        use JitValue::*;
        match (left, right) {
            // add rsp, 0x8 becomes a redefine of rsp with offset -= 1
            (Value(val_left), Value(val_right)) => {
                Value(self.builder.ins().isub(val_left, val_right))
            },
            (ref_val @ Ref(_,_), Value(ssa))
            | (Value(ssa), ref_val @ Ref(_,_)) => {
                let v_ptr = ref_val.into_ssa(self.int, self.builder);
                Value(self.builder.ins().isub(v_ptr, ssa))
            },
            (Ref(base, offset), Const(c))
            | (Const(c), Ref(base, offset)) => {
                Ref(base, (Wrapping(offset) - c).0)
            },
            (Const(left_c), Const(right_c)) => {
                Const(left_c - right_c)
            },
            (left, right) => unimplemented!("unimplemented sub {:?} {:?}", left, right)
        }
    }

}


