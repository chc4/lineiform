use crate::tracer::{self, Tracer};

use cranelift::prelude::*;
use cranelift_jit::{JITBuilder, JITModule};
use cranelift_module::{DataContext, Linkage, Module};
use crate::block::{Function};
use cranelift_codegen::ir::types::Type;

use yaxpeax_x86::long_mode::{Operand, Instruction, RegSpec, Opcode};

use std::collections::HashMap;
use std::convert::{TryInto, TryFrom};

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
}

//impl State {
//    pub fn run<A, O: Fn<A>>(&mut self, f: fn(A) -> O, args: A) -> O {
//        unimplemented!()
//    }
//
//    pub fn partial_evaluate<A, O>(&mut self, f: Function<A, O>)
//        -> Result<Vec<Instruction>, LiftError>
//    {
//        Ok(vec![])
//    }
//}

/// We use these locations essentially as the keys of an x86 operand -> Cranelift
/// SSA variable map. When we create a function, we enter all the calling convention's
/// inputs into a store, and when we decode x86 and lift it we try and fetch the
/// "variable" that operand corrosponds to.
#[derive(Clone, Hash, PartialEq, Eq, Debug)]
pub enum Location {
    Reg(RegSpec),
    Stack(usize), // TODO: if we ever support x86_32, we need these
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
    Ref { base: Rc<JitValue>, offset: usize },
    /// A frozen memory region. We can inline values from it safely.
    Frozen { addr: *const u8, size: usize },
    /// A statically known value.
    Const(usize),
}

impl JitValue {
    /// Get a Cranelift SSA Value for this JitValue. Don't use this if you can
    /// help it, since it erases statically known values and harms optimizations.
    pub fn into_ssa(&self, int: Type, builder: &mut FunctionBuilder) -> Value {
        use JitValue::*;
        match self {
            Value(val) => val.clone(),
            Const(c) => {
                builder.ins().iconst(int, i64::try_from(*c as isize).unwrap())
            },
            Frozen { .. } => unimplemented!("into_ssa for frozen"),
            Ref { base, offset } => {
                match **base {
                    Value(_) => unimplemented!("ref to unsupported"),
                    Const(c) => unimplemented!("ref to const"), // XXX: constant pool
                    Frozen { addr, size } => {
                        builder.ins().iconst(int, i64::try_from(
                            ((addr as usize) + offset) as isize).unwrap()
                        )
                    },
                    Ref { .. } => unimplemented!("ref to ref unsupported"),
                }
            },
        }
    }
}

struct Context {
    // XXX: this probably can't only use Variable! if we pin a frozen environment,
    // we can only assume that the *direct* contents of that environment are
    // valid. This is because we can't ban interior mutability in the closed
    // environment - we will have a custom allocator that we will put the closures
    // in that mean that Mutex<usize> can't mutate the value without crashing,
    // but a Mutex<&usize> we have to make sure we don't inline env->&usize->1
    // and have it changed. We probably need an enum, and have a Frozen enum that
    // always dereferences to a NonFrozen variant, and only const prop Frozen.
    bound: HashMap<Location, JitVariable>,
}

pub struct Jit<A, O> {
    f: Function<A, O>,
    builder_context: FunctionBuilderContext,
    ctx: codegen::Context,
    data_ctx: DataContext,
    module: JITModule,
    argument_layout: Vec<Type>,
    return_layout: Vec<Type>,
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
        println!("register info {}", self.target_isa.register_info().display_regunit(0));
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

impl<A, O> Jit<A, O> {
    pub fn lift(f: Function<A, O>) -> Jit<A, O> {
        let builder = JITBuilder::new(cranelift_module::default_libcall_names());
        let module = JITModule::new(builder);

        let int = module.target_config().pointer_type();
        let ptr = Type::triple_pointer_type(&HOST.triple);

        let mut ctx = module.make_context();
        ctx.func.signature.call_conv = isa::CallConv::SystemV;
        let argument_layout = vec![ptr, ptr, int]; // hardcode self, int argument first
        for arg in argument_layout.clone() {
            ctx.func.signature.params.push(AbiParam::new(arg));
        }

        let return_layout = vec![int,int]; // hardcode int return type
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
        builder.seal_block(entry_block);

        let mut function_translator = FunctionTranslator {
            int,
            builder: &mut builder,
            context: variables,
            module: &mut self.module,
            idx: &mut idx,
            stack_idx: 0,
        };

        for inst in self.f.instructions.iter() {
            function_translator.emit(inst)?;
        }
        println!("jit output: \n{}", function_translator.builder.display(None));
        function_translator.builder.finalize();
        Ok(())
    }

    fn make_variables<'a>(builder: &mut FunctionBuilder<'a>, idx: &mut usize, entry_block: Block,
        int: Type, arg_vars: &Vec<Type>, pinned_values: &Vec<(Location, usize)>) -> Context
    {
        // First, we make a variable for all of our pinned locations containing
        // the fed-in value.
        let mut ctx: HashMap<Location, JitVariable> = HashMap::new();
        for pinned in pinned_values.iter() {
            println!("adding pinned value {:?} = {}", pinned.0, pinned.1);
            ctx.insert(pinned.0.clone(), JitVariable::Known(JitValue::Const(pinned.1)));
        }
        // Then, for all the arguments to the function, we create a variable for
        // the ABI register *unless* it has already been pinned.
        // If we pin argument 0 = 1234 in SystemV for example, we want to compile
        // a function with RDI *always* set to 1234, and throw away the actual
        // argument.
        for (i, arg) in HOST.arguments.iter().enumerate() {
            ctx.entry(arg.clone()).or_insert_with(|| {
                println!("adding argument {:?}", arg);
                let val = builder.block_params(entry_block)[i];
                let var = Variable::new(*idx);
                *idx = *idx + 1;
                builder.declare_var(var, arg_vars[i]);
                builder.def_var(var, val);
                JitVariable::Variable(var)
            });
        }
        Context {
            bound: ctx,
        }
    }

    pub fn lower(&mut self) -> Result<(*const u8, u32),LiftError> {
        self.translate()?;

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
    int: Type,
    builder: &'a mut FunctionBuilder<'a>,
    context: Context,
    module: &'a mut Module,
    idx: &'a mut usize,
    stack_idx: usize,
}

impl<'a> FunctionTranslator<'a> {
    fn emit(&mut self, inst: &Instruction) -> Result<(), LiftError> {
        println!("emitting for {}", inst);
        match inst.opcode() {
            Opcode::MOV => {
                let val = self.value(inst.operand(1));
                self.store(inst.operand(0), val);
                Ok(())
            },
            Opcode::INC => {
                // TODO: set flags
                let val = self.value(inst.operand(0));
                let inced = self.add(val, JitValue::Const(1));
                self.store(inst.operand(0), inced);
                Ok(())
            },
            Opcode::ADD => {
                // TODO: set flags
                let left = self.value(inst.operand(0));
                let right = self.value(inst.operand(1));
                let added = self.add(left, right);
                self.store(inst.operand(0), added);
                Ok(())
            },
            Opcode::LEA => {
                let val = self.effective_address(inst.operand(1))?;
                self.store(inst.operand(0), val);
                Ok(())
            },
            Opcode::PUSH => {
                // TODO: figure out if we need to tell cranelift to allocate a stack
                // slot? if we just symbolize the stack variable then jumping to
                // native code might not work.
                // push eax
                let val = self.value(inst.operand(0)); // get rax
                self.store(Operand::RegDeref(RegSpec::rsp()), val); // [rsp] = rax
                self.stack_idx += 1; // rsp++
                Ok(())
            },
            Opcode::POP => {
                // pop rax
                let sp = self.value(Operand::RegDeref(RegSpec::rsp())); // [rsp]
                self.store(inst.operand(0), sp); // rax = [rsp]
                self.stack_idx -= 1; // rsp--
                Ok(())
            },
            Opcode::RETURN => {
                let return_values: Vec<Value> = HOST.outputs.iter().map(|r_val| {
                    let mut var = self.get(r_val.clone());
                    var.val(self.builder).into_ssa(self.int, self.builder)
                }).collect();
                self.builder.ins().return_(&return_values[..]);
                Ok(())
            },
            _ => {
                Err(LiftError::UnimplementedInst(inst.clone()))
            }
        }
    }

    fn effective_address(&mut self, loc: Operand) -> Result<JitValue, LiftError> {
        println!("lea of {}", loc);
        match loc {
            Operand::RegDeref(r) => {
                unimplemented!();
            },
            Operand::RegDisp(r, disp) => {
                let reg = self.get(Location::Reg(r)).val(self.builder);
                Ok(self.add(reg, JitValue::Const(disp as u32 as usize)))
            }
            _ => unimplemented!()
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

    /// Resolve an instruction operand into JitValue.
    /// If we have `mov eax, ecx`, we want to resolve ecx to either a use of the
    /// existing ecx variable in our context, or create a new one and use that.
    /// This has to handle *all* operand types, however: if there's an `[ecx]` we need
    /// to emit a deref instruction and return the value result of that as well.
    pub fn value(&mut self, loc: Operand) -> JitValue {
        match loc {
            Operand::Register(r) => {
                self.get(Location::Reg(r)).val(self.builder)
            },
            Operand::RegDeref(const { RegSpec::rsp() }) => {
                self.get(Location::Stack(self.stack_idx)).val(self.builder)
            },
            Operand::ImmediateI8(c) => {
                JitValue::Const(c as u8 as usize)
            },
            _ => unimplemented!("value for {:?}", loc)
        }
    }

    pub fn store(&mut self, loc: Operand, val: JitValue) {
        // The key to look up for the operand in our context.
        let key = match loc {
            Operand::Register(r) => Location::Reg(r),
            Operand::RegDeref(const { RegSpec::rsp() }) => {
                Location::Stack(self.stack_idx)
            },
            Operand::RegDisp(const { RegSpec::rsp() }, o) => {
                // We turn [rsp-8] into Stack(stack_idx - 1) - we count
                // stack slots up from 0.
                assert_eq!(o <= 0, true); // Make sure it's negative
                assert_eq!(o % 8, 0); // Make sure it aligns
                let stack_off: usize = (o.unsigned_abs() / 8)
                    .try_into().unwrap();
                Location::Stack(self.stack_idx - stack_off)
            },
            Operand::RegDeref(r) => Location::Reg(r),
            Operand::RegDisp(r, o) => Location::Reg(r),
            _ => unimplemented!("unimplemented key for {:?}", loc),
        };
        match val {
            // If we're just setting a variable to a value, we copy the value in
            JitValue::Frozen { .. } | JitValue::Const(_) => {
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
                    | Operand::RegDeref(const { RegSpec::rsp() })
                    // [rsp-8] = val becomes a redefine for the stack slot
                    | Operand::RegDisp(const { RegSpec::rsp() }, _) => {
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
            (Value(val_left), Value(val_right)) => {
                Value(self.builder.ins().iadd(val_left, val_right))
            },
            (ref_val @ Ref { .. }, Value(ssa))
            | (Value(ssa), ref_val @ Ref { .. }) => {
                let v_ptr = ref_val.into_ssa(self.int, self.builder);
                Value(self.builder.ins().iadd(v_ptr, ssa))
            },
            (Ref { base, offset}, Const(c))
            | (Const(c), Ref { base, offset }) => {
                Ref { base: base, offset: offset + c }
            },
            (Const(left_c), Const(right_c)) => {
                Const(left_c + right_c)
            },
            (left, right) => unimplemented!("unimplemented add {:?} {:?}", left, right)
        }
    }
}
