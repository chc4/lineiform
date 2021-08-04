use crate::tracer::{self, Tracer};

use cranelift::prelude::*;
use cranelift_jit::{JITBuilder, JITModule};
use cranelift_module::{DataContext, Linkage, Module};
use crate::block::{Function};
use cranelift_codegen::ir::types::Type;

use yaxpeax_x86::long_mode::{Operand, Instruction, RegSpec, Opcode};

use std::collections::HashMap;
use std::convert::TryInto;

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

struct Context {
    bound: HashMap<Location, Variable>,
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
        let mut variables = Self::make_variables(&mut builder, &mut idx, entry_block, &self.argument_layout);
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
        function_translator.builder.finalize();
        Ok(())
    }

    fn make_variables<'a>(builder: &mut FunctionBuilder<'a>, idx: &mut usize, entry_block: Block,
        arg_vars: &Vec<Type>) -> Context
    {
        let args = HOST.arguments.iter().enumerate()
            .map(|(i, arg)| {
                println!("adding argument {:?}", arg);
                let val = builder.block_params(entry_block)[i];
                let var = Variable::new(*idx);
                *idx = *idx + 1;
                builder.declare_var(var, arg_vars[i]);
                builder.def_var(var, val);
                //builder.set_val_label(val, format!("{}", arg));
                (arg.clone(), var)
            }).collect::<HashMap<_,_>>();
        Context {
            bound: args,
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
        match inst.opcode() {
            Opcode::MOV => {
                let val = self.resolve(inst.operand(1));
                self.store(inst.operand(0), val);
                Ok(())
            },
            Opcode::INC => {
                // TODO: set flags
                let val = self.resolve(inst.operand(0));
                let one = self.builder.ins().iconst(self.int, 1);
                let inced = self.builder.ins().iadd(val, one);
                self.store(inst.operand(0), inced);
                Ok(())
            },
            Opcode::ADD => {
                // TODO: set flags
                let left = self.resolve(inst.operand(0));
                let right = self.resolve(inst.operand(1));
                let added = self.builder.ins().iadd(left, right);
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
                let val = self.resolve(inst.operand(0)); // get eax
                let sp = self.get(Location::Stack(self.stack_idx)); // [rsp]
                self.builder.def_var(sp, val); // [rsp] = eax
                self.stack_idx += 1; // rsp++
                Ok(())
            },
            Opcode::POP => {
                // pop eax
                let sp = self.get(Location::Stack(self.stack_idx)); // [rsp]
                let sp = self.builder.use_var(sp);
                self.store(inst.operand(0), sp); // eax = [rsp]
                self.stack_idx -= 1; // rsp--
                Ok(())
            },
            Opcode::RETURN => {
                let return_values: Vec<Value> = HOST.outputs.iter().map(|r_val| {
                    let var = self.get(r_val.clone());
                    self.builder.use_var(var)
                }).collect();
                self.builder.ins().return_(&return_values[..]);
                Ok(())
            },
            _ => {
                Err(LiftError::UnimplementedInst(inst.clone()))
            }
        }
    }

    fn effective_address(&mut self, loc: Operand) -> Result<Value, LiftError> {
        println!("lea of {}", loc);
        match loc {
            Operand::RegDeref(r) => {
                unimplemented!();
            },
            Operand::RegDisp(r, disp) => {
                let reg = self.get(Location::Reg(r));
                let reg_use = self.builder.use_var(reg);
                let disp = self.builder.ins().iconst(self.int, i64::from(disp));
                Ok(self.builder.ins().iadd(reg_use, disp))
            }
            _ => unimplemented!()
        }
    }

    pub fn get(&mut self, loc: Location) -> Variable {
        // If we didn't already have the register bound to a variable,
        // create a fresh one and return it.
        let idx = &mut self.idx;
        let builder = &mut self.builder;
        let int = self.int;
        *self.context.bound.entry(loc).or_insert_with(|| {
            let fresh = Variable::new(**idx);
            **idx = **idx + 1;
            // FIXME: registers should be the correct width
            builder.declare_var(fresh, int);
            fresh.clone()
        })
    }

    /// Resolve an instruction operand into an SSA value.
    /// If we have `mov eax, ecx`, we want to resolve ecx to either a use of the
    /// existing ecx variable in our context, or create a new one and use that.
    /// This has to handle *all* operand types, however: if there's an `[ecx]` we need
    /// to emit a deref instruction and return the value result of that as well.
    pub fn resolve(&mut self, loc: Operand) -> Value {
        match loc {
            Operand::Register(r) => {
                let reg = self.get(Location::Reg(r));
                self.builder.use_var(reg)
            },
            Operand::RegDeref(const { RegSpec::rsp() }) => {
                let sp = self.get(Location::Stack(self.stack_idx));
                self.builder.use_var(sp)
            },
            Operand::ImmediateI8(c) => {
                let c = self.builder.ins().iconst(self.int, i64::from(c));
                c
            },
            _ => unimplemented!("resolve for {:?}", loc)
        }
    }

    pub fn store(&mut self, loc: Operand, val: Value) {
        match loc {
            Operand::Register(r) => {
                let reg = self.get(Location::Reg(r));
                self.builder.def_var(reg, val)
            },
            Operand::RegDeref(const { RegSpec::rsp() }) => {
                let sp = self.get(Location::Stack(self.stack_idx));
                self.builder.def_var(sp, val)
            }
            Operand::RegDisp(const { RegSpec::rsp() }, o) => {
                // We turn [rsp-8] into Stack(stack_idx - 1) - we count
                // stack slots up from 0.
                assert_eq!(o <= 0, true); // Make sure it's negative
                assert_eq!(o % 8, 0); // Make sure it aligns
                let stack_off: usize = (o.unsigned_abs() / 8).try_into().unwrap();
                let sp = self.get(Location::Stack(self.stack_idx - stack_off));
                self.builder.def_var(sp, val)
            }
            Operand::RegDeref(const { RegSpec::esp() } | const { RegSpec::sp() })
            | Operand::RegDisp(const { RegSpec::esp() } | const { RegSpec::sp()}, _) => {
                unimplemented!("non-native stack size");
            },
            Operand::RegDeref(r) => {
                let reg = self.get(Location::Reg(r));
                let reg_val = self.builder.use_var(reg);
                self.builder.ins().store(MemFlags::new(), val, reg_val, 0);
            },
            Operand::RegDisp(r, o) => {
                let reg = self.get(Location::Reg(r));
                let reg_val = self.builder.use_var(reg);
                self.builder.ins().store(MemFlags::new(), val, reg_val, o);
            },
            _ => unimplemented!("store for {} ({:?}) = {:?}", loc, loc, val)
        }
    }


}
