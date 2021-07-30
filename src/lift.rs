use crate::tracer::{self, Tracer};
use crate::closure::ClosureFn;
use iced_x86::{Instruction, Register};

use cranelift::prelude::*;
use cranelift_jit::{JITBuilder, JITModule};
use cranelift_module::{DataContext, Linkage, Module};
use crate::block::{Function};

#[derive(Copy, Clone)]
pub enum Value {
    Unknown,
    Known(usize),
}
pub type Registers = [Value; 16];

pub struct State {
    registers: Registers,
    stack: Vec<u8>,
}

use thiserror::Error;
#[derive(Error, Debug)]
pub enum LiftError {
    #[error("unable to lift function")]
    Lifting,
}

impl State {
    pub fn new() -> Self {
        Self {
            registers: [Value::Unknown; 16],
            stack: vec![]
        }
    }

    pub fn load_ctx(&mut self) {

    }

    pub fn run<A, O: Fn<A>>(&mut self, f: fn(A) -> O, args: A) -> O {
        unimplemented!()
    }

    pub fn partial_evaluate<A, O>(&mut self, f: Function<A, O>)
        -> Result<Vec<Instruction>, LiftError>
    {
        Ok(vec![])
    }
}

pub struct Jit<A, O> {
    f: Function<A, O>,
    builder_context: FunctionBuilderContext,
    ctx: codegen::Context,
    data_ctx: DataContext,
    module: JITModule,
}

impl<A, O> Jit<A, O> {
    pub fn lift(f: Function<A, O>) -> Jit<A, O> {
        let builder = JITBuilder::new(cranelift_module::default_libcall_names());
        let module = JITModule::new(builder);
        Self {
            f: f,
            builder_context: FunctionBuilderContext::new(),
            ctx: module.make_context(),
            data_ctx: DataContext::new(),
            module,
        }
    }

    pub fn lower(&self) -> Function<A, O> {
        unimplemented!("lower")
    }

    pub fn format(&self) {
        //println!("{:?}", self.module);
    }
}
