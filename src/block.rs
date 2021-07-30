use crate::tracer::{self, Tracer};
use iced_x86::Instruction;
use std::sync::Arc;

pub enum VariableValue {
    u8(u8),
    u16(u16),
    u32(u32),
    u64(u64),
    Renumber(usize),
}

pub enum Value {
    Variable(VariableValue),
    Const(usize),
}

pub enum LiftedInstruction {
    Native(Instruction), /// Any instruction we aren't able to lift to a better form
    Mov { dest: Value, src: Value }, /// dest <- src
    Add { dest: Value, src: Value }, /// dest += src
    Call(Value),
    Ret,
}

use std::ffi::c_void;
extern "C" fn c_fn<A, O>(
    cb: fn(data: *const c_void, A)->O, 
    d: *const c_void,
    a: A,
) -> O {
    cb(d, a)
}

pub fn foo<A, O, F: Fn(A)->O>(callback: F, args: (A,)) {
    let c: for <'a> extern "rust-call" fn(&'a F, (A,))->O = <F as Fn<(A,)>>::call;
    unsafe {
        c_fn(
            std::mem::transmute(c),
            &callback as *const _ as *const c_void,
            args
        )
    }
}

pub struct Function<ARG, OUT> {
    pub base: fn(data: *const c_void, ARG)->OUT,
    pub size: usize,
    pub instructions: Arc<Vec<Instruction>>,
}

use thiserror::Error;
#[derive(Error, Debug)]
pub enum BlockError {
    #[error("decompilation error")]
    Decompile(#[from] tracer::TracerError),
}

impl<A, O> Function<A, O> {
    /// Create a new function via disassembling a function pointer
    pub fn new<F: Fn(A)->O>(tracer: &mut Tracer, f: F) -> Result<Self, BlockError> {
        let c: for<'a> extern "rust-call" fn(&'a F, (A,))->O = <F as Fn<(A,)>>::call;
        let f_sym = tracer.get_symbol_from_address(c as *const ())?;
        let instructions = tracer.disassemble(c as *const())?;
        Ok(Self {
            base: unsafe { std::mem::transmute(c) },
            size: f_sym.st_size as usize,
            instructions: instructions,
        })
    }
}
