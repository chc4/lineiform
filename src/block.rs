use crate::tracer::{self, Tracer};
use std::sync::Arc;
use yaxpeax_x86::long_mode::Instruction;

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

use std::ffi::c_void;
/// Rust closures are rust-call calling convention only. This is a problem, since
/// we want to lift them to Cranelift, and we don't know what registers are "live"
/// at the start and end. We instead make it so that making a Function from an Fn
/// actually starts the trace from the Trampoline call for the correct type,
/// with it's call being extern "C". Rustc then emits a stdcall -> rust-call
/// prologue and epilogue for us, which we can lift.
extern "C" fn c_fn<A, O>(
    cb: extern fn(data: *const c_void, A)->O, // "rust-call", but adding that ICEs
    d: *const c_void,
    a: A
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

use std::marker::PhantomData;
pub struct Function<ARG, OUT> {
    pub base: *const (),
    pub size: usize,
    pub instructions: Arc<Vec<Instruction>>,
    _phantom: PhantomData<(ARG, OUT)>, //fn(data: *const c_void, ARG)->OUT
}

use thiserror::Error;
#[derive(Error, Debug)]
pub enum BlockError {
    #[error("decompilation error")]
    Decompile(#[from] tracer::TracerError),
}

///! When we lift an Fn(A)->O closure, we actually lift c_fn::<A,O>, which takes
///the Fn::call variant for the closure, and a *const c_void closure object, along
///with a tuple of actual arguments.
///This is an extern C function, because we need a stable ABI - but making it
///extern C means that when we *lower* the function back down, we are emitting
///the extern C prototype function to call! Because if you are using this as
///a JIT for a closure generator compiler you need to return a *closure* for your
///function. E.g. `Lineiform::jit(box move |a: A| -> O { o }) -> Fn(A, Output=O)`
///Which means we need to have a Rust->SystemV->Rust ABI dance: we provide a
///rust-call interface, which calls our extern C tracing trampoline/lift result,
///which calls whatever Rust closure body we inlined. We can at least hope that
///the last inlining reduces register waste.
///Maybe in the future Rust will allow for custom calling convention of closures,
///but the issue has ~0 traffic and no RFC, so I'm not holding my breath...
impl<A, O> Function<A, O> {
    /// Create a new function via disassembling an Fn trait object
    pub fn from_fn<F: Fn(A)->O>(tracer: &mut Tracer, f: F) -> Result<Self, BlockError> {
        // Get the trait method for calling a Fn of this type
        let c: for<'a> extern "rust-call" fn(&'a F, (A,))->O = <F as Fn<(A,)>>::call;
        let c: extern fn(data: *const c_void, A)->O = unsafe { std::mem::transmute(c) };
        //let base = unsafe { std::mem::transmute(c) };
        // We have to start tracing at the trampoline, since we need to be able
        // to lift the rust-call cconv prologue/epilogue.
        Function::new(tracer, c_fn::<A,O> as *const ())
            //.assume_args(vec![c, callback as *const _ as *const c_void]);
    }

    pub fn new(tracer: &mut Tracer, f: *const ()) -> Result<Self, BlockError> {
        let f_sym = tracer.get_symbol_from_address(f)?;
        let instructions = tracer.disassemble(f, f_sym.st_size as usize)?;
        Ok(Self {
            base: f,
            size: f_sym.st_size as usize,
            instructions: instructions,
            _phantom: PhantomData,
        })
    }
}
