use crate::tracer::{self, Tracer};
use std::sync::Arc;
use yaxpeax_x86::long_mode::Instruction;
use yaxpeax_x86::long_mode::RegSpec;
use crate::lift::JitValue;
use std::num::Wrapping;

use std::ffi::c_void;
use std::marker::PhantomData;
use crate::lift::Location;
pub struct Function<ARG, OUT> {
    pub base: *const (),
    /// Our offset from function base to wanted IP. (bytes, instructions)
    pub offset: (usize, usize),
    pub size: usize,
    pub instructions: Arc<Vec<Instruction>>,
    pub pinned: Arc<Vec<(Location, JitValue)>>,
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
    pub fn assume_args(mut self, pinning: Vec<(Location, JitValue)>) -> Self {
        self.pinned = Arc::new(pinning);
        self
    }

    pub fn new(tracer: &mut Tracer, f: *const ()) -> Result<Self, BlockError> {
        let base = tracer.get_base()?;
        let f_sym = tracer.get_symbol_from_address(f)?;
        // Our address could be in the middle of a function - we want to disassemble
        // from the start so that we can cache disassembly, and so that when we
        // are emitting from it we have the entire function for backwards jmp analysis
        let f_base = (base + (f_sym.st_value as usize));
        let f_off = (f as usize) - f_base;
        let instructions = tracer.disassemble(f_base as *const (), f_sym.st_size as usize)?;
        let mut inst_off = 0;
        let mut inst_addr = f_base;
        // unfortunately, due to x86 having irregular instruction widths, we can't
        // easily turn bytes offset -> instruction stream offset.
        // maybe we can put this in a cache as well? or at least have some skiplist
        // like structure.
        use crate::yaxpeax_arch::LengthedInstruction;
        for inst in instructions.iter() {
            if inst_addr == (f as usize) {
                break;
            } else if inst_addr > (f as usize) {
                panic!("trying to create a function for {:x} overshot! is it unaligned inside {:x}?", f as usize, f_base);
            } else {
                inst_off += 1;
                inst_addr += inst.len().to_const() as usize;
            }
        }
        Ok(Self {
            base: f_base as *const (),
            offset: (f_off, inst_off),
            size: f_sym.st_size as usize,
            instructions: instructions,
            pinned: Arc::new(Vec::new()),
            _phantom: PhantomData,
        })
    }
}
