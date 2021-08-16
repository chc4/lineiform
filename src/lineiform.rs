#[deny(bare_trait_objects)]
use yaxpeax_x86::long_mode::{Operand, Instruction, RegSpec, Opcode};
use std::collections::HashMap;
use core::marker::PhantomData;
use std::sync::Arc;
use std::rc::Rc;
use core::num::Wrapping;
use crate::lift::JitValue;

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

use core::ffi::c_void;
#[derive(Copy, Clone)]
struct FastFn<A, O> {
    f: extern "C" fn(usize, data: *const c_void, A)->O,
}

impl<A, O> FnOnce<A> for FastFn<A, O> {
    type Output=O;
    extern "rust-call" fn call_once(self, args: A) -> O {
        unimplemented!();
    }
}

impl<A, O> FnMut<A> for FastFn<A, O> where FastFn<A, O>: FnOnce<A> {
    extern "rust-call" fn call_mut(&mut self, args: A) -> <FastFn<A,O> as FnOnce<A>>::Output {
        unimplemented!();
    }
}

use core::hint::black_box;
#[inline(never)]
#[no_mangle]
pub extern "C" fn break_here(a: usize) -> usize {
    black_box(a)
}

impl<A: std::fmt::Debug,O> Fn<A> for FastFn<A, O> where
    FastFn<A, O>: FnOnce<A, Output=O>,
{
    extern "rust-call" fn call(&self, args: A) -> <Self as FnOnce<A>>::Output {
        println!("got arguments: {:?}", args);
        black_box(break_here(black_box(1)));
        (self.f)(0, self as *const Self as *const c_void, args)
    }
}

use crate::Jit;
use crate::Tracer;
use crate::Function;
pub struct Lineiform<A, O> {
    decompiled: HashMap<*const (), Arc<Vec<Instruction>>>,
    _phantom: PhantomData<fn(A)->O>,
    tracer: Tracer<'static>,
}

impl<A: std::fmt::Debug, O> Lineiform<A, O> {
    type JitFn = fn(A) -> O;
    pub fn new() -> Self {
        Self {
            tracer: Tracer::new().unwrap(),
            decompiled: HashMap::new(),
            _phantom: PhantomData,
        }
    }

    pub fn speedup<F>(&mut self, f: F) -> impl Fn(A)->O where F: Fn(A)->O {
        // We are given a [data, trait] fat pointer for f.
        // We want to feed c_fn into our lifter, calling F::call as arg 1, with
        // data as our argument 2.
        let call: for <'a> extern "rust-call" fn(&'a F, (A,))->O = <F as Fn<(A,)>>::call;
        let f_body = &f as *const _ as *const c_void;
        let call: extern fn(data: *const c_void, A)->O =
            unsafe { std::mem::transmute(call) };
        // We now compile c_fn(call, f_body, a: A) to a function that can throw
        // away call and f_body.
        use crate::lift::Location;
        let mut func = Function::<A, O>::new(&mut self.tracer, c_fn::<A,O> as *const ())
            .unwrap()
            .assume_args(vec![
                (Location::Reg(RegSpec::rdi()), JitValue::Const(Wrapping(call as usize))),
                (Location::Reg(RegSpec::rsi()), JitValue::Ref(
                        Rc::new(JitValue::Frozen {
                            addr: &f as *const _ as *const u8,
                            size: std::mem::size_of_val(&f),
                        }), 0)
                ),
            ]);
        let mut inlined = Jit::lift(&mut self.tracer, func);
        //inlined.assume(vec![call as *const u8, f_body as *const u8]);
        let (inlined, _size) = inlined.lower().unwrap();

        if true {
            let new_func_dis = self.tracer.disassemble(inlined as *const (), _size as usize).unwrap();
            println!("recompiled function:");
            self.tracer.format(&new_func_dis).unwrap();
        }

        // TODO: cache this? idk what our key is
        std::mem::forget(f); // don't run destructor for the closure
        FastFn { f: unsafe { std::mem::transmute(inlined) } }
    }
}
