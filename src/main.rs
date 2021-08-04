#![allow(unused_imports)]
#![deny(unused_must_use, improper_ctypes_definitions)]
#![feature(box_syntax, box_patterns, trait_alias, unboxed_closures, fn_traits, ptr_metadata, stmt_expr_attributes, entry_insert, map_try_insert, if_let_guard, bench_black_box, inline_const, inherent_associated_types, associated_type_bounds)]
//extern crate nom;
extern crate jemallocator;
extern crate thiserror;
#[macro_use]
extern crate enum_display_derive;
extern crate yaxpeax_arch;
extern crate yaxpeax_x86;
extern crate goblin;
extern crate cranelift;
extern crate cranelift_jit;
extern crate cranelift_codegen;
extern crate target_lexicon;
use thiserror::Error;
use std::fmt::Display;

//mod parser;
//use parser::parse_expr;
//mod closure;
//use closure::{CompileError, EvalError, compile_expr, generate_closure};
mod tracer;
use tracer::{Tracer, TracerError};
mod block;
use block::{Function, BlockError};
mod lift;
use lift::{Jit, LiftError};
mod lineiform;
use lineiform::{Lineiform};

use std::collections::HashMap;

#[derive(Error, Debug)]
enum MainError {
    //#[error("failed to compile: {0}")]
    //Compile(#[from] CompileError),
    //#[error("failed to evaluate: {0}")]
    //Eval(#[from] EvalError),
    #[error("tracer error: {0}")]
    Tracer(#[from] TracerError),
    #[error("block lifting error: {0}")]
    Block(#[from] BlockError),
    #[error("lifting error: {0}")]
    Lift(#[from] LiftError),
}


use core::hint::black_box;
fn main() -> Result<(), MainError> {
    println!("Hello, world!");
    let mut f = std::fs::File::open("/proc/self/maps").unwrap();
    let out = std::io::stdout();
    std::io::copy(&mut f, &mut out.lock()).unwrap();

//    let (s, sexpr) = parse_expr("(+ 1 (+ 2 3))")
//        .map_err(|e| MainError::Compile(CompileError::Parse(format!("{}", e).into())))?;
//    println!("{:?}", sexpr);
//    let clos = generate_closure(sexpr.clone())?;
//    let mut env = closure::Env {
//        variables: HashMap::new()
//    };
//    println!("clos ptr: 0x{:?}", closure::get_ptr_from_closure(&clos));
//    let clos2 = compile_expr("(* 2 6)")?;
//    println!("clos ptr: 0x{:?}", closure::get_ptr_from_closure(&clos2));
//    println!("clos: {:?}", clos(&mut env)?);
//    println!("clos: {:?}", clos2(&mut env)?);

    pub trait TestFn = Fn(usize) -> usize;
    pub(crate) type TestExpr = Box<
        dyn TestFn + Send + Sync,
    >;
    use core::cell::RefCell;
    use core::cell::Cell;
    use std::sync::Arc;
    let one: TestExpr = box move |e: usize| {
        if black_box(true) == true { 1 } else { 0 }
    };
    let mut jit = Lineiform::new();
    let five: TestExpr = box jit.speedup(move |e: usize| {
        let mut acc = e;
        for i in 0..5 {
            acc += one(e);
        }
        return acc;
    });
    let eval = five(0);
    assert_eq!(eval, 5);
    let eval2 = five(1);
    assert_eq!(eval2, 6);

    Ok(())
}

fn test_jit() -> Result<(), MainError> {
    let mut tracer = Tracer::new()?;
    //use closure::ClosureFn;
    //let mut func = Function::from_fn(&mut tracer, &clos)?;
    use core::num::Wrapping;
    #[repr(C)]
    #[derive(Debug, PartialEq)]
    struct Oversized {
        a: Wrapping<usize>,
        b: Wrapping<usize>,
        c: Wrapping<usize>
    }
    extern "C" fn testcase(n: Wrapping<usize>) -> Oversized {
        Oversized {
            a: black_box(n + Wrapping(1)) + Wrapping(2),
            b: n,
            c: n + Wrapping(15)
        }
    }

    let mut func = Function::<usize, usize>::new(&mut tracer, testcase as *const ())?;
    println!("base @ {:x}", func.base as usize);
    tracer.format(&func.instructions)?;

    let mut jitted = Jit::lift(func);
    //
    jitted.format();
    let (new_func, new_size) = jitted.lower()?;
    let new_func_dis = tracer.disassemble(new_func as *const (), new_size as usize)?;
    println!("recompiled function:");
    tracer.format(&new_func_dis)?;
    let callable: extern "C" fn(Wrapping<usize>) -> Oversized =
        unsafe { core::mem::transmute(new_func) };
    assert_eq!(testcase(Wrapping(5)), callable(Wrapping(5)));

    Ok(())
}
