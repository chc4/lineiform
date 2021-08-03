#![allow(unused_imports)]
#![deny(unused_must_use)]
#![feature(box_syntax, box_patterns, trait_alias, unboxed_closures, fn_traits, ptr_metadata, stmt_expr_attributes, entry_insert, map_try_insert, if_let_guard, bench_black_box, inline_const)]
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

    let mut tracer = Tracer::new()?;
    //use closure::ClosureFn;
    //let mut func = Function::from_fn(&mut tracer, &clos)?;
    use core::num::Wrapping;
    use core::hint::black_box;
    extern "C" fn testcase(n: Wrapping<usize>) -> Wrapping<usize> {
        black_box(n + Wrapping(1)) + Wrapping(2)
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

    Ok(())
}
