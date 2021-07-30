#![allow(unused_imports)]
#![feature(box_syntax, box_patterns, trait_alias, unboxed_closures, fn_traits, ptr_metadata, stmt_expr_attributes, entry_insert, map_try_insert, if_let_guard, bench_black_box)]
extern crate nom;
extern crate jemallocator;
extern crate thiserror;
#[macro_use]
extern crate enum_display_derive;
extern crate iced_x86;
extern crate goblin;
extern crate cranelift;
extern crate cranelift_jit;
extern crate cranelift_codegen;
use thiserror::Error;
use std::fmt::Display;

mod parser;
use parser::parse_expr;
mod closure;
use closure::{CompileError, EvalError, compile_expr, generate_closure};
mod tracer;
use tracer::{Tracer, TracerError};
mod block;
use block::{Function, BlockError};
mod lift;
use lift::{State, Jit};

use std::collections::HashMap;

#[derive(Error, Debug)]
enum MainError {
    #[error("failed to compile: {0}")]
    Compile(#[from] CompileError),
    #[error("failed to evaluate: {0}")]
    Eval(#[from] EvalError),
    #[error("tracer error: {0}")]
    Tracer(#[from] TracerError),
    #[error("block lifting error: {0}")]
    Block(#[from] BlockError),
}


fn main() -> Result<(), MainError> {
    println!("Hello, world!");
    let mut f = std::fs::File::open("/proc/self/maps").unwrap();
    let out = std::io::stdout();
    std::io::copy(&mut f, &mut out.lock()).unwrap();

    let (s, sexpr) = parse_expr("(+ 1 (+ 2 3))")
        .map_err(|e| MainError::Compile(CompileError::Parse(format!("{}", e).into())))?;
    println!("{:?}", sexpr);
    let clos = generate_closure(sexpr.clone())?;
    let mut env = closure::Env {
        variables: HashMap::new()
    };
//    println!("clos ptr: 0x{:?}", closure::get_ptr_from_closure(&clos));
//    let clos2 = compile_expr("(* 2 6)")?;
//    println!("clos ptr: 0x{:?}", closure::get_ptr_from_closure(&clos2));
//    println!("clos: {:?}", clos(&mut env)?);
//    println!("clos: {:?}", clos2(&mut env)?);

    let mut tracer = Tracer::new()?;
    use closure::ClosureFn;
    let mut func = Function::new(&mut tracer, &clos)?;
    println!("base @ {:x}", func.base as usize);
    tracer.format(&func.instructions);

    let jitted = Jit::lift(func);
    jitted.format();
    let new_func = jitted.lower();

    Ok(())
}
