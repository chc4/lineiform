#![allow(unused_imports)]
#![feature(box_syntax, box_patterns)]
extern crate nom;
extern crate jemallocator;
extern crate thiserror;
#[macro_use]
extern crate enum_display_derive;
use thiserror::Error;
use std::fmt::Display;

mod parser;
use parser::parse_expr;
mod closure;
use closure::{CompileError, EvalError, compile_expr, generate_closure};

use std::collections::HashMap;

#[derive(Error, Debug)]
enum MainError {
    #[error("failed to compile: {0}")]
    Compile(#[from] CompileError),
    #[error("failed to evaluate: {0}")]
    Eval(#[from] EvalError),
}


fn main() -> Result<(), MainError> {
    println!("Hello, world!");
    let (s, sexpr) = parse_expr("(+ 1 (+ 2 3))")
        .map_err(|e| MainError::Compile(CompileError::Parse(format!("{}", e).into())))?;
    println!("{:?}", sexpr);
    let clos = generate_closure(sexpr)?;
    let mut env = closure::Env {
        variables: HashMap::new()
    };
    println!("clos: {:?}", clos(&mut env)?);

    Ok(())
}
