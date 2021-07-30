use thiserror::Error;
use std::collections::HashMap;
use crate::parser::{Atom, BuiltIn, Expr, parse_expr};
use std::error::Error as StdError;

impl Atom {
    fn need_int(&mut self) -> Result<usize, EvalError> {
        match self {
            Atom::Num(u) => Ok(*u),
            v => Err(EvalError::TypeError("int", v._type()))
        }
    }

    fn _type(&self) -> &'static str {
        match self {
            Atom::Num(_) => "int",
            Atom::BuiltIn(_) => "builtin",
            _ => "unknown"
        }
    }
}

#[derive(thiserror::Error, Debug)]
pub enum EvalError {
    #[error("wanted type `{0}`, got `{1}`")]
    TypeError(&'static str, &'static str),
    #[error("runtime panic {0}")]
    Panic(&'static str),
}

pub struct Env<'a> {
    pub variables: HashMap<&'a str, Atom>
}

pub(crate) type ClosureExpr = Box<
    dyn for<'a> Fn(&mut Env<'a>) -> Result<Atom, EvalError> + Send + Sync,
>;

#[derive(thiserror::Error, Debug)]
pub enum CompileError {
    #[error("nom parsing error {0}")]
    Parse(String),
    #[error("too few arguments to {0}: wanted {1}, got {2}")]
    TooFew(BuiltIn, usize, usize),
    #[error("the variable {0} is unbound at the unsite")]
    Unbound(String),
    #[error("unknown data store error")]
    Unknown,
}
pub fn compile_expr(src: &str) -> Result<ClosureExpr, CompileError> {
  parse_expr(src)
    .map_err(|e| CompileError::Parse(format!("{}", e)))
    .and_then(|(_, exp)| generate_closure(exp))
}

pub fn generate_closure(e: Expr) -> Result<ClosureExpr, CompileError> {
    match e {
        Expr::Constant(a) => Ok(box move |e|{ Ok(a.clone()) }),
        Expr::Application(op, args) => {
            match op {
                box Expr::Constant(Atom::BuiltIn(opcode)) => match opcode {
                    BuiltIn::Plus => {
                        if let [x, y] = args.as_slice() {
                            let x = generate_closure(x.clone())?;
                            let y = generate_closure(y.clone())?;
                            Ok(box move |e| {
                                Ok(Atom::Num(
                                        x(e)?.need_int()? + y(e)?.need_int()?
                                ))
                            })
                        } else {
                            Err(CompileError::TooFew(opcode, 2, args.len()))
                        }
                    },
                    _ => unimplemented!("unimplemented opcode {}", opcode)
                },
                _ => unimplemented!("unimplemented application type")
            }
        }
        u @ _ => unimplemented!("unimplemented: {:?}", u),
    }
}
