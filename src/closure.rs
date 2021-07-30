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

    fn need_keyword(&mut self) -> Result<String, EvalError> {
        match self {
            Atom::Keyword(u) => Ok(u.to_string()),
            v => Err(EvalError::TypeError("keyword", v._type()))
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
    #[error("the variable {0} would shadow")]
    Shadow(String),
    #[error("the variable {0} is unbound at the unsite")]
    Unbound(String),
    #[error("wanted type `{0}`, got `{1}`")]
    TypeError(&'static str, &'static str),
    #[error("runtime panic {0}")]
    Panic(&'static str),
}

pub struct Env {
    pub variables: HashMap<String, Atom>,
}

impl Env {
    fn new() -> Self {
        Self {
            variables: HashMap::new()
        }
    }
}

pub trait ClosureFn = for<'a> Fn(&mut Env) -> Result<Atom, EvalError>;
type ClosureFnPtr = *const (); // fn(&Self, &mut Env<'a>) -> Result<Atom, EvalError>
pub(crate) type ClosureExpr = Box<
    dyn ClosureFn + Send + Sync,
>;

use core::ptr::*;
use core::ptr::DynMetadata;
use core::mem;
use core::ptr;
pub fn get_ptr_from_closure<T: ClosureFn>(f: &T) -> usize {
    let fn_call = <T>::call_once;
    let (addr, meta) = (&*f as &dyn ClosureFn as *const dyn ClosureFn).to_raw_parts();
    #[derive(Debug)]
    #[repr(C)]
    struct RawMeta {
        vtable: &'static [usize;4]
    }
    unsafe {
        let vtable = mem::transmute::<_, RawMeta>(addr);
        println!("meta = {:x?}", vtable.vtable[1]);
        let methods = mem::transmute::<_, RawMeta>(vtable.vtable[1]);
        println!("virtual functions: {:x?}", methods);
        let call = methods.vtable[3];
        println!("closure body: {:x}", call);
    }
    let fn_call_as_ptr = fn_call as usize;
    println!("fn_call addr = 0x{:x}", fn_call_as_ptr);
    fn_call_as_ptr
}

#[derive(thiserror::Error, Debug)]
pub enum CompileError {
    #[error("nom parsing error {0}")]
    Parse(String),
    #[error("too few arguments to {0}: wanted {1}, got {2}")]
    TooFew(BuiltIn, usize, usize),
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
        Expr::IfElse(cond, t, f) => {
            let cond = generate_closure(*cond)?;
            let t = generate_closure(*t)?;
            let f = generate_closure(*f)?;
            Ok(box move |e| {
                if cond(e)?.need_int()? == 0 {
                    f(e)
                } else {
                    t(e)
                }
            })
        },
        Expr::Application(op, mut args) => {
            match op {
                box Expr::Constant(Atom::BuiltIn(opcode)) => match opcode {
                    BuiltIn::Equal => {
                        if let [x, y] = args.as_slice() {
                            let x = generate_closure(x.clone())?;
                            let y = generate_closure(y.clone())?;
                            Ok(box move |e| {
                                Ok(Atom::Num(
                                        if x(e)?.need_int()? == y(e)?.need_int()? {
                                            1
                                        } else {
                                            0
                                        }
                                ))
                            })
                        } else {
                            Err(CompileError::TooFew(opcode, 2, args.len()))
                        }
                    },
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
                    BuiltIn::Times => {
                        if let [x, y] = args.as_slice() {
                            let x = generate_closure(x.clone())?;
                            let y = generate_closure(y.clone())?;
                            Ok(box move |e| {
                                Ok(Atom::Num(
                                        x(e)?.need_int()? * y(e)?.need_int()?
                                ))
                            })
                        } else {
                            Err(CompileError::TooFew(opcode, 2, args.len()))
                        }
                    },
                    BuiltIn::Let => {
                        if let [name, val, cont] = args.as_slice() {
                            let name = generate_closure(name.clone())?;
                            let val = generate_closure(val.clone())?;
                            let cont = generate_closure(cont.clone())?;
                            Ok(box move |e| {
                                let conc_name = &*name(e)?.need_keyword()?;
                                let conc_value = val(e)?;
                                e.variables.try_insert(conc_name.to_string(), conc_value).map_err(|e| EvalError::Shadow(conc_name.to_string()))?;
                                let r =  cont(e);
                                e.variables.remove(conc_name);
                                r
                            })
                        } else {
                            Err(CompileError::TooFew(opcode, 3, args.len()))
                        }
                    },
                    BuiltIn::Set => {
                        if let [name, val] = args.as_slice() {
                            let name = generate_closure(name.clone())?;
                            let val = generate_closure(val.clone())?;
                            Ok(box move |e| {
                                let conc_name = &*name(e)?.need_keyword()?;
                                let conc_value = val(e)?;
                                let entry = e.variables.entry(conc_name.to_string());
                                if let std::collections::hash_map::Entry::Vacant(_) = entry {
                                    Err(EvalError::Unbound(conc_name.to_string()))
                                } else {
                                    entry.and_modify(|v| *v = conc_value.clone());
                                    Ok(conc_value)
                                }
                            })
                        } else {
                            Err(CompileError::TooFew(opcode, 3, args.len()))
                        }
                    },
                    BuiltIn::Get => {
                        if let [name] = args.as_slice() {
                            let name = generate_closure(name.clone())?;
                            Ok(box move |e| {
                                let conc_name = &*name(e)?.need_keyword()?;
                                e.variables.get(&conc_name.to_string())
                                    .map(|v| Ok(v.clone()))
                                    .unwrap_or_else(|| Err(EvalError::Unbound(conc_name.to_string())))
                            })
                        } else {
                            Err(CompileError::TooFew(opcode, 1, args.len()))
                        }
                    },
                    BuiltIn::Do => {
                        let mut comp_args = args.drain(..).map(|v| generate_closure(v) )
                            .collect::<Result<Vec<ClosureExpr>, _>>()?;
                        Ok(box move |e| {
                            Ok(comp_args.iter().try_fold(Atom::Unit, |i, v| v(e))?)
                        })
                    },
                    BuiltIn::Loop => {
                        if let [times, body] = args.as_slice() {
                            let times = generate_closure(times.clone())?;
                            let body = generate_closure(body.clone())?;
                            Ok(box move |e| {
                                let times = times(e)?.need_int()?;
                                let mut v = Atom::Unit;
                                for i in 0..times {
                                    v = body(e)?;
                                }
                                Ok(v)
                            })
                        } else {
                            Err(CompileError::TooFew(opcode, 2, args.len()))
                        }
                    },
                    _ => unimplemented!("unimplemented opcode {}", opcode)
                },
                _ => unimplemented!("unimplemented application type")
            }
        },
        u @ _ => unimplemented!("unimplemented: {:?}", u),
    }
}

#[cfg(test)]
mod test {
    use crate::*;
    use crate::parser::Atom;
    use crate::closure::Env;
    #[derive(Error, Debug)]
    enum TestError {
        #[error("failed to compile: {0}")]
        Compile(#[from] CompileError),
        #[error("failed to evaluate: {0}")]
        Eval(#[from] EvalError),
    }

    #[test]
    fn test_plus() -> Result<(), TestError> {
        assert_eq!(compile_expr("(+ 1 2)")?(&mut Env::new())?, Atom::Num(3));
        Ok(())
    }

    #[test]
    fn test_plus_eval() -> Result<(), TestError> {
        assert_eq!(compile_expr("(+ 1 (+ 2 3))")?(&mut Env::new())?, Atom::Num(6));
        Ok(())
    }

    #[test]
    fn test_let() -> Result<(), TestError> {
        assert_eq!(compile_expr("(let :x 1 2)")?(&mut Env::new())?, Atom::Num(2));
        Ok(())
    }

    #[test]
    fn test_get() -> Result<(), TestError> {
        assert_eq!(compile_expr("(let :x 1 (get :x))")?(&mut Env::new())?, Atom::Num(1));
        Ok(())
    }

    #[test]
    fn test_set() -> Result<(), TestError> {
        assert_eq!(compile_expr("(let :x 1 (do (set :x 2) (get :x)))")?(&mut Env::new())?, Atom::Num(2));
        Ok(())
    }

    #[test]
    fn test_factorial() -> Result<(), TestError> {
        assert_eq!(compile_expr("
        (let :acc 1
        (let :i 0
        (loop 10 (do
            (set :i (+ (get :i) 1))
            (if (= (get :i) 10)
                (get :acc)
            (set :acc (* (get :acc) (get :i))))
        ))))
        ")?(&mut Env::new())?, Atom::Num(2));
        Ok(())
    }
}
