#![allow(unused_imports, unused_parens)]
#![deny(unused_must_use, improper_ctypes_definitions)]
#![feature(box_syntax, box_patterns, trait_alias, unboxed_closures, fn_traits, ptr_metadata, stmt_expr_attributes, entry_insert, map_try_insert, if_let_guard, bench_black_box, inline_const, inherent_associated_types, associated_type_bounds, let_chains, asm, destructuring_assignment)]
//extern crate nom;
extern crate thiserror;
#[macro_use]
extern crate enum_display_derive;
extern crate yaxpeax_arch;
extern crate yaxpeax_x86;
extern crate goblin;
extern crate target_lexicon;
extern crate bitvec;
extern crate bitflags;
extern crate rangemap;

use thiserror::Error;
use std::fmt::Display;

//mod parser;
//use parser::parse_expr;
//mod closure;
//use closure::{CompileError, EvalError, compile_expr, generate_closure};
extern crate lineiform;
use lineiform::{Lineiform};
use lineiform::tracer::{Tracer, TracerError};
use lineiform::block::{Function, BlockError};
use lineiform::lift::{Jit, LiftError, Location, JitValue};

use std::collections::HashMap;

#[derive(Error, Debug)]
pub enum MainError {
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

    {
        let mut jit = crate::Lineiform::new();
        use core::hint::black_box;
        use core::num::Wrapping;
        let clos = jit.speedup(move |a: usize| {
            let val: usize;
            if a > 32 {
                val = (1 as usize);
            } else {
                val = (0 as usize);
            }
            val
        });
        assert_eq!(clos(0), 0);
        assert_eq!(clos(31), 0);
        assert_eq!(clos(32), 0);
        assert_eq!(clos(33), 1);
        return Ok(())
    }

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
    use std::sync::Arc;
    use std::sync::Mutex;
    let external = Arc::new(Mutex::new(1));
    let one: TestExpr = box move |e: usize| {
        if black_box(true) == true { 1 } else { 0 }
    };
    let five: TestExpr = box move |e: usize| {
        let mut acc = e;
        for i in 0..5 {
            acc += one(e);
        }
        return acc;
    };
    let eval = five(0);
    assert_eq!(eval, 5);
    let eval2 = five(1);
    assert_eq!(eval2, 6);

    use core::num::Wrapping;
    extern "C" fn test(a: Wrapping<usize>, b: Wrapping<usize>) -> Wrapping<usize> {
        a + Wrapping(2)
    }

    use yaxpeax_x86::long_mode::RegSpec;
    let mut tracer = Tracer::new()?;
    let assumed_test = Function::<(usize, usize), usize>::new(&mut tracer, test as *const ())?
        .assume_args(vec![(Location::Reg(RegSpec::rdi()), JitValue::Const(Wrapping(3)))]);
    let mut lifted = Jit::new(&mut tracer);
    let (lowered_test, size) = lifted.lower(assumed_test)?;
    unsafe {
        let jitted_pinned_test = std::mem::transmute::<_, extern "C" fn(usize, usize)->usize>(lowered_test);
        assert_eq!(jitted_pinned_test(1, 2), 5);
    }
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

    let mut jitted = Jit::new(&mut tracer);
    let (new_func, new_size) = jitted.lower(func)?;
    let new_func_dis = tracer.disassemble(new_func as *const (), new_size as usize)?;
    println!("recompiled function:");
    tracer.format(&new_func_dis)?;
    let callable: extern "C" fn(Wrapping<usize>) -> Oversized =
        unsafe { core::mem::transmute(new_func) };
    assert_eq!(testcase(Wrapping(5)), callable(Wrapping(5)));

    Ok(())
}

#[cfg(test)]
mod test {
    use crate::*;
    #[test]
    pub fn test_can_pin_argument() -> Result<(), crate::MainError> {
        use core::num::Wrapping;
        extern "C" fn test(a: Wrapping<usize>, _b: Wrapping<usize>) -> Wrapping<usize> {
            a + Wrapping(2)
        }

        use yaxpeax_x86::long_mode::RegSpec;
        let mut tracer = Tracer::new()?;
        let assumed_test = Function::<(usize, usize), usize>::new(&mut tracer, test as *const ())?
            .assume_args(vec![
                (Location::Reg(RegSpec::rdi()), JitValue::Const(Wrapping(3)))]);
        let mut lifted = Jit::new(&mut tracer);
        let (lowered_test, size) = lifted.lower(assumed_test)?;
        unsafe {
            let jitted_pinned_test = std::mem::transmute::<_, extern "C" fn(usize, usize)->usize>(lowered_test);
            assert_eq!(jitted_pinned_test(1, 2), 5);
        }
        Ok(())
    }

    #[test]
    pub fn test_can_optimize_closure() -> Result<(), crate::MainError> {
        use core::num::Wrapping;
        let a: Wrapping<usize> = Wrapping(1);
        let mut jit = crate::Lineiform::new();
        use core::hint::black_box;
        let clos = jit.speedup(move |()| { black_box(a) + Wrapping(2) });
        assert_eq!(clos(()), Wrapping(3));
        Ok(())
    }

    #[test]
    pub fn test_can_optimize_two_closures() -> Result<(), crate::MainError> {
        use core::num::Wrapping;
        let a: Wrapping<usize> = Wrapping(1);
        let mut jit = crate::Lineiform::new();
        use core::hint::black_box;
        let clos1 = black_box(move |()| { black_box(a) });
        let clos2 = jit.speedup(move |()| { black_box(clos1)(()) + Wrapping(2) });
        assert_eq!(clos2(()), Wrapping(3));
        Ok(())
    }

    #[test]
    pub fn test_passthrough_usize() -> Result<(), crate::MainError> {
        use core::num::Wrapping;
        let mut jit = crate::Lineiform::new();
        use core::hint::black_box;
        let clos = jit.speedup(move |a: usize| {
            let b = black_box(0) + black_box(0);
            a + b
        });
        for i in vec![0, !0, 0xFFFF_0000, 0x284591, &jit as &_ as *const _ as *const () as usize] {
            assert_eq!(clos(i), i);
        }
        Ok(())
    }

    #[test]
    pub fn test_handles_wrapping_and_widths() -> Result<(), crate::MainError> {
        use core::num::Wrapping;
        let a: Wrapping<u32> = Wrapping(-3 as i32 as u32);
        let mut jit = crate::Lineiform::new();
        use core::hint::black_box;
        let clos = jit.speedup(move |()| { black_box(a) + Wrapping(2) });
        assert_eq!(clos(()), Wrapping(-1 as i32 as u32));
        Ok(())
    }


    #[test]
    pub fn test_handles_branches_const_true() -> Result<(), crate::MainError> {
        let a: u32 = 33;
        let mut jit = crate::Lineiform::new();
        use core::hint::black_box;
        let clos = jit.speedup(move |()| {
            let val;
            if black_box(a) > 32 {
                val = 1;
            } else {
                val = 2;
            }
            val
        });
        assert_eq!(clos(()), 1);
        Ok(())
    }

    #[test]
    pub fn test_handles_branches_const_false() -> Result<(), crate::MainError> {
        let a: u32 = 32;
        let mut jit = crate::Lineiform::new();
        use core::hint::black_box;
        let clos = jit.speedup(move |()| {
            let val;
            if black_box(a) > 32 {
                val = 1;
            } else {
                val = 2;
            }
            val
        });
        assert_eq!(clos(()), 2);
        Ok(())
    }

    #[test]
    pub fn test_handles_dyn_branches() -> Result<(), crate::MainError> {
        let mut jit = crate::Lineiform::new();
        use core::hint::black_box;
        use core::num::Wrapping;
        let clos = jit.speedup(move |a: usize| {
            let val: usize;
            if a > 32 {
                val = (1 as usize);
            } else {
                val = (0 as usize);
            }
            val
        });
        assert_eq!(clos(0), 0);
        assert_eq!(clos(31), 0);
        assert_eq!(clos(32), 0);
        assert_eq!(clos(33), 1);
        Ok(())
    }

    #[test]
    pub fn test_handles_overflow_dyn_branches() -> Result<(), crate::MainError> {
        let mut jit = crate::Lineiform::new();
        use core::hint::black_box;
        use core::num::Wrapping;
        let clos = jit.speedup(move |a: usize| {
            let val: usize;
            if Wrapping(a) + Wrapping(0x5) < Wrapping(a) {
                val = 1;
            } else {
                val = 2;
            }
            val
        });
        assert_eq!(clos(0), 2);
        assert_eq!(clos((-1 as isize) as usize), 1);
        assert_eq!(clos((-6 as isize) as usize), 2);
        Ok(())
    }

    #[test]
    pub fn test_handles_branches_dyn_blocks() -> Result<(), crate::MainError> {
        let mut jit = crate::Lineiform::new();
        use core::hint::black_box;
        let clos = jit.speedup(move |a: usize| {
            let val: usize;
            if black_box(a) > 32 {
                val = 1;
                black_box(val);
            } else {
                val = 2;
            }
            val
        });
        assert_eq!(clos(31), 2);
        assert_eq!(clos(32), 2);
        assert_eq!(clos(33), 1);
        Ok(())
    }

    #[test]
    pub fn test_handles_multiple_branches() -> Result<(), crate::MainError> {
        let mut jit = crate::Lineiform::new();
        use core::hint::black_box;
        let clos = jit.speedup(move |a: usize| {
            let mut val: usize;
            if black_box(a) > 32 {
                val = 1;
                black_box(val);
            } else {
                val = 2;
            }
            black_box(val);
            if black_box(a) > 64 {
                val += 1;
                black_box(val);
            } else {
                val += 2;
            }
            val
        });
        assert_eq!(clos(31), 4);
        assert_eq!(clos(32), 4);
        assert_eq!(clos(33), 3);
        assert_eq!(clos(63), 3);
        assert_eq!(clos(64), 3);
        assert_eq!(clos(65), 2);
        Ok(())
    }



    #[test]
    pub fn test_handles_loops() -> Result<(), crate::MainError> {
        use core::num::Wrapping;
        let a: Wrapping<u32> = Wrapping(10 as i32 as u32);
        let mut jit = crate::Lineiform::new();
        use core::hint::black_box;
        let clos = jit.speedup(move |()| {
            let mut acc = Wrapping(0);
            for i in 0..black_box(a).0 {
                println!("i {} acc {}", i, acc);
                acc += acc + Wrapping(1);
            }
            acc
        });
        assert_eq!(clos(()), Wrapping(1023 as i32 as u32));
        Ok(())
    }

}
