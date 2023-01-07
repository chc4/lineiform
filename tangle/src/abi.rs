use crate::region::Region;
use crate::port::Storage;
use yaxpeax_x86::long_mode::RegSpec;

use core::fmt::Debug;

pub trait Abi: Debug {
    fn provide_arguments(&self, request: Vec<AbiRequest>) -> Vec<AbiStorage>;
    fn provide_returns(&self, request: Vec<AbiRequest>) -> Vec<AbiStorage>;
}

#[derive(Default, Clone, Debug)]
pub struct x86_64;

pub enum AbiRequest {
    Integer(usize),
    Float(usize),
    Vector(usize),
}

#[derive(Clone, Debug)]
pub enum AbiStorage {
    Register(RegSpec),
    // FPRegister
    // XMMRegister
    // etc
    StackSlot(usize),
    Problem(),
}
use AbiStorage::*;

impl Abi for x86_64 {
    // this probably has to be something to do with a generic argument that has a Tracable trait
    fn provide_arguments(&self, request: Vec<AbiRequest>) -> Vec<AbiStorage> {
        request.iter().map(|req| {
            match req {
                AbiRequest::Integer(n) =>
                    vec![
                        Register(RegSpec::rdi()),
                        Register(RegSpec::rsi()),
                        Register(RegSpec::rdx()),
                        Problem()
                    ].drain(..).take(*n).collect::<Vec<_>>(),
                _ => unimplemented!()
            }
        }).flatten().collect()
    }

    fn provide_returns(&self, request: Vec<AbiRequest>) -> Vec<AbiStorage> {
        request.iter().map(|req| {
            match req {
                AbiRequest::Integer(n) =>
                    vec![
                        Register(RegSpec::rax()),
                        Register(RegSpec::rdx()),
                        Problem()
                    ].drain(..).take(*n).collect::<Vec<_>>(),
                _ => unimplemented!()
            }
        }).flatten().collect()
    }
}
