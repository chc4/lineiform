#![allow(unused_variables, unused_mut, unused_imports, non_snake_case, dead_code, non_camel_case_types)]
#![feature(box_syntax, let_chains, trait_upcasting, associated_type_defaults)]
#![deny(unused_must_use, improper_ctypes_definitions)]
extern crate lazy_static;
extern crate petgraph;
extern crate yaxpeax_x86;
extern crate dynasmrt;
extern crate ena;
extern crate rangemap;
extern crate fixedbitset;
pub mod port;
pub mod node;
pub mod region;
pub mod ir;
pub mod time;
pub mod abi;
pub mod opt;
pub mod select;
pub use ir::*;
