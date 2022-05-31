use crate::tracer::{self, Tracer};
use tangle::ir::PortIdx;

use crate::block::{Function};

use yaxpeax_x86::long_mode::{Operand, Instruction, RegSpec, Opcode};
use yaxpeax_arch::LengthedInstruction;

use bitvec::vec::BitVec;
use bitvec::slice::BitSlice;

use core::marker::PhantomData;
use std::collections::HashMap;
use std::convert::{TryInto, TryFrom};
use core::num::Wrapping;
use core::cmp::max;
use rangemap::RangeInclusiveMap;

const HOST_WIDTH: u8 = std::mem::size_of::<usize>() as u8;
const STACK_TOP: usize = 0xFFFF_FFFF_FFFF_FFF0;

use thiserror::Error;
#[derive(Error, Debug)]
pub enum LiftError {
    #[error("unable to lift function")]
    Lifting,
    #[error("unsupported target")]
    Unsupported,
    #[error("unknown register {0}")]
    UnknownRegister(&'static str),
    #[error("lifting unimplemented for inst {0}")]
    UnimplementedInst(Instruction),
    #[error("disassembling call target {0}")]
    Block(#[from] crate::block::BlockError),
    #[error("tracer error {0}")]
    Tracer(#[from] crate::tracer::TracerError),
    #[error("we hit a return to {0:x}")]
    FunctionEnded(usize),
    #[error("we didn't return to the callsite in our lifted function")]
    TranslateOut(()),
}

trait OperandFun {
    fn is_imm(&self) -> bool;
}

impl OperandFun for Operand {
    fn is_imm(&self) -> bool {
        match self {
            Operand::ImmediateI8( _) | Operand::ImmediateI16(_) |
            Operand::ImmediateI32(_) | Operand::ImmediateI64(_) =>
                true,
            _ => false,
        }
    }
}

/// We use these locations essentially as the keys of an x86 operand -> Tangle
/// port map. When we create a function, we enter all the calling convention's
/// inputs into a store, and when we decode x86 and lift it we try and fetch the
/// "variable" that operand corrosponds to.
use std::fmt::Display;
#[derive(Clone, Hash, PartialEq, Eq, Debug, Display)]
pub enum Location {
    /// A register value
    Reg(RegSpec),
    /// A stack slot value. The `usize` is the "stack address" of it:
    /// `push rax` will create a new Stack(STACK_TOP) entry if it's the first
    /// stack operation, for example.
    Stack(usize),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum JitVariable {
    Variable(PortIdx),
    Known(JitValue),
}

/*
impl JitVariable {
    /// Get a native width JitValue from a JitVariable. You should probably not
    /// use this.
    pub fn value(&mut self, builder: &mut FunctionBuilder) -> JitValue {
        match self {
            JitVariable::Variable(var) => {
                let mut val = builder.use_var(*var);
                JitValue::Value(val)
            },
            JitVariable::Known(val) => {
                val.clone()
            },
        }
    }

    /// Get a proper width temporary JitTemp value from this JitVariable.
    /// In order to store it in the concrete context as a JitValue, it must be
    /// either zero or sign extended.
    pub fn tmp(&mut self, builder: &mut FunctionBuilder, width: u8) -> JitTemp {
        match self {
            JitVariable::Variable(var) => {
                let mut val = builder.use_var(*var);
                use types::{I8, I16, I32, I64};
                let typ = match width {
                    1 => I8,
                    2 => I16,
                    4 => I32,
                    8 => I64,
                    _ => unimplemented!(),
                };
                if width != HOST_WIDTH {
                    // we want a memory or stack value as a certain width:
                    // get a use of the variable backing it, and mask to the correct
                    // size.
                    JitTemp::Value(builder.ins().ireduce(typ, val), typ)
                } else {
                    JitTemp::Value(val, typ)
                }
            },
            JitVariable::Known(val) => {
                //let width_mask = Wrapping((1 << ((width*8)+1)) - 1);
                match val {
                    JitValue::Const(c) => match width {
                        1 => JitTemp::Const8(c.0 as u8),
                        2 => JitTemp::Const16(c.0 as u16),
                        4 => JitTemp::Const32(c.0 as u32),
                        8 => JitTemp::Const64(c.0 as u64),
                        _ => unimplemented!(),
                    },
                    id if width == HOST_WIDTH => match id {
                        JitValue::Ref(base, offset) =>
                            JitTemp::Ref(base.clone(), *offset),
                        JitValue::Frozen { addr, size } =>
                            JitTemp::Frozen { addr: *addr, size: *size },
                        x @ _ => unimplemented!("temp {:?}", x),
                    },
                    _ => unimplemented!(),
                }
            },
        }
    }
}
*/

use std::rc::Rc;
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum JitValue {
    /// An SSA value
    Value(PortIdx),
    /// An SSA comparison flag value
    Flag(PortIdx),
    /// A reference to a value, plus an offset into it
    Ref(Rc<JitValue>, usize),
    /// A memory region we use to represent the stack: `sub rsp, 0x8` becomes
    /// manipulating a Ref to this, and load/stores can be concretized.
    Stack,
    /// A frozen memory region. We can inline values from it safely.
    Frozen { addr: *const u8, size: usize },
    /// A statically known value.
    Const(Wrapping<usize>),
}

impl JitValue {
}


// TODO: fp registers and stuff
type Type = usize;

/// These are the temporary values used by operations - they, unlike JitValues,
/// are variable width, and have operations to sign-extend or zero-extend that
/// yield native width JitValues.
/// This also allows us to optimize a bit, since we can leave off a few masking
/// operations for values if we know exactly what width they are.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum JitTemp {
    /// An SSA value
    Value(PortIdx, Type),
    Flag(PortIdx),
    // XX: how do we handle these "opaque" values? we want to be able to reassemble
    // them from a memcpy, for example. worry about it when we have a better
    // use-case?
    /// A reference to a value, plus an offset into it
    Ref(Rc<JitValue>,usize),
    /// A memory region we use to represent the stack: `sub rsp, 0x8` becomes
    /// manipulating a Ref to this, and load/stores can be concretized.
    //Stack,
    /// A frozen memory region. We can inline values from it safely.
    Frozen { addr: *const u8, size: usize },
    /// A statically known value.
    Const8(u8),
    Const16(u16),
    Const32(u32),
    Const64(u64),
}

#[derive(Clone)]
struct Context {
    /// Our currently known execution environment. This holds values like `rax`
    /// and stored stack values, mapping them to either constant propagated
    /// values, or Cranelift SSA variables if they are unknown at compilation
    /// time.
    bound: HashMap<Location, JitVariable>,
    flags: Vec<PortIdx>, // array of eflags source ports
}

impl Context {
    fn new() -> Self {
        Self {
            bound: HashMap::new(),
            flags: Vec::new(),
        }
    }
}

pub struct Jit<'a> {
    tracer: &'a mut Tracer<'static>,
}

enum EmitEffect {
    Advance,
    Jmp(usize),
    Branch(PortIdx, PortIdx, usize),
    Call(usize),
    Ret(Option<usize>),
}

struct JitFunction<const A_n: usize, const O_n: usize> {
    ir: tangle::IR,
    f: tangle::node::Function<A_n, O_n>,
    context: Context,
}

use std::mem::size_of;
impl<'a> Jit<'a> {
    pub fn new(tracer: &'a mut Tracer<'static>) -> Jit<'a> {

        Self {
            tracer,
        }
    }

    pub fn lower<A, O>(&mut self, f: Function<A, O>)
    -> Result<(extern "C" fn((A,))->O, usize),LiftError> where
    [(); size_of::<A>()]: Sized,
    [(); size_of::<O>()]: Sized {
        let mut ir = tangle::IR::new();
        let ctx = Context::new();
        let mut tangle_f = tangle::node::Node::function::<{ size_of::<A>() }, { size_of::<O>() }>(&mut ir);
        let mut func = JitFunction {
            ir: ir,
            f: tangle_f,
            context: ctx,
        };
        let translate_result = func.translate(f, self)?;
        Ok(func.ir.compile_fn().unwrap())
    }
}

impl<const A_n: usize, const O_n: usize> JitFunction<A_n, O_n> {
    /// Translate a Function into Cranelift IR.
    /// Calling conventions here are a bit weird: essentially we only ever build
    ///
    fn translate<'a, A, O>
    (&mut self, f: Function<A, O>, jit: &mut Jit<'a>) -> Result<(), LiftError> {
        unimplemented!("{} {}", A_n, O_n);
        // add and bind ports for all the function arguments
        for i in 0..(A_n/8) {
            println!("adding argument {}", i);
            // TODO
        }
        let mut base = (f.base as usize) + f.offset.0;
        let mut ip = base;
        println!("starting emitting @ base+0x{:x}", ip - jit.tracer.get_base()?);
        let mut stream = f.instructions.clone();
        let mut start_i = f.offset.1;
        let mut i = f.offset.1;

        loop {
            // snapshot of our context when we started this basic block
            let mut snap = self.context.bound.clone();
            let inst = stream.get(i);
            if let None = inst {
                // we ran out of inputs but didn't hit a ret!
                println!("hit translate out @ 0x{:x}", ip);
                return Err(LiftError::TranslateOut(()));
            }
            let inst = inst.unwrap();
            ip += inst.len().to_const() as usize;
            let mut eff = self.emit(ip, inst)?;
            match eff {
                EmitEffect::Advance => {
                    i += 1;
                },
                _ => unimplemented!("emit effect"),
            }
        }
        for i in 0..O_n {
            unimplemented!("adding output {}", i);
        }

        self.ir.set_body(self.f);
        Ok(())
    }

    fn emit(&mut self, ip: usize, inst: &Instruction) -> Result<EmitEffect, LiftError> {
        println!("---- {}", inst);
        let ms = inst.mem_size().and_then(|m| m.bytes_size());
        match inst.opcode() {
            Opcode::MOV => {
                // we need to support mov dword [eax+4], rcx and vice versa, so
                // both the load and store need a mem_size for memory width.
                let val = self.port_for(ip, inst.operand(1), ms);
                //self.store(inst.operand(0), val, ms);
            },
            //Opcode::ADD => {
            //    let left = self.operand_value(ip, inst.operand(0), ms);
            //    let mut right = self.operand_value(ip, inst.operand(1), ms);
            //    if inst.operand(1).is_imm() {
            //        right = right.sign_extend(self.builder, inst.operand(0).width().or(ms).unwrap());
            //    }
            //    let added = self.add::<true>(left, right);
            //    self.store(inst.operand(0), added, ms);
            //},
            //Opcode::ADC => {
            //    let left = self.operand_value(ip, inst.operand(0), ms);
            //    let mut right = self.operand_value(ip, inst.operand(1), ms);
            //    if inst.operand(1).is_imm() {
            //        right = right.sign_extend(self.builder, inst.operand(0).width().or(ms).unwrap());
            //    }
            //    let carry = self.context.check_flag(Flags::CF, true, self.builder);
            //    println!("adc {:?} {:?} {:?}", left, right, carry);
            //    let added = self.adc::<true>(left, right, carry);
            //    self.store(inst.operand(0), added, ms);
            //},
            op @ (Opcode::SUB | Opcode::CMP) => {
                if let (Opcode::SUB, Operand::Register(const { RegSpec::rsp() })) = (op, inst.operand(0)) {
                    // This is a sub rsp, 8; or whatever instruction allocating stack
                    // space. We don't want to emit any instructions, just allocate
                    // stack slots.
                    let space = match inst.operand(1) {
                        Operand::ImmediateI8(i) => usize::try_from(i).unwrap(),
                        x => unimplemented!("unknown space for stack allocating {:?}", x),
                    };
                    println!("emitting {} stack slots", space / HOST_WIDTH as usize);
                    assert!(space % HOST_WIDTH as usize == 0);
                    for i in 0..(space / HOST_WIDTH as usize) {
                        self.f.add_stack_slot(&mut self.ir);
                    }
                } else {
                    // sub eax, ff
                    // ff gets sign extended to 0xffff_ffff
                    let left = self.port_for(ip, inst.operand(0), ms);
                    let mut right = self.port_for(ip, inst.operand(1), ms);
                    //if inst.operand(1).is_imm() {
                    //    right = right.sign_extend(self.builder, inst.operand(0).width().or(ms).unwrap());
                    //}
                    //let subbed = self.sub::<true>(left, right);
                    //if let Opcode::SUB = op {
                    //    self.store(inst.operand(0), subbed, ms);
                    //}
                }
            },
            x => unimplemented!("unimplemented opcode {:?}", x),
        }
        Ok(EmitEffect::Advance)
    }

    /// Get the Tangle port that corrosponds with the requested operand.
    ///
    /// If we have `mov eax, ecx`, we want to resolve ecx to the last emitted ecx port.
    /// This has to handle *all* operand types, however: if there's an `[ecx]` we need
    /// to emit a StackLoad instruction and return the value result of that as well.
    ///
    /// If the location is a load, `width` is the memory operation size in bytes.
    /// It is ignored for other operand types, so that e.g. `mov dword [rax+4], rcx`
    /// doesn't mistakenly truncate rcx.
    pub fn port_for(&mut self, ip: usize, operand: Operand, ms: Option<u8>) -> PortIdx {
        println!("getting port for {}", operand);
        match operand {
            Operand::RegDisp(const { RegSpec::rsp() }, o) => {
                unimplemented!("stack ref");
            },
            Operand::Register(const { RegSpec::rip() }) => {
                unimplemented!("emit const")
                //HOST_TMP(ip as _)
            },
            //Operand::RegDisp(const { RegSpec::rip() }, o) => {
            //    HOST_TMP((Wrapping(ip) + Wrapping(o as isize as usize)).0 as _)
            //},
            //Operand::Register(r) if r.width() == 1 => {
            //    match r {
            //        const { RegSpec::al() } | const { RegSpec::bl() } |
            //        const { RegSpec::cl() } => {
            //            // I should probably re-think Const, and add variable
            //            // widths to it: there's not really a good reason for
            //            // `and al, 0x1` to have to mask out rax for the value
            //            // and then bitselect it back in at the store.
            //            self.get(Location::Reg(r)).tmp(self.builder, r.width())
            //        },
            //        _ => unimplemented!("al etc unimplemented")
            //    }
            //},
            x => unimplemented!("getting a port_for {} unimplemented", x),
        }
    }

    pub fn format(&self) {
        // FIXME: do some sort of debug printing
    }
}
