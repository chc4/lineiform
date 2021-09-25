use crate::tracer::{self, Tracer};

use cranelift::prelude::*;
use cranelift_jit::{JITBuilder, JITModule};
use cranelift_module::{DataContext, Linkage, Module};
use crate::block::{Function};
use cranelift_codegen::ir::types::Type;
use cranelift_codegen::ir::condcodes::CondCode;

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

use thiserror::Error;
#[derive(Error, Debug)]
pub enum LiftError {
    #[error("unable to lift function")]
    Lifting,
    #[error("unsupported target")]
    Unsupported,
    #[error("unsupported cranelift builder backend")]
    Lookup(#[from] cranelift_codegen::isa::LookupError),
    #[error("unknown register {0}")]
    UnknownRegister(&'static str),
    #[error("error setting compilation option")]
    Setting(#[from] settings::SetError),
    #[error("lifting unimplemented for inst {0}")]
    UnimplementedInst(Instruction),
    #[error("error creating cranelift module {0}")]
    Module(#[from] cranelift_module::ModuleError),
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

const HOST_WIDTH: u8 = std::mem::size_of::<usize>() as u8;
const STACK_TOP: usize = 0xFFFF_FFFF_FFFF_FFF0;
const STACK: RegSpec = RegSpec::rsp();
// we need to map eax -> rax here, so the registers alias in storage
use lazy_static::lazy_static;
lazy_static! {
    static ref REGMAP: HashMap<RegSpec, RegSpec> = [
        (RegSpec::al(), RegSpec::rax()),
        (RegSpec::ah(), RegSpec::rax()),
        (RegSpec::ax(), RegSpec::rax()),
        (RegSpec::eax(), RegSpec::rax()),

        (RegSpec::bl(), RegSpec::rbx()),
        (RegSpec::bh(), RegSpec::rbx()),
        (RegSpec::bx(), RegSpec::rbx()),
        (RegSpec::ebx(), RegSpec::rbx()),

        (RegSpec::cl(), RegSpec::rcx()), // no cx() in real_mode
        (RegSpec::ch(), RegSpec::rcx()), // no cx() in real_mode
        (RegSpec::cx(), RegSpec::rcx()), // no cx() in real_mode
        (RegSpec::ecx(), RegSpec::rcx()),

        (RegSpec::dl(), RegSpec::rdx()),
        (RegSpec::dh(), RegSpec::rdx()),
        (RegSpec::dx(), RegSpec::rdx()),
        (RegSpec::edx(), RegSpec::rdx()),

        (RegSpec::sil(), RegSpec::rsi()), // esi is not public
        (RegSpec::esi(), RegSpec::rsi()), // esi is not public

        (RegSpec::dil(), RegSpec::rdi()), // edi is not public
        (RegSpec::edi(), RegSpec::rdi()), // edi is not public

        (RegSpec::bpl(), RegSpec::rbp()), // there's only a bp() helper in real_mode
        (RegSpec::bp(), RegSpec::rbp()), // there's only a bp() helper in real_mode
        (RegSpec::ebp(), RegSpec::rbp()), // no ebp() helper
    ].iter().cloned().collect();
}

/// We use these locations essentially as the keys of an x86 operand -> Cranelift
/// SSA variable map. When we create a function, we enter all the calling convention's
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
    Variable(Variable),
    Known(JitValue),
}
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

use std::rc::Rc;
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum JitValue {
    /// An SSA value
    Value(Value),
    /// An SSA comparison flag value
    Flag(Value),
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

/// These are the temporary values used by operations - they, unlike JitValues,
/// are variable width, and have operations to sign-extend or zero-extend that
/// yield native width JitValues.
/// This also allows us to optimize a bit, since we can leave off a few masking
/// operations for values if we know exactly what width they are.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum JitTemp {
    /// An SSA value
    Value(Value, Type),
    Flag(Value),
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
const HOST_TMP: fn(u64) -> JitTemp = JitTemp::Const64;

impl JitTemp {
    /// Get a Cranelift SSA Value for this JitValue. Don't use this if you can
    /// help it, since it erases statically known values and harms optimizations.
    pub fn into_ssa(&self, int: Type, builder: &mut FunctionBuilder) -> Value {
        use JitTemp::*;
        use types::{I8, I16, I32, I64};
        fn make_const<T>(builder: &mut FunctionBuilder, int: Type, c: T) -> cranelift::prelude::Value where i64: From<T> {
            //unimplemented!("double check this");
            builder.ins().iconst(int, i64::try_from(c).unwrap())
        }
        match self {
            Value(val, typ) => *val,
            Flag(val) => *val,
            Const8(c) => make_const(builder, I8, *c),
            Const16(c) => make_const(builder, I16, *c),
            Const32(c) => make_const(builder, I32, *c),
            Const64(c) => make_const(builder, I64, *c as i64),
            x => unimplemented!("into_ssa for {:?}", x),
        }
    }

    fn val_of_width(c: usize, width: u8) -> JitTemp {
        use JitTemp::*;
        match width {
            1 => Const8(c as u8),
            2 => Const16(c as u16),
            4 => Const32(c as u32),
            8 => Const64(c as u64),
            _ => unimplemented!(),
        }
    }

    fn is_const(&self) -> bool {
        use JitTemp::*;
        match self {
            Const8(_) | Const16(_) | Const32(_) | Const64(_) => true,
            _ => false
        }
    }

    /// Get the width in bytes of a JitTemp value
    fn width(&self) -> u8 {
        use JitTemp::*;
        match self {
            Const8(_) => 1,
            Const16(_) => 2,
            Const32(_) => 4,
            Const64(_) => 8,
            Value(v, typ) => typ.bytes() as u8,
            Ref(_, _) => HOST_WIDTH,
            _ => unimplemented!(),
        }
    }

    fn into_usize(self, builder: &mut FunctionBuilder) -> Option<usize> {
        assert_eq!(HOST_WIDTH, 8);
        let ex = self.zero_extend(builder, HOST_WIDTH);
        match ex {
            JitTemp::Const64(c) => Some(c.try_into().unwrap()),
            _ => None
        }
    }

    fn into_native(self, builder: &mut FunctionBuilder) -> Option<JitValue> {
        assert_eq!(HOST_WIDTH, 8);
        match self {
            JitTemp::Value(v, typ) if typ.bytes()  == HOST_WIDTH.into() =>
                Some(JitValue::Value(v)),
            JitTemp::Const64(c) =>
                Some(JitValue::Const(Wrapping(c.try_into().unwrap()))),
            JitTemp::Ref(base, offset) => Some(JitValue::Ref(base, offset)),
            JitTemp::Frozen { addr, size } => Some(JitValue::Frozen { addr, size }),
            _ => panic!("wrong width constant"),
        }
    }
    fn sign_extend(self, builder: &mut FunctionBuilder, width: u8) -> JitTemp {
        if self.width() == width { return self }
        match self.clone() {
            JitTemp::Value(val, typ) => {
                if typ.bytes() != width.into() {
                    let new_typ = Type::int((width*8) as u16).unwrap();
                    JitTemp::Value(builder.ins().sextend(new_typ, val), new_typ)
                } else {
                    self
                }
            },
            c if c.is_const() => {
                match width {
                    2 => match self {
                        JitTemp::Const8(c) => JitTemp::Const16(c as i8 as i16 as u16),
                        _ => panic!(),
                    },
                    4 => match self {
                        JitTemp::Const8(c) => JitTemp::Const32(c as i8 as i32 as u32),
                        JitTemp::Const16(c) => JitTemp::Const32(c as i16 as i32 as u32),
                        _ => panic!(),
                    },
                    8 => match self {
                        JitTemp::Const8(c) => JitTemp::Const64(c as i8 as i64 as u64),
                        JitTemp::Const16(c) => JitTemp::Const64(c as i16 as i64 as u64),
                        JitTemp::Const32(c) => JitTemp::Const64(c as i32 as i64 as u64),
                        _ => panic!(),
                    },
                    x => panic!("tried to sign-extend a {} value to {}", self.width(), x),
                }
            }
            _ => unimplemented!(),
        }
    }

    fn zero_extend(self, builder: &mut FunctionBuilder, width: u8) -> JitTemp {
        if self.width() == width { return self }
        match self.clone() {
            JitTemp::Value(val, typ) => {
                if typ.bytes() != width.into() {
                    let new_typ = Type::int((width*8) as u16).unwrap();
                    JitTemp::Value(builder.ins().uextend(new_typ, val), new_typ)
                } else {
                    self
                }
            },
            c if c.is_const() => {
                match width {
                    2 => match self {
                        JitTemp::Const8(c) => JitTemp::Const16(c as u16),
                        x @ JitTemp::Const16(_) => x,
                        _ => panic!("{:?} to {}", c, width),
                    },
                    4 => match self {
                        JitTemp::Const8(c) => JitTemp::Const32(c as u32),
                        JitTemp::Const16(c) => JitTemp::Const32(c as u32),
                        x @ JitTemp::Const32(_) => x,
                        _ => panic!("{:?} to {}", c, width),
                    },
                    8 => match self {
                        JitTemp::Const8(c) => JitTemp::Const64(c as u64),
                        JitTemp::Const16(c) => JitTemp::Const64(c as u64),
                        JitTemp::Const32(c) => JitTemp::Const64(c as u64),
                        x @ JitTemp::Const64(_) => x,
                        _ => panic!("{:?} to {}", c, width),
                    },
                    x => panic!("tried to zero-extend a {} value to {}", self.width(), x),
                }
            }
            _ => unimplemented!(),
        }
    }
}


#[derive(Hash, PartialEq, Clone, Copy, Display, Debug)]
enum Flags {
    CF = 0,
    PF = 2,
    AF = 4,
    ZF = 6,
    SF = 7,
    TF = 8,
    IF = 9,
    DF = 10,
    OF = 11,
    FINAL = 12,
}
use Flags::*;

/// A macro that allows for saving of `eflags` values to a Context after
/// operations. Care should be taken that the last operation of `e` is the
/// operation you want to collect flags from - you should probably only
/// call this with some inline assembly expression to prevent the compiler
/// from turning your a + b into a lea, for example.
/// TODO: CPUID checks for if we have lahf
macro_rules! getflags {
    ($ctx:expr, $e:expr, $bits:expr) => {
        $e;
        let mut flags: u64;
        asm!("
            pushfq;
            pop {0};
        ", out(reg) flags);
        println!("flags are 0b{:b}", flags);
        $ctx.set_flags_const($bits, flags);
    }
}

macro_rules! do_op {
    ($ctx:expr, $flag:expr, $left:expr, $right:expr, $asm:expr, $flags:expr, $op:tt) => {
        do_op!($ctx, $flag, reg, $left, $right, $asm, $flags, $op)
    };
    ($ctx:expr, $flag:expr, $class:ident, $left:expr, $right:expr, $asm:expr, $flags:expr, $op:tt) => {
        if $flag {
            let mut val = $left;
            unsafe {
                getflags!($ctx, asm!($asm, inout($class) val, in($class) $right),
                $flags);
            }
            val
        } else {
            (Wrapping($left) $op (Wrapping($right))).0
        }
    }
}

/// A macro to create operations on all same-width JitTemp constants
macro_rules! const_ops {
    ($ctx:expr, $flag:expr, $left:expr, $right:expr, $asm:expr, $flags:expr, $op:tt) => { {
        use JitTemp::*;
        match ($left, $right) {
            (Const8(l), Const8(r)) =>
                Const8(do_op!($ctx, $flag, reg_byte, l, r, $asm, $flags, $op)),
            (Const16(l), Const16(r)) =>
                Const16(do_op!($ctx, $flag, reg, l, r, $asm, $flags, $op)),
            (Const32(l), Const32(r)) =>
                Const32(do_op!($ctx, $flag, reg, l, r, $asm, $flags, $op)),
            (Const64(l), Const64(r)) =>
                Const64(do_op!($ctx, $flag, reg, l, r, $asm, $flags, $op)),
            _ => unimplemented!(
                "op {} for {:?} {:?}",
                stringify!($op), $left, $right),
        }
    } }
}

/// A conditional bool for our JIT. These are used for lazily computing branch
/// conditions: we can store Known(true|false) for constant computed adds, while
/// setting Unknown(ssa_values) to the *result* of our add - and only do the icmp
/// and bz when we need the flag value for a conditional jump instruction, to avoid
/// generating a billion SSA values and instructions that would be pruned the
/// majority of the time.
#[derive(Clone, Debug, PartialEq)]
enum JitFlag {
    Known(u64),
    Unknown(Value, Value, Value), // left <op> right = <result>
}

#[derive(Clone)]
struct Context {
    /// Our currently known execution environment. This holds values like `rax`
    /// and stored stack values, mapping them to either constant propagated
    /// values, or Cranelift SSA variables if they are unknown at compilation
    /// time.
    bound: HashMap<Location, JitVariable>,
    flags: Vec<JitFlag>,
    int: Type,
    /// This is a bitvec for keeping track of instructions that we have seen and
    /// emitted, so that we can track backwards jumps to know when to emit loops.
    /// Technically this should be updated at each instruction emission - we can
    /// optimize it a bit by only updating it when we exit a block, however, and
    /// mark (start..end) all at once.
    seen: HashMap<*const (), Vec<bool>>,

    /// The callstack for this execution context. Notably, this includes calls
    /// and returns from inlined functions. This is so we can clear the `seen`
    /// bitmap for inlined functions when we return, so that inlining the same
    /// method twice is not detected as a loop.
    callstack: Vec<usize>,
}

impl Context {
    pub fn stack(&self) -> usize {
        let sp = self.bound.get(&Location::Reg(RegSpec::rsp()));
        match sp {
            Some(JitVariable::Known(JitValue::Ref(base, offset)))
                if let JitValue::Stack = **base =>
            {
                //println!("current stack @ 0x{:x}", offset);
                assert!(offset <= &STACK_TOP);
                *offset
            },
            _ => unimplemented!("non-concrete stack??"),
        }
    }

    #[inline]
    pub fn set_flags(&mut self, flags: Vec<Flags>, val: (Value, Value, Value)) -> JitValue {
        for flag in flags {
            self.flags[flag as usize] = JitFlag::Unknown(val.0, val.1, val.2);
        }
        JitValue::Flag(val.2)
    }

    #[inline]
    pub fn set_flags_const(&mut self, flags: Vec<Flags>, c: u64) {
        for flag in flags {
            self.flags[flag as usize] = JitFlag::Known(c);
        }
    }

    pub fn check_flag(&mut self, flag: Flags, set: bool, builder: &mut FunctionBuilder) -> JitTemp {
        let val = &self.flags[flag as usize];
        println!("eflag {} is {:?}", flag, val);
        let flag_mask = (1 << (flag as usize));
        match val {
            JitFlag::Known(b) => {
                println!("{:b} & {:b}", b, flag_mask);
                if set {
                    HOST_TMP((*b as usize & flag_mask == flag_mask) as usize as _)
                } else {
                    HOST_TMP((*b as usize & flag_mask == 0) as usize as _)
                }
            },
            JitFlag::Unknown(left, right, result) => JitTemp::Flag({
                //let flag = match flag {
                //    Flags::ZF => builder.ins().icmp_imm(if set { IntCC::Equal } else { IntCC::NotEqual }, *result, 0),
                //    Flags::CF => {
                //        let (res, flag) = builder.ins().iadd(*left, *right);
                //        builder.ins().icmp(if set { IntCC::UnsignedLessThan } else { IntCC::UnsignedGreaterThanOrEqual }, res, *result)
                //    },
                //    _ => unimplemented!(),
                //};
                *result
            }),
        }
    }

    pub fn dump(&self) {
        println!("STACK @ 0x{:x}", self.stack());
        for (key, val) in &self.bound {
            match key {
                Location::Stack(s) => {
                    println!("0x{:x} = {:?}", s, val)
                },
                _ => println!("{} = {:?}", key, val)
            }
        }
    }
}

pub struct Jit<'a, A, O> {
    builder_context: FunctionBuilderContext,
    ctx: codegen::Context,
    data_ctx: DataContext,
    module: JITModule,
    argument_layout: Vec<Type>,
    return_layout: Vec<Type>,
    tracer: &'a mut Tracer<'static>,
    _phantom: PhantomData<(A, O)>,
}

enum EmitEffect {
    Advance,
    Jmp(usize),
    Branch(IntCC, Value, usize),
    Call(usize),
    Ret(Option<usize>),
}

use cranelift_codegen::ir::ArgumentLoc;
use isa::RegInfo;
use target_lexicon::{Architecture, CallingConvention, Triple};
struct Target {
    triple: Triple,
    target_isa: Box<dyn isa::TargetIsa + 'static>,
    arguments: Vec<Location>,
    outputs: Vec<Location>,
}

lazy_static! {
    static ref HOST: Target = Target::for_target(Triple::host()).unwrap();
}

impl Target {
    pub fn for_target(targ: Triple) -> Result<Self, LiftError> {
        let isa = Target::isa(targ.clone())?;
        let mut arch = Self {
            target_isa: isa,
            triple: targ,
            arguments: vec![],
            outputs: vec![],
        };
        if let Ok(CallingConvention::SystemV) = arch.triple.default_calling_convention() {
            arch.fill_in_out()?;
            Ok(arch)
        } else {
            Err(LiftError::Unsupported)
        }
    }

    fn isa(trip: Triple) -> Result<Box<dyn isa::TargetIsa + 'static>, LiftError> {
        let builder = isa::lookup(trip)?;
        let mut settings = settings::builder();
        // Configure Cranelift compilation options
        settings.set("opt_level", "speed_and_size")?;
        let flags = settings::Flags::new(settings);
        Ok(builder.finish(flags))
    }

    fn fill_in_out(&mut self) -> Result<(), LiftError> {
        match self.triple.architecture {
            Architecture::X86_64 => {
                self.arguments.append(&mut vec![
                    Location::Reg(RegSpec::rdi()),
                    Location::Reg(RegSpec::rsi()),
                    Location::Reg(RegSpec::rdx()),
                ]);
                self.outputs.append(&mut vec![
                    Location::Reg(RegSpec::rax()),
                    Location::Reg(RegSpec::rdx()),
                ]);
                Ok(())
            },
            Architecture::X86_32(_) => {
                unimplemented!()
            },
            _ => Err(LiftError::Unsupported)
        }
    }
}

pub struct JitPath<A, O>(Function<A,O>, Block, Context);

impl<'a, A, O> Jit<'a, A, O> {
    pub fn new(tracer: &'a mut Tracer<'static>) -> Jit<'a, A, O> {
        let builder = JITBuilder::new(cranelift_module::default_libcall_names());
        let module = JITModule::new(builder);

        let int = module.target_config().pointer_type();
        let ptr = Type::triple_pointer_type(&HOST.triple);

        let mut ctx = module.make_context();
        ctx.func.signature.call_conv = isa::CallConv::SystemV;
        let argument_layout = vec![ptr, ptr, int]; // hardcode self, int argument first
        //let argument_layout = vec![int, int]; // hardcode self, int argument first
        for arg in argument_layout.clone() {
            ctx.func.signature.params.push(AbiParam::new(arg));
        }

        let return_layout = vec![int]; // hardcode int return type
        for ret in return_layout.clone() {
            ctx.func.signature.returns.push(AbiParam::new(ret));
        }

        Self {
            builder_context: FunctionBuilderContext::new(),
            ctx: ctx,
            data_ctx: DataContext::new(),
            module,
            argument_layout,
            return_layout,
            tracer,
            _phantom: PhantomData,
        }
    }

    /// Translate a Function into Cranelift IR.
    /// Calling conventions here are a bit weird: essentially we only ever build
    ///
    fn translate(&mut self, f: Function<A, O>) -> Result<(), LiftError> {
        let int = self.module.target_config().pointer_type();
        // We are translating extern "C" fn(A) -> O;
        // Create the builder to build a function.
        let mut builder = FunctionBuilder::new(&mut self.ctx.func, &mut self.builder_context);

        // Create the entry block, to start emitting code in.
        let entry_block = builder.create_block();

        // Since this is the entry block, add block parameters corresponding to
        // the function's parameters.
        builder.append_block_params_for_function_params(entry_block);

        // Tell the builder to emit code in this block.
        builder.switch_to_block(entry_block);

        // And, tell the builder that this block will have no further
        // predecessors. Since it's the entry block, it won't have any
        // predecessors.

        let mut idx = 0; // Why do we need to do this instead of asking cranelift for
        // a fresh variable??
        let mut variables = Self::make_variables(&mut builder, &mut idx, entry_block, int, &self.argument_layout, &f.pinned);

        let mut function_translator = FunctionTranslator {
            depth: 0,
            int,
            builder: &mut builder,
            context: variables.clone(),
            module: &mut self.module,
            idx: &mut idx,
            return_layout: &mut self.return_layout,
            tracer: &mut self.tracer,
            changed: RangeInclusiveMap::new(),
        };
        // We step forward all paths through the function until we are done
        // I think we can do something clever here: we can advance the branches
        // with *the lowest f.offset.0* each time, and coallesce when we have
        // identical jump targets.
        // pred
        // if cond {
        //  body { block } body2
        // } else {
        //  shorter_body
        // }
        // merge
        //
        // We have two paths after the cond, [pred] and [pred], shorter_body > body,
        // so we'd step the first branch until it's [pred, body],
        // and then we'd see that the jump target for both blocks is merge and
        // can union the states together.
        // This doesn't properly handle detours through blocks that are towards
        // the end of the function and then jump back, since we'd advance the
        // frontier all the way to the end before we reach them even though they
        // are short. We can probably have some heuristic to inline path length
        // too, so that it's advanced until it returns and hopefully merges at some
        // other branch - but we'd have to be careful not to break merging of
        // our example.
        // TODO: think about how this interacts with loops?
        let mut need = vec![JitPath(f, entry_block, variables)];
        while let Some(next) = need.pop() {
            let mut new = function_translator.translate(next)?;
            need.append(&mut new);
        }
        // function_translator.builder.seal_block(entry_block);
        println!("jit output: \n{}", function_translator.builder.display(None));
        function_translator.builder.finalize();
        Ok(())
    }


    fn make_variables<'b>(builder: &mut FunctionBuilder<'b>, idx: &mut usize, entry_block: Block,
        int: Type, arg_vars: &Vec<Type>, pinned_values: &Vec<(Location, JitValue)>) -> Context
    {
        // First, we make a variable for all of our pinned locations containing
        // the fed-in value.
        let mut ctx: HashMap<Location, JitVariable> = HashMap::new();
        for pinned in pinned_values.iter() {
            println!("adding pinned value {} = {:?}", pinned.0, pinned.1);
            ctx.insert(pinned.0.clone(),
                JitVariable::Known(pinned.1.clone()));
        }
        // Then, for all the arguments to the function, we create a variable for
        // the ABI register *unless* it has already been pinned.
        // If we pin argument 0 = 1234 in SystemV for example, we want to compile
        // a function with RDI *always* set to 1234, and throw away the actual
        // argument.
        for (i, arg_ty) in arg_vars.iter().enumerate() {
            let arg_slot = &HOST.arguments[i];
            ctx.entry(arg_slot.clone()).or_insert_with(|| {
                println!("adding argument {}", arg_slot);
                let val = builder.block_params(entry_block)[i];
                let var = Variable::new(*idx);
                *idx = *idx + 1;
                builder.declare_var(var, *arg_ty);
                builder.def_var(var, val);
                JitVariable::Variable(var)
            });
        }
        // We add a "concrete" stack pointer as well - this means that manipulating
        // the stack by a constant value is tracked, and we can constant fold
        // load/stores.
        ctx.insert(Location::Reg(STACK),
            JitVariable::Known(JitValue::Ref(
                Rc::new(JitValue::Stack),
                STACK_TOP
            ))
        );
        Context {
            int,
            bound: ctx,
            // XXX: set this to the real default flags
            flags: vec![JitFlag::Known(0); Flags::FINAL as usize],
            seen: HashMap::new(),
            callstack: vec![],
        }
    }

    pub fn lower(&mut self, f: Function<A, O>) -> Result<(*const u8, u32),LiftError> {
        let translate_result = self.translate(f)?;

        let id = self.module.declare_function(
            "test function",
            Linkage::Export,
            &self.ctx.func.signature)?;
        // Define the function to jit. This finishes compilation, although
        // there may be outstanding relocations to perform. Currently, jit
        // cannot finish relocations until all functions to be called are
        // defined. For this toy demo for now, we'll just finalize the
        // function below.
        let def = self.module.define_function(
            id,
            &mut self.ctx,
            &mut codegen::binemit::NullTrapSink {},
            &mut codegen::binemit::NullStackMapSink {})?;

        // Now that compilation is finished, we can clear out the context state.
        self.module.clear_context(&mut self.ctx);

        // Finalize the functions which we just defined, which resolves any
        // outstanding relocations (patching in addresses, now that they're
        // available).
        self.module.finalize_definitions();

        // We can now retrieve a pointer to the machine code.
        let code = self.module.get_finalized_function(id);
        Ok((code, def.size))
    }

    pub fn format(&self) {
        //println!("{:?}", self.module);
    }

}

// We can't hold a FunctionBuilder and the FunctionBuilderCtx in the same struct,
// so we need this helper struct for the Jit.
struct FunctionTranslator<'a> {
    depth: usize,
    int: Type,
    builder: &'a mut FunctionBuilder<'a>,
    context: Context,
    module: &'a mut dyn Module,
    idx: &'a mut usize,
    return_layout: &'a mut Vec<Type>,
    tracer: &'a mut Tracer<'static>,
    ///// This is a list of blocks that we visited: each pointer is the address of
    ///// the start (aka the jump target).
    //flow: Vec<*const ()>,
    /// a = 1
    /// b = 5
    /// c = 3
    /// do {
    ///     a += 1;
    ///     b -= 1;
    /// } while (b > 0);
    /// a + c
    ///
    /// We pair a snapshot of the context with every entry to a basic block.
    /// This means that on a backwards jump we can find the difference between
    /// the start of block containing the loop and the end we're currently at, so
    /// we have a set of changed registers + stack values. We can then pass these
    /// values in as opaque block parameters in the recompiled loop body, and have
    /// them become parameters for the loop exit block.
    ///
    /// We can also diff the bound set at the start and end of the recompiled loop
    /// to find values that were modified in the loop's *block*, but not the actual
    /// loop body: in our example it would allow us to recover `c = 3`.
    ///
    /// There's a small snag due to multiple loop exits: we can handle this by simply
    /// emitting branches breadth-first in our high-level emit loop, and delay
    /// building the loop body until we have seen all entries, and use the union
    /// of the bound set of all the entries to find the path invariant over all
    /// possibly paths through the loop.
    changed: RangeInclusiveMap<usize, HashMap<Location, JitVariable>>,
}

impl<'a> FunctionTranslator<'a> {
    fn translate<A, O>(&mut self, JitPath(f, bl, ctx): JitPath<A,O>)
            -> Result<Vec<JitPath<A,O>>, LiftError> {

        self.context = ctx;
        let mut base = (f.base as usize) + f.offset.0;
        let mut ip = base;
        println!("starting emitting @ base+0x{:x}", ip - self.tracer.get_base()?);
        let mut stream = f.instructions.clone();
        let mut start_i = f.offset.1;
        let mut i = f.offset.1;
        // snapshot of our context when we started this basic block
        let mut snap = self.context.bound.clone();
        self.builder.switch_to_block(bl);
        // We never loop back to block we've already visited - loops emit a new
        // copy of the body.
        self.builder.seal_block(bl);
        // First, we check if we've already visited the entrypoint of this block
        // before.
        {
            // XXX: hmm i think this actually has to be done on every instruction...
            // if we have a basic block that continues into another one we already
            // emitted with a jump we won't detect it as "looping". maybe that's ok?
            let this_f = self.context.seen.entry(f.base);
            if let std::collections::hash_map::Entry::Occupied(emitted) = this_f {
                if let Some(true) = emitted.get().get(start_i) {
                    unimplemented!("looping @ base+{} ({}), set {:?}",
                        f.base as usize - self.tracer.get_base()?, start_i, emitted.get());
                }
            }
        }

        // Otherwise, we emit all the instructions in our block and handle effects
        'emit: loop {
            let inst = stream.get(i);
            if let None = inst {
                // we ran out of inputs but didn't hit a ret!
                println!("hit translate out @ 0x{:x}", ip);
                return Err(LiftError::TranslateOut(()));
            }
            let inst = inst.unwrap();
            ip += inst.len().to_const() as usize;
            let mut eff = self.emit(ip, inst)?;
            let mut seal = |bl: Block, function_translator: &mut FunctionTranslator| {
                // Mark the entire basic block as visited
                let this_f = function_translator.context.seen.entry(f.base);
                let entry = this_f.or_insert(Vec::with_capacity(i));
                // if we don't have enough slots to mark all our data, we
                // need to grow it so it fits.
                println!("basic block range is {}-{}", start_i, i);
                if entry.len() <= i {
                    entry.resize(i, false);
                }
                for inst in
                    &mut entry[start_i..i] {
                        *inst = true;
                }
                // And then we set the context snapshot we made at the start of the
                // jump to cover the entire range of this block
                // TODO: should this not snapshot if we already have one?
                function_translator.changed.insert(start_i..=i, (&snap).clone());
                // XXX: technically we shouldn't do this, but we can't require
                // that it breaks 'handle after a seal?
                // snap = function_translator.context.bound.clone();
            };
            'handle: loop { match eff {
                EmitEffect::Advance => i += 1,
                EmitEffect::Jmp(target) => {
                    if !(target >= (f.base as usize) && target < (f.base as usize) + f.size) {
                        // this is an unconditional jump out - we clear our coverage
                        // bitmap for the function that's jumping, because it means
                        // we have a tailcall. if we don't do this than two inlined
                        // calls would be detected as a loop, since they go through
                        // the same basic block twice.
                        // we don't unwrap() this because e.g. Fn:call tailcalls from the
                        // first block - which means we never created coverage in the
                        // first place.
                        self.context.seen.remove(&f.base);
                    } else {
                        seal(bl, self);
                    }
                    let jump_target = Function::<A, O>::new(self.tracer, target as *const ())?;
                    //self.tracer.format(&jump_target.instructions)?;
                    //self.inline(jump_target)?;
                    println!("jmp to 0x{:x}", target);
                    let jump_block = self.builder.create_block();
                    self.builder.ins().jump(jump_block, &[]);
                    return Ok(vec![JitPath(jump_target, jump_block, self.context.clone())]);
                },
                EmitEffect::Branch(cond, flags, target) => {
                    seal(bl, self);
                    // if cond isn't false, then we branch to target, otherwise we
                    // fallthrough.
                    // handling branchs is a bit tricky: we snapshot our context,
                    // because we need to isolate effects from one control flow path
                    // from the other. we also give the branches different "version" -
                    // i think there's a way to use (version, addr) tuples for
                    // better block compilation or something idk
                    //
                    // we probably dont ever want to *merge* control flow path,
                    // unfortunately - it's pretty unlikely that both sides of a
                    // branch end up with identical contexts when they merge, and
                    // doing eta nodes or erasing their values back to SSA is hairy
                    // because we lose constant value knowledge, which is our bread
                    // and butter. we can probably have some heuristic idk
                    let jump_target = self.builder.create_block();
                    let continue_target = self.builder.create_block();
                    self.builder.ins().brif(cond, flags,
                        jump_target, &[]);
                    self.builder.ins().jump(continue_target, &[]);

                    let target = Function::<A, O>::new(self.tracer, target as *const ())?;
                    // Our continuation is from here
                    let mut cont = f;
                    cont.offset = (ip - (cont.base as usize), i+1);
                    return Ok(vec![
                        // The branch path
                        JitPath(target, jump_target, self.context.clone()),
                        // The fallthrough
                        JitPath(cont, continue_target, self.context.clone())
                    ]);
                },
                // The emitted code calls an address
                EmitEffect::Call(targ) => {
                    seal(bl, self);
                    // TODO: some inlining heuristic
                    println!("calling {:x}", targ);
                    self.context.callstack.push(ip);
                    let call_targ = Function::<A, O>::new(self.tracer, targ as *const ())?;
                    //self.tracer.format(&call_targ.instructions)?;
                    //self.inline(call_targ)?;
                    let inlined_block = self.builder.create_block();
                    self.builder.ins().jump(inlined_block, &[]);
                    return Ok(vec![JitPath(call_targ, inlined_block, self.context.clone())]);
                },
                // The emitted code tried to return
                EmitEffect::Ret(targ) => {
                    if let Some(targ) = targ {
                        // We keep track of the callstack from call/ret,
                        // so let's also use it as a shadow stack for some
                        // sanity checking.
                        let shadow = self.context.callstack.pop();
                        println!("returning, shadow = {:x}, stack = {:x}", shadow.unwrap(), targ);
                        assert_eq!(shadow, Some(targ));
                        println!("returning to {:x}", targ);
                        // We clear the seen bitmap for our current function:
                        // this is so a new call to it has a clean visitation
                        self.context.seen.remove(&f.base);
                        // then we jump back to callsite to continue the function
                        // that inlined us.
                        let callsite = self.builder.create_block();
                        self.builder.ins().jump(callsite, &[]);

                        let target = Function::<A, O>::new(self.tracer, targ as *const ())?;
                        return Ok(vec![JitPath(target, callsite, self.context.clone())]);


                    } else {
                        seal(bl, self);
                            // We are returning out of the JIT function
                        let r_layout = self.return_layout.clone();
                        let return_values: Vec<Value> = r_layout.iter().enumerate()
                            .map(|(i, r_ty)| {
                                let r_val = &HOST.outputs[i];
                                let mut var = self.get(r_val.clone());
                                var.tmp(self.builder, HOST_WIDTH)
                                    .into_ssa(self.int, self.builder)
                            }).collect();
                        self.builder.ins().return_(&return_values[..]);
                    }
                    break 'emit;
                },
            }; break 'handle; }
        };
        Ok(vec![])
    }

    fn emit(&mut self, ip: usize, inst: &Instruction) -> Result<EmitEffect, LiftError> {

        println!("---- {}", inst);
        let ms = inst.mem_size().and_then(|m| m.bytes_size());
        match inst.opcode() {
            Opcode::MOV => {
                // we need to support mov dword [eax+4], rcx and vice versa, so
                // both the load and store need a mem_size for memory width.
                let val = self.operand_value(ip, inst.operand(1), ms);
                self.store(inst.operand(0), val, ms);
            },
            //Opcode::INC => {
            //    // TODO: set flags
            //    let val = self.operand_value(ip, inst.operand(0), ms);
            //    let inced = self.add::<false>(val, JitValue::Const(Wrapping(1)));
            //    self.store(inst.operand(0), inced, ms);
            //},
            Opcode::ADD => {
                let left = self.operand_value(ip, inst.operand(0), ms);
                let mut right = self.operand_value(ip, inst.operand(1), ms);
                if inst.operand(1).is_imm() {
                    right = right.sign_extend(self.builder, inst.operand(0).width().or(ms).unwrap());
                }
                let added = self.add::<true>(left, right);
                self.store(inst.operand(0), added, ms);
            },
            Opcode::ADC => {
                let left = self.operand_value(ip, inst.operand(0), ms);
                let mut right = self.operand_value(ip, inst.operand(1), ms);
                if inst.operand(1).is_imm() {
                    right = right.sign_extend(self.builder, inst.operand(0).width().or(ms).unwrap());
                }
                let carry = self.context.check_flag(Flags::CF, true, self.builder);
                println!("adc {:?} {:?} {:?}", left, right, carry);
                let added = self.adc::<true>(left, right, carry);
                self.store(inst.operand(0), added, ms);
            },
            op @ (Opcode::SUB | Opcode::CMP) => {
                // sub eax, ff
                // ff gets sign extended to 0xffff_ffff
                let left = self.operand_value(ip, inst.operand(0), ms);
                let mut right = self.operand_value(ip, inst.operand(1), ms);
                if inst.operand(1).is_imm() {
                    right = right.sign_extend(self.builder, inst.operand(0).width().or(ms).unwrap());
                }
                let subbed = self.sub::<true>(left, right);
                if let Opcode::SUB = op {
                    self.store(inst.operand(0), subbed, ms);
                }
            },
            //Opcode::NEG => {
            //    let dest = self.operand_value(ip, inst.operand(0), inst.operand(0).width());
            //    let negged = self.sub::<true>(JitValue::Const(Wrapping(0)), dest);
            //    self.store(inst.operand(0), negged, inst.operand(0).width());
            //},
            op @ (Opcode::AND | Opcode::TEST) => {
                let left = self.operand_value(ip, inst.operand(0), ms);
                let right = self.operand_value(ip, inst.operand(1), ms);
                let anded = self.band(left.clone(), right.clone());
                if let Opcode::AND = op {
                    self.store(inst.operand(0), anded, ms);
                }
            },
            //Opcode::NOP => (),
            Opcode::XOR => {
                if inst.operand(0) == inst.operand(1) {
                    self.store(inst.operand(0), JitTemp::val_of_width(0, inst.operand(0).width().unwrap()), ms);
                }
                let left = self.operand_value(ip, inst.operand(0), ms);
                let right = self.operand_value(ip, inst.operand(1), ms);
                let xored = self.bxor(left.clone(), right.clone());
                self.store(inst.operand(0), xored, ms);
            },
            setcc @ (Opcode::SETA | Opcode::SETAE | Opcode::SETB) => {
                // get what condition they corrospond to
                let cond = self.cond_from_opcode(setcc);
                // and then get the either constant or dynamic flag for whether
                // to branch or not from the condition
                let take = self.check_cond(cond);
                if let JitValue::Const(c) = take {
                    println!("SETcc conditional is {}", c.0);
                    self.store(inst.operand(0), JitTemp::Const8(if c.0 == 1 {
                        1
                    } else {
                        0
                    }), Some(1));
                } else if let JitValue::Value(flags) = take {
                    let one = self.builder.ins().iconst(types::I8, 1);
                    let zero = self.builder.ins().iconst(types::I8, 0);
                    let store = self.builder.ins().selectif(types::I8, cond,
                        flags, one, zero);

                    self.store(inst.operand(0),
                        JitTemp::Value(store, types::I8), Some(1));
                } else {
                    unimplemented!();
                }
            },
            jcc @ (Opcode::JZ | Opcode::JNZ | Opcode::JA | Opcode::JB | Opcode::JNA | Opcode::JNB) => {
                let _target = self.jump_target(inst.operand(0), ip, ms);

                let target;
                if let JitValue::Const(c) = _target {
                    println!("known conditional jump location: 0x{:x}", c.0);
                    target = c.0;
                } else {
                    unimplemented!("dynamic call");
                }

                let cond = self.cond_from_opcode(jcc);
                let take = self.check_cond(cond);
                match take {
                    JitValue::Const(Wrapping(const { false as usize })) => {
                        // we know statically we aren't taking this branch - we
                        // can just go to the next instruction
                        ()
                    },
                    JitValue::Const(Wrapping(_)) => {
                        // we know statically we are taking this branch - just
                        // jump
                        return Ok(EmitEffect::Jmp(target))
                    },
                    JitValue::Flag(flags) => {
                        // we don't know until runtime if we're taking this branch
                        // or not - we return Brnz(cond, target) as an effect,
                        // so our emit loop can emit both sides of the branch.
                        return Ok(EmitEffect::Branch(cond, flags, target));
                    },
                    _ => {
                        unimplemented!();
                    },
                }
            },
            Opcode::LEA => {
                let val = self.effective_address(ip, inst.operand(1))?;
                self.store(inst.operand(0), val, inst.operand(1).width());
            },
            Opcode::PUSH => {
                // push eax
                let val = self.operand_value(ip, inst.operand(0), Some(HOST_WIDTH)); // get rax
                self.shift_stack(-1); // rsp -= 8
                self.store(Operand::RegDeref(STACK), val, Some(HOST_WIDTH)); // [rsp] = rax
            },
            Opcode::POP => {
                // pop rax
                let sp = self.operand_value(ip, Operand::RegDeref(STACK), Some(HOST_WIDTH)); // [rsp]
                self.shift_stack(1); // rsp += 8
                self.store(inst.operand(0), sp, Some(HOST_WIDTH)); // rax = [rsp]
            },
            Opcode::JMP => {
                let target = self.jump_target(inst.operand(0), ip, ms);
                // If we know where the jump is going, we can try to inline
                if let JitValue::Const(c) = target {
                    println!("known jump location: 0x{:x}", c.0);
                    return Ok(EmitEffect::Jmp(c.0));
                } else {
                    unimplemented!("dynamic call");
                }
            },
            Opcode::CALL => {
                // Resolve the call target (either absolute or relative)
                let target = self.jump_target(inst.operand(0), ip, ms);
                if let JitValue::Const(c) = target {
                    println!("putting return address in {:x}", self.context.stack());
                    self.shift_stack(-1); // rsp -= 8
                    self.store(Operand::RegDeref(STACK),
                        HOST_TMP(ip as u64), Some(HOST_WIDTH));
                    // and then we just jump to the call target
                    return Ok(EmitEffect::Call(c.0));
                } else {
                    unimplemented!("call to {} ({:?})", inst.operand(0), target)
                }
            },
            Opcode::RETURN => {
                if inst.operand_present(0) {
                    unimplemented!("return with stack pops");
                }
                // if we were trying to return to the value past the top of the
                // stack, then we were returning out of our emitted function:
                // we're all done jitting, and can tell cranelift to stop.
                if self.context.stack() == STACK_TOP {
                    return Ok(EmitEffect::Ret(None));
                }
                let new_rip = self.operand_value(ip, Operand::RegDeref(STACK), Some(HOST_WIDTH));
                if let Some(JitValue::Const(c)) = new_rip.clone().into_native(self.builder) {
                    self.shift_stack(1);
                    return Ok(EmitEffect::Ret(Some(c.0)));
                } else {
                    self.context.dump();
                    unimplemented!("return to unknown location {:?}", new_rip);
                }
            },
            _ => {
                return Err(LiftError::UnimplementedInst(inst.clone()))
            }
        }
        Ok(EmitEffect::Advance)
    }

    pub fn cond_from_opcode(&mut self, op: Opcode) -> IntCC {
        match op {
            Opcode::JA | Opcode::SETA => IntCC::UnsignedGreaterThan,
            Opcode::JNA => IntCC::UnsignedGreaterThan.inverse(),
            Opcode::SETAE => IntCC::UnsignedGreaterThanOrEqual,
            Opcode::JB | Opcode::SETB => IntCC::UnsignedLessThan,
            Opcode::JNB => IntCC::UnsignedGreaterThanOrEqual,
            Opcode::JZ | Opcode::SETZ => IntCC::Equal,
            Opcode::JNZ | Opcode::SETNZ => IntCC::Equal.inverse(),
            _ => unimplemented!(),
        }
    }

    fn jump_target(&mut self, op: Operand, ip: usize, ms: Option<u8>) -> JitValue {
        // Resolve the jump target (either absolute or relative)
        let target: JitValue = match op {
            absolute @ (
                Operand::Register(_) |
                Operand::RegDeref(_) |
                Operand::RegDisp(_, _)
            ) => {
                self.operand_value(ip, absolute, ms)
                    .zero_extend(self.builder, HOST_WIDTH).into_native(self.builder).unwrap()
            },
            relative @ (
                Operand::ImmediateI8(_)  |
                Operand::ImmediateI16(_) |
                Operand::ImmediateI32(_)
            )=> {
                let val = match relative {
                    Operand::ImmediateI8(i) => i as isize as usize,
                    Operand::ImmediateI16(i) => i as isize as usize,
                    Operand::ImmediateI32(i) => i as isize as usize,
                    _ => unreachable!(),
                };
                JitValue::Const(Wrapping(ip) + Wrapping(val))
            },
            _ => unimplemented!("jump target operand {}", op),
        };
        target
    }


    fn effective_address(&mut self, ip: usize, loc: Operand) -> Result<JitTemp, LiftError> {
        assert_eq!(HOST_WIDTH, 8);
        match loc {
            Operand::RegDeref(r) => {
                unimplemented!();
            },
            Operand::RegDisp(r, disp) => {
                // we can't do this, because `lea bl, [ah]` would be wrong.
                // self::get is kinda dangerous huh
                //let reg = self.get(Location::Reg(r)).tmp(self.builder, r.width());
                let reg = self.operand_value(ip, Operand::Register(r), None);
                let zx = reg.zero_extend(self.builder, HOST_WIDTH);
                Ok(self.add::<false>(zx,
                    HOST_TMP(disp as isize as usize as _))) // XXX: is this right?
            }
            _ => unimplemented!()
        }
    }

    /// Move the stack either up or down N slots. -1 becomes a -4 or -8
    pub fn shift_stack(&mut self, slots: isize) {
        let stack_reg = self.operand_value(0, Operand::Register(STACK), None);
        match stack_reg {
            JitTemp::Ref(ref base, offset)
                if let JitValue::Stack = **base =>
            {
                //println!("shifting stack 0x{:x}", offset);
                assert_eq!(HOST_WIDTH, 8);
                let new_stack = self.add::<false>(stack_reg,
                    HOST_TMP((slots * 8) as usize as u64));
                self.store(Operand::Register(STACK), new_stack, Some(HOST_WIDTH));
            }
            _ => unimplemented!("non-concrete stack!!"),
        }
    }

    pub fn stack_load(&mut self, slot: usize, width: u8) -> JitTemp {
        assert!(slot <= STACK_TOP);
        let offset = slot % (HOST_WIDTH as usize);
        if offset == 0 {
            return self.get(Location::Stack(slot)).tmp(self.builder, width);
        }
        let base = slot - offset;
        assert_eq!(base % (HOST_WIDTH as usize), 0);
        if (offset as u8) + width > HOST_WIDTH {
            unimplemented!("spliced load, {:x}+{}", base, offset);
        } else {
            // A load at Stack(4) of 4 is actually Stack(0) & 0xFFFF_FFFF
            // (little endian)
            let val = self.get(Location::Stack(base)).tmp(self.builder, HOST_WIDTH);
            self.band(val, HOST_TMP((1 << (width*8)+1) - 1))
        }
    }

    pub fn get(&mut self, loc: Location) -> JitVariable {
        // If we didn't already have the register bound to a variable,
        // create a fresh one and return it.
        // This always returns HOST_WIDTH wide values.
        let idx = &mut self.idx;
        let builder = &mut self.builder;
        let int = self.int;
        let key = match loc {
            Location::Reg(r) if r.width() != HOST_WIDTH => Location::Reg(*REGMAP.get(&r).unwrap_or(&r)),
            Location::Stack(s) if s % (HOST_WIDTH as usize) != 0 =>
                panic!("self.get shouldn't be called with non-aligned stack slots. did you mean to use stack_load?"),
            _ => loc
        };
        self.context.bound.entry(key).or_insert_with_key(|key: &Location| {
            if let Location::Stack(s) = key {
                // provide a zeroed stack
                return JitVariable::Known(JitValue::Const(Wrapping(0)));
            }
            let fresh = Variable::new(**idx);
            **idx = **idx + 1;
            // FIXME: registers should be the correct width
            builder.declare_var(fresh, int);
            JitVariable::Variable(fresh)
        }).clone()
    }

    /// Resolve an instruction operand into a JitTemp.
    /// If we have `mov eax, ecx`, we want to resolve ecx to either a use of the
    /// existing ecx variable in our context, or create a new one and use that.
    /// This has to handle *all* operand types, however: if there's an `[ecx]` we need
    /// to emit a deref instruction and return the value result of that as well.
    ///
    /// If the location is a load, `width` is the memory operation size in bytes.
    /// It is ignored for other operand types, so that e.g. `mov dword [rax+4], rcx`
    /// doesn't mistakenly truncate rcx.
    pub fn operand_value(&mut self, ip: usize, loc: Operand, width: Option<u8>) -> JitTemp {
        match loc {
            Operand::Register(const { RegSpec::rip() }) => {
                HOST_TMP(ip as _)
            },
            Operand::RegDisp(const { RegSpec::rip() }, o) => {
                HOST_TMP((Wrapping(ip) + Wrapping(o as isize as usize)).0 as _)
            },
            Operand::Register(r) if r.width() == 1 => {
                match r {
                    const { RegSpec::al() } | const { RegSpec::bl() } |
                    const { RegSpec::cl() } => {
                        // I should probably re-think Const, and add variable
                        // widths to it: there's not really a good reason for
                        // `and al, 0x1` to have to mask out rax for the value
                        // and then bitselect it back in at the store.
                        self.get(Location::Reg(r)).tmp(self.builder, r.width())
                    },
                    _ => unimplemented!("al etc unimplemented")
                }
            },
            Operand::Register(r) => {
                // if we're told to get a register at any width, we actually return
                // the register's width
                self.get(Location::Reg(r)).tmp(self.builder, r.width())
            },
            Operand::Register(const { RegSpec::eip() } | const { RegSpec::esp() }) => {
                unimplemented!("non-native registers")
            },
            // aligned reads are handled by val(), which stitches together the
            // value from multiple stack slots if needed. We only ever store
            // HOST_WIDTH aligned words in the bound map.
            Operand::RegDeref(STACK) => {
                let sp = self.context.stack();
                let v = self.stack_load(sp, width.unwrap());
                println!("[rsp] = {:?}", v);
                v
                //self.get(Location::Stack(sp)).val(self.builder, width.unwrap())
            },
            Operand::RegDisp(STACK, o) => {
                // [rsp-8] becomes Stack(self.stack() - 8)
                let slot = Wrapping(self.context.stack()) + Wrapping(o as isize as usize);
                self.stack_load(slot.0, width.unwrap())
                //self.get(Location::Stack(slot.0 as usize)).val(self.builder, width.unwrap())
            },
            Operand::RegDeref(r) => {
                // XXX: this should properly handle [eax] too - but that's
                // not very likely to show up in real 64bit code, so let's just
                // ignore it for now
                assert_eq!(r.width(), HOST_WIDTH);
                let reg_val = self.get(Location::Reg(r)).tmp(self.builder, r.width());
                match reg_val {
                    JitTemp::Ref(base, offset) => {
                        // we are dereferencing a ref - we just get the data
                        // it's pointing to!
                        match &*base {
                            JitValue::Frozen { addr, size } => {
                                // we are dereferencing a pointer inside our
                                // frozen region: we return the constant data
                                if offset >= *size {
                                    unimplemented!("read outside frozen memory region");
                                }
                                // XXX: self.load(width, jitvalue)?
                                unsafe {
                                    let val = std::ptr::read::<usize>(
                                        addr.offset(offset.try_into().unwrap()) as *const usize);
                                    JitTemp::val_of_width(val, width.unwrap())
                                }
                            },
                            JitValue::Stack => {
                                //self.get(Location::Stack(offset)).val(self.builder, width.unwrap())
                                self.stack_load(offset, width.unwrap())
                            },
                            val @ _ => unimplemented!("value for ref to {:?}", val),
                        }
                    },
                    _ => unimplemented!("deref to {:?}", reg_val),
                }
            },
            Operand::ImmediateI8(c) => {
                JitTemp::Const8(c as u8)
            },
            Operand::ImmediateI32(c) => {
                JitTemp::Const32(c as u32)
            },
            Operand::ImmediateI64(c) => {
                JitTemp::Const64(c as u64)
            },
            _ => unimplemented!("value for {:?}", loc)
        }
    }

    /// Store a JitValue at a specified location.
    /// If the location is a store, it will truncate the value to `width` bytes.
    /// Other location types ignore width, so that `mov rcx, dword [rax+4]` works
    /// properly.
    pub fn store(&mut self, loc: Operand, mut val: JitTemp, width: Option<u8>) {
        // The key to look up for the operand in our context.
        let mut key = match loc {
            Operand::Register(STACK) => {
                // sub rsp, 0x8 gets the stack as the value of rsp,
                // which means it becomes e.g. STACK_TOP-8 after a push.
                // we just get the offset from STACK_TOP, and move stack
                match val {
                    JitTemp::Ref(ref base,offset) if let JitValue::Stack = **base => {
                        assert!(offset <= STACK_TOP);
                        Location::Reg(STACK)
                    }
                    _ => unimplemented!("non-concrete stack! {:?}", val),
                }
            },
            Operand::Register(r) if r.width() != HOST_WIDTH => {
                match width {
                    Some(1) => {
                        let mask = match r {
                            // mov al, 1 is actually mov rax, rax[64:8]:0x1
                            // there's no bl() helper, and b(3) isn't const :(
                            const { RegSpec::al() } | const { RegSpec::bl() } |
                            const { RegSpec::cl() } | const { RegSpec::dl() } => {
                                let parent = *REGMAP.get(&r).unwrap();
                                let parent = self.get(Location::Reg(parent))
                                    .tmp(self.builder, HOST_WIDTH);
                                println!("before on reg = {:?}, val = {:?}", parent, val);
                                let select_mask = HOST_TMP(0xFF);
                                val = self.bitselect(select_mask, val, parent);
                                println!("set lower on reg = {:?}", val);
                            },
                            _ => unimplemented!(),
                        };
                    },
                    Some(2) => unimplemented!(),
                    Some(4) => {
                        // e.g. `mov eax, rcx` means we mask and load only the low
                        // 4 bytes.
                        val = self.band(val, HOST_TMP(0xFFFF_FFFF));
                        ()
                    },
                    Some(8) => (),
                    Some(_) => unimplemented!(),
                    None => (),
                };
                Location::Reg(*REGMAP.get(&r).unwrap())
            },
            Operand::Register(r) if r.width() == HOST_WIDTH => {
                Location::Reg(r)
            },
            Operand::RegDeref(STACK) => {
                Location::Stack(self.context.stack())
            },
            Operand::RegDisp(STACK, o) => {
                let sp = Wrapping(self.context.stack()) + Wrapping(o as isize as usize);
                println!("stack {} = {:x}", loc, sp.0 as usize);
                Location::Stack(sp.0 as usize)
            },
            //Operand::RegDeref(r) => Location::Reg(r),
            //Operand::RegDisp(r, o) => Location::Reg(r),
            _ => unimplemented!("unimplemented key for {:?}", loc),
        };
        // We have to switch stores to unaligned stack slots together as well
        if let Location::Stack(s) = key { if s % (HOST_WIDTH as usize) != 0 {
                println!("unaligned store to stack {:x}", s);
                let off: usize = s % (HOST_WIDTH as usize);
                let slot: usize = s - off;
                let width = width.unwrap();
                if (off as u8) + width > HOST_WIDTH {
                    unimplemented!("splice store, stack(0x{:x}+{}) write {}",
                        slot, off, width);
                }
                // If we're storing 4 bytes to Stack(4), we're actually setting
                // Stack(0) to bitselect(0xFFFF_FFFF, val, Stack(0))
                let main = self.get(Location::Stack(slot)).tmp(self.builder, HOST_WIDTH);
                val = self.bitselect(
                    HOST_TMP((1 << ((off+1)*8)) - 1),
                    val, main);
                println!("value to put aligned is {:?}", val);
                // Our key is now always HOST_WIDTH aligned, so we can just store
                // into it in our bound map.
                key = Location::Stack(slot);
        }};
        match val {
            // If we're just setting a variable to a known value, we copy the
            // value in.
            JitTemp::Frozen { .. } | JitTemp::Ref(_,_) |
            JitTemp::Const8(_) | JitTemp::Const16(_) |
            JitTemp::Const32(_) | JitTemp::Const64(_) => {
                // XXX: this can't just do this. [rax+8] = frozen needs to
                // freeze some constant memory map we keep as well.
                //unimplemented!("fix this");
                let val = val.zero_extend(self.builder, HOST_WIDTH).into_native(self.builder).unwrap();
                self.context.bound.entry(key).insert(JitVariable::Known(val));
            },
            // If we're setting to an SSA value...
            JitTemp::Value(val, typ) => {
                match loc {
                    // rax = val becomes a redefine for the register
                    Operand::Register(_)
                    // [rsp] = val becomes a redefine for the current stack
                    | Operand::RegDeref(STACK)
                    // [rsp-8] = val becomes a redefine for the stack slot
                    | Operand::RegDisp(STACK, _) => {
                        println!("set symbolic");
                        let var = Variable::new(*self.idx);
                        *self.idx = *self.idx + 1;
                        self.builder.declare_var(var, self.int);
                        self.builder.def_var(var, val);
                        self.context.bound.insert(key,
                            JitVariable::Variable(var));
                    },
                    Operand::RegDeref(const { RegSpec::esp() } | const { RegSpec::sp() })
                    | Operand::RegDisp(const { RegSpec::esp() } | const { RegSpec::sp()}, _) => {
                        unimplemented!("non-native stack size");
                    },
                    Operand::RegDeref(r) => {
                        unimplemented!();
                        // [rax] = val becomes a store to the contents of register
                        let reg_val = self.get(key)
                            .tmp(self.builder, r.width()).into_ssa(self.int, self.builder);
                        let ins = self.builder.ins();
                        match width {
                            Some(1) => ins.istore8(MemFlags::new(), val, reg_val, 0),
                            Some(2) => ins.istore16(MemFlags::new(), val, reg_val, 0),
                            Some(4) => ins.istore32(MemFlags::new(), val, reg_val, 0),
                            _ => ins.store(MemFlags::new(), val, reg_val, 0), // ??
                        };
                    },
                    Operand::RegDisp(r, o) => {
                        unimplemented!();
                        let reg_val = self.get(key)
                            .tmp(self.builder, r.width()).into_ssa(self.int, self.builder);
                        let ins = self.builder.ins();
                        match width {
                            Some(1) => ins.istore8(MemFlags::new(), val, reg_val, o),
                            Some(2) => ins.istore16(MemFlags::new(), val, reg_val, o),
                            Some(4) => ins.istore32(MemFlags::new(), val, reg_val, o),
                            _ => ins.store(MemFlags::new(), val, reg_val, o), // ??
                        };
                    },
                    _ => unimplemented!("store for {} ({:?}) = {:?}", loc, loc, val)
                }
            },
            _ => unimplemented!("unknown store for {:?}", val),
        }
    }

    pub fn check_cond(&mut self, cond: IntCC) -> JitValue {
        let flags = match cond {
            IntCC::UnsignedGreaterThan => {
                vec![Flags::CF, Flags::ZF]
            },
            IntCC::UnsignedGreaterThanOrEqual => {
                vec![Flags::CF]
            },
            IntCC::UnsignedLessThan => {
                vec![Flags::CF]
            },
            IntCC::UnsignedLessThanOrEqual => {
                vec![Flags::CF, Flags::ZF]
            },
            IntCC::Equal => {
                vec![Flags::ZF]
            },
            IntCC::NotEqual => {
                vec![Flags::ZF]
            },
            _ => unimplemented!("unimplemented check_cond for {}", cond),
        };
        let mut val = None;
        let mut same = true;
        for flag in flags {
            let flag_cond = &self.context.flags[flag as usize];
            if let Some(set_val) = val {
                if set_val != flag_cond {
                    same = false;
                    break;
                }
            } else {
                val = Some(flag_cond);
            }
        }
        if !same {
            unimplemented!();
        }
        if let Some(JitFlag::Unknown(left, right, res)) = val {
            JitValue::Flag(self.builder.ins().ifcmp(*left, *right))
        } else if let Some(JitFlag::Known(c)) = val {
            println!("constant eflags {:?} with cond {}", c, cond);
            let tmp = match cond {
                IntCC::UnsignedGreaterThan => {
                    // CF=0 and ZF=0
                    let cf = self.context.check_flag(Flags::CF, false, self.builder);
                    let zf = self.context.check_flag(Flags::ZF, false, self.builder);
                    self.band(cf, zf)
                },
                IntCC::UnsignedGreaterThanOrEqual => {
                    // CF=0
                    self.context.check_flag(Flags::CF, false, self.builder)
                },
                IntCC::UnsignedLessThan => {
                    // CF=1
                    self.context.check_flag(Flags::CF, true, self.builder)
                },
                IntCC::UnsignedLessThanOrEqual => {
                    // CF=1 or ZF=1
                    let cf = self.context.check_flag(Flags::CF, true, self.builder);
                    let zf = self.context.check_flag(Flags::ZF, true, self.builder);
                    self.bor(cf, zf)
                },
                IntCC::Equal => {
                    self.context.check_flag(Flags::ZF, true, self.builder)
                },
                IntCC::NotEqual => {
                    self.context.check_flag(Flags::ZF, false, self.builder)
                }
                _ => unimplemented!(),
            };
            // XXX: does cranelift do something dumb and actually make this clobber
            // an entire register or something?
            tmp.zero_extend(self.builder, HOST_WIDTH).into_native(self.builder).unwrap()
        } else {
            unimplemented!()
        }
    }

    /// Get left+right for JitValues.
    /// if FLAG is true, then self.context.flags are updated with eflags
    pub fn add<const FLAG:bool>(&mut self, left: JitTemp, right: JitTemp) -> JitTemp {
        use JitTemp::*;
        use Flags::*;
        let flags = vec![OF, SF, ZF, AF, PF, CF];
        match (left, right) {
            (Value(val_left, typ_left), Value(val_right, _)) => {
                let (res, flag) = self.builder.ins().iadd_cout(val_left, val_right);
                self.context.set_flags(flags, (val_left, val_right, flag));
                Value(res, typ_left)
            },
            (left @ _ , right @ Value(_, _))
            | (left @ Value(_, _), right @ _) => {
                let typ = Type::int((left.width() * 8) as u16).unwrap();
                let _left = left.into_ssa(typ, self.builder);
                let _right = right.zero_extend(self.builder, left.width()).into_ssa(typ, self.builder);
                let (res, flag) = self.builder.ins().iadd_cout(_left, _right);
                self.context.set_flags(flags, (_left, _right, res));
                Value(res, typ)
            },
            (Ref(base, offset), c) if c.is_const() => {
                let c = c.into_usize(self.builder).unwrap();
                Ref(base, do_op!(self.context, FLAG, offset, (c), "add {}, {}", flags, +))
            },
            (offset, Ref(base, c)) if offset.is_const() => {
                let offset = offset.into_usize(self.builder).unwrap();
                Ref(base, do_op!(self.context, FLAG, offset, (c), "add {}, {}", flags, +))
            },
            (left_c, mut right_c) if left_c.clone().is_const() && right_c.clone().is_const() => {
                right_c = right_c.zero_extend(self.builder, left_c.clone().width());
                const_ops!(self.context, FLAG, left_c.clone(), (right_c.clone()), "add {}, {}", flags, +)
            },
            (left, right) => unimplemented!("unimplemented add {:?} {:?}", left, right)
        }
    }

    /// Add with carry
    pub fn adc<const FLAG:bool>(&mut self, left: JitTemp, right: JitTemp, carry: JitTemp) -> JitTemp {
        use JitTemp::*;
        use Flags::*;
        let flags = vec![OF, SF, ZF, AF, PF, CF];
        match (left.clone(), right.clone(), carry.clone()) {
            (Value(val_left, typ_left), Value(val_right, _), Flag(val_carry)) => {
                let (res, flag) = self.builder.ins().iadd_carry(val_left, val_right, val_carry);
                self.context.set_flags(flags, (val_left, val_right, flag));
                Value(res, typ_left)
            },
            (_, _, carry) if carry.is_const() => {
                // basically, this sucks a lot:
                // iadd_carry is broken on cranelift (#2860), so we work around
                // it by lowering to a normal iadd_cout in the CF=false case,
                // and to two iadd_cout's in the CF=true case (and then have to
                // fixup our carry flag so the spliced +1 doesn't break).
                let carry = carry.into_usize(self.builder).unwrap();
                if carry == 0 {
                    return self.add::<FLAG>(left, right);
                } else {
                    let left_plus_one = self.add::<FLAG>(left, Const8(1));
                    // track if the +1 overflowed
                    let carried = self.context.check_flag(Flags::CF, true, self.builder);

                    let res = self.add::<FLAG>(left_plus_one, right);
                    if(FLAG) {
                        // if the +1 definitely carried, we know that carry has to
                        // be set.
                        println!("carried = {:?}", carried);
                        if let JitTemp::Const64(1) = carried {
                            self.context.flags[Flags::CF as usize] = JitFlag::Known(1 << Flags::CF as usize);
                        } else if let JitTemp::Const64(0) = carried {
                            ();
                        } else if let JitTemp::Value(val, typ) = carried {
                            unimplemented!("double check this");
                            // but if we don't know, then we have to OR it with
                            // the other carry flag (which sucks!)
                            let other_carried = self.context.check_flag(Flags::CF, true, self.builder);
                            let maybe_carried = self.bor(other_carried, carried);
                            self.context.set_flags(vec![Flags::CF],
                                (left_plus_one.into_ssa(typ, self.builder),
                                 right.into_ssa(typ, self.builder),
                                 maybe_carried.into_ssa(typ, self.builder)));
                        } else {
                            unimplemented!();
                        }
                    }
                    return res;
                }
            },
            (left @ Value(_, _), right @ _, carry @ _) |
            (left @ _, right @ Value(_, _), carry @ _) |
            (left @ _, right @ _, carry @ Flag(_)) => {
                let typ = Type::int((left.width() * 8) as u16).unwrap();
                let _left = left.into_ssa(typ, self.builder);
                let _right = right.zero_extend(self.builder, left.width()).into_ssa(typ, self.builder);
                let mut _carry = carry.into_ssa(types::IFLAGS, self.builder);
                let (res, flag) = self.builder.ins().iadd_ifcarry(_left, _right, _carry);
                self.context.set_flags(flags, (_left, _right, flag));
                Value(res, typ)
            },
            (Ref(base, offset), off, carry) if off.is_const() && carry.is_const() => {
                let off = off.into_usize(self.builder).unwrap();
                let carry = carry.into_usize(self.builder).unwrap();
                assert_eq!(HOST_WIDTH, 8);
                if carry == 0 {
                    Ref(base, do_op!(self.context, FLAG, offset, off, "add {}, {}", flags, +))
                } else {
                    Ref(base, do_op!(self.context, FLAG, offset, off, "stc; adc {}, {}", flags, +))
                }
            },
            (offset, Ref(base, off), carry) if offset.is_const() && carry.is_const() => {
                let offset = offset.into_usize(self.builder).unwrap();
                let carry = carry.into_usize(self.builder).unwrap();
                assert_eq!(HOST_WIDTH, 8);
                if carry == 0 {
                    Ref(base, do_op!(self.context, FLAG, offset, off, "add {}, {}", flags, +))
                } else {
                    Ref(base, do_op!(self.context, FLAG, offset, off, "stc; adc {}, {}", flags, +))
                }
            },
            (left_c, mut right_c, mut carry_c)
            if left_c.clone().is_const()
            && right_c.clone().is_const()
            && carry_c.clone().is_const() => {
                right_c = right_c.zero_extend(self.builder, left_c.clone().width());
                let carry_c = carry_c.into_usize(self.builder).unwrap();
                assert_eq!(HOST_WIDTH, 8);
                if carry_c == 0 {
                    const_ops!(self.context, FLAG, left_c.clone(), right_c.clone(), "add {}, {}", flags, +)
                } else {
                    const_ops!(self.context, FLAG, left_c.clone(), right_c.clone(), "stc; adc {}, {}", flags, +)
                }
            },
            (left, right, carry) => unimplemented!("unimplemented adc {:?} {:?} {:?}", left, right, carry)
        }
    }



    pub fn sub<const FLAG:bool>(&mut self, left: JitTemp, right: JitTemp) -> JitTemp {
        use JitTemp::*;
        use Flags::*;
        let flags = vec![OF, SF, ZF, AF, PF, CF];
        match (left, right) {
            // sub dest, val is always a dest sized output
            (Value(val_left, typ_left), Value(val_right, _)) => {
                let (res, flag) = self.builder.ins().isub_ifbout(val_left, val_right);
                self.context.set_flags(flags, (val_left, val_right, flag));
                Value(res, typ_left)
            },
            (left @ _ , right @ Value(_, _))
            | (left @ Value(_, _), right @ _) => {
                let typ = Type::int((left.width() * 8) as u16).unwrap();
                let _left = left.into_ssa(typ, self.builder);
                let _right = right.zero_extend(self.builder, left.width()).into_ssa(typ, self.builder);
                let (res, flag) = self.builder.ins().isub_ifbout(_left, _right);
                self.context.set_flags(flags, (_left, _right, flag));
                Value(res, typ)
            },
            // XXX: this is technically incorrect: flags will be wrong, because
            // it's actually supposed to be the flags for (base+offset) - c.
            // let's just miscompile for now? not sure how common cmp reg, c
            // to test pointer equality would be.
            (Ref(base, offset), c) if c.is_const() => {
                let c = c.into_usize(self.builder).unwrap();
                assert!(c < offset && c < 0x100);
                Ref(base, do_op!(self.context, FLAG, offset, c, "sub {}, {}", flags, -))
            },
            (offset, Ref(base, c)) if offset.is_const() => {
                let offset = offset.into_usize(self.builder).unwrap();
                assert!(c < offset && c < 0x100);
                Ref(base, do_op!(self.context, FLAG, offset, c, "sub {}, {}", flags, -))
            },
            (left_c, mut right_c) if left_c.clone().is_const() && right_c.clone().is_const() => {
                right_c = right_c.zero_extend(self.builder, left_c.clone().width());
                const_ops!(self.context, FLAG, left_c.clone(), right_c.clone(), "sub {}, {}", flags, -)
            },
            (left, right) => unimplemented!("unimplemented sub {:?} {:?}", left, right)
        }
    }

    /// Sub with borrow
    pub fn sbb<const FLAG:bool>(&mut self, left: JitTemp, right: JitTemp, borrow: JitTemp) -> JitTemp {
        use JitTemp::*;
        use Flags::*;
        let flags = vec![OF, SF, ZF, AF, PF, CF];
        match (left.clone(), right.clone(), borrow.clone()) {
            (Value(val_left, typ_left), Value(val_right, _), Flag(val_borrow)) => {
                let (res, flag) = self.builder.ins().isub_borrow(val_left, val_right, val_borrow);
                self.context.set_flags(flags, (val_left, val_right, flag));
                Value(res, typ_left)
            },
            (_, _, borrow) if borrow.is_const() => {
                // see note in self.adc
                let borrow = borrow.into_usize(self.builder).unwrap();
                if borrow == 0 {
                    return self.sub::<FLAG>(left, right);
                } else {
                    unimplemented!()
                }
            },
            (left @ Value(_, _), right @ _, borrow @ _) |
            (left @ _, right @ Value(_, _), borrow @ _) |
            (left @ _, right @ _, borrow @ Flag(_)) => {
                let typ = Type::int((left.width() * 8) as u16).unwrap();
                let _left = left.into_ssa(typ, self.builder);
                let _right = right.zero_extend(self.builder, left.width()).into_ssa(typ, self.builder);
                let mut _borrow = borrow.into_ssa(types::IFLAGS, self.builder);
                let (res, flag) = self.builder.ins().isub_borrow(_left, _right, _borrow);
                self.context.set_flags(flags, (_left, _right, flag));
                Value(res, typ)
            },
            (Ref(base, offset), off, borrow) if off.is_const() && borrow.is_const() => {
                let off = off.into_usize(self.builder).unwrap();
                let borrow = borrow.into_usize(self.builder).unwrap();
                assert_eq!(HOST_WIDTH, 8);
                if borrow == 0 {
                    Ref(base, do_op!(self.context, FLAG, offset, off, "sub {}, {}", flags, +))
                } else {
                    Ref(base, do_op!(self.context, FLAG, offset, off, "stc; sbb {}, {}", flags, +))
                }
            },
            (offset, Ref(base, off), borrow) if offset.is_const() && borrow.is_const() => {
                let offset = offset.into_usize(self.builder).unwrap();
                let borrow = borrow.into_usize(self.builder).unwrap();
                assert_eq!(HOST_WIDTH, 8);
                if borrow == 0 {
                    Ref(base, do_op!(self.context, FLAG, offset, off, "sub {}, {}", flags, +))
                } else {
                    Ref(base, do_op!(self.context, FLAG, offset, off, "stc; sbb {}, {}", flags, +))
                }
            },
            (left_c, mut right_c, mut borrow)
            if left_c.clone().is_const()
            && right_c.clone().is_const()
            && borrow.clone().is_const() => {
                right_c = right_c.zero_extend(self.builder, left_c.clone().width());
                let borrow = borrow.into_usize(self.builder).unwrap();
                assert_eq!(HOST_WIDTH, 8);
                if borrow == 0 {
                    const_ops!(self.context, FLAG, left_c.clone(), right_c.clone(), "sub {}, {}", flags, +)
                } else {
                    const_ops!(self.context, FLAG, left_c.clone(), right_c.clone(), "stc; sbb {}, {}", flags, +)
                }
            },
            (left, right, borrow) => unimplemented!("unimplemented sbb {:?} {:?} {:?}", left, right, borrow)
        }
    }



    pub fn band(&mut self, mut left: JitTemp, mut right: JitTemp) -> JitTemp {
        use JitTemp::*;
        let biggest = max(left.width(), right.width());
        left = left.zero_extend(self.builder, biggest);
        right = right.zero_extend(self.builder, biggest);
        // XXX: set flags!!
        match (left.clone(), right.clone()) {
            (c, other) | (other, c) if c.is_const() => {
                let fixed_c = c.into_usize(self.builder).unwrap();
                match (fixed_c, other.clone()) {
                    //0 & val or val & 0 = 0
                    (0, _) => return JitTemp::val_of_width(0, biggest),
                    // !0 & val or val & !0 = val
                    (const { !0 as usize }, _) => return other,
                    // left_c & right_c is just left & right
                    (fixed_c, other) if other.clone().is_const() => {
                        let fixed_other = other.into_usize(self.builder).unwrap();
                        return JitTemp::val_of_width(fixed_c & fixed_other, biggest)
                    },
                    (_, _) => (),
                }
            },
            _ => (),
        };

        match (left, right) {
            // add rsp, 0x8 becomes a redefine of rsp with offset -= 1
            (Value(val_left, typ_left), Value(val_right, typ_right)) => {
                Value(self.builder.ins().band(val_left, val_right), typ_left)
            },
            (val @ _, Value(ssa, ssa_typ))
            | (Value(ssa, ssa_typ), val @ _) => {
                let ssa_val = val.into_ssa(self.int, self.builder);
                Value(self.builder.ins().band(ssa_val, ssa), ssa_typ)
            },
            (Ref(base, offset), _)
            | (_, Ref(base, offset)) => {
                unimplemented!("band pointer")
            },
            (left, right) => unimplemented!("unimplemented band {:?} {:?}", left, right)
        }
    }

    pub fn bor(&mut self, mut left: JitTemp, mut right: JitTemp) -> JitTemp {
        use JitTemp::*;
        let biggest = max(left.width(), right.width());
        left = left.zero_extend(self.builder, biggest);
        right = right.zero_extend(self.builder, biggest);
        // XXX: set flags!!
        match (left.clone(), right.clone()) {
            (c, other) | (other, c) if c.is_const() => {
                let fixed_c = c.into_usize(self.builder).unwrap();
                match (fixed_c, other) {
                    //0 | val or val | 0 = 0
                    (0, val) => return val,
                    // left_c | right_c is just left | right
                    (fixed_c, other) if other.is_const() => {
                        let fixed_other = other.into_usize(self.builder).unwrap();
                        return JitTemp::val_of_width(fixed_c | fixed_other, biggest)
                    },
                    (_, _) => (),
                }
            },
            _ => (),
        };

        match (left, right) {
            (Value(val_left, typ_left), Value(val_right, typ_right)) => {
                Value(self.builder.ins().bor(val_left, val_right), typ_left)
            },
            (val @ _, Value(ssa, ssa_typ))
            | (Value(ssa, ssa_typ), val @ _) => {
                let ssa_val = val.into_ssa(self.int, self.builder);
                Value(self.builder.ins().bor(ssa_val, ssa), ssa_typ)
            },
            (Ref(base, offset), _)
            | (_, Ref(base, offset)) => {
                unimplemented!("bor pointer")
            },
            (left, right) => unimplemented!("unimplemented bor {:?} {:?}", left, right)
        }
    }

    pub fn bxor(&mut self, mut left: JitTemp, mut right: JitTemp) -> JitTemp {
        use JitTemp::*;
        if left == right {
            return JitTemp::val_of_width(0, left.width())
        }
        let biggest = max(left.width(), right.width());
        left = left.zero_extend(self.builder, biggest);
        right = right.zero_extend(self.builder, biggest);
        // XXX: set flags
        match (left.clone(), right.clone()) {
            (c, other) | (other, c) if c.is_const() => {
                let fixed_c = c.into_usize(self.builder).unwrap();
                match (fixed_c, other) {
                    (fixed_c, other) if other.is_const() => {
                        let fixed_other = other.into_usize(self.builder).unwrap();
                        return JitTemp::val_of_width(fixed_c ^ fixed_other, biggest)
                    },
                    (_, _) => (),
                }
            },
            _ => (),
        }

        match (left, right) {
            (Value(val_left, typ_left), Value(val_right, typ_right)) => {
                Value(self.builder.ins().bxor(val_left, val_right), typ_left)
            },
            (val @ _, Value(ssa, ssa_typ))
            | (Value(ssa, ssa_typ), val @ _) => {
                let ssa_val = val.into_ssa(self.int, self.builder);
                Value(self.builder.ins().bxor(ssa_val, ssa), ssa_typ)
            },
            (left, right) => unimplemented!("unimplemented bxor {:?} {:?}", left, right)
        }
    }

    pub fn bitselect(&mut self, mut control: JitTemp, mut left: JitTemp, mut right: JitTemp) -> JitTemp {
        use JitTemp::*;
        let biggest = max(control.width(), max(left.width(), right.width()));
        println!("bitselect {:?} {:?} {:?} (biggest={})", control, left, right, biggest);
        control = control.zero_extend(self.builder, biggest);
        left = left.zero_extend(self.builder, biggest);
        right = right.zero_extend(self.builder, biggest);
        // bitselect doesn't have a set flags version
        if control.is_const() {
            let fixed_control = control.clone().into_usize(self.builder).unwrap();
            match fixed_control {
                //bitselect(0, left, right) => right
                0 => return right,
                //bitselect(!0, left, right) => left
                const { !0 as usize } => return left,
                _ => (),
            };
        }
        if left.is_const() {
            let fixed_left = left.clone().into_usize(self.builder).unwrap();
            match fixed_left {
                //bitselect(control, 0, right) => !control & right
                0 => {
                    let ncontrol = self.bnot(control);
                    return self.band(ncontrol, right)
                },
                _ => ()
            };
        }
        if right.is_const() {
            let fixed_right = right.clone().into_usize(self.builder).unwrap();
            match fixed_right {
                //bitselect(control, left, 0) => control & left
                0 => return self.band(control, left),
                _ => ()
            }
        }
        match (control, left, right) {
            (control, left, right) if control.is_const() && left.is_const() && right.is_const() => {
                let true_mask = self.band(control.clone(), left);
                let not_control = self.bnot(control);
                let false_mask = self.band(not_control, right);
                self.bor(true_mask, false_mask)
            },
            (control @ _, Value(val_left, typ_left), Value(val_right, _)) => {
                let control = control.into_ssa(self.int, self.builder);
                Value(self.builder.ins().bitselect(control, val_left, val_right), typ_left)
            },
            (control, left, right) =>
                unimplemented!("unimplemented bitselect {:?} {:?} {:?}", control, left, right)

        }
    }

    pub fn bnot(&mut self, val: JitTemp) -> JitTemp {
        use JitTemp::*;
        match val {
            Value(val, typ) => Value(self.builder.ins().bnot(val), typ),
            Const8(c) => Const8(!c),
            Const16(c) => Const16(!c),
            Const32(c) => Const32(!c),
            Const64(c) => Const64(!c),
            _ => unimplemented!("bnot {:?}", val),
        }
    }
}