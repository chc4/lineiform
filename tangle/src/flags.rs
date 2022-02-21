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

