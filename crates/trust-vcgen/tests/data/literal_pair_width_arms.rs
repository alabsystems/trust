// LITERAL-PAIR-WIDTH-1 and SELF-GUARDED-LITERAL-OPERAND-2: the source of
// `literal_pair_<fn>.json` (README, "Literal pair width family"). Each dump is the
// compiler's own extracted verification input for the function `<fn>`.
//
// A width-less signed literal (`ConstValue::Int`) carries no type, and
// `operand_ty` types it i64 (i128 when the value does not fit i64). When BOTH
// operands of a signed `Div`/`Rem`, or both arguments of an `unchecked_*` method
// call, are such literals, no operand carries the operation's width. These rows
// were built at i64. The signed-literal SHIFT amount (`x << 40`, amount `i32`) is
// the shift-binder sibling: the assert compares a cast temporary
// `_t = const 40_i32 as u32`, and the binder refused a literal cast source.
//
// Every function below except the `ok_*` and `ctl_*` ones fails on every call (a
// panic, or UB for the intrinsics), so none of its rows may read `proved`. The
// `ok_*` twins are safe and keep one honest row. The `ctl_*` controls were already
// typed at their true width and must not move.
#![feature(core_intrinsics)]
#![allow(internal_features, arithmetic_overflow, unconditional_panic, overflowing_literals)]

use std::intrinsics::{unchecked_div, unchecked_rem};

// The intrinsics: `LowerIntrinsics` leaves a bare `_0 = Div(const MIN, const -1)`
// with NO assert, so this row is the function's ONLY obligation.
pub fn ud8() -> i8 {
    unsafe { unchecked_div(i8::MIN, -1) }
}

pub fn ud16() -> i16 {
    unsafe { unchecked_div(i16::MIN, -1) }
}

pub fn ud32() -> i32 {
    unsafe { unchecked_div(i32::MIN, -1) }
}

pub fn ud128() -> i128 {
    unsafe { unchecked_div(i128::MIN, -1) }
}

pub fn ur8() -> i8 {
    unsafe { unchecked_rem(i8::MIN, -1) }
}

// i64: the fabricated width coincides with the true one.
pub fn ctl_ud64() -> i64 {
    unsafe { unchecked_div(i64::MIN, -1) }
}

// A place on either side carries the width.
pub fn ctl_ud_px(x: i8) -> i8 {
    unsafe { unchecked_div(x, -1) }
}

pub fn ctl_ud_py(y: i8) -> i8 {
    unsafe { unchecked_div(-128, y) }
}

// The checked chain: zero assert (a nonzero literal divisor, folded), the overflow
// assert `Eq(const -1, const -1) & Eq(const MIN, const MIN)`, then the operation.
pub fn cd8() -> i8 {
    i8::MIN / -1
}

pub fn cd32() -> i32 {
    i32::MIN / -1
}

pub fn cr16() -> i16 {
    i16::MIN % -1
}

pub fn cd128() -> i128 {
    i128::MIN / -1
}

pub fn ctl_cd64() -> i64 {
    i64::MIN / -1
}

pub fn ctl_cdsize() -> isize {
    isize::MIN / -1
}

// The safe twin: `100 / 7` cannot overflow.
pub fn ok_cd32() -> i32 {
    100 / 7
}

// `unchecked_{add,mul}` as METHOD calls (stable): the call arm, not the
// `AddUnchecked` statement the intrinsic lowers to.
pub fn ua8() -> i8 {
    unsafe { i8::MAX.unchecked_add(1) }
}

pub fn um8() -> i8 {
    unsafe { 100i8.unchecked_mul(2) }
}

pub fn ok_ua8() -> i8 {
    unsafe { 100i8.unchecked_add(27) }
}

// Signed-literal shift amounts (the default `i32`, and a suffixed one).
pub fn shl_lit(x: u32) -> u32 {
    x << 40
}

pub fn shr_lit(x: i64) -> i64 {
    x >> 64
}

pub fn shl_u8x(x: u8) -> u8 {
    x << 8
}

pub fn shl_i32c(x: u64) -> u64 {
    x << 64i32
}

pub fn shl_neg(x: u32) -> u32 {
    x << -1
}

// The safe twin: `x << 8` on a `u32`.
pub fn ok_shl(x: u32) -> u32 {
    x << 8
}

// Unsigned literal amounts: no cast temporary, the assert compares the literal.
pub fn ctl_shl_u8(x: u32) -> u32 {
    x << 40u8
}

pub fn ctl_shl_u64(x: u64) -> u64 {
    x << 64u64
}

pub fn ctl_shl_usize(x: u64) -> u64 {
    x << 64usize
}
