//@ revisions: div neg shl shr dminm1 rem16 div128
//@ run-fail
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=off
//@[div] error-pattern: attempt to divide by zero
//@[neg] error-pattern: attempt to negate with overflow
//@[shl] error-pattern: attempt to shift left with overflow
//@[shr] error-pattern: attempt to shift right with overflow
//@[dminm1] error-pattern: attempt to divide with overflow
//@[rem16] error-pattern: attempt to calculate the remainder with overflow
//@[div128] error-pattern: attempt to divide with overflow
//@ ignore-emscripten no processes
//! The WITNESS for `self_guarded_literal_operand.rs` (SELF-GUARDED-LITERAL-OPERAND-1):
//! `div_lit(0)` panics "attempt to divide by zero" and `n32()` panics "attempt to
//! negate with overflow". Before the fix the verifier published a clean-kernel
//! `Certified` PROVED `divzero` row at `100 / x` (beside the assert lane's FAILED
//! one) and the only `negation` row of `-i32::MIN`, PROVED and certified. This file
//! passes before and after the fix: it pins the panics those rows must not deny.
//!
//! SELF-GUARDED-LITERAL-OPERAND-2 (2026-10-13): `x << 40` (`u32`), `x >> 64` (`i64`),
//! `i32::MIN / -1`, `i16::MIN % -1` and `i128::MIN / -1` panic on every call, as stock
//! rustc's binaries do (`scratchpad/scout26/confirm-litop2/runbin.rs`, exit 101 each),
//! while the verifier published a clean-kernel `Certified` PROVED `shift:*` or
//! `overflow:div|rem` row at each span beside the FAILED one.
#![allow(arithmetic_overflow, unconditional_panic)]

#[inline(never)]
pub fn div_lit(x: i32) -> i32 {
    100 / x
}

#[inline(never)]
pub fn n32() -> i32 {
    -i32::MIN
}

#[inline(never)]
pub fn shl_lit(x: u32) -> u32 {
    x << 40
}

#[inline(never)]
pub fn shr_lit(x: i64) -> i64 {
    x >> 64
}

#[inline(never)]
pub fn d_minm1() -> i32 {
    i32::MIN / -1
}

#[inline(never)]
pub fn r16() -> i16 {
    i16::MIN % -1
}

#[inline(never)]
pub fn d128() -> i128 {
    i128::MIN / -1
}

fn main() {
    #[cfg(div)]
    println!("{}", div_lit(std::hint::black_box(0)));
    #[cfg(neg)]
    println!("{}", n32());
    #[cfg(shl)]
    println!("{}", shl_lit(std::hint::black_box(1)));
    #[cfg(shr)]
    println!("{}", shr_lit(std::hint::black_box(1)));
    #[cfg(dminm1)]
    println!("{}", d_minm1());
    #[cfg(rem16)]
    println!("{}", r16());
    #[cfg(div128)]
    println!("{}", d128());
}
