//@ revisions: nm_zero nm_overflow nm_negative_overflow nm_i8_literal
//@ revisions: funnel_shl funnel_shr funnel_shl_literal
//@ revisions: cast cast_signed_target cast_negative cast_signed cast_unsigned cast_fn_item
//@ revisions: cast_from cast_from_assoc cast_from_fn_item
//@ revisions: from_days from_weeks
//@ run-fail
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=off -Coverflow-checks=on
//@[nm_zero] error-pattern: attempt to calculate the remainder with a divisor of zero
//@[nm_overflow] error-pattern: attempt to add with overflow
//@[nm_negative_overflow] error-pattern: attempt to add with overflow
//@[nm_i8_literal] error-pattern: attempt to add with overflow
//@[funnel_shl] error-pattern: attempt to funnel shift left with overflow
//@[funnel_shr] error-pattern: attempt to funnel shift right with overflow
//@[funnel_shl_literal] error-pattern: attempt to funnel shift left with overflow
//@[cast] error-pattern: attempt to cast integer with overflow
//@[cast_signed_target] error-pattern: attempt to cast integer with overflow
//@[cast_negative] error-pattern: attempt to cast integer with overflow
//@[cast_signed] error-pattern: attempt to cast integer with overflow
//@[cast_unsigned] error-pattern: attempt to cast integer with overflow
//@[cast_fn_item] error-pattern: attempt to cast integer with overflow
//@[cast_from] error-pattern: attempt to cast integer with overflow
//@[cast_from_assoc] error-pattern: attempt to cast integer with overflow
//@[cast_from_fn_item] error-pattern: attempt to cast integer with overflow
//@[from_days] error-pattern: overflow in Duration::from_days
//@[from_weeks] error-pattern: overflow in Duration::from_weeks
//@ ignore-emscripten no processes
//! The run twin of `std_numeric_value_panics_charged_nightly.rs`
//! (NUM-NIGHTLY-UNCHARGED-1): the WITNESS that every function of that file's
//! `nightly` revision really panics on the caller's value. Built with
//! verification OFF, each revision calls one of them with the panicking value and
//! exits 101 with core's own message, so a verifier that ever accepted one of
//! those functions again would be reporting a panicking program panic-free.
//!
//! `nm_negative_overflow` is the witness for the `rhs < -1` half of the signed
//! `next_multiple_of` row: `i32::MIN.next_multiple_of(-3)` rounds DOWN past
//! `MIN` (`MIN % -3 == -2`, so core adds `-3 - -2 == -1`).
//!
//! Measured 2026-10-06 on the stage 1 of `9e11546767` (`scratchpad/stage1-w17`),
//! this file's flags plus `--cfg <revision>`: every revision exits 101 with its
//! `error-pattern` on stderr. Verification is off, so the fix does not move it.
//!
//! The `cast_from*` revisions (wave-19 review, 2026-10-09) witness the trait spelling
//! `CheckedCastFromInt::strict_cast_from` that `strict_cast` delegates to: the UFCS
//! call, the `i8::strict_cast_from` associated-function call and the fn item.

#![allow(unused)]
// `funnel_shifts` stabilized in 1.101; naming it in the feature list now warns.
#![feature(int_roundings, integer_casts, integer_cast_extras)]
#![feature(duration_constructors)]
use core::convert::CheckedCastFromInt;
use std::hint::black_box;
use std::time::Duration;

#[inline(never)]
fn next_mult_i32(a: i32, b: i32) -> i32 {
    a.next_multiple_of(b)
}

#[inline(never)]
fn next_mult_i8_lit(a: i8) -> i8 {
    a.next_multiple_of(8)
}

#[inline(never)]
fn funnel_shl_u32(a: u32, b: u32, n: u32) -> u32 {
    a.funnel_shl(b, n)
}

#[inline(never)]
fn funnel_shr_u64(a: u64, b: u64, n: u32) -> u64 {
    a.funnel_shr(b, n)
}

#[inline(never)]
fn funnel_shl_lit_bad(a: u32, b: u32) -> u32 {
    a.funnel_shl(b, 32)
}

#[inline(never)]
fn strict_cast_u32_u8(a: u32) -> u8 {
    a.strict_cast::<u8>()
}

#[inline(never)]
fn strict_cast_i64_i8(a: i64) -> i8 {
    a.strict_cast::<i8>()
}

#[inline(never)]
fn strict_cast_i32_u64(a: i32) -> u64 {
    a.strict_cast::<u64>()
}

#[inline(never)]
fn strict_cast_signed_u32(a: u32) -> i32 {
    a.strict_cast_signed()
}

#[inline(never)]
fn strict_cast_unsigned_i32(a: i32) -> u32 {
    a.strict_cast_unsigned()
}

#[inline(never)]
fn strict_cast_signed_fn_item(o: Option<u32>) -> Option<i32> {
    o.map(u32::strict_cast_signed)
}

#[inline(never)]
fn strict_cast_from_ufcs(a: u32) -> u8 {
    <u8 as core::convert::CheckedCastFromInt<u32>>::strict_cast_from(a)
}

#[inline(never)]
fn strict_cast_from_assoc(a: i64) -> i8 {
    i8::strict_cast_from(a)
}

#[inline(never)]
fn strict_cast_from_fn_item(o: Option<u32>) -> Option<u8> {
    o.map(<u8 as core::convert::CheckedCastFromInt<u32>>::strict_cast_from)
}

#[inline(never)]
fn dur_from_days(d: u64) -> Duration {
    Duration::from_days(d)
}

#[inline(never)]
fn dur_from_weeks(w: u64) -> Duration {
    Duration::from_weeks(w)
}

fn main() {
    #[cfg(nm_zero)]
    black_box(next_mult_i32(black_box(5), black_box(0)));
    #[cfg(nm_overflow)]
    black_box(next_mult_i32(black_box(i32::MAX), black_box(2)));
    #[cfg(nm_negative_overflow)]
    black_box(next_mult_i32(black_box(i32::MIN), black_box(-3)));
    #[cfg(nm_i8_literal)]
    black_box(next_mult_i8_lit(black_box(121)));
    #[cfg(funnel_shl)]
    black_box(funnel_shl_u32(black_box(1), black_box(2), black_box(40)));
    #[cfg(funnel_shr)]
    black_box(funnel_shr_u64(black_box(1), black_box(2), black_box(64)));
    #[cfg(funnel_shl_literal)]
    black_box(funnel_shl_lit_bad(black_box(1), black_box(2)));
    #[cfg(cast)]
    black_box(strict_cast_u32_u8(black_box(300)));
    #[cfg(cast_signed_target)]
    black_box(strict_cast_i64_i8(black_box(300)));
    #[cfg(cast_negative)]
    black_box(strict_cast_i32_u64(black_box(-1)));
    #[cfg(cast_signed)]
    black_box(strict_cast_signed_u32(black_box(3_000_000_000)));
    #[cfg(cast_unsigned)]
    black_box(strict_cast_unsigned_i32(black_box(-1)));
    #[cfg(cast_fn_item)]
    black_box(strict_cast_signed_fn_item(black_box(Some(u32::MAX))));
    #[cfg(cast_from)]
    black_box(strict_cast_from_ufcs(black_box(300)));
    #[cfg(cast_from_assoc)]
    black_box(strict_cast_from_assoc(black_box(300)));
    #[cfg(cast_from_fn_item)]
    black_box(strict_cast_from_fn_item(black_box(Some(300))));
    #[cfg(from_days)]
    black_box(dur_from_days(black_box(u64::MAX)));
    #[cfg(from_weeks)]
    black_box(dur_from_weeks(black_box(u64::MAX)));
}
