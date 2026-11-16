//@ needs-trust-verify
//@ edition: 2021
//@ revisions: clamp_int clamp_non_primitive clamp_float ilog2 ilog10 ilog isqrt
//@ revisions: next_multiple_of next_power_of_two strict operator_calls to_digit from_digit
//@ revisions: from_str_radix nonzero_negation duration_constructors duration_float
//@ revisions: duration_arith time_point range_iteration adversarial guarded
//@ revisions: from_ascii_radix
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@[clamp_int] check-fail
//@[clamp_non_primitive] check-fail
//@[clamp_float] check-fail
//@[ilog2] check-fail
//@[ilog10] check-fail
//@[ilog] check-fail
//@[isqrt] check-fail
//@[next_multiple_of] check-fail
//@[next_power_of_two] check-fail
//@[strict] check-fail
//@[operator_calls] check-fail
//@[to_digit] check-fail
//@[from_digit] check-fail
//@[from_str_radix] check-fail
//@[from_ascii_radix] check-fail
//@[nonzero_negation] check-fail
//@[duration_constructors] check-fail
//@[duration_float] check-fail
//@[duration_arith] check-fail
//@[time_point] check-fail
//@[range_iteration] check-fail
//@[adversarial] check-fail
//@[guarded] check-pass
//! THE STD NUMERIC METHODS THAT PANIC ON AN ARGUMENT VALUE (audit and fix,
//! 2026-09-25): a FALSE ACCEPT class. Every function in a check-fail revision
//! below was measured on the default verifying lane of stage-1 origin/main
//! `8d6aadf7e9` — built rc=0 (most with one runtime-checked row for the
//! tolerated sysroot callee, some with none at all) — and a verify-off driver
//! passing the named value panicked (exit 101):
//!
//!   * `clamp_int` / `clamp_non_primitive` — `Ord::clamp` with `min > max`
//!     ("min > max. min = 10, max = 1" / "assertion failed: min <= max");
//!   * `clamp_float` — `f64/f32::clamp` with `min > max` or a NaN bound;
//!   * `ilog2` / `ilog10` / `ilog` — a non-positive argument, or a base < 2;
//!   * `isqrt` — a negative signed argument (also handed over as a fn item);
//!   * `next_multiple_of` / `next_power_of_two` — a zero divisor, or overflow;
//!   * `strict` — the `strict_*` family (stable 1.91), which panics
//!     unconditionally on overflow, `MIN % -1`, an over-wide shift, and (for
//!     an unsigned `strict_neg`) any nonzero value;
//!   * `operator_calls` — `Add::add(a, b)`, `Shl::shl`, `Neg::neg` spelled as
//!     explicit by-value calls, which skipped the obligation `a + b` owes, and
//!     the compound-assign calls `a.add_assign(b)`/`sub_assign`/`mul_assign`/
//!     `shl_assign` (no row at all; review of `ff3a28cc92`, 2026-09-28);
//!   * `to_digit` / `from_digit` / `from_str_radix` — a radix outside `[2, 36]`
//!     (`from_digit`: `> 36`), including `NonZero::from_str_radix`;
//!   * `from_ascii_radix` — the nightly `int_from_ascii` sibling of
//!     `from_str_radix` (which calls it), on a primitive and on `NonZero`: the
//!     same radix panic, missed by the stable-only audit (ASCII-FROM-ASCII-RADIX-1,
//!     added 2026-10-05; see the revision's own section for BEFORE/AFTER);
//!   * `nonzero_negation` — `NonZero<iN>::abs` and `-nz` at `MIN`;
//!   * `duration_constructors` / `duration_float` / `duration_arith` —
//!     `Duration::new` nanosecond carry, `from_mins/hours/nanos_u128`, the
//!     float constructors and scalings, `+ - * /` and their assign forms, and
//!     `Iterator::sum` over `Duration` (also into `Option`/`Result<Duration>`);
//!   * `time_point` — `Instant`/`SystemTime` `+ -` a caller's `Duration`, and a
//!     literal `Duration` on a CALLER's time point (built at the representable
//!     edge with `checked_add`) or on a loop-carried `+=` receiver;
//!   * `range_iteration` — `(a..).next()`/`nth` past `MAX` (including a `for`
//!     loop, `char`, every advancing consumer such as `find`/`any`/`count`, and
//!     the explicit `&mut RangeFrom` spelling), and `count()` past `usize::MAX`;
//!   * `adversarial` — the same panics behind a closure, a private helper, a
//!     guard on the wrong variable or the wrong way round, and an off-by-one.
//!
//! Their panic lives INSIDE the library (an `assert!`, a `#[cold]` panic
//! helper, `.expect`, or core's own overflow check), where the bundled member's
//! check is reported rather than failed, and the caller's MIR had no `Assert`
//! for it. The call now carries a call-site row (`generate::numeric_panic`): a
//! precise bound the guard proves and an unguarded call refutes, or a
//! fail-closed `UnsupportedMir` row where no sound linear model exists (a
//! non-literal float bound, a non-primitive `Ord`, `Duration` arithmetic on
//! non-literal values, a `RangeFrom` whose current start is loop state).
//!
//! `guarded` pins the other direction: the guarded twins, literal arguments
//! that cannot panic, the total siblings (`checked_ilog2`, unsigned `isqrt`,
//! `NonZero::ilog2`, `Instant - Instant`), a guard through a private helper,
//! user methods and traits that merely share a name, and the ruled
//! reference-arithmetic class (`foundational_member_qualified_path.rs`).

#![allow(unused)]
#![cfg_attr(any(from_ascii_radix, guarded), feature(int_from_ascii))]
use std::num::{NonZeroI32, NonZeroU32, NonZeroU64};
use std::ops::{AddAssign, MulAssign, ShlAssign, SubAssign};
use std::time::{Duration, Instant, SystemTime};

// ---- clamp_int ----

#[cfg(clamp_int)]
pub fn clamp_i32(x: i32, lo: i32, hi: i32) -> i32 {
    //[clamp_int]~^ ERROR `std_numeric_value_panics_charged::clamp_i32`
    x.clamp(lo, hi)
}

#[cfg(clamp_int)]
pub fn clamp_u8(x: u8, lo: u8, hi: u8) -> u8 {
    //[clamp_int]~^ ERROR `std_numeric_value_panics_charged::clamp_u8`
    x.clamp(lo, hi)
}

#[cfg(clamp_int)]
pub fn clamp_usize(x: usize, lo: usize, hi: usize) -> usize {
    //[clamp_int]~^ ERROR `std_numeric_value_panics_charged::clamp_usize`
    x.clamp(lo, hi)
}

#[cfg(clamp_int)]
pub fn clamp_char(c: char, lo: char, hi: char) -> char {
    //[clamp_int]~^ ERROR `std_numeric_value_panics_charged::clamp_char`
    c.clamp(lo, hi)
}

#[cfg(clamp_int)]
pub fn clamp_ufcs(x: i64, lo: i64, hi: i64) -> i64 {
    //[clamp_int]~^ ERROR `std_numeric_value_panics_charged::clamp_ufcs`
    Ord::clamp(x, lo, hi)
}

#[cfg(clamp_int)]
pub fn clamp_literal_inverted(x: i32) -> i32 {
    //[clamp_int]~^ ERROR `std_numeric_value_panics_charged::clamp_literal_inverted`
    x.clamp(10, 1)
}

// ---- clamp_non_primitive ----

#[cfg(clamp_non_primitive)]
pub fn clamp_bool(x: bool, lo: bool, hi: bool) -> bool {
    //[clamp_non_primitive]~^ ERROR `std_numeric_value_panics_charged::clamp_bool`
    x.clamp(lo, hi)
}

#[cfg(clamp_non_primitive)]
pub fn clamp_tuple(x: (u32, u32), lo: (u32, u32), hi: (u32, u32)) -> (u32, u32) {
    //[clamp_non_primitive]~^ ERROR `std_numeric_value_panics_charged::clamp_tuple`
    x.clamp(lo, hi)
}

#[cfg(clamp_non_primitive)]
pub fn clamp_str<'a>(x: &'a str, lo: &'a str, hi: &'a str) -> &'a str {
    //[clamp_non_primitive]~^ ERROR `std_numeric_value_panics_charged::clamp_str`
    x.clamp(lo, hi)
}

#[cfg(clamp_non_primitive)]
pub fn clamp_nonzero(x: NonZeroU32, lo: NonZeroU32, hi: NonZeroU32) -> NonZeroU32 {
    //[clamp_non_primitive]~^ ERROR `std_numeric_value_panics_charged::clamp_nonzero`
    x.clamp(lo, hi)
}

#[cfg(clamp_non_primitive)]
pub fn clamp_duration(d: Duration, lo: Duration, hi: Duration) -> Duration {
    //[clamp_non_primitive]~^ ERROR `std_numeric_value_panics_charged::clamp_duration`
    d.clamp(lo, hi)
}

// ---- clamp_float ----

#[cfg(clamp_float)]
pub fn clamp_f64(x: f64, lo: f64, hi: f64) -> f64 {
    //[clamp_float]~^ ERROR `std_numeric_value_panics_charged::clamp_f64`
    x.clamp(lo, hi)
}

#[cfg(clamp_float)]
pub fn clamp_f64_nan_bound(x: f64, lo: f64) -> f64 {
    //[clamp_float]~^ ERROR `std_numeric_value_panics_charged::clamp_f64_nan_bound`
    x.clamp(lo, 10.0)
}

#[cfg(clamp_float)]
pub fn clamp_f32(x: f32, lo: f32, hi: f32) -> f32 {
    //[clamp_float]~^ ERROR `std_numeric_value_panics_charged::clamp_f32`
    x.clamp(lo, hi)
}

#[cfg(clamp_float)]
pub fn clamp_f64_literal_inverted(x: f64) -> f64 {
    //[clamp_float]~^ ERROR `std_numeric_value_panics_charged::clamp_f64_literal_inverted`
    x.clamp(1.0, 0.0)
}

// ---- ilog2 ----

#[cfg(ilog2)]
pub fn ilog2_u8(x: u8) -> u32 {
    //[ilog2]~^ ERROR `std_numeric_value_panics_charged::ilog2_u8`
    x.ilog2()
}

#[cfg(ilog2)]
pub fn ilog2_u32(x: u32) -> u32 {
    //[ilog2]~^ ERROR `std_numeric_value_panics_charged::ilog2_u32`
    x.ilog2()
}

#[cfg(ilog2)]
pub fn ilog2_u64(x: u64) -> u32 {
    //[ilog2]~^ ERROR `std_numeric_value_panics_charged::ilog2_u64`
    x.ilog2()
}

#[cfg(ilog2)]
pub fn ilog2_u128(x: u128) -> u32 {
    //[ilog2]~^ ERROR `std_numeric_value_panics_charged::ilog2_u128`
    x.ilog2()
}

#[cfg(ilog2)]
pub fn ilog2_usize(x: usize) -> u32 {
    //[ilog2]~^ ERROR `std_numeric_value_panics_charged::ilog2_usize`
    x.ilog2()
}

#[cfg(ilog2)]
pub fn ilog2_i32(x: i32) -> u32 {
    //[ilog2]~^ ERROR `std_numeric_value_panics_charged::ilog2_i32`
    x.ilog2()
}

#[cfg(ilog2)]
pub fn ilog2_ufcs(x: u32) -> u32 {
    //[ilog2]~^ ERROR `std_numeric_value_panics_charged::ilog2_ufcs`
    <u32>::ilog2(x)
}

#[cfg(ilog2)]
pub fn ilog2_literal_zero() -> u32 {
    //[ilog2]~^ ERROR `std_numeric_value_panics_charged::ilog2_literal_zero`
    let z = 0u32;
    z.ilog2()
}

// ---- ilog10 ----

#[cfg(ilog10)]
pub fn ilog10_u32(x: u32) -> u32 {
    //[ilog10]~^ ERROR `std_numeric_value_panics_charged::ilog10_u32`
    x.ilog10()
}

#[cfg(ilog10)]
pub fn ilog10_i64(x: i64) -> u32 {
    //[ilog10]~^ ERROR `std_numeric_value_panics_charged::ilog10_i64`
    x.ilog10()
}

#[cfg(ilog10)]
pub fn ilog10_ufcs(x: i64) -> u32 {
    //[ilog10]~^ ERROR `std_numeric_value_panics_charged::ilog10_ufcs`
    i64::ilog10(x)
}

// ---- ilog ----

#[cfg(ilog)]
pub fn ilog_zero_argument(x: u32, b: u32) -> u32 {
    //[ilog]~^ ERROR `std_numeric_value_panics_charged::ilog_zero_argument`
    x.ilog(b)
}

#[cfg(ilog)]
pub fn ilog_literal_base_one(x: u32) -> u32 {
    //[ilog]~^ ERROR `std_numeric_value_panics_charged::ilog_literal_base_one`
    x.ilog(1)
}

#[cfg(ilog)]
pub fn ilog_signed(x: i32, b: i32) -> u32 {
    //[ilog]~^ ERROR `std_numeric_value_panics_charged::ilog_signed`
    x.ilog(b)
}

// ---- isqrt ----

#[cfg(isqrt)]
pub fn isqrt_i32(x: i32) -> i32 {
    //[isqrt]~^ ERROR `std_numeric_value_panics_charged::isqrt_i32`
    x.isqrt()
}

#[cfg(isqrt)]
pub fn isqrt_i64(x: i64) -> i64 {
    //[isqrt]~^ ERROR `std_numeric_value_panics_charged::isqrt_i64`
    x.isqrt()
}

#[cfg(isqrt)]
pub fn isqrt_fn_item(x: Option<i32>) -> Option<i32> {
    //[isqrt]~^ ERROR `std_numeric_value_panics_charged::isqrt_fn_item`
    x.map(i32::isqrt)
}

// ---- next_multiple_of ----

#[cfg(next_multiple_of)]
pub fn next_multiple_of_zero(a: u32, b: u32) -> u32 {
    //[next_multiple_of]~^ ERROR `std_numeric_value_panics_charged::next_multiple_of_zero`
    a.next_multiple_of(b)
}

#[cfg(next_multiple_of)]
pub fn next_multiple_of_zero_guarded_only(a: u64, b: u64) -> u64 {
    //[next_multiple_of]~^ ERROR `std_numeric_value_panics_charged::next_multiple_of_zero_guarded_only`
    if b != 0 { a.next_multiple_of(b) } else { 0 }
}

// ---- next_power_of_two ----

#[cfg(next_power_of_two)]
pub fn next_power_of_two_u8(a: u8) -> u8 {
    //[next_power_of_two]~^ ERROR `std_numeric_value_panics_charged::next_power_of_two_u8`
    a.next_power_of_two()
}

#[cfg(next_power_of_two)]
pub fn next_power_of_two_u32(a: u32) -> u32 {
    //[next_power_of_two]~^ ERROR `std_numeric_value_panics_charged::next_power_of_two_u32`
    a.next_power_of_two()
}

#[cfg(next_power_of_two)]
pub fn next_power_of_two_usize(a: usize) -> usize {
    //[next_power_of_two]~^ ERROR `std_numeric_value_panics_charged::next_power_of_two_usize`
    a.next_power_of_two()
}

#[cfg(next_power_of_two)]
pub fn next_power_of_two_ufcs(a: u64) -> u64 {
    //[next_power_of_two]~^ ERROR `std_numeric_value_panics_charged::next_power_of_two_ufcs`
    u64::next_power_of_two(a)
}

// ---- strict ----

#[cfg(strict)]
pub fn strict_add_u32(a: u32, b: u32) -> u32 {
    //[strict]~^ ERROR `std_numeric_value_panics_charged::strict_add_u32`
    a.strict_add(b)
}

#[cfg(strict)]
pub fn strict_sub_u32(a: u32, b: u32) -> u32 {
    //[strict]~^ ERROR `std_numeric_value_panics_charged::strict_sub_u32`
    a.strict_sub(b)
}

#[cfg(strict)]
pub fn strict_mul_i32(a: i32, b: i32) -> i32 {
    //[strict]~^ ERROR `std_numeric_value_panics_charged::strict_mul_i32`
    a.strict_mul(b)
}

#[cfg(strict)]
pub fn strict_rem_i32(a: i32, b: i32) -> i32 {
    //[strict]~^ ERROR `std_numeric_value_panics_charged::strict_rem_i32`
    a.strict_rem(b)
}

#[cfg(strict)]
pub fn strict_neg_u32(a: u32) -> u32 {
    //[strict]~^ ERROR `std_numeric_value_panics_charged::strict_neg_u32`
    a.strict_neg()
}

#[cfg(strict)]
pub fn strict_neg_i32(a: i32) -> i32 {
    //[strict]~^ ERROR `std_numeric_value_panics_charged::strict_neg_i32`
    a.strict_neg()
}

#[cfg(strict)]
pub fn strict_abs_i32(a: i32) -> i32 {
    //[strict]~^ ERROR `std_numeric_value_panics_charged::strict_abs_i32`
    a.strict_abs()
}

#[cfg(strict)]
pub fn strict_shl_u32(a: u32, b: u32) -> u32 {
    //[strict]~^ ERROR `std_numeric_value_panics_charged::strict_shl_u32`
    a.strict_shl(b)
}

#[cfg(strict)]
pub fn strict_shr_i32(a: i32, b: u32) -> i32 {
    //[strict]~^ ERROR `std_numeric_value_panics_charged::strict_shr_i32`
    a.strict_shr(b)
}

#[cfg(strict)]
pub fn strict_pow_u32(a: u32, b: u32) -> u32 {
    //[strict]~^ ERROR `std_numeric_value_panics_charged::strict_pow_u32`
    a.strict_pow(b)
}

#[cfg(strict)]
pub fn strict_add_signed(a: u32, b: i32) -> u32 {
    //[strict]~^ ERROR `std_numeric_value_panics_charged::strict_add_signed`
    a.strict_add_signed(b)
}

#[cfg(strict)]
pub fn strict_sub_signed(a: u32, b: i32) -> u32 {
    //[strict]~^ ERROR `std_numeric_value_panics_charged::strict_sub_signed`
    a.strict_sub_signed(b)
}

#[cfg(strict)]
pub fn strict_add_unsigned(a: i32, b: u32) -> i32 {
    //[strict]~^ ERROR `std_numeric_value_panics_charged::strict_add_unsigned`
    a.strict_add_unsigned(b)
}

#[cfg(strict)]
pub fn strict_sub_unsigned(a: i32, b: u32) -> i32 {
    //[strict]~^ ERROR `std_numeric_value_panics_charged::strict_sub_unsigned`
    a.strict_sub_unsigned(b)
}

// ---- operator_calls ----

#[cfg(operator_calls)]
pub fn ufcs_add_u32(a: u32, b: u32) -> u32 {
    //[operator_calls]~^ ERROR `std_numeric_value_panics_charged::ufcs_add_u32`
    std::ops::Add::add(a, b)
}

#[cfg(operator_calls)]
pub fn ufcs_add_i16_qualified(a: i16, b: i16) -> i16 {
    //[operator_calls]~^ ERROR `std_numeric_value_panics_charged::ufcs_add_i16_qualified`
    <i16 as std::ops::Add>::add(a, b)
}

#[cfg(operator_calls)]
pub fn ufcs_shl_u32(a: u32, b: u32) -> u32 {
    //[operator_calls]~^ ERROR `std_numeric_value_panics_charged::ufcs_shl_u32`
    std::ops::Shl::shl(a, b)
}

#[cfg(operator_calls)]
pub fn ufcs_shl_signed_rhs(a: u8, b: i8) -> u8 {
    //[operator_calls]~^ ERROR `std_numeric_value_panics_charged::ufcs_shl_signed_rhs`
    std::ops::Shl::shl(a, b)
}

#[cfg(operator_calls)]
pub fn ufcs_neg_i32(a: i32) -> i32 {
    //[operator_calls]~^ ERROR `std_numeric_value_panics_charged::ufcs_neg_i32`
    std::ops::Neg::neg(a)
}

#[cfg(operator_calls)]
pub fn add_assign_call_i32(mut a: i32, b: i32) -> i32 {
    //[operator_calls]~^ ERROR `std_numeric_value_panics_charged::add_assign_call_i32`
    a.add_assign(b);
    a
}

#[cfg(operator_calls)]
pub fn sub_assign_call_through_ref(a: &mut u32, b: u32) {
    //[operator_calls]~^ ERROR `std_numeric_value_panics_charged::sub_assign_call_through_ref`
    a.sub_assign(b)
}

#[cfg(operator_calls)]
pub fn mul_assign_call_i64(mut a: i64, b: i64) -> i64 {
    //[operator_calls]~^ ERROR `std_numeric_value_panics_charged::mul_assign_call_i64`
    a.mul_assign(b);
    a
}

#[cfg(operator_calls)]
pub fn shl_assign_call_u32(mut a: u32, b: u32) -> u32 {
    //[operator_calls]~^ ERROR `std_numeric_value_panics_charged::shl_assign_call_u32`
    a.shl_assign(b);
    a
}

// ---- to_digit ----

#[cfg(to_digit)]
pub fn to_digit_radix(c: char, r: u32) -> Option<u32> {
    //[to_digit]~^ ERROR `std_numeric_value_panics_charged::to_digit_radix`
    c.to_digit(r)
}

#[cfg(to_digit)]
pub fn to_digit_ufcs(c: char, r: u32) -> Option<u32> {
    //[to_digit]~^ ERROR `std_numeric_value_panics_charged::to_digit_ufcs`
    char::to_digit(c, r)
}

#[cfg(to_digit)]
pub fn to_digit_radix_from_u8(c: char, r: u8) -> Option<u32> {
    //[to_digit]~^ ERROR `std_numeric_value_panics_charged::to_digit_radix_from_u8`
    c.to_digit(r as u32)
}

#[cfg(to_digit)]
pub fn is_digit_radix(c: char, r: u32) -> bool {
    //[to_digit]~^ ERROR `std_numeric_value_panics_charged::is_digit_radix`
    c.is_digit(r)
}

#[cfg(to_digit)]
pub fn is_digit_literal_radix(c: char) -> bool {
    //[to_digit]~^ ERROR `std_numeric_value_panics_charged::is_digit_literal_radix`
    c.is_digit(37)
}

// ---- from_digit ----

#[cfg(from_digit)]
pub fn from_digit_assoc(d: u32, r: u32) -> Option<char> {
    //[from_digit]~^ ERROR `std_numeric_value_panics_charged::from_digit_assoc`
    char::from_digit(d, r)
}

#[cfg(from_digit)]
pub fn from_digit_std_free(d: u32, r: u32) -> Option<char> {
    //[from_digit]~^ ERROR `std_numeric_value_panics_charged::from_digit_std_free`
    std::char::from_digit(d, r)
}

#[cfg(from_digit)]
pub fn from_digit_core_free(d: u32, r: u32) -> Option<char> {
    //[from_digit]~^ ERROR `std_numeric_value_panics_charged::from_digit_core_free`
    core::char::from_digit(d, r)
}

// ---- from_str_radix ----

#[cfg(from_str_radix)]
pub fn from_str_radix_u32(s: &str, r: u32) -> Option<u32> {
    //[from_str_radix]~^ ERROR `std_numeric_value_panics_charged::from_str_radix_u32`
    u32::from_str_radix(s, r).ok()
}

#[cfg(from_str_radix)]
pub fn from_str_radix_i64(s: &str, r: u32) -> Option<i64> {
    //[from_str_radix]~^ ERROR `std_numeric_value_panics_charged::from_str_radix_i64`
    i64::from_str_radix(s, r).ok()
}

#[cfg(from_str_radix)]
pub fn from_str_radix_u8(s: &str, r: u32) -> bool {
    //[from_str_radix]~^ ERROR `std_numeric_value_panics_charged::from_str_radix_u8`
    u8::from_str_radix(s, r).is_ok()
}

#[cfg(from_str_radix)]
pub fn from_str_radix_usize(s: &str, r: u32) -> bool {
    //[from_str_radix]~^ ERROR `std_numeric_value_panics_charged::from_str_radix_usize`
    usize::from_str_radix(s, r).is_ok()
}

#[cfg(from_str_radix)]
pub fn from_str_radix_nonzero(s: &str, r: u32) -> bool {
    //[from_str_radix]~^ ERROR `std_numeric_value_panics_charged::from_str_radix_nonzero`
    NonZeroU32::from_str_radix(s, r).is_ok()
}

// ---- from_ascii_radix ----
//
// ASCII-FROM-ASCII-RADIX-1. BEFORE (the stage 1 of `ec03f72395`,
// `scratchpad/stage1-w15r`, 2026-10-05, this revision's flags plus `-Zui-testing
// -Zdeduplicate-diagnostics=no --emit=metadata`): exit 0 — no function below
// gets an error, each carries only the bundled member's `runtime_checked`
// panic-freedom row — and a verify-off driver calling `far(b"7", 37)` panics
// "from_ascii_radix: radix must lie in the range `[2, 36]` - found 37" (exit
// 101; `NonZero`'s with radix 1 likewise; the scout's `utf8/confirm` probes).
// AFTER (predicted before the build; it held, MEASURED 2026-10-06 on the stage 1 of `9e11546767`):
// each gets the call-site radix row `from_str_radix` gets, which reads `unknown`
// here as `from_str_radix`'s does, so the default policy refuses it; the
// `guarded` twins below prove that row.

#[cfg(from_ascii_radix)]
pub fn from_ascii_radix_u32(b: &[u8], r: u32) -> Option<u32> {
    //[from_ascii_radix]~^ ERROR `std_numeric_value_panics_charged::from_ascii_radix_u32`
    u32::from_ascii_bytes_radix(b, r).ok()
}

#[cfg(from_ascii_radix)]
pub fn from_ascii_radix_i64(b: &[u8], r: u32) -> Option<i64> {
    //[from_ascii_radix]~^ ERROR `std_numeric_value_panics_charged::from_ascii_radix_i64`
    i64::from_ascii_bytes_radix(b, r).ok()
}

// The `match` shape: `.ok()` on `Result<NonZero<u32>, _>` is refused today for
// an unrelated reason (its drop glue is charged), which would mask the radix row.
#[cfg(from_ascii_radix)]
pub fn from_ascii_radix_nonzero(b: &[u8], r: u32) -> u32 {
    //[from_ascii_radix]~^ ERROR `std_numeric_value_panics_charged::from_ascii_radix_nonzero`
    match std::num::NonZero::<u32>::from_ascii_bytes_radix(b, r) {
        Ok(v) => v.get(),
        Err(_) => 0,
    }
}

// ---- nonzero_negation ----

#[cfg(nonzero_negation)]
pub fn nonzero_abs(x: NonZeroI32) -> NonZeroI32 {
    //[nonzero_negation]~^ ERROR `std_numeric_value_panics_charged::nonzero_abs`
    x.abs()
}

#[cfg(nonzero_negation)]
pub fn nonzero_neg(x: NonZeroI32) -> NonZeroI32 {
    //[nonzero_negation]~^ ERROR `std_numeric_value_panics_charged::nonzero_neg`
    -x
}

// ---- duration_constructors ----

#[cfg(duration_constructors)]
pub fn duration_new(s: u64, n: u32) -> Duration {
    //[duration_constructors]~^ ERROR `std_numeric_value_panics_charged::duration_new`
    Duration::new(s, n)
}

#[cfg(duration_constructors)]
pub fn duration_from_mins(m: u64) -> Duration {
    //[duration_constructors]~^ ERROR `std_numeric_value_panics_charged::duration_from_mins`
    Duration::from_mins(m)
}

#[cfg(duration_constructors)]
pub fn duration_from_hours(h: u64) -> Duration {
    //[duration_constructors]~^ ERROR `std_numeric_value_panics_charged::duration_from_hours`
    Duration::from_hours(h)
}

#[cfg(duration_constructors)]
pub fn duration_from_nanos_u128(n: u128) -> Duration {
    //[duration_constructors]~^ ERROR `std_numeric_value_panics_charged::duration_from_nanos_u128`
    Duration::from_nanos_u128(n)
}

// ---- duration_float ----

#[cfg(duration_float)]
pub fn duration_from_secs_f64(x: f64) -> Duration {
    //[duration_float]~^ ERROR `std_numeric_value_panics_charged::duration_from_secs_f64`
    Duration::from_secs_f64(x)
}

#[cfg(duration_float)]
pub fn duration_from_secs_f32(x: f32) -> Duration {
    //[duration_float]~^ ERROR `std_numeric_value_panics_charged::duration_from_secs_f32`
    Duration::from_secs_f32(x)
}

#[cfg(duration_float)]
pub fn duration_mul_f64(d: Duration, x: f64) -> Duration {
    //[duration_float]~^ ERROR `std_numeric_value_panics_charged::duration_mul_f64`
    d.mul_f64(x)
}

#[cfg(duration_float)]
pub fn duration_mul_f32(d: Duration, x: f32) -> Duration {
    //[duration_float]~^ ERROR `std_numeric_value_panics_charged::duration_mul_f32`
    d.mul_f32(x)
}

#[cfg(duration_float)]
pub fn duration_div_f64(d: Duration, x: f64) -> Duration {
    //[duration_float]~^ ERROR `std_numeric_value_panics_charged::duration_div_f64`
    d.div_f64(x)
}

#[cfg(duration_float)]
pub fn duration_div_f32(d: Duration, x: f32) -> Duration {
    //[duration_float]~^ ERROR `std_numeric_value_panics_charged::duration_div_f32`
    d.div_f32(x)
}

// ---- duration_arith ----

#[cfg(duration_arith)]
pub fn duration_add(a: Duration, b: Duration) -> Duration {
    //[duration_arith]~^ ERROR `std_numeric_value_panics_charged::duration_add`
    a + b
}

#[cfg(duration_arith)]
pub fn duration_sub(a: Duration, b: Duration) -> Duration {
    //[duration_arith]~^ ERROR `std_numeric_value_panics_charged::duration_sub`
    a - b
}

#[cfg(duration_arith)]
pub fn duration_mul(a: Duration, k: u32) -> Duration {
    //[duration_arith]~^ ERROR `std_numeric_value_panics_charged::duration_mul`
    a * k
}

#[cfg(duration_arith)]
pub fn duration_mul_by_literal(a: Duration) -> Duration {
    //[duration_arith]~^ ERROR `std_numeric_value_panics_charged::duration_mul_by_literal`
    a * 2
}

#[cfg(duration_arith)]
pub fn duration_scalar_mul(a: Duration, k: u32) -> Duration {
    //[duration_arith]~^ ERROR `std_numeric_value_panics_charged::duration_scalar_mul`
    k * a
}

#[cfg(duration_arith)]
pub fn duration_div(a: Duration, k: u32) -> Duration {
    //[duration_arith]~^ ERROR `std_numeric_value_panics_charged::duration_div`
    a / k
}

#[cfg(duration_arith)]
pub fn duration_add_assign(mut a: Duration, b: Duration) -> Duration {
    //[duration_arith]~^ ERROR `std_numeric_value_panics_charged::duration_add_assign`
    a += b;
    a
}

#[cfg(duration_arith)]
pub fn duration_sub_assign(mut a: Duration, b: Duration) -> Duration {
    //[duration_arith]~^ ERROR `std_numeric_value_panics_charged::duration_sub_assign`
    a -= b;
    a
}

#[cfg(duration_arith)]
pub fn duration_mul_assign(mut a: Duration, k: u32) -> Duration {
    //[duration_arith]~^ ERROR `std_numeric_value_panics_charged::duration_mul_assign`
    a *= k;
    a
}

#[cfg(duration_arith)]
pub fn duration_div_assign(mut a: Duration, k: u32) -> Duration {
    //[duration_arith]~^ ERROR `std_numeric_value_panics_charged::duration_div_assign`
    a /= k;
    a
}

#[cfg(duration_arith)]
pub fn duration_plus_literal(d: Duration) -> Duration {
    //[duration_arith]~^ ERROR `std_numeric_value_panics_charged::duration_plus_literal`
    d + Duration::from_secs(1)
}

#[cfg(duration_arith)]
pub fn duration_literal_overflow() -> Duration {
    //[duration_arith]~^ ERROR `std_numeric_value_panics_charged::duration_literal_overflow`
    Duration::from_secs(u64::MAX) + Duration::from_secs(1)
}

#[cfg(duration_arith)]
pub fn duration_sum(v: &[Duration]) -> Duration {
    //[duration_arith]~^ ERROR `std_numeric_value_panics_charged::duration_sum`
    v.iter().sum()
}

#[cfg(duration_arith)]
pub fn duration_sum_into_option(v: Vec<Option<Duration>>) -> Option<Duration> {
    //[duration_arith]~^ ERROR `std_numeric_value_panics_charged::duration_sum_into_option`
    v.into_iter().sum()
}

#[cfg(duration_arith)]
pub fn duration_sum_into_result(v: Vec<Result<Duration, u8>>) -> Result<Duration, u8> {
    //[duration_arith]~^ ERROR `std_numeric_value_panics_charged::duration_sum_into_result`
    v.into_iter().sum()
}

// ---- time_point ----

#[cfg(time_point)]
pub fn instant_add(i: Instant, d: Duration) -> Instant {
    //[time_point]~^ ERROR `std_numeric_value_panics_charged::instant_add`
    i + d
}

#[cfg(time_point)]
pub fn instant_sub_duration(i: Instant, d: Duration) -> Instant {
    //[time_point]~^ ERROR `std_numeric_value_panics_charged::instant_sub_duration`
    i - d
}

#[cfg(time_point)]
pub fn instant_add_assign(mut i: Instant, d: Duration) -> Instant {
    //[time_point]~^ ERROR `std_numeric_value_panics_charged::instant_add_assign`
    i += d;
    i
}

#[cfg(time_point)]
pub fn instant_sub_assign(mut i: Instant, d: Duration) -> Instant {
    //[time_point]~^ ERROR `std_numeric_value_panics_charged::instant_sub_assign`
    i -= d;
    i
}

#[cfg(time_point)]
pub fn instant_now_plus_param(d: Duration) -> Instant {
    //[time_point]~^ ERROR `std_numeric_value_panics_charged::instant_now_plus_param`
    Instant::now() + d
}

#[cfg(time_point)]
pub fn system_time_add(t: SystemTime, d: Duration) -> SystemTime {
    //[time_point]~^ ERROR `std_numeric_value_panics_charged::system_time_add`
    t + d
}

#[cfg(time_point)]
pub fn system_time_sub(t: SystemTime, d: Duration) -> SystemTime {
    //[time_point]~^ ERROR `std_numeric_value_panics_charged::system_time_sub`
    t - d
}

#[cfg(time_point)]
pub fn system_time_add_assign(mut t: SystemTime, d: Duration) -> SystemTime {
    //[time_point]~^ ERROR `std_numeric_value_panics_charged::system_time_add_assign`
    t += d;
    t
}

#[cfg(time_point)]
pub fn instant_param_plus_literal(t: Instant) -> Instant {
    //[time_point]~^ ERROR `std_numeric_value_panics_charged::instant_param_plus_literal`
    t + Duration::from_secs(1)
}

#[cfg(time_point)]
pub fn system_time_param_minus_literal(t: SystemTime) -> SystemTime {
    //[time_point]~^ ERROR `std_numeric_value_panics_charged::system_time_param_minus_literal`
    t - Duration::from_secs(1)
}

#[cfg(time_point)]
pub fn instant_now_add_assign_in_a_loop(n: u64) -> Instant {
    //[time_point]~^ ERROR `std_numeric_value_panics_charged::instant_now_add_assign_in_a_loop`
    let mut t = Instant::now();
    for _ in 0..n {
        t += Duration::from_secs(1 << 62);
    }
    t
}

// ---- range_iteration ----

#[cfg(range_iteration)]
pub fn range_from_next_u8(a: u8) -> Option<u8> {
    //[range_iteration]~^ ERROR `std_numeric_value_panics_charged::range_from_next_u8`
    (a..).next()
}

#[cfg(range_iteration)]
pub fn range_from_nth_u8(a: u8, n: usize) -> Option<u8> {
    //[range_iteration]~^ ERROR `std_numeric_value_panics_charged::range_from_nth_u8`
    (a..).nth(n)
}

#[cfg(range_iteration)]
pub fn range_from_next_char(c: char) -> Option<char> {
    //[range_iteration]~^ ERROR `std_numeric_value_panics_charged::range_from_next_char`
    (c..).next()
}

#[cfg(range_iteration)]
pub fn range_from_find_u8(s: u8) -> Option<u8> {
    //[range_iteration]~^ ERROR `std_numeric_value_panics_charged::range_from_find_u8`
    (s..).find(|&x| x < s)
}

#[cfg(range_iteration)]
pub fn range_from_any_u8(s: u8, v: u8) -> bool {
    //[range_iteration]~^ ERROR `std_numeric_value_panics_charged::range_from_any_u8`
    (s..).any(|x| x == v)
}

#[cfg(range_iteration)]
pub fn range_from_count_u8(s: u8) -> usize {
    //[range_iteration]~^ ERROR `std_numeric_value_panics_charged::range_from_count_u8`
    (s..).count()
}

#[cfg(range_iteration)]
pub fn range_from_next_through_mut_ref(s: u8) -> Option<u8> {
    //[range_iteration]~^ ERROR `std_numeric_value_panics_charged::range_from_next_through_mut_ref`
    let mut r = s..;
    <&mut std::ops::RangeFrom<u8> as Iterator>::next(&mut &mut r)
}

#[cfg(range_iteration)]
pub fn for_range_from_u8(n: u8) -> u8 {
    //[range_iteration]~^ ERROR `std_numeric_value_panics_charged::for_range_from_u8`
    let mut t = 0;
    for i in 0u8.. {
        if i == n {
            break;
        }
        t = i;
    }
    t
}

#[cfg(range_iteration)]
pub fn range_inclusive_count_usize(a: usize) -> usize {
    //[range_iteration]~^ ERROR `std_numeric_value_panics_charged::range_inclusive_count_usize`
    (a..=usize::MAX).count()
}

#[cfg(range_iteration)]
pub fn range_inclusive_count_u64(a: u64, b: u64) -> usize {
    //[range_iteration]~^ ERROR `std_numeric_value_panics_charged::range_inclusive_count_u64`
    (a..=b).count()
}

#[cfg(range_iteration)]
pub fn range_count_u128(a: u128, b: u128) -> usize {
    //[range_iteration]~^ ERROR `std_numeric_value_panics_charged::range_count_u128`
    (a..b).count()
}

// ---- adversarial ----

#[cfg(adversarial)]
fn clamp_helper(x: f64, lo: f64, hi: f64) -> f64 {
    //[adversarial]~^ ERROR `std_numeric_value_panics_charged::clamp_helper`
    x.clamp(lo, hi)
}

#[cfg(adversarial)]
pub fn closure_ilog2(x: u32) -> u32 {
    let g = |v: u32| v.ilog2();
    //[adversarial]~^ ERROR `std_numeric_value_panics_charged::closure_ilog2::{closure#0}`
    g(x)
}

#[cfg(adversarial)]
pub fn float_clamp_through_helper(x: f64, lo: f64) -> f64 {
    clamp_helper(x, lo, 1.0)
}

#[cfg(adversarial)]
pub fn guard_the_wrong_way(x: i32, a: i32, b: i32) -> i32 {
    //[adversarial]~^ ERROR `std_numeric_value_panics_charged::guard_the_wrong_way`
    if a <= b { x.clamp(b, a) } else { x }
}

#[cfg(adversarial)]
pub fn guard_on_another_variable(x: u32, y: u32) -> u32 {
    //[adversarial]~^ ERROR `std_numeric_value_panics_charged::guard_on_another_variable`
    if y > 0 { x.ilog10() } else { 0 }
}

#[cfg(adversarial)]
pub fn radix_guard_off_by_one(c: char, r: u32) -> Option<u32> {
    //[adversarial]~^ ERROR `std_numeric_value_panics_charged::radix_guard_off_by_one`
    if r >= 2 && r <= 37 { c.to_digit(r) } else { None }
}

#[cfg(adversarial)]
pub fn nonzero_get_minus_one(x: NonZeroU32) -> u32 {
    //[adversarial]~^ ERROR `std_numeric_value_panics_charged::nonzero_get_minus_one`
    (x.get() - 1).ilog2()
}

// ---- guarded: every function here must verify ----

#[cfg(guarded)]
fn radix_ok(r: u32) -> bool {
    r >= 2 && r <= 36
}

#[cfg(guarded)]
pub struct Mine(pub u32);

#[cfg(guarded)]
impl Mine {
    pub fn ilog2(self) -> u32 {
        self.0
    }
}

#[cfg(guarded)]
pub trait MyClamp {
    fn clamp(self, a: Self, b: Self) -> Self;
}

#[cfg(guarded)]
impl MyClamp for u32 {
    fn clamp(self, _a: u32, _b: u32) -> u32 {
        self
    }
}

#[cfg(guarded)]
pub fn clamp_guarded(x: i32, lo: i32, hi: i32) -> i32 {
    if lo <= hi { x.clamp(lo, hi) } else { x }
}

#[cfg(guarded)]
pub fn clamp_literal(x: i32) -> i32 {
    x.clamp(-10, 10)
}

#[cfg(guarded)]
pub fn clamp_widened_bounds(x: i64) -> i32 {
    x.clamp(i32::MIN as i64, i32::MAX as i64) as i32
}

#[cfg(guarded)]
pub fn clamp_ufcs_early_return(x: i64, lo: i64, hi: i64) -> i64 {
    if lo > hi {
        return x;
    }
    Ord::clamp(x, lo, hi)
}

#[cfg(guarded)]
pub fn clamp_zero_floor(x: u8, hi: u8) -> u8 {
    x.clamp(0, hi)
}

#[cfg(guarded)]
pub fn clamp_char_literal(c: char) -> char {
    c.clamp('a', 'z')
}

#[cfg(guarded)]
pub fn clamp_byte_literal(x: u8) -> u8 {
    x.clamp(b'0', b'9')
}

#[cfg(guarded)]
pub fn clamp_f64_literal(x: f64) -> f64 {
    x.clamp(0.0, 1.0)
}

#[cfg(guarded)]
pub fn clamp_f32_literal(x: f32) -> f32 {
    x.clamp(-1.0, 1.0)
}

#[cfg(guarded)]
pub fn ilog2_guarded(x: u32) -> u32 {
    if x == 0 { 0 } else { x.ilog2() }
}

#[cfg(guarded)]
pub fn ilog2_early_return(x: u32) -> u32 {
    if x == 0 {
        return 0;
    }
    x.ilog2()
}

#[cfg(guarded)]
pub fn ilog2_or_one(x: u32) -> u32 {
    (x | 1).ilog2()
}

#[cfg(guarded)]
pub fn ilog2_literal() -> u32 {
    1024u32.ilog2()
}

#[cfg(guarded)]
pub fn ilog10_match(x: u64) -> u32 {
    match x {
        0 => 0,
        v => v.ilog10(),
    }
}

#[cfg(guarded)]
pub fn ilog10_signed_guarded(x: i32) -> u32 {
    if x > 0 { x.ilog10() } else { 0 }
}

#[cfg(guarded)]
pub fn ilog_literal_base(x: u32) -> u32 {
    if x >= 1 { x.ilog(10) } else { 0 }
}

#[cfg(guarded)]
pub fn ilog_guarded_base(x: u32, b: u32) -> u32 {
    if x >= 1 && b >= 2 { x.ilog(b) } else { 0 }
}

#[cfg(guarded)]
pub fn ilog2_nonzero(x: NonZeroU64) -> u32 {
    x.ilog2()
}

#[cfg(guarded)]
pub fn ilog2_nonzero_get(x: NonZeroU32) -> u32 {
    x.get().ilog2()
}

#[cfg(guarded)]
pub fn checked_ilog2_total(x: u32) -> Option<u32> {
    x.checked_ilog2()
}

#[cfg(guarded)]
pub fn isqrt_guarded(x: i32) -> i32 {
    if x >= 0 { x.isqrt() } else { 0 }
}

#[cfg(guarded)]
pub fn isqrt_unsigned_total(x: u64) -> u64 {
    x.isqrt()
}

#[cfg(guarded)]
pub fn next_multiple_of_guarded(a: u32, b: u32) -> u32 {
    if b != 0 && a <= u32::MAX - b { a.next_multiple_of(b) } else { 0 }
}

#[cfg(guarded)]
pub fn next_multiple_of_small(a: u16) -> u32 {
    (a as u32).next_multiple_of(8)
}

#[cfg(guarded)]
pub fn next_power_of_two_guarded(a: u32) -> u32 {
    if a <= (1 << 31) { a.next_power_of_two() } else { 0 }
}

#[cfg(guarded)]
pub fn next_power_of_two_small(a: u16) -> u32 {
    (a as u32).next_power_of_two()
}

#[cfg(guarded)]
pub fn strict_add_guarded(a: u32, b: u32) -> u32 {
    if a <= u32::MAX - b { a.strict_add(b) } else { 0 }
}

#[cfg(guarded)]
pub fn to_digit_literal(c: char) -> Option<u32> {
    c.to_digit(16)
}

#[cfg(guarded)]
pub fn to_digit_guarded(c: char, r: u32) -> Option<u32> {
    if r >= 2 && r <= 36 { c.to_digit(r) } else { None }
}

#[cfg(guarded)]
pub fn to_digit_helper_guard(c: char, r: u32) -> Option<u32> {
    if radix_ok(r) { c.to_digit(r) } else { None }
}

#[cfg(guarded)]
pub fn is_digit_literal(c: char) -> bool {
    c.is_digit(10)
}

#[cfg(guarded)]
pub fn from_digit_literal(d: u32) -> Option<char> {
    char::from_digit(d, 10)
}

#[cfg(guarded)]
pub fn from_digit_guarded(d: u32, r: u32) -> Option<char> {
    if r <= 36 { char::from_digit(d, r) } else { None }
}

#[cfg(guarded)]
pub fn from_str_radix_literal(s: &str) -> Option<u32> {
    u32::from_str_radix(s, 16).ok()
}

#[cfg(guarded)]
pub fn from_str_radix_guarded(s: &str, r: u32) -> Option<i64> {
    if r >= 2 && r <= 36 { i64::from_str_radix(s, r).ok() } else { None }
}

#[cfg(guarded)]
pub fn from_ascii_radix_literal(b: &[u8]) -> Option<u32> {
    u32::from_ascii_bytes_radix(b, 16).ok()
}

#[cfg(guarded)]
pub fn from_ascii_radix_guarded(b: &[u8], r: u32) -> Option<u32> {
    if r >= 2 && r <= 36 { u32::from_ascii_bytes_radix(b, r).ok() } else { None }
}

#[cfg(guarded)]
pub fn from_ascii_is_total(b: &[u8]) -> Option<u32> {
    u32::from_ascii_bytes(b).ok()
}

#[cfg(guarded)]
pub fn parse_total(s: &str) -> Option<u32> {
    s.parse().ok()
}

#[cfg(guarded)]
pub fn duration_new_guarded(s: u64, n: u32) -> Duration {
    if n < 1_000_000_000 { Duration::new(s, n) } else { Duration::ZERO }
}

#[cfg(guarded)]
pub fn duration_new_zero_nanos(s: u64) -> Duration {
    Duration::new(s, 0)
}

#[cfg(guarded)]
pub fn duration_new_reduced_nanos(s: u64, n: u32) -> Duration {
    Duration::new(s, n % 1_000_000_000)
}

#[cfg(guarded)]
pub fn duration_from_f64_literal() -> Duration {
    Duration::from_secs_f64(1.5)
}

#[cfg(guarded)]
pub fn duration_div_guarded(d: Duration, k: u32) -> Duration {
    if k != 0 { d / k } else { d }
}

#[cfg(guarded)]
pub fn duration_div_literal(d: Duration) -> Duration {
    d / 2
}

#[cfg(guarded)]
pub fn duration_literal_math() -> Duration {
    Duration::from_secs(60) * 60 + Duration::from_millis(500)
}

#[cfg(guarded)]
pub fn duration_checked_add(a: Duration, b: Duration) -> Option<Duration> {
    a.checked_add(b)
}

#[cfg(guarded)]
pub fn duration_saturating_sub(a: Duration, b: Duration) -> Duration {
    a.saturating_sub(b)
}

#[cfg(guarded)]
pub fn instant_now_plus_literal() -> Instant {
    Instant::now() + Duration::from_millis(250)
}

#[cfg(guarded)]
pub fn instant_now_let_plus_literal() -> Instant {
    let t = Instant::now();
    t + Duration::from_secs(1)
}

#[cfg(guarded)]
pub fn system_time_now_minus_literal() -> SystemTime {
    SystemTime::now() - Duration::from_secs(60)
}

#[cfg(guarded)]
pub fn shl_assign_call_guarded(mut a: u32, b: u32) -> u32 {
    if b < 32 {
        a.shl_assign(b);
    }
    a
}

#[cfg(guarded)]
pub fn sub_assign_call_guarded_on_the_pointee(a: &mut u32, b: u32) {
    if b <= *a {
        a.sub_assign(b)
    }
}

#[cfg(guarded)]
pub fn instant_elapsed(i: Instant) -> Duration {
    i.elapsed()
}

#[cfg(guarded)]
pub fn instant_minus_instant_saturates(a: Instant, b: Instant) -> Duration {
    a - b
}

#[cfg(guarded)]
pub fn range_inclusive_count_narrow(a: u32, b: u32) -> usize {
    (a..=b).count()
}

#[cfg(guarded)]
pub fn range_inclusive_count_guarded(a: u64, b: u64) -> usize {
    if b < u64::MAX { (a..=b).count() } else { 0 }
}

#[cfg(guarded)]
pub fn user_method_named_ilog2(x: u32) -> u32 {
    Mine(x).ilog2()
}

#[cfg(guarded)]
pub fn user_trait_named_clamp(x: u32, a: u32, b: u32) -> u32 {
    MyClamp::clamp(x, a, b)
}

#[cfg(guarded)]
pub fn reference_addition_stays_ruled(v: &[i32]) -> i32 {
    v.iter().fold(0, |a, b| a + b)
}
