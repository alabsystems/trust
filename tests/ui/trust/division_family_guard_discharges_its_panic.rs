//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-pass
#![crate_type = "lib"]
//! A primitive-integer division-family method panics on exactly a documented
//! condition of its arguments (a zero divisor, and for a signed `div_euclid` or
//! `rem_euclid` also `MIN / -1`), so a guard that excludes it discharges the call.
//! Each function below was refused (a fatal absent-callee row) before the bridge
//! lowered the call's marker as that condition. The twin is
//! `division_family_guard_discharges_its_panic_refused.rs`.

pub fn wrap_index(i: i64, n: i64) -> i64 {
    if n <= 0 { 0 } else { i.rem_euclid(n) }
}

pub fn unsigned_rem_euclid(a: u64, n: u64) -> u64 {
    if n == 0 { 0 } else { a.rem_euclid(n) }
}

// `wrapping_rem` does not panic on `MIN % -1` (it wraps), so a nonzero divisor is
// the whole condition.
pub fn wrapping_rem_guarded(a: i32, n: i32) -> i32 {
    if n != 0 { a.wrapping_rem(n) } else { 0 }
}

pub fn saturating_div_guarded(a: i32, n: i32) -> i32 {
    if n != 0 { a.saturating_div(n) } else { 0 }
}

// A literal divisor is an untyped constant in the extracted MIR; it used to be
// typed i64, so these narrow and wide signed widths fell to the absent-callee arm
// while `i64` proved (review of 2026-09-30).
pub fn literal_divisor_i32(a: i32) -> i32 {
    a.wrapping_div(3)
}

pub fn literal_divisor_i8(a: i8) -> i8 {
    a.wrapping_rem(-3)
}

pub fn literal_divisor_i128(a: i128) -> i128 {
    a.div_euclid(7)
}

// NOT PROVED, and kept here only as a build pin: std's own body checks the divisor
// before its `div_euclid` call, and the call is now charged by that condition, but
// the bundled `checked_*_euclid` body still reports one advisory row (an
// `UnsupportedDirectCallSummary` inside std's body). The default policy reports it
// and builds; `-Ztrust-policy=certify` refuses (review of 2026-09-30).
pub fn checked_div_euclid(a: i32, b: i32) -> Option<i32> {
    a.checked_div_euclid(b)
}

pub fn checked_rem_euclid(a: i32, n: i32) -> Option<i32> {
    a.checked_rem_euclid(n)
}
