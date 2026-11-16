//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-pass
#![crate_type = "lib"]
//! Result ranges of the integer logarithms, of `leading_zeros`/`trailing_zeros` on
//! a NONZERO receiver, and of the sub-slice `get(a..b)` returns.
//!
//! MEASURED OVER-REFUSALS, 2026-09-29, on the 659-program ordinary-Rust sweep:
//! each function below was refuted — a counterexample, fatal on the default lane —
//! with the payload at `u32::MAX`, the zero count at the type's width, or the
//! sub-slice at length 0. `ilog2(x) < bits(x)`, `ilog10(x)` is at most the digit
//! count of the type's MAX less one, a nonzero value has fewer than `bits` leading
//! or trailing zeros, and `get(a..b)` returns `Some` only with a sub-slice of
//! length `b - a` (`trust-vcgen` `build_intrinsic_bound_facts`,
//! `slice_get_some_index_bound_definitions`).
//!
//! `integer_log_and_zero_count_ranges_refused.rs` holds the twins that really
//! overflow or index out of bounds.

pub fn digits(x: u32) -> u32 {
    match x.checked_ilog10() {
        Some(d) => d + 1,
        None => 1,
    }
}

pub fn bit_length(x: u64) -> u32 {
    match x.checked_ilog2() {
        Some(b) => b + 1,
        None => 0,
    }
}

pub fn log2_floor(x: u64) -> u32 {
    if x == 0 { 0 } else { 63 - x.leading_zeros() }
}

pub fn lowest_set(t: &[u8; 64], x: u64) -> u8 {
    if x == 0 { 0 } else { t[x.trailing_zeros() as usize] }
}

pub fn middle(v: &[u32]) -> u32 {
    if let Some(s) = v.get(1..3) { s[0].max(s[1]) } else { 0 }
}
