//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-pass
#![crate_type = "lib"]
//! A running sum of widened elements over a bounded iteration proves, whatever
//! the element's source.
//!
//! MEASURED OVER-REFUSAL, 2026-09-29, on the 659-program ordinary-Rust sweep:
//! each function below was REFUTED with `s = u32::MAX` (or `u64::MAX`) — a
//! counterexample, so fatal on the default lane — although the sum cannot
//! overflow. Two gaps in `trust-vcgen`'s accumulator lane:
//!
//! * `addend_per_iteration_bound` required the element to be traced to a
//!   for-each over a fixed-size array or to a `Range`-indexed load, only to
//!   compute a trip count both callers discarded for `block_execution_bound`'s.
//!   The widened element's own type (`MAX(u8)`) is the per-iteration bound it
//!   needed; `for &b in a.iter()` (reached through an unsize cast) and
//!   `for b in a` (no `Deref` in the binding) failed the trace.
//! * `iterated_source_yield_bound` gave `a as &[u8]` the slice bound
//!   `isize::MAX` instead of the array's length, and had no count for
//!   `take(n)`, `chain` or `Option::iter`.
//!
//! The lane stays self-limiting: `accumulator_bound_really_overflows_is_refused.rs`
//! holds the same shapes where the sum really can overflow.

pub fn sum_array_ref(a: &[u8; 4]) -> u32 {
    let mut s = 0u32;
    for &b in a.iter() {
        s += b as u32;
    }
    s
}

pub fn sum_array_by_value(a: [u8; 4]) -> u32 {
    let mut s = 0u32;
    for b in a {
        s += b as u32;
    }
    s
}

pub fn sum_first_three(v: &[u32]) -> u64 {
    let mut s = 0u64;
    for &x in v.iter().take(3) {
        s += x as u64;
    }
    s
}

pub fn sum_options(a: Option<u32>, b: Option<u32>) -> u64 {
    let mut s = 0u64;
    for x in a.iter().chain(b.iter()) {
        s += *x as u64;
    }
    s
}

pub fn scaled(a: &[u8; 16]) -> u16 {
    let mut t = 0u16;
    for &x in a.iter() {
        t += (x as u16) << 4;
    }
    t
}
