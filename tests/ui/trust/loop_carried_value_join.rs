//@ needs-trust-verify
//@ edition: 2021
//@ revisions: argmax argmax_o1 one_past arith reborrowed
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[argmax] check-pass
//@[argmax_o1] check-pass
//@[argmax_o1] compile-flags: -Copt-level=1 -Coverflow-checks=on
//@[one_past] check-fail
//@[arith] check-fail
//@[reborrowed] check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ dont-require-annotations: ERROR
//! Trust (2026-10-04): a local whose every value is a constant, a copy, or a
//! constant range-loop payload is bounded by the join of those values at EVERY read
//! (`type_ranges::local_value_join_interval_map`), so a loop-carried index proves.
//!
//! # Before (measured on the stage 1 of `0d0ff693d6`, 2026-10-04)
//!
//! `argmax` (a3d_solve `argmax_abs`): the in-loop `v[b]` row FAILED.
//!
//! # The refused rails, each a program that really panics
//!
//! * `one_past` — `for k in 1..4` over a `[f64; 3]`: `b` reaches 3.
//! * `arith` — `b = k + 2`: not a join of constants, copies and payloads.
//! * `reborrowed` — `b` is written through `&mut b` to 7.

#[cfg(any(argmax, argmax_o1))]
pub fn argmax(v: [f64; 3]) -> usize {
    let mut b = 0;
    for k in 1..3 {
        if v[k].abs() > v[b].abs() {
            b = k;
        }
    }
    b
}

#[cfg(one_past)]
pub fn one_past(v: [f64; 3], w: [f64; 4]) -> f64 {
    let mut b = 0;
    for k in 1..4 {
        if w[k] > 0.0 {
            b = k;
        }
    }
    v[b]
}

#[cfg(arith)]
pub fn arith(v: [f64; 3], w: [f64; 3]) -> f64 {
    let mut b = 0;
    for k in 0..3 {
        if w[k] > 0.0 {
            b = k + 2;
        }
    }
    v[b]
}

#[cfg(reborrowed)]
pub fn reborrowed(v: [f64; 3], c: bool) -> f64 {
    let mut b = 0;
    let r = &mut b;
    if c {
        *r = 7;
    }
    v[b]
}
