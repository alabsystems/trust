//@ run-fail
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=off -Coverflow-checks=on
//@ error-pattern: the precondition `x == y` does not hold
//@ ignore-emscripten no processes
//! The WITNESS for `spec_float_eq_ieee.rs` (SPEC-FLOAT-EQ-STRUCTURAL-1,
//! docs/KNOWN_HAZARDS.md): the `callsite_nan` revision's call, built with
//! verification OFF and the clause checked by hand inside the callee.
//!
//! Rust's `==` on `f64` is IEEE equality, so `f64::NAN == f64::NAN` is false and
//! `c_xy(f64::NAN, f64::NAN)` breaks `requires x == y`. Verified BEFORE the fix
//! (stage 1 of 4ccd862830, default policy), that same call's precondition row was
//! PROVED — the clause was read as structural SMT `=`, under which NaN equals
//! itself — and the crate was accepted (the scout's `q5.rs`, built with
//! verification ON, returned `false` from `x == y` inside the callee and exited
//! 3). This program is what that verdict certified: it panics.

#[inline(never)]
fn c_xy(x: f64, y: f64) -> f64
    requires x == y
{
    assert!(x == y, "the precondition `x == y` does not hold for x = {x}, y = {y}");
    x
}

fn main() {
    let nan = std::hint::black_box(f64::NAN);
    c_xy(nan, nan);
}
