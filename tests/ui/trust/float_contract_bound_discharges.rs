//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-pass
//! A magnitude bound on a float parameter, which until this landed could not be
//! WRITTEN: the clause was a hard compile error reporting `x` out of scope, on a
//! parameter.
//!
//! It is the documented way to verify float arithmetic, and without it there was
//! no way at all. `x * 2.0` on an unconstrained `f64` really can overflow to
//! infinity, so the obligation is honest and its witness is exact. The interval
//! tracer follows a value through `clamp` and through an integer cast, and NOT
//! through a float comparison guard, so a contract bound was the remaining
//! route — and `float_range::contract_range` was written for exactly it, with
//! this spelling in its own doc comment.
//!
//! `float_contract_bound_unbounded_still_refuses.rs` is the other half: the same
//! body without the bound, and with only half of it, must still be refused.

pub fn doubled(x: f64) -> f64
    requires x <= 1.0 && x >= -1.0
{
    x * 2.0
}

pub fn summed(a: f64, b: f64) -> f64
    requires a <= 1.0 && a >= -1.0 && b <= 1.0 && b >= -1.0
{
    a + b
}
