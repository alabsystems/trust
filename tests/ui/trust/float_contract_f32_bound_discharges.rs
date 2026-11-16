//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-pass
//! The `f32` twin of `float_contract_bound_discharges.rs`.
//!
//! This file was a KNOWN-GAP refusal until 2026-09-17. An `f32` magnitude bound
//! could be written, scoped, typed, lowered and admitted as an assumption —
//! every step the `f64` one takes — and then was NOT discharged, because the
//! discharge measured every interval against f64-scaled thresholds.
//!
//! Wiring the bound into that lane unchanged was a measured FALSE PROOF: the
//! tiny-operand bound was `2^970` and the margin sat near `f64::MAX`, both
//! astronomically above `f32::MAX`, so an `f32` add of two operands near `3e38`
//! read as "tiny" and verified when its true result is infinity.
//!
//! The fix was to make the DISCHARGE carry the operation's IEEE width and pick
//! its thresholds from it — `MAX / 8` for the margin, `ulp(MAX) / 2` for the
//! tiny bound — so a binary32 op is measured against binary32 figures.
//! `float_contract_f32_near_max_is_not_discharged.rs` is the other half.

pub fn bounded_f32_add(a: f32, b: f32) -> f32
    requires a <= 1.0 && a >= -1.0 && b <= 1.0 && b >= -1.0
{
    a + b
}

pub fn bounded_f32_mul(x: f32) -> f32
    requires x <= 1.0 && x >= -1.0
{
    x * 2.0
}
