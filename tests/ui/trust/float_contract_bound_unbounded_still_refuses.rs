//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=certify --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! THE SOUNDNESS HALF of `float_contract_bound_discharges.rs`.
//!
//! Admitting a float contract must not admit the CONCLUSION. `x * 2.0` on an
//! unconstrained `f64` overflows to infinity at `x = 1e308`, and a ONE-SIDED
//! bound leaves the other side free, so both must stay refused. A two-sided
//! bound is what makes the witness unsatisfiable, and nothing weaker may.
//!
//! WHY `certify` (changed 2026-09-18). This file used to run under the default
//! policy and expect "Trust Level 0 safety verification incomplete". That used
//! "the build fails" as a proxy for "the row is not discharged", and the proxy
//! stopped holding when the Level-0 accounting was fixed to honour
//! `proof_level()`: `FloatOverflowToInfinity` is `L1Functional`, because
//! overflow to +/-inf is DEFINED in Rust — no trap, no UB, no panic — so under
//! the DEFAULT policy an undischarged float row is now REPORTED rather than
//! fatal. That is DESIGN_PHILOSOPHY section 9 and the 2026-08-02 float report's
//! resolution, which promised exactly this split.
//!
//! `certify` is the policy that demands full static discharge, so it is where
//! "is not discharged" is still an error, and it is the honest place for this
//! file's claim. The soundness property is unchanged: under either policy the
//! row is UNPROVED. A false proof would be a PROVED row, and that is what would
//! break this file.

pub fn unbounded(x: f64) -> f64 {
    //~^ ERROR Trust strict verification failed
    x * 2.0
}

pub fn half_bounded(x: f64) -> f64
    //~^ ERROR Trust strict verification failed
    requires x <= 1.0
{
    x * 2.0
}
