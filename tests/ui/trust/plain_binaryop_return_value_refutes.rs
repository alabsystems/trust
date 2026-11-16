//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! THE SOUNDNESS HALF of `plain_binaryop_return_value_proves.rs`.
//!
//! Same body, but the clause is FALSE: `half_nonneg(0) == 0`, which is not
//! `>= 1`. Restoring the division's defining equation gives the solver strictly
//! MORE true facts about the program, and more true facts must never turn a
//! false claim into a proof. This file pins that the build is still refused.
//!
//! Read the pair together. The completeness half alone would pass just as well
//! if the verifier had been taught to believe anything.

pub fn claims_too_much(x: i32) -> i32
//~^ ERROR Trust strict verification failed
    requires x >= 0
    ensures result >= 1
{
    if x < 0 { 0 } else { x / 2 }
}
