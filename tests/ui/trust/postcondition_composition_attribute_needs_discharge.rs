//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
//! Trust (postcondition composition — the ATTRIBUTE spelling's FALSE-PROVE
//! MACHINE, kept shut).
//!
//! The attribute half of
//! `postcondition_composition_preconditioned_needs_discharge.rs`, and it is the
//! load-bearing companion of
//! `postcondition_composition_attribute_at_call_site.rs`: the lane that file
//! opens is the same guarded lane, so it must be checked with the same negative.
//!
//! `positive_part` promises `*ret > 0` — but only for `x > 0`. Its body is the
//! identity, so the promise is FALSE for every `x <= 0`. `triple` calls it with
//! its own unconstrained parameter, so `x > 0` is not derivable at the call site
//! and the caller must learn NOTHING about `y`.
//!
//! There is a runtime witness: `triple(i32::MIN)` calls `positive_part(i32::MIN)`
//! (out of contract, so the promise does not apply), gets `i32::MIN` back, takes
//! the `y < 100` arm, and `y * 3` UNDERFLOWS. A caller that inherited `y > 0`
//! unconditionally would report the `Mul` obligation PROVED for a program that
//! panics.
//!
//! `VcKind::Precondition` is hardcoded `L1Functional` and `triple` declares no
//! contract, so it verifies at `L0Safety` and the call-site precondition row is
//! FILTERED OUT before any solver sees it. At this level the guard riding with
//! the assumption is the only thing between this file and that false prove.
#![feature(contracts)]
#![allow(incomplete_features)]

#[core::contracts::ensures(move |ret: &i32| *ret > 0)]
pub fn positive_part(x: i32) -> i32
    requires x > 0
{
    x
}

pub fn triple(x: i32) -> i32 {
//~^ ERROR Trust Level 0 safety verification incomplete for `postcondition_composition_attribute_needs_discharge::triple`
//~| ERROR Trust strict verification failed for `postcondition_composition_attribute_needs_discharge::triple`
    let y = positive_part(x);
    if y < 100 { y * 3 } else { 0 }
}
