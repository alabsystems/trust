//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
//! Trust (postcondition composition, slice 2 — THE FALSE-PROVE MACHINE, kept shut).
//!
//! A callee's `ensures` is guaranteed only WHEN ITS `requires` HELD. A caller
//! may therefore assume the postcondition only where the precondition is
//! DISCHARGED AT THAT CALL SITE. This file is the case where it is not.
//!
//! `positive_part` promises `result > 0` — but only for `x > 0`. Its body is
//! the identity, so the promise is FALSE for every `x <= 0`. `triple` calls it
//! with its own unconstrained parameter, so `x > 0` is not derivable at the
//! call site and the caller must learn NOTHING about `y`.
//!
//! THIS IS NOT A COMPLETENESS NICETY — it has a runtime witness.
//! `triple(i32::MIN)` calls `positive_part(i32::MIN)` (out of contract, so the
//! callee's promise does not apply), gets `i32::MIN` back, takes the
//! `y < 100` arm, and `y * 3` UNDERFLOWS. If the caller inherited `y > 0`
//! unconditionally, the `Mul` obligation would be reported PROVED for a
//! program that panics — a false PROVE with a witness, not a missed proof.
//!
//! The `Mul` is also the only thing that can catch it here. `VcKind::Precondition`
//! is hardcoded `L1Functional` (`trust-types` `vc_kind.rs` `proof_level`) and
//! `triple` declares no contract, so it verifies at `L0Safety` and the
//! call-site precondition row is FILTERED OUT before any solver sees it. At
//! this level the call-site guard on the assumption is the ONLY thing standing
//! between this file and the false prove above.
//!
//! Companions: `postcondition_composition_preconditioned_at_call_site.rs` adds
//! the `x > 0` guard and must PASS;
//! `postcondition_composition_preconditioned_upper_bound_only.rs` keeps the
//! guard and weakens the clause, and must still FAIL.

pub fn positive_part(x: i32) -> i32
    requires x > 0
    ensures result > 0
{
    x
}

pub fn triple(x: i32) -> i32 {
//~^ ERROR Trust Level 0 safety verification incomplete for `postcondition_composition_preconditioned_needs_discharge::triple`
//~| ERROR Trust strict verification failed for `postcondition_composition_preconditioned_needs_discharge::triple`
    let y = positive_part(x);
    if y < 100 { y * 3 } else { 0 }
}
