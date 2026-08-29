//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ dont-check-compiler-stderr
//! **R1 — THE HONEST VERIFY-ON BOUNDARY FOR A STRUCTURAL-RECURSION CALL.**
//!
//! The sibling (`clean_origin_structural_rec.rs`) proves the lane under
//! `-Z trust-verify=off`: the mint, the emission and the per-defining-
//! equation gate all run, and `tozero(3)` computes 0. This file pins what
//! verification-ON adds — and, deliberately, what it does NOT add yet.
//!
//! CALL MODELING FOR RECURSION IS A LATER INCREMENT. The cross-authority
//! summary lane (`trust_verify.rs`, `clean_origin_call_model_of_record`)
//! carries an EXPLICIT fail-closed `None` arm for `StructuralNatRec` —
//! never a fall-through — because the recursive shapes are the first whose
//! honest summary is not a plain dest equality: it would have to carry the
//! defining equations plus a termination-derived totality claim, and the
//! panic-freedom half is genuinely false to claim structurally (the emitted
//! recursion is O(value) deep and its bignum ops allocate, so the call CAN
//! abort on real inputs). Until a summary lane states exactly what the
//! per-equation gate licenses and no more, a caller of `tozero` fails
//! closed: the call's result stays havocked, the absent-callee
//! panic-freedom obligation stays unproven, and a strict build REFUSES —
//! with the v7/D3 note naming the callee as a local Clean-origin function
//! and the options (restate in a modeled shape; wrap with a proven
//! `ensures` contract; `-Z trust-policy=advisory`).
//!
//! WHAT THIS FIXTURE MUST NEVER BECOME: a run-pass flipped by weakening
//! strict policy or by a summary that blesses caller claims. The flip, when
//! it comes, is a summary lane for the recursive shapes with its own
//! refutation control (the `clean_origin_caller_wrong_claim.rs` pattern) —
//! and this header rewritten IN THAT CHANGE, per the no-silent-ratchet rule.
//!
//! The GATE half is not what refuses here — the gate already admitted the
//! emitted body (the sibling proves it, and the gate runs identically in
//! both modes; it is not behind the switch). What refuses is the CALLER'S
//! obligation lane, which is exactly the division of labor the design
//! records: gate = compilation correctness of the emitted body; verification
//! = the caller's proof obligations.

extern crate trust_bignum;

clean {
    def tozero : Nat -> Nat
      | 0 => 0
      | n + 1 => tozero n
}

fn main() {
    //~^ WARN Trust Level 0 safety verification incomplete
    //~| ERROR Trust strict verification failed
    // The call compiles and its body is kernel-gated; under verify-on the
    // CALL SITE fails closed — no summary exists for a recursive shape, so
    // the absent-callee panic-freedom obligation is unproven and strict
    // refuses the build.
    let out = tozero(trust_bignum::Nat::from_u64(3));
    // No claim about `out` is needed to pin the boundary: the refusal is the
    // call's own panic-freedom lane, not a refuted caller assertion.
    drop(out);
}
