//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ dont-check-compiler-stderr
//! **R2 — THE HONEST VERIFY-ON BOUNDARY FOR A WELL-FOUNDED CALL.**
//!
//! The sibling (`clean_origin_wf_rec.rs`) proves the lane under
//! `-Z trust-verify=off`: the mint, the emission and the F-layer gate all run,
//! and `countdownSum(5)` computes 15. This file pins what verification-ON
//! adds — and, deliberately, what it does NOT add yet.
//!
//! CALL MODELING FOR RECURSION IS A LATER INCREMENT. The cross-authority
//! summary lane (`trust_verify.rs`, `clean_origin_call_model_of_record`)
//! carries an EXPLICIT fail-closed `None` arm for `WellFoundedNatRec` — never
//! a fall-through — and it carries it for one reason more than the structural
//! arm does. An honest summary for `countdownSum` would have to state the
//! defining equations plus a totality claim; here that totality rests on the
//! kernel's typing rule at the decrease slot **and** on an audited-empty axiom
//! closure, and a caller-side summary has no way to state the second: it is a
//! property of the DECLARATION's environment, not of the call. Claiming
//! totality at a call site without it would be claiming precisely what probe
//! c1 measures to be assumable away.
//!
//! The panic-freedom half is genuinely false to claim structurally besides:
//! the emitted recursion is O(value) deep and each frame allocates a bignum,
//! so the call CAN abort on real inputs.
//!
//! So a caller of `countdownSum` fails closed: the call's result stays
//! havocked, the absent-callee panic-freedom obligation stays unproven, and a
//! strict build REFUSES — with the v7/D3 note naming the callee as a local
//! Clean-origin function and the options (restate in a modeled shape; wrap
//! with a proven `ensures` contract; `-Z trust-policy=advisory`).
//!
//! WHAT THIS FIXTURE MUST NEVER BECOME: a run-pass flipped by weakening strict
//! policy or by a summary that blesses caller claims. The flip, when it comes,
//! is a summary lane for the recursive shapes with its own refutation control
//! (the `clean_origin_caller_wrong_claim.rs` pattern) — and this header
//! rewritten IN THAT CHANGE, per the no-silent-ratchet rule.
//!
//! The GATE half is not what refuses here — the gate already admitted the
//! emitted body (the sibling proves it, and the gate runs identically in both
//! modes; it is not behind the switch). What refuses is the CALLER'S
//! obligation lane, which is exactly the division of labor the design records:
//! gate = compilation correctness of the emitted body; verification = the
//! caller's proof obligations.

extern crate trust_bignum;

clean {
    def countdownSum (n : Nat) : Nat := if h : 0 < n then n + countdownSum (n - 1) else 0
    termination_by n
}

fn main() {
    //~^ WARN Trust Level 0 safety verification incomplete
    //~| ERROR Trust strict verification failed
    // The call compiles and its body is kernel-gated; under verify-on the
    // CALL SITE fails closed — no summary exists for a recursive shape, so the
    // absent-callee panic-freedom obligation is unproven and strict refuses
    // the build.
    let out = countdownSum(trust_bignum::Nat::from_u64(3));
    // No claim about `out` is needed to pin the boundary: the refusal is the
    // call's own panic-freedom lane, not a refuted caller assertion.
    drop(out);
}
