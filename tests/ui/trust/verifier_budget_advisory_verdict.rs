//@ needs-trust-verify
//@ build-pass
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory -Ztrust-verify-function-budget-steps=1 --crate-type=lib
//@ dont-check-compiler-stderr
// The advisory lane reports the overrun and the substituted `Unknown` budget
// row here. HOW the row renders is not what this test pins — it pins that the
// build SURVIVES with the finding reported — and pinning the exact report
// wording would make an unrelated reporting improvement look like a regression
// in this guard.
//@ dont-require-annotations: WARN

//! **Regression: a preprocessing budget overrun must not hard-fail advisory.**
//!
//! `TrustVerifyPolicy` documents advisory as "NOTHING in the verify pass is a
//! hard error — verification is purely advisory", and
//! `trust_types::verify_budget` promises a budget trip "costs only
//! completeness — an `Unknown` obligation — never soundness". Until 2026-08-30
//! the preprocessing checkpoints (`preprocessing_budget_exceeded`) violated
//! both: they emitted an unconditional `span_err`, so one over-budget function
//! in a THIRD-PARTY dependency killed a whole advisory survey build. The live
//! casualty was `syn` 1.0.109 — `ty::parsing::ambig_ty` exhausted the
//! 120000 ms / 64M step VC-generation budget and
//! `RUSTFLAGS=-Ztrust-policy=advisory cargo build` could not compile the crate
//! at all, which is exactly the survey lane advisory exists for:
//!
//! ```text
//! error: Trust verification exceeded its per-function budget (120000 ms /
//!        64000000 steps) during VC generation of `ty::parsing::ambig_ty` —
//!        possible verifier non-termination. ...
//! error: could not compile `syn` (lib) due to 1 previous error
//! ```
//!
//! Now the overrun in a non-fail-closed lane is a located WARNING plus the
//! honest per-function verdict: the (incomplete) obligation inventory is
//! DISCARDED and replaced by one synthetic `Unknown` row
//! (`preprocessing_budget_artifacts`), so the function can never read as
//! `Proved` and a strict lane still fails on the same row via the
//! unknowns-not-permitted policy. The fail-closed hard error is pinned by the
//! sibling `verifier_budget_termination.rs`.

pub fn stepped(mut n: u32) { //~ WARN exceeded its per-function budget
    while n > 0 invariant n <= 100 {
        n -= 1;
    }
}
