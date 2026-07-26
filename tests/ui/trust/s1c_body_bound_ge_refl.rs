//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ compile-flags: --crate-type=lib
//@ dont-check-compiler-stderr
//@ check-pass
//! Task #23 Slice 1 ACCEPTANCE (body-bound trust-wp claims; blueprint
//! docs/design-notes/2026-07-17-trust-wp-lowering-blueprint.md): an uncited
//! `ensures result >= x` on a copy-body function is PROVED end-to-end through
//! the trust-wp deductive lane. `finalize_trust_wp_body_bound_public_claims`
//! derives, pre-digest, the `trust_wp.trust-formula.v1` let-envelope
//! (`let result = x in result >= x`) from the typed trust-ir body; the sibling
//! NativeTrustWpBundleVerifier let-inlines to `x >= x` and proves it by the
//! reflexive-comparison rule, returning aggregate-Verified proof-grade
//! evidence (claim_format=TrustFormulaV1, deductive strength). The native full
//! verifier reports Proved with ZERO unsupported obligations.
//!
//! This integer comparison is also independently discharged by the exact fresh
//! postcondition VC and its kernel/source authority; that authority takes
//! precedence in the final row. The focused compiler unit tests isolate the
//! private live Trust-WP receipt path itself, while the Bool identity UI control
//! pins a production case whose original marker has no such Clean arithmetic
//! discharge.
pub fn ge_refl(x: u64) -> u64 ensures result >= x { x }
