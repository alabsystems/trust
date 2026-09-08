//@ needs-trust-verify
//@ aux-build:cross_crate_value_dep.rs
//@ compile-flags: -Ztrust-verify=on --crate-type lib -Ztrust-bundle-foreign-crate=trust_xcbundle_dep
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-pass
//! **ARM 4 — the RETURN VALUE of a foreign call is MODELLED, so a caller that
//! USES it can discharge its own obligations.**
//!
//! `cross_crate_bundle_scope_declared.rs` (arm 2) pins that a verified crate can
//! be CALLED: it writes `let _ = clamp_index(3);` and throws the value away. A
//! caller that BINDS the value and computes with it still failed after that
//! landed, and the row that did it was the caller's whole obligation content:
//!
//! ```text
//! [unsupported_mir] UnmodeledCalleeReturn: ArithmeticOverflow(Add)
//! ```
//!
//! `UnmodeledCalleeReturn` is not a gate and must not be relaxed — it is an
//! honest label, a DROP-ONLY reclassification (`trust-vcgen`'s
//! `reclassify_havoc_only_refutations`) applied to a row that would OTHERWISE BE
//! REFUTED, because the only value source for `c` is a foreign call and moving
//! `c` across `u8`'s declared range flips the obligation. Weakening its
//! predicate buys back a refutation whose counterexample no execution can
//! produce. The fix is to give the hypotheses a real PIN so the row never mints,
//! and the pin is the callee's own postcondition.
//!
//! # What crosses, and what does not
//!
//! **MIR BYTES and a CONTRACT CLAUSE cross. A VERDICT does not, and cannot.**
//! `clamp_index`'s `ensures result <= 31` is never assumed on the strength of
//! the clause. It is assumed only after `trust_proof_results` has run the LOCAL
//! provider over the foreign MIR **in this compilation, under this policy** and
//! returned a verdict that passes the shipped assumption-root gate. There is no
//! extern provider and no disk cache for that query, so there is no foreign
//! verdict anywhere to read — the re-derivation is not a fallback, it is the
//! only thing available. `cross_crate_value_no_clause_import.rs` is the arm that
//! pins the difference.
//!
//! # Why this body and not a passthrough
//!
//! `c + 1` is an obligation the caller must genuinely discharge, and it is
//! discharge-ABLE only with the callee's fact: `c <= 31` gives `c + 1 <= 32`,
//! while an unmodelled `c` ranges to `255` and the add really can overflow. So
//! this is a pass WITH proofs, and it differs from the failing shape by exactly
//! the presence of one hypothesis. A body whose only content is the call would
//! pass with an empty ledger, which is a shape this tree has been burned by.
extern crate trust_xcbundle_dep;

pub fn bump_capped() -> u8 {
    let c = trust_xcbundle_dep::clamp_index(3);
    c + 1
}
