//@ needs-trust-verify
//@ aux-build:user_written_automatically_derived_dep.rs
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
//~? RAW Trust
//! **ARM 1 — a user-written `#[automatically_derived]` must not admit an
//! UNVERIFIED dependency body into the proof bundle.**
//!
//! **STATUS: this test was RED when written and is GREEN as of 2026-08-27.** It
//! is now a LIVE GATE against the hole re-opening, not a pending bug report. The
//! `//@ ignore-test` line it carried while the hole was open has been removed.
//! Everything below is kept verbatim because it is the evidence, and a gate
//! whose reason has been deleted is one somebody deletes next.
//!
//! It was never a prediction: the false verify below was reproduced end to end,
//! on the authenticated lane, with a runtime witness.
//!
//! # The gate — what it was, and what it is now
//!
//! `trust_verify.rs`'s cross-crate callee admission WAS
//!
//! ```text
//! if resolved_def_id.as_local().is_none()
//!     && !callee_is_automatically_derived_method(tcx, resolved_def_id) { continue; }
//! ```
//!
//! and `callee_is_automatically_derived_method` was, in full,
//! `def_kind == AssocFn && parent is Impl && tcx.is_automatically_derived(impl)`.
//! `is_automatically_derived` is `find_attr!(.., AutomaticallyDerived)` — a
//! lookup for one **stable, ungated, user-writable** attribute that is encoded
//! cross-crate. The comment guarding this admission called such bodies
//! "compiler-generated and panic-free by construction". Nothing enforced either
//! half; the attribute is a claim by the dependency's author about the
//! dependency's own code, believed without check.
//!
//! It is now, in full:
//!
//! ```text
//! if resolved_def_id.as_local().is_none() { continue; }
//! ```
//!
//! The helper is deleted. This is CONTAINMENT, not the root fix — see the
//! closing section.
//!
//! # Why "admitted" means "silently trusted", not "verified"
//!
//! Admission is decided by MIR AVAILABILITY. VERIFICATION is decided by the
//! PRODUCING compilation, and under `targo` every dependency unit is compiled
//! `-Ztrust-verify=off` (the report names it: `proof_role="excluded"`,
//! `reason="dependency-policy-excluded"`). So the bundled member arrives with no
//! obligations requested — and a bundled member's own `Assert` mints none either
//! — leaving `requested_obligations == 0`, `native_run_is_vacuously_clean`
//! satisfied, and the caller reported "trivially panic-free".
//!
//! This is the SAME defect the `std|core|alloc` conjunct was removed for on
//! 2026-08-25, re-entered through the one spelling that removal left open.
//!
//! # The measured witness (`targo trust build`, default `unix_hardened`)
//!
//! ```text
//! Summary: 0 proved, 0 failed, 0 runtime-checked, 0 assumed, 0 mandated,
//!          0 contract-panic, 0 inconclusive (0 total)
//! Coverage: 1/1 eligible function bodies verified (complete)
//! Verdict: NO OBLIGATIONS
//! Gate: PASS [strict lane, exit 0]
//! Result: PASS
//! ```
//!
//! and the binary that verdict was issued about:
//!
//! ```text
//! thread 'main' panicked at advdep/src/lib.rs:13:9:
//! index out of bounds: the len is 3 but the index is 5
//! RUNTIME_EXIT=101
//! ```
//!
//! Both crates compiled (`Finished dev profile`), so this is a false verify, not
//! a vacuous run over a crate that failed to build.
//!
//! The native bundle dump shows the mechanism with no inference required: the
//! module carries BOTH functions, the callee's bounds check is fully lowered —
//!
//! ```text
//! FUNCTION m
//!   PtrMetadata -> %5
//!   ICmp { op: Ult, lhs: 1, rhs: 5 } -> %6
//!   Assert { cond: 6 }   proofs: ["InBounds"]
//! ```
//!
//! — and `module.proof_obligations` holds exactly ONE entry, for the ROOT's
//! `main`. The caller's own body meanwhile holds `Const U64 3` (the length) and
//! `Const U64 5` (the index) as siblings in that same module. Everything needed
//! to REFUTE the call was present, and no obligation was ever minted over it.
//!
//! # What had to happen for this test to go green — and what did
//!
//! Both calls below had to be REFUSED. The attribute is not the right predicate
//! — the right question is whether the callee was actually VERIFIED, and an
//! attribute cannot answer it. Note especially `Inherent::get`: `#[derive(..)]`
//! expands to `impl Trait for Type` and never to an inherent `impl`, so that
//! shape is one no derive macro can produce, and it was admitted anyway.
//!
//! MEASURED 2026-08-27 after the containment fix, both refused, one row each:
//!
//! ```text
//! error: Trust strict verification failed for `..::dep_marked`:
//!        1 obligation(s) were not fully verified
//! error: Trust strict verification failed for `..::dep_inherent`:
//!        1 obligation(s) were not fully verified
//! ```
//!
//! Against the pre-fix compiler the same file is EXIT=0 with **zero** error
//! lines and empty stderr — that contrast is the mutation proof, and it is why
//! this file may not be weakened to a warning-level or `dont-check` assertion.
//!
//! # This is CONTAINMENT, and the root fix is still owed
//!
//! Locality is a sound gate but a blunt one: it refuses every cross-crate body
//! on this lane, including genuinely derive-generated ones. The cost is recorded
//! as a live test in
//! `automatically_derived_real_derive_still_bundled.rs`, which flipped from
//! `check-pass` to `check-fail` in the same change and carries the argument for
//! why a lost FALSE completeness is not a real loss.
//!
//! The root fix is to make a bundled member's own obligations REAL and locally
//! discharged, so that admission stops being a question about provenance at all.
//! `reset_native_trust_ir_proof_inventory_to_public_bundle` currently CLEARS the
//! module's private inventory and rebuilds it ROOT-scoped, which is exactly why
//! a bundled member's `Assert` mints nothing. When that is fixed, this file must
//! STILL be green — it must be green because the dependency's body was checked
//! and found wanting, never because an attribute stopped being believed.
//!
//! # Why there is no in-file negative control
//!
//! There was one — a `Plain::get` call in this same file — and it made the test
//! pass for the WRONG REASON. `check-fail` is satisfied by ANY error, so the
//! refusal of the un-attributed control alone turned the file green while both
//! subjects were still being silently trusted. Measured: EXIT=1 with the sole
//! diagnostic naming `<user_ad_dep::Plain as user_ad_dep::Idx>::get`, and not one
//! word about `Marked` or `Inherent`.
//!
//! The control therefore lives in its own file,
//! `automatically_derived_absent_attribute_stays_closed.rs`, where its verdict
//! cannot be mistaken for this one's. This file contains ONLY calls that must be
//! refused and are not, so its exit code is a statement about the subject.

extern crate user_ad_dep;

use user_ad_dep::{Idx, Inherent, Marked};

/// ARM 1a — trait impl carrying a hand-written `#[automatically_derived]`.
/// `xs` has 3 elements and the index is 5: this call panics in every execution.
pub fn dep_marked() -> u32 {
    let xs: [u32; 3] = [10, 20, 30];
    <Marked as Idx>::get(&xs, 5)
}

/// ARM 1b — inherent impl carrying a hand-written `#[automatically_derived]`.
/// No derive expansion can emit an inherent impl, so "compiler-generated" is
/// false here by construction.
pub fn dep_inherent() -> u32 {
    let xs: [u32; 3] = [10, 20, 30];
    Inherent::get(&xs, 5)
}
