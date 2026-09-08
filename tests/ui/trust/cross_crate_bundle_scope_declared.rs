//@ needs-trust-verify
//@ aux-build:cross_crate_bundle_scope_dep.rs
//@ compile-flags: -Ztrust-verify=on --crate-type lib -Ztrust-bundle-foreign-crate=xcbundle_dep
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-pass
//! **ARM 2 — a BUILD-DECLARED bundling scope lets the caller re-derive a foreign
//! callee's body, and the call stops being fatal.**
//!
//! The body below is byte-identical to
//! `cross_crate_bundle_scope_undeclared_stays_closed.rs`. The ONLY difference is
//! `-Ztrust-bundle-foreign-crate=xcbundle_dep` in the compile
//! flags. That is the controlled pair: one variable, both directions pinned.
//!
//! # What crosses the crate boundary, and what does not
//!
//! **MIR BYTES cross. A VERDICT does not, and cannot.** The declared scope makes
//! the callee's body available to the bundler; every obligation over that body is
//! then minted and discharged by THIS compilation's verifier, in this
//! compilation, under this compilation's policy. Nothing is inherited.
//!
//! The verdict channel is not closed by a guard someone could delete — it does
//! not exist. `trust_proof_results` is declared `arena_cache` and nothing else:
//! no `separate_provide_extern`, so a foreign `DefId` key has no provider to
//! answer it, and no `cache_on_disk`, so nothing is persisted. A foreign
//! verdict is unreadable at every point of this compilation, before and after
//! this lane. Do not "fix" that query.
//!
//! The scope is declared by the CALLER, deliberately. The 2026-08-25 cross-crate
//! admission hole keyed on `#[automatically_derived]`, a callee SELF-CLAIM that
//! is stable, ungated, user-writable and encoded cross-crate. A list of units
//! the invoking build compiled itself is not a claim the callee makes about
//! itself. `targo trust check|build` injects exactly that list.
//!
//! # What this test does NOT establish
//!
//! It does not establish that the dependency is verified. It is compiled
//! `-Ztrust-verify=off`, like every dependency unit under `targo`. What passes
//! here is the CALLER, on obligations the caller discharged over bytes it read.
//! Its companion `cross_crate_bundle_scope_no_clause_import.rs` pins the other
//! half: the caller may not lean on the dependency's declared clause either.
extern crate xcbundle_dep;

/// Deliberately NOT a bare passthrough. A body whose only content is the
/// foreign call has an empty obligation ledger once the call stops being an
/// absent callee, and "PASS with zero obligations" is a shape this tree has
/// been burned by. The capped increment gives the caller two obligations it
/// must genuinely discharge itself — an `Add` overflow and its hardened
/// boundary — so the passing arm is a pass WITH proofs, and the failing arm
/// differs from it by exactly one extra row.
pub fn bump_capped(a: u8) -> u8 {
    let _ = xcbundle_dep::clamp_index(3);
    if a > 200 {
        return 201;
    }
    a + 1
}
