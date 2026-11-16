//@ needs-trust-verify
//@ aux-build:cross_crate_bundle_scope_dep.rs
//@ compile-flags: -Ztrust-verify=on --crate-type lib -Ztrust-bundle-foreign-crate=xcbundle_dep
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-pass
//! D4 increment A (2026-09-24): the `ExternalDep` twin of
//! `cross_crate_value_used.rs`. The declared scope's bucket conjunct now admits
//! `ExternalDep` (`foreign_rederivation::declared_scope_bucket_is_rederivable`),
//! so an ordinary-named declared dependency's `ensures` is RE-DERIVED over its
//! encoded MIR here and reused exactly as the `trust_`-named twin's is.
//!
//! Measured BEFORE (stage-1 with wave 0, `a8c853de6f`): refused — the callee's
//! verification decision was `Skip(ExternalDependencyScope)`, so
//! `trust_proof_results` returned `None` and the reuse gate declined
//! (`TRUST_COMPOSE: verdict:none`), while the `trust_xcbundle_dep` twin minted.
//! The crate NAME was the only difference.
//!
//! The negative controls stay refused and are the point of this arm:
//! `cross_crate_bundle_scope_no_clause_import.rs` (THIS aux crate, declared, a
//! FALSE `ensures` that the re-derivation must refute) and
//! `cross_crate_bundle_scope_undeclared_stays_closed.rs` (undeclared).
extern crate xcbundle_dep;

/// `c + 1` overflows only if `c == u32::MAX`; it is discharged by, and only by,
/// the callee's re-derived `result <= 31`.
pub fn bump_capped() -> u32 {
    let c = xcbundle_dep::clamp_index(3);
    c + 1
}
