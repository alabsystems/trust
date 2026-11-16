//! Content fingerprints and verification-semantics keys used as cache keys.
//!
//! - [`compute_content_hash`] hashes the function body + contracts + spec.
//!   It delegates to [`VerifiableFunction::content_hash`], so there is one
//!   definition of the key.
//! - [`compose_semantics_key`] folds the whole-program bit into a
//!   verification-semantics key.
//!
//! Trust (plan P4 / T4.1, 2026-10-10): the solver-binary fingerprint
//! (`SolverBinaryFingerprint`, `snapshot_solver_binary`,
//! `fingerprint_solver_binary`, `compute_solver_fingerprint`) is deleted. Its
//! one caller was trustc's snapshot of the `ay` beside it; trustc now runs the
//! ay linked into the compiler, which the seal identity names.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::VerifiableFunction;

/// Compute a SHA-256 content hash of a function's body, contracts, and spec.
///
/// This is the cache key: if the hash matches a stored entry, the function
/// has not changed and verification can be skipped.
///
/// Delegates to [`VerifiableFunction::content_hash()`] to ensure a single
/// source of truth. The two must always agree.
#[must_use]
pub fn compute_content_hash(func: &VerifiableFunction) -> String {
    func.content_hash()
}

/// The stable verification-semantics segment recording whether the crate being
/// compiled is a *whole-program* artifact (executable / staticlib / cdylib)
/// rather than a downstream-extensible one (rlib / dylib / proc-macro).
///
/// Some obligations are discharged using facts that hold only for a closed
/// compilation. The canonical case is dyn-dispatch trait sealedness: a local
/// trait with no blanket impls has a fully known impl set only when every crate
/// type is whole-program — for an `rlib` a downstream crate may still add a
/// non-conforming impl, so the trait is open and a dyn-dispatch postcondition
/// may not strengthen caller VCs. The same function, byte-identical body,
/// contracts, and solver, can therefore legitimately prove when compiled into a
/// `bin` and must not prove when compiled into an `rlib`. Omitting the bit would
/// let one key serve both, so it belongs in the key rather than in a caller's
/// discipline.
///
/// Deliberately coarse — one boolean, not the crate-type list — so two
/// whole-program shapes (`[Executable]` vs `[StaticLib, Cdylib]`) that are
/// equivalent for sealedness still share a key, while a whole-program shape can
/// never alias a downstream-extensible one.
fn whole_program_semantics_segment_str(whole_program: bool) -> &'static str {
    if whole_program { "whole_program=true" } else { "whole_program=false" }
}

#[must_use]
pub fn whole_program_semantics_segment(whole_program: bool) -> String {
    whole_program_semantics_segment_str(whole_program).to_string()
}

/// Append the whole-program segment to a verification-semantics key.
///
/// Every producer of such a key composes it here so the folding is
/// byte-identical across them; a second spelling would silently create two key
/// spaces for the same semantics.
#[must_use]
pub fn compose_semantics_key(base_semantics_key: &str, whole_program: bool) -> String {
    format!("{base_semantics_key};{}", whole_program_semantics_segment_str(whole_program))
}

#[cfg(test)]
mod semantics_key_tests {
    use super::{compose_semantics_key, whole_program_semantics_segment};

    #[test]
    fn whole_program_shape_cannot_alias_a_downstream_extensible_one() {
        let base = "v3;mode=Full;level=1";
        let bin = compose_semantics_key(base, true);
        let rlib = compose_semantics_key(base, false);
        assert_ne!(bin, rlib);
        assert!(bin.starts_with(base) && rlib.starts_with(base));
        assert!(bin.ends_with(&whole_program_semantics_segment(true)));
        assert!(rlib.ends_with(&whole_program_semantics_segment(false)));
        assert_eq!(compose_semantics_key(base, true), bin);
    }
}
