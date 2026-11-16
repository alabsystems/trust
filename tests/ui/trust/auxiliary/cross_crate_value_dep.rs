//@ compile-flags: --crate-type=rlib -Ztrust-verify=off -Zalways-encode-mir
//@ no-prefer-dynamic
//! The `cross_crate_bundle_scope_dep` pair again — same two functions, same
//! discrimination — under a crate NAME that `trust_mir_extract::policy::
//! classify_crate` buckets `TrustOwnedDefault` rather than `ExternalDep`.
//!
//! # Why a second aux crate rather than a rename
//!
//! The postcondition-REUSE lane forces `trust_proof_results` on the callee,
//! which makes the foreign body a verification SUBJECT of this compilation.
//! When this aux was written that was admitted only for a declared crate in a
//! `TrustOwned*` bucket, on the reasoning that an `ExternalDep` bucket's
//! `unsupported_is_failure() == false` would record a gap as an ASSUMPTION row.
//! That method has no compiler caller, and D4 increment A (2026-09-24) widened
//! the declared scope to `ExternalDep` (`foreign_rederivation::
//! declared_scope_bucket_is_rederivable`). `classify_crate` reads the crate
//! NAME, and `xcbundle_dep` is not a `trust_*` name.
//!
//! Keeping BOTH crates keeps the bucket conjunct measurable: the `xcbundle_dep`
//! arms and these arms differ in exactly that one classification. Before D4-A
//! the `xcbundle_dep` twin of `cross_crate_value_used.rs` was refused
//! (`verdict:none`); `cross_crate_value_used_external_dep.rs` now pins that it
//! passes, with the same refutation control.
//!
//! Everything else is deliberately identical to the sibling aux crate: compiled
//! `-Ztrust-verify=off` exactly as `targo` compiles a dependency unit, so
//! **nothing in this file has been verified by the compilation that produced
//! it**; `-Zalways-encode-mir` so a caller can read the BODY and not only the
//! signature; non-generic; `Assert`-free.
//!
//! | fn | declared `ensures` | true of the body? |
//! |---|---|---|
//! | `clamp_index` | `result <= 31` | YES |
//! | `overclaims`  | `result <= 3`  | **NO** — `overclaims(10)` returns `10` |
//!
//! `overclaims` is not a mistake and must not be "fixed". It is the negative
//! control for the failure mode that would make this lane unsound.
//!
//! The width is `u8` rather than `u32` so that a caller multiplying the result
//! by a constant OVERFLOWS on the callee's TRUE range (`31 * 200 > 255`). That
//! is the pre-registered REFUTATION direction: pinning the destination moves a
//! row from "unknown, unmodelled return" to a genuine counterexample, and a
//! reader counting only `proved` would call that a regression.
#![no_std]
#![crate_name = "trust_xcbundle_dep"]

/// Truthful postcondition. Every value this returns really is `<= 31`.
pub fn clamp_index(k: u8) -> u8 ensures result <= 31 {
    if k > 31 {
        return 31;
    }
    k
}

/// FALSE postcondition, on purpose. `overclaims(10) == 10`, which is not `<= 3`.
/// Nothing in the compilation that produced this file has checked the clause;
/// the caller's compilation re-derives it and must refute it.
pub fn overclaims(k: u8) -> u8 ensures result <= 3 {
    if k > 31 {
        return 31;
    }
    k
}
