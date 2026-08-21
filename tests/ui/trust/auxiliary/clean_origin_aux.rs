//@ no-prefer-dynamic
//@ compile-flags: -Z trust-verify=off
#![crate_type = "lib"]

//! **I7 — the exporting side of the cross-crate Clean-origin lane.**
//!
//! `pick` is minted from the island below (Projection fragment, parameter 0 —
//! the same shape `crates/trust-clean-origin/src/lib.rs` names as the one that
//! runs), gated by the sole constructor, and — because this crate is built as
//! an rlib dependency — exported through the I7 encode half: a
//! `trust_clean_verdict_digest` row, the island sources, and the
//! `trust_clean_origin_exports` list all land in this crate's rmeta.
//!
//! The module is `pub` DELIBERATELY (I7 review, defect 2): the mint forces the
//! DEF's visibility to `Public`, but nothing touches the module's, so a
//! private `mod m` here would kill every downstream fixture at E0603 and the
//! chokepoint would never be traversed. The private-module configuration is
//! pinned separately by `clean_origin_aux_private.rs` +
//! `clean_origin_cross_crate_private_mod.rs`.
//!
//! Reachability, per the corrected I7 chain (do not re-derive it from the old
//! plan text): in THIS configuration — a Clean-origin def in a `pub mod` of an
//! rlib — the def IS in `reachable_set` (the mint plants a `Public` binding in
//! the module's resolutions; effective-visibilities iterates resolutions, not
//! HIR; privacy clones that table; `reachable_set` seeds from it and inserts
//! `Node::Synthetic` worklist items unconditionally for library crate types).
//! The body still travels only because `should_encode_mir`'s registry arm
//! encodes both MIR rows unconditionally — at O0 a monomorphic def would
//! otherwise fail the `requires_monomorphization || cross_crate_inlinable`
//! conjunct, and in check-mode rmeta `should_codegen()` is false.
//!
//! `-Z trust-verify=off` is load-bearing evidence, not convenience: the mint,
//! the MIR gate, the digest export, and the importer's readmission are all
//! deliberately NOT behind the verification switch.

#![crate_type = "rlib"]

pub mod m {
    clean {
        def pick (x y : UInt64) : UInt64 := x
    }
}
