//@ no-prefer-dynamic
//@ compile-flags: -Z trust-verify=off

//! **I7 — the private-module control aux.**
//!
//! Identical to `clean_origin_aux.rs` except the module is PRIVATE. The mint
//! forces the planted DEF's visibility to `Public` (a parity requirement —
//! see `tests/ui/trust/clean_origin_call_parity.rs`), and this crate pins
//! that the enclosing MODULE's visibility is left alone: a downstream crate
//! naming `clean_origin_aux_private::m::pick` must be refused exactly as it
//! would be for an ordinary private-module Rust item
//! (`clean_origin_cross_crate_private_mod.rs` is the consumer).
//!
//! This crate still builds, still mints `pick` locally, and still encodes the
//! digest row + exports list into its rmeta — privacy is a NAMING question in
//! the importer, not an exporting one.

#![crate_type = "rlib"]

mod m {
    clean {
        def pick (x y : UInt64) : UInt64 := x
    }
}

/// Keep the private module exercised in-crate, the same way the local parity
/// fixtures call `crate::m::f` — this also pins that the def resolves and
/// runs where it IS nameable.
pub fn pick_via_owner(x: u64, y: u64) -> u64 {
    crate::m::pick(x, y)
}
