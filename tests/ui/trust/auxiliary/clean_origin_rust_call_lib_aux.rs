//@ no-prefer-dynamic
//@ compile-flags: -Z trust-verify=off
#![crate_type = "rlib"]
// The `dead_code` lint does not yet see a call that exists only in a Clean-origin
// body (same note as `clean_origin_rust_call.rs`).
#![allow(dead_code)]

//! **A LIBRARY crate that DEFINES a Clean def calling its own Rust `fn`.**
//!
//! The Lean→Rust edge (W5, `docs/design/2026-09-13-lean-calls-rust-lane.md`)
//! was bin-crate-only before 2026-09-16: `twice_inc` plans as a
//! `RustCallChain`, an importer has no table of THIS crate's Rust callees to
//! re-plan it against, and the export provider answered that with a fatal
//! `Clean declaration `twice_inc` cannot be exported for cross-crate calls` —
//! failing the crate that merely defined it (wf1 probe 18d, verbatim below
//! plus the wrapper).
//!
//! The provider now writes a non-exportable NOTICE in the certificate's place.
//! `bump2` — ordinary, non-generic, no `#[inline]` — is compiled here, where
//! the sole constructor gated `twice_inc`'s body, and is what another crate
//! calls (`clean_origin_rust_call_lib_wrapper_call.rs`). Naming
//! `m::twice_inc` from another crate is refused at the importer's readmission
//! chokepoint (`clean_origin_rust_call_lib_direct_call_refused.rs`).
//!
//! `keep` is the SIBLING control: a projection that calls no Rust and exports
//! a real certificate. It still cannot be called from another crate, because
//! readmission re-elaborates ALL of this crate's islands and `inc` is a
//! compiler-declared constant of THIS crate's environment only — and that
//! refusal must say so rather than guess at kernel skew
//! (`clean_origin_rust_call_lib_sibling_call_refused.rs`).

pub mod m {
    fn inc(x: u64) -> u64 {
        x.wrapping_add(1)
    }

    clean {
        def twice_inc (x : UInt64) : UInt64 := inc (inc x)
        def keep (x : UInt64) : UInt64 := x
    }
}

pub fn bump2(x: u64) -> u64 {
    m::twice_inc(x)
}
