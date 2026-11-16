//@ needs-trust-verify
//@ aux-build:clean_origin_rust_call_lib_aux.rs
//@ run-pass
//@ compile-flags: -Z trust-verify=off
//@ dont-check-compiler-stderr

//! **A library may DEFINE a Clean def that calls its own Rust `fn` — positive
//! lane.** The Lean→Rust twin of `clean_origin_wf_lib_wrapper_call.rs`.
//!
//! The aux used to fail to build (`Clean declaration `twice_inc` cannot be
//! exported for cross-crate calls`, wf1 probe 18d), so the whole Lean→Rust
//! edge was bin-crate-only. It now exports a non-exportable NOTICE for
//! `twice_inc`, builds as an rlib, and `bump2` — compiled in the aux, where
//! `twice_inc`'s body was kernel-gated against the aux's own callee table —
//! is what this crate links and calls.
//!
//! The values are the ones `clean_origin_rust_call.rs` pins locally: two
//! applications of `inc` (a single one would give 6), wrapping through the
//! intermediate.
//!
//! THE CLOSE NEGATIVE TWIN is
//! `clean_origin_rust_call_lib_direct_call_refused.rs` (same aux).

extern crate clean_origin_rust_call_lib_aux;

fn main() {
    assert_eq!(clean_origin_rust_call_lib_aux::bump2(5), 7, "two applications of `inc`");
    assert_eq!(
        clean_origin_rust_call_lib_aux::bump2(u64::MAX),
        1,
        "the chain wraps through the intermediate"
    );
}
