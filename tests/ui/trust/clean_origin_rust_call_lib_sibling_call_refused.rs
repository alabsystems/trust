//@ needs-trust-verify
//@ aux-build:clean_origin_rust_call_lib_aux.rs
//@ build-fail
//@ compile-flags: -Z trust-verify=off
//@ dont-check-compiler-stderr

//! **The SIBLING of a Rust-calling Clean def cannot be imported either — and
//! the refusal names the real cause, not kernel skew.**
//!
//! `keep` is an ordinary projection: it calls no Rust, and the aux exports a
//! real certificate for it (NOT a non-exportable notice — `control_28` pins
//! that a non-chain plan gets no notice). What stops it is one step later:
//! readmission re-elaborates ALL of the aux's `clean { … }` islands in a fresh
//! session under this compiler's kernel, and the same island declares
//! `twice_inc := inc (inc x)`. `inc` is a constant the compiler declares in
//! the DEFINING crate's Clean environment from its Rust callee table; it is
//! never island text, and no callee table crosses the crate boundary
//! (Lean-calls-Rust increment 6). The island therefore does not elaborate
//! here, and every certificate of the aux refuses.
//!
//! That was unreachable before 2026-09-16 (such an aux did not build at all),
//! so allowing the library to build is what exposed it. The arm it lands on
//! used to have one explanation — "the islands no longer elaborate under this
//! compiler's Clean kernel … rebuild the dependency" — which is wrong here and
//! sends the user nowhere. The provider now asks whether the exporter wrote a
//! Rust-callee notice and, if so, says what is true: which def, why, and the
//! options (wrapper `fn`, split the crate, restate without the callee).
//!
//! Fail-closed either way; this fixture pins the DIAGNOSTIC and that the
//! sibling is refused rather than served. The positive twin is
//! `clean_origin_rust_call_lib_wrapper_call.rs` (same aux); the note's text is
//! pinned in `crates/trust-clean-origin/tests/control_28_non_exportable_notice.rs`.

extern crate clean_origin_rust_call_lib_aux;

fn main() {
    let v = clean_origin_rust_call_lib_aux::m::keep(5);
    assert_eq!(v, 5);
}

//~? ERROR cannot be re-elaborated in this crate
