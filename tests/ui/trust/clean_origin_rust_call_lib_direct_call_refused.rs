//@ needs-trust-verify
//@ aux-build:clean_origin_rust_call_lib_aux.rs
//@ build-fail
//@ compile-flags: -Z trust-verify=off

//! **A Clean def that calls its crate's own Rust `fn` cannot be CALLED from
//! another crate — the two-crate negative control (close twin of
//! `clean_origin_rust_call_lib_wrapper_call.rs`, same aux).**
//!
//! `twice_inc` plans as a `RustCallChain` against the AUX's Rust callee table.
//! This crate's Clean environment has no such table, so no certificate for it
//! could be re-admitted here, and the aux exported a non-exportable NOTICE in
//! the certificate's place. The mechanics are
//! `clean_origin_wf_lib_direct_call_refused.rs`'s: the path resolves and
//! type-checks, the aux emitted no linkable symbol for a Clean-origin def, so
//! codegen must instantiate the body through the guarded extern
//! `optimized_mir` arm, whose `trust_clean_extern_readmission` recognises the
//! notice and fatals with its v7/D3 note — what, why (no table of the defining
//! crate's Rust callees on this side), and the options.
//!
//! This is the refusal that used to fail the AUX's own build; it moved to
//! where a cross-crate call is actually attempted, and it did not get weaker:
//! there is no arm on which a recognised notice serves a body.
//!
//! The note's text is pinned against this file's `.stderr` by
//! `crates/trust-clean-origin/tests/control_28_non_exportable_notice.rs`.

extern crate clean_origin_rust_call_lib_aux;

fn main() {
    let v = clean_origin_rust_call_lib_aux::m::twice_inc(5);
    assert_eq!(v, 7);
}

//~? ERROR `clean_origin_rust_call_lib_aux::m::twice_inc` cannot be called from another crate
