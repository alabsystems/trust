//@ needs-trust-verify
//@ aux-build:clean_origin_wf_lib_aux.rs
//@ run-pass
//@ compile-flags: -Z trust-verify=off
//@ dont-check-compiler-stderr

//! **A library may DEFINE a well-founded Clean def, and another crate may use
//! the library — positive lane.**
//!
//! `clean_origin_wf_lib_aux.rs` is an rlib containing the well-founded
//! `countdownSum`. It used to fail to build (`internal: refusing to export a
//! certificate …`, wf1 probes 18b/18c/36b/36d), which made recursion
//! bin-crate-only. It now exports a non-exportable NOTICE for that def instead
//! of a certificate, so:
//!
//!   1. the aux builds as a library at all — the defect this fixture exists
//!      for; a regression fails the aux build and this test with it;
//!   2. `triangle`, an ordinary non-generic Rust `fn` of the aux, is compiled
//!      IN the aux, where the sole constructor kernel-gated `countdownSum`'s
//!      emitted body; this crate links `triangle`'s symbol and never needs —
//!      and is never served — `countdownSum`'s body.
//!
//! The asserts are the value half: the triangular numbers, computed by the
//! emitted well-founded recursion inside the library.
//!
//! THE CLOSE NEGATIVE TWIN is `clean_origin_wf_lib_direct_call_refused.rs`:
//! same aux, but it names `m::countdownSum` directly, and must be refused.
//! Read together they are the scope `trust-clean-origin`'s crate docs state:
//! the DEF is crate-local, the crate is not.

extern crate clean_origin_wf_lib_aux;

fn main() {
    for (input, expected) in [(0u64, 0u64), (1, 1), (3, 6), (5, 15)] {
        assert_eq!(
            clean_origin_wf_lib_aux::triangle(input),
            Some(expected),
            "triangle({input}) must compute {expected} through the library's emitted \
             well-founded recursion"
        );
    }
}
