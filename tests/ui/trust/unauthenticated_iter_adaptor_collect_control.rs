//@ needs-trust-verify
//@ no-prefer-dynamic
//@ aux-build:unauthenticated_iter_adaptor_dep.rs
//@ compile-flags: -Ztrust-verify=on --crate-type=lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! THE NON-VACUITY CONTROL for `unauthenticated_iter_adaptor_collect_refused.rs`.
//!
//! Byte-identical to that file's `boom` but for one identifier: `nudge` instead of
//! `map`. `mycrate::Adapt::nudge` has the same signature and the same body, and it
//! returns the same endless iterator — so this program is unbounded in exactly the
//! same way. Because `nudge` is not a member of the length-preserving NAME set,
//! the bounded-source walk declined it and the obligation survived.
//!
//! It reports on pristine `main` and must keep reporting after the fix: the fix
//! only removes a grant, so nothing here changes. This file is what makes the
//! exploit's silence measurable — the difference between a build error and a clean
//! compile was one identifier in a dependency.
//!
//! ANNOTATION PLACEMENT: under the `pub fn boom(..)` signature, because that is
//! where both errors' primary span starts (MEASURED). Same rule as
//! `e2_mut_prime_undischarged.rs` / `e9_definitional_call_undischarged.rs`.
#![allow(dead_code)]

extern crate mycrate;

#[inline(never)]
pub fn boom(v: &Vec<u8>) -> Vec<u8> {
    //~^ ERROR Trust Level 0 safety verification incomplete
    //~| ERROR Trust strict verification failed
    mycrate::Adapt::nudge(v.iter(), 0).collect()
}
