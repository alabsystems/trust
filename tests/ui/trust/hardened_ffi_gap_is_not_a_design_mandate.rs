//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Ztrust-verify-profile=unix_hardened --crate-type lib
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! G3-MANDATE-L1-ONLY-1 (2026-10-27): an FFI call with no summary is a
//! modelling gap, never a hardened design mandate, with or without a bounded
//! local. Negative control for `hardened_design_mandate_with_bounded_locals.rs`.
//!
//! The vcgen fails such a call closed with an L0 `ffi_boundary` row whose
//! violation formula is the literal `Bool(true)` (`trust-vcgen`
//! `ffi_vcgen::unmodeled_ffi_obligation`). The compiler used to call ANY hardened
//! category with a `Bool(true)` violation a design mandate, so the default
//! policy's tolerance skipped the row and the strict gate printed an ADVISORY
//! ("keeps the runtime check rustc already emits") for a call that has no
//! runtime check at all; targo counted it `mandated`. On main `723f9ec299` that
//! happened only in a function with no bounded local (`ffi_top`): the interval
//! augmentation rewrote the row elsewhere. The first G3 fix (which leaves a
//! closed constant unaugmented) made every function below advisory, and only
//! the separate Level 0 gate still refused them.
//!
//! Now a mandate is only an L1 profile rule (`VcKind::is_hardened_design_mandate`),
//! so each function fails BOTH gates. ERROR annotations are required here: an
//! advisory strict gate leaves its `Trust strict verification failed` ERROR
//! unmatched and the test fails. The design mandate in `mandate_beside` is the
//! positive control in the same compile: it stays advisory.

extern "C" {
    fn getpgrp() -> i32;
    fn raise(sig: i32) -> i32;
}

pub fn ffi_top() -> i32 {
    //~^ ERROR Trust Level 0 safety verification incomplete
    //~| ERROR Trust strict verification failed
    unsafe { getpgrp() }
}

pub fn ffi_bounded(x: u8) -> i32 {
    //~^ ERROR Trust Level 0 safety verification incomplete
    //~| ERROR Trust strict verification failed
    let g = unsafe { getpgrp() };
    if x > 200 { 0 } else { g }
}

pub fn ffi_raise(sig: i32) -> i32 {
    //~^ ERROR Trust Level 0 safety verification incomplete
    //~| ERROR Trust strict verification failed
    unsafe { raise(sig) }
}

pub fn mandate_beside(s: &str) -> Option<u32> {
    //~^ WARN Trust verification advisory
    s.parse().ok()
}
