//@ needs-trust-verify
//@ aux-build: no_std_to_string_impostor_dep.rs
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=certify --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
//! THE PLANTED REFUTATION FOR BOUNDARY HOLE 3 of the `ToString::to_string`
//! totality stamp (`trust_mir_extract::convert::tcx_marked_total_to_string_path`).
//!
//! The salvaged stamp identified the callee — at the TRAIT-ITEM spelling that
//! source-built MIR records for `x.to_string()` — by
//! `get_diagnostic_item("to_string_method")` alone, then read `Self` from the
//! call's generic arguments and admitted `u32` as foundational. A diagnostic item
//! is a source ATTRIBUTE. This crate is `#![no_std]` and never loads `alloc`, so
//! the auxiliary crate's `#[rustc_diagnostic_item = "to_string_method"]` is
//! uncontested and IS the answer to that lookup. Its `impl ToString for u32`
//! panics on every call, and the stamp would have called `victim` total: a
//! false PROVED on a call into third-party code (the dependency was built with
//! verification off, exactly as Targo builds dependencies).
//!
//! The fix anchors the trait item, the impl item and the `String` ADT on the
//! compiler's OWN `alloc` by artifact residency (`is_real_sysroot_crate`, the R2
//! discipline), which no attribute can claim. The call below must therefore keep
//! its honest may-panic obligation, and under `certify` that is an error.
//!
//! IF THIS FILE EVER COMPILES CLEAN, the stamp is admitting an identity on an
//! attribute again.
#![no_std]

extern crate no_std_to_string_impostor_dep;

use no_std_to_string_impostor_dep::ToString;

pub fn victim(x: u32) -> u8 {
    //~^ ERROR Trust Level 0 safety verification incomplete for `to_string_stamp_no_std_diagnostic_item_impostor_refuted::victim`
    //~| ERROR Trust strict verification failed for `to_string_stamp_no_std_diagnostic_item_impostor_refuted::victim`
    x.to_string()
}
