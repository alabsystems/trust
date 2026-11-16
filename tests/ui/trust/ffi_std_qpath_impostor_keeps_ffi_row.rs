//@ needs-trust-verify
//@ edition: 2024
// `aux-crate`, not `aux-build`: the aux's crate NAME is `alloc`, and only an explicit
// `--extern alloc=<path>` makes `alloc::` resolve to it (see
// `policy_b/dropglue_spoofed_alloc_refused.rs`).
//@ aux-crate: alloc=ffi_qpath_impostor/alloc.rs
//@ compile-flags: -Ztrust-verify=on -Coverflow-checks=on --crate-type lib
//@ check-fail
//@ dont-check-compiler-stderr
//@ rustc-env:TRUST_NO_SYSROOT_CENSUS=1
//! FFI-STD-QPATH-1 review, finding 2 (2026-10-26). The exemption reads `ffi` type
//! paths out of a qualified `<Self as Trait>` header and out of generic arguments, and
//! took an unstamped `std::`/`alloc::`/`core::` root there for the sysroot. The
//! extractor stamps `__trust_crate@…` only on the ROOT of a path it renders; a type
//! inside the header or the arguments renders plain, and the producer marks the call
//! with the duplicate-crate-name argument fingerprint `::<__trust_args@…>` instead
//! (ARGS-FINGERPRINT-READ-1: a reader of a TYPE PATH in a tagged call's arguments must
//! decline). The first version of the exemption did not, so a verify-off dependency
//! named `alloc` (`auxiliary/ffi_qpath_impostor/alloc.rs`, whose `Handle: Clone`
//! hands `write(2)` a null buffer) lost the `unmodeled FFI call` row on
//! `<alloc::ffi::Handle as core::clone::Clone>::clone::<__trust_args@…>` and
//! `<alloc::vec::Vec<alloc::ffi::Handle> as core::clone::Clone>::clone::<__trust_args@…>`.
//! A fingerprinted callee is now never exempt.
//!
//! Measured 2026-10-26 with the header's flags plus `-Zui-testing
//! -Zdeduplicate-diagnostics=no -A unused --emit=metadata`. Before the decline (the
//! stage 1 at version identity `003c01d50`): `fake_qpath` and `fake_generic_in_real_std`
//! report a Level 0 WARNING with 1 obligation where an ERROR with 2 is annotated (the
//! absent-callee row alone; still refused by the strict lane, which is why this was a
//! wrong argument rather than a false proof). After: every annotation fires and
//! nothing else is reported. Controls: `fake_free`'s head IS stamped and routes on
//! both; `real_qpath` (`<std::ffi::os_str::OsString as Clone>::clone`, untagged in
//! this graph because `std`'s name is not shared) stays exempt on both.

use std::ffi::OsString;

/// `<alloc::ffi::Handle as core::clone::Clone>::clone::<__trust_args@…>`.
pub fn fake_qpath(h: &alloc::ffi::Handle) -> alloc::ffi::Handle {
    //~^ ERROR Trust Level 0 safety verification incomplete for `ffi_std_qpath_impostor_keeps_ffi_row::fake_qpath`: 2 obligation(s) were not proved
    //~^^ ERROR Trust strict verification failed for `ffi_std_qpath_impostor_keeps_ffi_row::fake_qpath`: 2 obligation(s) were not fully verified
    h.clone()
}

/// `<alloc::vec::Vec<alloc::ffi::Handle> as core::clone::Clone>::clone::<__trust_args@…>`.
pub fn fake_generic_in_real_std(v: &Vec<alloc::ffi::Handle>) -> Vec<alloc::ffi::Handle> {
    //~^ ERROR Trust Level 0 safety verification incomplete for `ffi_std_qpath_impostor_keeps_ffi_row::fake_generic_in_real_std`: 2 obligation(s) were not proved
    //~^^ ERROR Trust strict verification failed for `ffi_std_qpath_impostor_keeps_ffi_row::fake_generic_in_real_std`: 2 obligation(s) were not fully verified
    v.clone()
}

/// Control: `__trust_crate@…::alloc::ffi::f`, stamped at the root.
pub fn fake_free() -> isize {
    //~^ ERROR Trust Level 0 safety verification incomplete for `ffi_std_qpath_impostor_keeps_ffi_row::fake_free`: 2 obligation(s) were not proved
    //~^^ ERROR Trust strict verification failed for `ffi_std_qpath_impostor_keeps_ffi_row::fake_free`: 2 obligation(s) were not fully verified
    alloc::ffi::f()
}

/// Control: the real std's `OsString`, no fingerprint, exempt.
pub fn real_qpath(s: &OsString) -> OsString {
    //~^ WARN Trust Level 0 safety verification incomplete for `ffi_std_qpath_impostor_keeps_ffi_row::real_qpath`: 1 obligation(s) were not proved
    //~^^ WARN Trust verification advisory for `ffi_std_qpath_impostor_keeps_ffi_row::real_qpath`: 1 obligation(s) were not fully verified
    s.clone()
}
