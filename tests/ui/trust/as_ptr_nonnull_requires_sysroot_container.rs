//@ revisions: default certify memsafe
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Coverflow-checks=on --crate-type lib
//@[certify] compile-flags: -Ztrust-policy=certify
//@[memsafe] compile-flags: -Ztrust-policy=memory-safe
//@ check-fail
//@ dont-check-compiler-stderr
//@ rustc-env:TRUST_NO_SYSROOT_CENSUS=1
//! An FFI argument is non-null by std's container accessor only when the call IS
//! that accessor, by its compiler-minted key (ASPTR-KEY-1).
//!
//! `container_len::is_std_container_as_ptr` licensed the `strlen: parameter 0 must be
//! non-null` discharge for the result of any call whose rendered path ended in
//! `::as_ptr`/`::as_mut_ptr`, began with `core::`/`std::`/`alloc::`, and contained a
//! container substring ANYWHERE. std's RAW-slice accessor
//! `core::ptr::const_ptr::<impl *const [T]>::as_ptr` returns `self as *const T`, null
//! for a null receiver, and its rendering carries `T`: `*const [VecDeque<u8>]` supplies
//! `vec_deque` (`lie`), `*const [Vec<u8>]` supplies `alloc::vec` (`lie_vec`). Both lost
//! the FFI row; `twin` (`*const [u8]`, no substring) and `control` kept it `unknown`.
//! Built verify-off, `lie(slice_from_raw_parts(null(), 0))` hands `strlen` a null
//! pointer and segfaults (`scratchpad/scout13/S-ASPTR/run.rs`, exit 139).
//!
//! BEFORE (`scratchpad/stage1-w11fix`, each revision's flags plus `-Zui-testing
//! -Zdeduplicate-diagnostics=no -A unused --emit=metadata`, 2026-10-04): every
//! revision exits 1 (the `[unsafe] missing SAFETY comment` row fails on every FFI
//! call), but `lie` and `lie_vec` report "2 obligation(s)" where the annotations
//! below say 3, and under default their second diagnostic is the advisory WARN, not
//! the strict ERROR: no annotation on `lie`/`lie_vec` matches.
//!
//! AFTER (predicted, then measured): the accessor is named by its key
//! (`SliceAsPtr`, `SliceAsMutPtr`, `VecAsPtr`, `VecAsMutPtr`, `StrAsPtr`,
//! `StrAsMutPtr`, `CStrAsPtr`); `RawSlicePtrAsPtr` is not among them, and a raw-pointer
//! receiver is refused. The annotations were derived on the BEFORE compiler from a
//! twin of this file whose `lie`/`lie_vec` take `*const [u8]` (nothing else changed),
//! which the BEFORE recognizer already refuses: checked the way compiletest checks
//! (line, kind, substring; every error and warning annotated), it matches all three
//! revisions. The std controls keep the FFI row proved (it is absent from their
//! counts) before and after: their keys are measured `SliceAsPtr`, `VecAsPtr`,
//! `StrAsPtr`, `CStrAsPtr`.
//! Measured on the stage 1 of `4463aeeb6d` (2026-10-04): every annotation below fires in
//! every revision and nothing else is reported. `lie` and `lie_vec` carry the
//! `hardened_ffi_boundary` row (unknown), as `twin` does.
//!
//! Runs with `TRUST_NO_SYSROOT_CENSUS=1` (2026-10-08, std-absent-callee): this file
//! pins obligation COUNTS of the FFI lane, and the sysroot panic census derives each
//! accessor call here panic-free (`<*const [T]>::as_ptr`, `Vec::as_ptr`, `CStr::as_ptr`,
//! `str::as_ptr`: casts and field reads), which removes one panic-freedom row per
//! function. Withholding the census (it only removes proof) keeps the counts measured.
//!
//! G3-MANDATE-L1-ONLY-1 (2026-10-27): under `default`, `std_cstr`'s strict gate is an
//! ERROR, like `std_str`'s, not the advisory WARN it had. Its failed
//! `hardened_unsafe_operation` row (the `[unsafe] missing SAFETY comment` stand-in, a
//! constant `true` violation) was skipped by the default policy's tolerance as a
//! "design mandate" in a function with no bounded local; a mandate is now an L1 profile
//! rule only (`VcKind::is_hardened_design_mandate`). Counts unchanged.

#![feature(slice_ptr_get)]
use core::ffi::{c_char, CStr};
use std::collections::VecDeque;

unsafe extern "C" {
    safe fn strlen(s: *const c_char) -> usize;
}

/// std's RAW-slice `as_ptr`, whose generic argument spells `vec_deque`.
pub fn lie(p: *const [VecDeque<u8>]) -> usize {
    //[default,certify]~^ ERROR Trust Level 0 safety verification incomplete for `as_ptr_nonnull_requires_sysroot_container::lie`: 3 obligation(s) were not proved
    //[default,certify]~^^ ERROR Trust strict verification failed for `as_ptr_nonnull_requires_sysroot_container::lie`: 3 obligation(s) were not fully verified
    //[memsafe]~^^^ WARN Trust Level 0 safety verification incomplete for `as_ptr_nonnull_requires_sysroot_container::lie`: 3 obligation(s) were not proved
    //[memsafe]~^^^^ ERROR Trust memory-safe verification failed for `as_ptr_nonnull_requires_sysroot_container::lie`: at least one result is not an authenticated memory-safe assumption
    let q = p.as_ptr();
    strlen(q as *const c_char)
}

/// The same, whose generic argument spells `alloc::vec`.
pub fn lie_vec(p: *const [Vec<u8>]) -> usize {
    //[default,certify]~^ ERROR Trust Level 0 safety verification incomplete for `as_ptr_nonnull_requires_sysroot_container::lie_vec`: 3 obligation(s) were not proved
    //[default,certify]~^^ ERROR Trust strict verification failed for `as_ptr_nonnull_requires_sysroot_container::lie_vec`: 3 obligation(s) were not fully verified
    //[memsafe]~^^^ WARN Trust Level 0 safety verification incomplete for `as_ptr_nonnull_requires_sysroot_container::lie_vec`: 3 obligation(s) were not proved
    //[memsafe]~^^^^ ERROR Trust memory-safe verification failed for `as_ptr_nonnull_requires_sysroot_container::lie_vec`: at least one result is not an authenticated memory-safe assumption
    let q = p.as_ptr();
    strlen(q as *const c_char)
}

/// The same over `*const [u8]`: no container substring, refused before and after.
pub fn twin(p: *const [u8]) -> usize {
    //[default,certify]~^ ERROR Trust Level 0 safety verification incomplete for `as_ptr_nonnull_requires_sysroot_container::twin`: 3 obligation(s) were not proved
    //[default,certify]~^^ ERROR Trust strict verification failed for `as_ptr_nonnull_requires_sysroot_container::twin`: 3 obligation(s) were not fully verified
    //[memsafe]~^^^ WARN Trust Level 0 safety verification incomplete for `as_ptr_nonnull_requires_sysroot_container::twin`: 3 obligation(s) were not proved
    //[memsafe]~^^^^ ERROR Trust memory-safe verification failed for `as_ptr_nonnull_requires_sysroot_container::twin`: at least one result is not an authenticated memory-safe assumption
    let q = p.as_ptr();
    strlen(q as *const c_char)
}

/// No `as_ptr` at all: the raw pointer goes straight to `strlen`.
pub fn control(p: *const VecDeque<u8>) -> usize {
    //[default,certify]~^ ERROR Trust Level 0 safety verification incomplete for `as_ptr_nonnull_requires_sysroot_container::control`: 2 obligation(s) were not proved
    //[default,certify]~^^ ERROR Trust strict verification failed for `as_ptr_nonnull_requires_sysroot_container::control`: 2 obligation(s) were not fully verified
    //[memsafe]~^^^ WARN Trust Level 0 safety verification incomplete for `as_ptr_nonnull_requires_sysroot_container::control`: 2 obligation(s) were not proved
    //[memsafe]~^^^^ ERROR Trust memory-safe verification failed for `as_ptr_nonnull_requires_sysroot_container::control`: at least one result is not an authenticated memory-safe assumption
    strlen(p as *const c_char)
}

// std's container accessors keep the non-null fact (`SliceAsPtr`, `VecAsPtr`,
// `StrAsPtr`, `CStrAsPtr`): their `parameter 0 must be non-null` row stays proved.
// RE-PINNED 2026-10-15 (the merge of 2026-10-14), `default`: each is still refused, now
// with "strict verification failed" in place of the advisory warning, because the
// `strlen` call's hardened unsafe-operation row fails closed as FAILED ("unproved, no
// counterexample") on the merged tree and a FAILED row is never reported as advisory.
pub fn std_slice(s: &[u8]) -> usize {
    //[default,certify]~^ ERROR Trust Level 0 safety verification incomplete for `as_ptr_nonnull_requires_sysroot_container::std_slice`: 1 obligation(s) were not proved
    //[default]~^^ ERROR Trust strict verification failed for `as_ptr_nonnull_requires_sysroot_container::std_slice`: 1 obligation(s) were not fully verified
    //[certify]~^^^ ERROR Trust strict verification failed for `as_ptr_nonnull_requires_sysroot_container::std_slice`: 1 obligation(s) were not fully verified
    //[memsafe]~^^^^ WARN Trust Level 0 safety verification incomplete for `as_ptr_nonnull_requires_sysroot_container::std_slice`: 1 obligation(s) were not proved
    //[memsafe]~^^^^^ ERROR Trust memory-safe verification failed for `as_ptr_nonnull_requires_sysroot_container::std_slice`: at least one result is not an authenticated memory-safe assumption
    strlen(s.as_ptr() as *const c_char)
}

pub fn std_vec(v: &Vec<u8>) -> usize {
    //[default,certify]~^ ERROR Trust Level 0 safety verification incomplete for `as_ptr_nonnull_requires_sysroot_container::std_vec`: 2 obligation(s) were not proved
    //[default]~^^ ERROR Trust strict verification failed for `as_ptr_nonnull_requires_sysroot_container::std_vec`: 2 obligation(s) were not fully verified
    //[certify]~^^^ ERROR Trust strict verification failed for `as_ptr_nonnull_requires_sysroot_container::std_vec`: 2 obligation(s) were not fully verified
    //[memsafe]~^^^^ WARN Trust Level 0 safety verification incomplete for `as_ptr_nonnull_requires_sysroot_container::std_vec`: 2 obligation(s) were not proved
    //[memsafe]~^^^^^ ERROR Trust memory-safe verification failed for `as_ptr_nonnull_requires_sysroot_container::std_vec`: at least one result is not an authenticated memory-safe assumption
    strlen(v.as_ptr() as *const c_char)
}

pub fn std_str(s: &str) -> usize {
    //[default,certify]~^ ERROR Trust Level 0 safety verification incomplete for `as_ptr_nonnull_requires_sysroot_container::std_str`: 1 obligation(s) were not proved
    //[default]~^^ ERROR Trust strict verification failed for `as_ptr_nonnull_requires_sysroot_container::std_str`: 1 obligation(s) were not fully verified
    //[certify]~^^^ ERROR Trust strict verification failed for `as_ptr_nonnull_requires_sysroot_container::std_str`: 1 obligation(s) were not fully verified
    //[memsafe]~^^^^ WARN Trust Level 0 safety verification incomplete for `as_ptr_nonnull_requires_sysroot_container::std_str`: 1 obligation(s) were not proved
    //[memsafe]~^^^^^ ERROR Trust memory-safe verification failed for `as_ptr_nonnull_requires_sysroot_container::std_str`: at least one result is not an authenticated memory-safe assumption
    strlen(s.as_ptr() as *const c_char)
}

pub fn std_cstr(s: &CStr) -> usize {
    //[default,certify]~^ ERROR Trust Level 0 safety verification incomplete for `as_ptr_nonnull_requires_sysroot_container::std_cstr`: 2 obligation(s) were not proved
    //[default]~^^ ERROR Trust strict verification failed for `as_ptr_nonnull_requires_sysroot_container::std_cstr`: 2 obligation(s) were not fully verified
    //[certify]~^^^ ERROR Trust strict verification failed for `as_ptr_nonnull_requires_sysroot_container::std_cstr`: 2 obligation(s) were not fully verified
    //[memsafe]~^^^^ WARN Trust Level 0 safety verification incomplete for `as_ptr_nonnull_requires_sysroot_container::std_cstr`: 2 obligation(s) were not proved
    //[memsafe]~^^^^^ ERROR Trust memory-safe verification failed for `as_ptr_nonnull_requires_sysroot_container::std_cstr`: at least one result is not an authenticated memory-safe assumption
    strlen(s.as_ptr())
}
