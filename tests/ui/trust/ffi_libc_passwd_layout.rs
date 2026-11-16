//@ needs-trust-verify
//@ only-macos
//@ edition: 2024
//@ aux-crate: libc=g1_libc_passwd_layout/libc.rs
//@ compile-flags: -Ztrust-verify=on -Coverflow-checks=on --crate-type lib
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ rustc-env:TRUST_NO_SYSROOT_CENSUS=1
//! REVIEW-A4C4-MINORS-1 fix-forward (2026-11-07): `getpwuid`'s return contract
//! (`trust_vcgen::ffi_pointer_contract`) is for Darwin's `struct passwd`, and the member
//! list the extractor shows cannot reveal a `repr`. So the contract requires rustc's
//! computed layout of the declaration to be the C object's (72 bytes, 8-aligned, the
//! members at their `<pwd.h>` offsets). The verifying extractor never fills
//! `Ty::Adt::layout`; the compiler hands the layout over for the call's block
//! (`trust_verify.rs` `foreign_return_pointee_layouts`). The first cut checked a layout
//! only when the model carried one, which on this lane is never.
//!
//! The dependency named `libc` (`auxiliary/g1_libc_passwd_layout/libc.rs`) declares the
//! same ten members twice: `honest::passwd` under `#[repr(C)]`, and
//! `over_aligned::passwd` under `#[repr(C, align(16))]` (80 bytes). Each function reads
//! the whole struct through a null-checked `getpwuid` result, before any other call.
//!
//! * `honest_whole` is the positive control: the contract applies (the null row proves,
//!   and the allocation-validity row and rustc's null and alignment asserts are
//!   dropped), exactly as for the sysroot `libc`'s `passwd_dir_is_null` in
//!   `ffi_libc_return_contract.rs`. Its unknown row is the `getpwuid` call itself
//!   (`unmodeled FFI call`), outside this change.
//! * `over_aligned_whole` reads 80 bytes from the 72-byte object. Before this fix the
//!   contract applied to it too (measured on a stage 1 of the first cut: "2 proved, 0
//!   failed, 2 unknown, ... 2 skipped out of 6", the allocation-validity row dropped and
//!   only the `CheckAlignment` assert left unknown). Now it lends nothing, and the
//!   function keeps every row of an uncontracted pointer: the null, allocation-validity
//!   and alignment rows fail, and both of rustc's asserts are unknown.
//!
//! The per-function counts below pin both.

extern crate libc;

pub fn honest_whole(uid: u32) -> bool {
    //~^ NOTE Trust verification: 2 proved, 0 failed, 1 unknown, 0 timed out, 0 runtime-checked, 2 skipped out of 5 obligation(s)
    //~| ERROR Trust Level 0 safety verification incomplete for `ffi_libc_passwd_layout::honest_whole`: 1 obligation(s) were not proved
    //~| ERROR Trust strict verification failed for `ffi_libc_passwd_layout::honest_whole`: 2 obligation(s) were not fully verified
    // SAFETY: static storage or null, read before any other call.
    unsafe {
        let pw = libc::honest::getpwuid(uid);
        if pw.is_null() {
            return true;
        }
        let whole = *pw;
        whole.pw_dir.is_null()
    }
}

pub fn over_aligned_whole(uid: u32) -> bool {
    //~^ NOTE Trust verification: 1 proved, 3 failed, 3 unknown, 0 timed out, 0 runtime-checked, 2 skipped out of 9 obligation(s)
    //~| ERROR Trust Level 0 safety verification incomplete for `ffi_libc_passwd_layout::over_aligned_whole`: 6 obligation(s) were not proved
    //~| ERROR Trust strict verification failed for `ffi_libc_passwd_layout::over_aligned_whole`: 6 obligation(s) were not fully verified
    // SAFETY: deliberately over-aligned declaration (negative control).
    unsafe {
        let pw = libc::over_aligned::getpwuid(uid);
        if pw.is_null() {
            return true;
        }
        let whole = *pw;
        whole.pw_dir.is_null()
    }
}
