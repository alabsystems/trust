//@ needs-trust-verify
//@ only-macos
//@ edition: 2024
//@ compile-flags: -Ztrust-verify=on -Coverflow-checks=on --crate-type lib
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ rustc-env:TRUST_NO_SYSROOT_CENSUS=1
//! FFI-CALL-DEST-STORAGE-1 (2026-11-01): a call's whole-local destination of an exactly
//! sized type is initialized storage on the call's return edge, so a `&raw const` of it
//! has that many bytes of extent (`trust_vcgen` `generate::ffi_buffer_extent::after_call`;
//! docs/DECISION_QUEUE.md, under FFI-SCALAR-LIBC-1). The vcgen lane on the same shapes'
//! extracted MIR is `generate/ffi_buffer_extent_tests.rs`.
//!
//! Before: the `write` capacity row (`parameter 2 byte count must fit parameter 1
//! available byte extent`) of each function below was UNKNOWN, because a call result
//! never seeded storage. On the strict `targo trust check` lane that row was the only
//! failing row of the agy-alab and claude-code-alab self-pipe signal handlers. Now it is
//! PROVED in `sig_byte` and `sig_word`; the two negative controls keep it UNKNOWN: two
//! bytes from a one-byte result, and a tuple result the extent lane does not size.
//! Every function also keeps the runtime-checked panic-freedom row of the `write` call
//! itself (a foreign callee with no body in the bundle), which is outside this change
//! and which this raw strict run holds fail-closed in an unsafe-using function. The
//! per-function counts below pin all four.

#![feature(rustc_private)]

extern crate libc;

use core::ffi::c_int;

/// The self-pipe signal handler shape: one byte, the result of a call, written whole:
/// the capacity row proves.
pub fn sig_byte(fd: c_int, sig: c_int) -> isize {
    //~^ NOTE Trust verification: 1 proved, 0 failed, 0 unknown, 0 timed out, 1 runtime-checked, 1 skipped out of 3 obligation(s)
    //~^^ WARN Trust Level 0 safety verification incomplete for `ffi_write_call_result_extent::sig_byte`: 1 obligation(s) were not proved
    //~^^^ ERROR Trust strict verification failed for `ffi_write_call_result_extent::sig_byte`: 2 obligation(s) were not fully verified
    let byte = u8::try_from(sig).unwrap_or(0);
    // SAFETY: one byte on this frame.
    unsafe { libc::write(fd, (&raw const byte).cast(), 1) }
}

/// A four-byte call result written whole: the capacity row proves.
pub fn sig_word(fd: c_int, sig: c_int) -> isize {
    //~^ NOTE Trust verification: 1 proved, 0 failed, 0 unknown, 0 timed out, 1 runtime-checked, 1 skipped out of 3 obligation(s)
    //~^^ WARN Trust Level 0 safety verification incomplete for `ffi_write_call_result_extent::sig_word`: 1 obligation(s) were not proved
    //~^^^ ERROR Trust strict verification failed for `ffi_write_call_result_extent::sig_word`: 2 obligation(s) were not fully verified
    let word = u32::try_from(sig).unwrap_or(0);
    // SAFETY: four bytes on this frame.
    unsafe { libc::write(fd, (&raw const word).cast(), 4) }
}

/// Two bytes from a one-byte call result: the row stays.
pub fn sig_byte_two(fd: c_int, sig: c_int) -> isize {
    //~^ NOTE Trust verification: 0 proved, 0 failed, 1 unknown, 0 timed out, 1 runtime-checked, 1 skipped out of 3 obligation(s)
    //~^^ ERROR Trust Level 0 safety verification incomplete for `ffi_write_call_result_extent::sig_byte_two`: 2 obligation(s) were not proved
    //~^^^ ERROR Trust strict verification failed for `ffi_write_call_result_extent::sig_byte_two`: 2 obligation(s) were not fully verified
    let byte = u8::try_from(sig).unwrap_or(0);
    // SAFETY: deliberately over-long (negative control).
    unsafe { libc::write(fd, (&raw const byte).cast(), 2) }
}

#[inline(never)]
fn pair(sig: c_int) -> (u32, u32) {
    (sig as u32, 0)
}

/// A tuple result the extent lane does not size: the row stays.
pub fn sig_pair(fd: c_int, sig: c_int) -> isize {
    //~^ NOTE Trust verification: 0 proved, 0 failed, 1 unknown, 0 timed out, 1 runtime-checked, 1 skipped out of 3 obligation(s)
    //~^^ ERROR Trust Level 0 safety verification incomplete for `ffi_write_call_result_extent::sig_pair`: 2 obligation(s) were not proved
    //~^^^ ERROR Trust strict verification failed for `ffi_write_call_result_extent::sig_pair`: 2 obligation(s) were not fully verified
    let p = pair(sig);
    // SAFETY: deliberately unsized for the lane (negative control).
    unsafe { libc::write(fd, (&raw const p).cast(), 8) }
}
