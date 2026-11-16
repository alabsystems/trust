//@ needs-trust-verify
//@ edition: 2024
//@ compile-flags: -Ztrust-verify=on -Coverflow-checks=on --crate-type lib
//@ check-fail
//@ dont-check-compiler-stderr
//! FFI-BUFFER-CAPACITY-1: a SAFETY comment does not discharge the real byte
//! capacity demand. Historically only non-nullness was modeled, so both over-long
//! spellings below were accepted on the disclosed assumption and could overrun a
//! 64-byte stack array (the original review measured exit 139 with 8192 input bytes).
//! Keep that assumption disclosure and the bare-call refusal, and additionally
//! require the over-long count to be refused in both cast spellings. Valid and
//! zero-byte array calls retain their existing assumption-bearing posture.
//! These new diagnostics require compiled qualification; source review is no PASS.

use core::ffi::{c_int, c_void};

unsafe extern "C" {
    fn read(fd: c_int, buf: *mut c_void, n: usize) -> isize;
}

/// Over-long count, `.cast()` spelling: refused despite the comment.
pub fn cast_read_commented(fd: c_int) -> isize {
    //~^ ERROR Trust Level 0 safety verification incomplete for `ffi_nonnull_cast_buffer_capacity_assumed::cast_read_commented`: 1 obligation(s) were not proved
    //~^^ ERROR Trust strict verification failed for `ffi_nonnull_cast_buffer_capacity_assumed::cast_read_commented`: 1 obligation(s) were not fully verified
    //~^^^ WARN Trust verification advisory for `ffi_nonnull_cast_buffer_capacity_assumed::cast_read_commented`: an unsafe block is ASSUMED sound on its `// SAFETY:` comment, not proved
    let mut buf = [0u8; 64];
    // SAFETY: `buf` is a live, writable stack array.
    unsafe { read(fd, buf.as_mut_ptr().cast(), 4096) }
}

/// The same call with no SAFETY comment: refused.
pub fn cast_read_bare(fd: c_int) -> isize {
    //~^ ERROR Trust Level 0 safety verification incomplete for `ffi_nonnull_cast_buffer_capacity_assumed::cast_read_bare`: 2 obligation(s) were not proved
    //~^^ ERROR Trust strict verification failed for `ffi_nonnull_cast_buffer_capacity_assumed::cast_read_bare`: 2 obligation(s) were not fully verified
    let mut buf = [0u8; 64];
    unsafe { read(fd, buf.as_mut_ptr().cast(), 4096) }
}

/// The `as` twin keeps the same capacity refusal and assumption disclosure.
pub fn as_read_commented(fd: c_int) -> isize {
    //~^ ERROR Trust Level 0 safety verification incomplete for `ffi_nonnull_cast_buffer_capacity_assumed::as_read_commented`: 1 obligation(s) were not proved
    //~^^ ERROR Trust strict verification failed for `ffi_nonnull_cast_buffer_capacity_assumed::as_read_commented`: 1 obligation(s) were not fully verified
    //~^^^ WARN Trust verification advisory for `ffi_nonnull_cast_buffer_capacity_assumed::as_read_commented`: an unsafe block is ASSUMED sound on its `// SAFETY:` comment, not proved
    let mut buf = [0u8; 64];
    // SAFETY: `buf` is a live, writable stack array.
    unsafe { read(fd, buf.as_mut_ptr() as *mut c_void, 4096) }
}

/// Correct count: the extent fact must discharge the new capacity demand.
pub fn cast_read_fits(fd: c_int) -> isize {
    //~^ WARN Trust verification advisory for `ffi_nonnull_cast_buffer_capacity_assumed::cast_read_fits`: an unsafe block is ASSUMED sound on its `// SAFETY:` comment, not proved
    let mut buf = [0u8; 64];
    // SAFETY: the live writable array contains the requested bytes.
    unsafe { read(fd, buf.as_mut_ptr().cast(), buf.len()) }
}

/// Zero count has no capacity requirement, including an empty backing array.
pub fn cast_read_empty(fd: c_int) -> isize {
    //~^ WARN Trust verification advisory for `ffi_nonnull_cast_buffer_capacity_assumed::cast_read_empty`: an unsafe block is ASSUMED sound on its `// SAFETY:` comment, not proved
    let mut buf = [0u8; 0];
    // SAFETY: the non-null dangling pointer is never dereferenced.
    unsafe { read(fd, buf.as_mut_ptr().cast(), 0) }
}
