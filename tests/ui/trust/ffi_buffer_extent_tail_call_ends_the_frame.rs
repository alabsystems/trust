//@ needs-trust-verify
//@ edition: 2024
//@ revisions: o0 o1
//@ compile-flags: -Ztrust-verify=on -Coverflow-checks=on --crate-type lib
//@[o1] compile-flags: -Copt-level=1
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ rustc-env:TRUST_NO_SYSROOT_CENSUS=1
//! REVIEW-A4C4-MINORS-1 fix-forward (2026-11-07): a `become` ends the caller's frame
//! before the callee runs, so the FFI buffer-extent lane may not discharge a foreign
//! callee's "byte count must fit parameter 1 available byte extent" row with the extent
//! of storage in that frame (`trust_vcgen::generate::ffi_buffer_extent::call_facts`,
//! `BufferFacts::across_frame_end`; docs/DECISION_QUEUE.md "REVIEW-A4C4-MINORS-1").
//!
//! `write` is declared here, so the legacy `write` summary binds it by name with its
//! buffer contract (parameter 2 bytes from parameter 1); its prototype is the caller's,
//! as `become` requires. Each `*_become` function differs from its `*_call` control only
//! in `become`.
//!
//! * `array_become`: `b` is a local `[u8; 4]`, passed as `b.as_ptr() as *const c_void`.
//!   No `&raw`, so no `[unsafe:sep:addr_of]` row exists to keep the function failing:
//!   the extent row alone decides. Before this fix it was PROVED against `b`'s 4 bytes
//!   and the function had no error at all (measured on a stage 1 of the first cut, both
//!   revisions: "1 proved, ... 2 skipped out of 3"). Now the row is unknown.
//! * `param_become_cast`: `fd` is a parameter, passed as `(&raw const fd).cast()`. The
//!   `.cast()` call handed the pointer back past the addr_of confinement, so no addr_of
//!   row was minted, and the extent row was PROVED against `fd`'s 4 bytes (the same stage
//!   1: "1 proved, ... 1 runtime-checked, 2 skipped out of 4", no Level 0 error). Now the
//!   addr_of row is minted and fails, and the extent row is unknown.
//!
//! The controls make the same calls with the frame live: their extent rows prove, and
//! `param_call_cast`'s addr_of row stays confined (the sysroot `cast` is a link, not a
//! consumer), so neither has a Level 0 error. `array_call` has no error. The `cast`
//! functions keep the runtime-checked absent-callee panic row of `cast`, outside this
//! change, so both fail the strict lane.

#![feature(explicit_tail_calls)]
#![expect(incomplete_features)]

use core::ffi::{c_int, c_void};

unsafe extern "C" {
    fn write(fd: c_int, buf: *const c_void, n: usize) -> isize;
}

pub extern "C" fn array_become(fd: c_int, _b: *const c_void, _n: usize) -> isize {
    //~^ NOTE Trust verification: 0 proved, 0 failed, 1 unknown, 0 timed out, 0 runtime-checked, 2 skipped out of 3 obligation(s)
    //~| ERROR Trust Level 0 safety verification incomplete for `ffi_buffer_extent_tail_call_ends_the_frame::array_become`: 1 obligation(s) were not proved
    //~| ERROR Trust strict verification failed for `ffi_buffer_extent_tail_call_ends_the_frame::array_become`: 1 obligation(s) were not fully verified
    let b = [7u8; 4];
    // SAFETY: `b` is four initialized bytes (but not once this frame ends).
    unsafe { become write(fd, b.as_ptr() as *const c_void, 4) }
}

pub extern "C" fn array_call(fd: c_int, _b: *const c_void, _n: usize) -> isize {
    //~^ NOTE Trust verification: 1 proved, 0 failed, 0 unknown, 0 timed out, 0 runtime-checked, 2 skipped out of 3 obligation(s)
    let b = [7u8; 4];
    // SAFETY: `b` is four initialized bytes.
    unsafe { write(fd, b.as_ptr() as *const c_void, 4) }
}

pub extern "C" fn param_become_cast(fd: c_int, _b: *const c_void, _n: usize) -> isize {
    //~^ NOTE Trust verification: 0 proved, 1 failed, 1 unknown, 0 timed out, 1 runtime-checked, 2 skipped out of 5 obligation(s)
    //~| ERROR Trust Level 0 safety verification incomplete for `ffi_buffer_extent_tail_call_ends_the_frame::param_become_cast`: 3 obligation(s) were not proved
    //~| ERROR Trust strict verification failed for `ffi_buffer_extent_tail_call_ends_the_frame::param_become_cast`: 3 obligation(s) were not fully verified
    // SAFETY: `fd` is four initialized bytes (but not once this frame ends).
    unsafe { become write(fd, (&raw const fd).cast(), 4) }
}

pub extern "C" fn param_call_cast(fd: c_int, _b: *const c_void, _n: usize) -> isize {
    //~^ NOTE Trust verification: 1 proved, 0 failed, 0 unknown, 0 timed out, 1 runtime-checked, 2 skipped out of 4 obligation(s)
    //~| WARN Trust Level 0 safety verification incomplete for `ffi_buffer_extent_tail_call_ends_the_frame::param_call_cast`: 1 obligation(s) were not proved
    //~| ERROR Trust strict verification failed for `ffi_buffer_extent_tail_call_ends_the_frame::param_call_cast`: 2 obligation(s) were not fully verified
    // SAFETY: `fd` is four initialized bytes.
    unsafe { write(fd, (&raw const fd).cast(), 4) }
}
