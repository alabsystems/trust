//@ needs-trust-verify
//@ only-macos
//@ edition: 2024
//@ revisions: o0 o1
//@ compile-flags: -Ztrust-verify=on -Coverflow-checks=on --crate-type lib
//@[o1] compile-flags: -Copt-level=1
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ rustc-env:TRUST_NO_SYSROOT_CENSUS=1
//! G1 (2026-10-27): the `[unsafe:sep:addr_of] … (source liveness unverified)` row of a
//! `&raw` pointer defined one call before the call that takes it, discharged by the
//! straight-run confinement (`trust_vcgen::sep_engine::call_arg_confined_addr_of_locals`;
//! docs/DECISION_QUEUE.md "G1-FFI-UNSAFE-BOUNDARY" item 4). This is the
//! `pthread_sigmask(how, &raw const set, null_mut())` lowering: `null_mut()` is a call,
//! so the `&raw const` is taken one block before the call that consumes it.
//!
//! The run past the defining block needs the source's storage markers. At
//! `-Copt-level=0` (revision `o0`) rustc's `RemoveStorageMarkers` deletes every
//! `StorageLive`/`StorageDead` before `TrustVerify`, so a scope end on the run would be
//! invisible, and the row stays for a non-argument source. At `-Copt-level=1` (revision
//! `o1`) the markers survive: `unblock`'s row is discharged and `unblock_after_dead`,
//! whose source's scope ends before the call, keeps it. An argument's storage is the
//! whole frame, so `unblock_arg` is discharged in both revisions.
//!
//! G1 review finding 3 (2026-10-27): a MOVE out of the source also ends it. In
//! `dropped_by_call_then_used` the run's intermediate call `drop(s)` frees `s`'s heap
//! buffer while `s`'s storage stays live (its `StorageDead` comes after the use), and in
//! `moved_then_used` the non-`Copy` `Buf` is moved into `sink_buf`. Both keep the row in
//! both revisions (at `-O1` the move is visible as `move _2` on the run; the first G1
//! build discharged both there). `copied_then_used` is the positive control: a `Copy`
//! array passed by value is copied, `s` still holds its value, and at `-O1` the row is
//! discharged.
//!
//! Every function also keeps the FFI lane's `unmodeled FFI call` rows for the libc calls
//! (G3's group); the per-function counts below include them. That row is an L0
//! `FfiBoundary` fail-close, not an L1 design mandate (G3-MANDATE-L1-ONLY-1), so it draws
//! no advisory. `unblock_arg`, whose only unproved row it is, fails the strict lane in both
//! revisions (combined G1+G3 landing, 2026-11-01; before G3 it was pinned as an advisory).

#![feature(rustc_private)]

extern crate libc;

use core::ffi::c_int;

unsafe extern "C" {
    fn take_ptr(p: *const [u8; 32]);
}

/// `&raw const set` defined one call before the call that takes it.
pub fn unblock(sig: c_int) {
    //[o0]~^ NOTE Trust verification: 0 proved, 1 failed, 2 unknown, 0 timed out, 0 runtime-checked, 1 skipped out of 4 obligation(s)
    //[o0]~^^ ERROR Trust Level 0 safety verification incomplete for `addr_of_straight_run_storage_markers::unblock`: 3 obligation(s) were not proved
    //[o0]~^^^ ERROR Trust strict verification failed for `addr_of_straight_run_storage_markers::unblock`: 3 obligation(s) were not fully verified
    //[o1]~^^^^ NOTE Trust verification: 0 proved, 0 failed, 2 unknown, 0 timed out, 0 runtime-checked, 1 skipped out of 3 obligation(s)
    //[o1]~^^^^^ ERROR Trust Level 0 safety verification incomplete for `addr_of_straight_run_storage_markers::unblock`: 2 obligation(s) were not proved
    //[o1]~^^^^^^ ERROR Trust strict verification failed for `addr_of_straight_run_storage_markers::unblock`: 2 obligation(s) were not fully verified
    let mut set: libc::sigset_t = 0;
    // SAFETY: `set` is writable storage for a signal set.
    unsafe {
        libc::sigaddset(&raw mut set, sig);
        libc::pthread_sigmask(libc::SIG_UNBLOCK, &raw const set, core::ptr::null_mut());
    }
}

/// The pointer outlives its source's scope: the source-liveness row stays.
pub fn unblock_after_dead(sig: c_int) {
    //[o0]~^ NOTE Trust verification: 0 proved, 1 failed, 2 unknown, 0 timed out, 0 runtime-checked, 2 skipped out of 5 obligation(s)
    //[o0]~^^ ERROR Trust Level 0 safety verification incomplete for `addr_of_straight_run_storage_markers::unblock_after_dead`: 3 obligation(s) were not proved
    //[o0]~^^^ ERROR Trust strict verification failed for `addr_of_straight_run_storage_markers::unblock_after_dead`: 3 obligation(s) were not fully verified
    //[o1]~^^^^ NOTE Trust verification: 0 proved, 1 failed, 2 unknown, 0 timed out, 0 runtime-checked, 2 skipped out of 5 obligation(s)
    //[o1]~^^^^^ ERROR Trust Level 0 safety verification incomplete for `addr_of_straight_run_storage_markers::unblock_after_dead`: 3 obligation(s) were not proved
    //[o1]~^^^^^^ ERROR Trust strict verification failed for `addr_of_straight_run_storage_markers::unblock_after_dead`: 3 obligation(s) were not fully verified
    let p;
    {
        let mut set: libc::sigset_t = 0;
        // SAFETY: `set` is writable storage for a signal set.
        unsafe { libc::sigaddset(&raw mut set, sig) };
        p = &raw const set;
    }
    // SAFETY: deliberately dangling (negative control).
    unsafe { libc::pthread_sigmask(libc::SIG_UNBLOCK, p, core::ptr::null_mut()) };
}

/// The source is an argument, whose storage is the whole frame.
pub fn unblock_arg(set: libc::sigset_t) {
    //[o0]~^ NOTE Trust verification: 0 proved, 0 failed, 1 unknown, 0 timed out, 0 runtime-checked, 1 skipped out of 2 obligation(s)
    //[o0]~^^ ERROR Trust Level 0 safety verification incomplete for `addr_of_straight_run_storage_markers::unblock_arg`: 1 obligation(s) were not proved
    //[o0]~^^^ ERROR Trust strict verification failed for `addr_of_straight_run_storage_markers::unblock_arg`: 1 obligation(s) were not fully verified
    //[o1]~^^^^ NOTE Trust verification: 0 proved, 0 failed, 1 unknown, 0 timed out, 0 runtime-checked, 1 skipped out of 2 obligation(s)
    //[o1]~^^^^^ ERROR Trust Level 0 safety verification incomplete for `addr_of_straight_run_storage_markers::unblock_arg`: 1 obligation(s) were not proved
    //[o1]~^^^^^^ ERROR Trust strict verification failed for `addr_of_straight_run_storage_markers::unblock_arg`: 1 obligation(s) were not fully verified
    // SAFETY: `set` is this frame's argument.
    unsafe { libc::pthread_sigmask(libc::SIG_UNBLOCK, &raw const set, core::ptr::null_mut()) };
}

#[inline(never)]
pub fn sink(v: [u8; 32]) -> u8 {
    //[o0]~^ NOTE Trust verification: 1 proved, 0 failed, 0 unknown, 0 timed out, 0 runtime-checked out of 1 obligation(s)
    //[o1]~^^ NOTE Trust verification: 1 proved, 0 failed, 0 unknown, 0 timed out, 0 runtime-checked out of 1 obligation(s)
    v[0]
}

/// Positive control: `[u8; 32]` is `Copy`, so `sink(s)` passes a COPY (`_4 = copy _2;
/// sink(move _4)`) and `s` still holds its value at the use. At `-O1` the row is
/// discharged; at `-O0` the run does not extend (no storage markers) and it stays.
pub fn copied_then_used(b: u8) -> u8 {
    //[o0]~^ NOTE Trust verification: 0 proved, 1 failed, 1 unknown, 0 timed out, 0 runtime-checked, 2 skipped out of 4 obligation(s)
    //[o0]~^^ ERROR Trust Level 0 safety verification incomplete for `addr_of_straight_run_storage_markers::copied_then_used`: 2 obligation(s) were not proved
    //[o0]~^^^ ERROR Trust strict verification failed for `addr_of_straight_run_storage_markers::copied_then_used`: 2 obligation(s) were not fully verified
    //[o1]~^^^^ NOTE Trust verification: 0 proved, 0 failed, 1 unknown, 0 timed out, 0 runtime-checked, 2 skipped out of 3 obligation(s)
    //[o1]~^^^^^ ERROR Trust Level 0 safety verification incomplete for `addr_of_straight_run_storage_markers::copied_then_used`: 1 obligation(s) were not proved
    //[o1]~^^^^^^ ERROR Trust strict verification failed for `addr_of_straight_run_storage_markers::copied_then_used`: 1 obligation(s) were not fully verified
    let s = [b; 32];
    let p = &raw const s;
    let r = sink(s);
    // SAFETY: `s` is live and unchanged at the use.
    unsafe { take_ptr(p) };
    r
}

pub struct Buf(pub [u8; 32]);

#[inline(never)]
pub fn sink_buf(v: Buf) -> u8 {
    //[o0]~^ NOTE Trust verification: 1 proved, 0 failed, 0 unknown, 0 timed out, 0 runtime-checked out of 1 obligation(s)
    //[o1]~^^ NOTE Trust verification: 1 proved, 0 failed, 0 unknown, 0 timed out, 0 runtime-checked out of 1 obligation(s)
    v.0[0]
}

/// The source is MOVED into a call on the run (`sink_buf(move _2)`; `Buf` is not
/// `Copy`) before the pointer's use: the row stays in both revisions.
pub fn moved_then_used(b: u8) -> u8 {
    //[o0]~^ NOTE Trust verification: 0 proved, 1 failed, 1 unknown, 0 timed out, 0 runtime-checked, 2 skipped out of 4 obligation(s)
    //[o0]~^^ ERROR Trust Level 0 safety verification incomplete for `addr_of_straight_run_storage_markers::moved_then_used`: 2 obligation(s) were not proved
    //[o0]~^^^ ERROR Trust strict verification failed for `addr_of_straight_run_storage_markers::moved_then_used`: 2 obligation(s) were not fully verified
    //[o1]~^^^^ NOTE Trust verification: 0 proved, 1 failed, 1 unknown, 0 timed out, 0 runtime-checked, 2 skipped out of 4 obligation(s)
    //[o1]~^^^^^ ERROR Trust Level 0 safety verification incomplete for `addr_of_straight_run_storage_markers::moved_then_used`: 2 obligation(s) were not proved
    //[o1]~^^^^^^ ERROR Trust strict verification failed for `addr_of_straight_run_storage_markers::moved_then_used`: 2 obligation(s) were not fully verified
    let s = Buf([b; 32]);
    let p = &raw const s;
    let r = sink_buf(s);
    // SAFETY: deliberately after a move of the source (negative control).
    unsafe { take_ptr(p as *const [u8; 32]) };
    r
}

pub struct Owned(pub Vec<u8>);

/// The source is dropped by a call on the run before the pointer's use: the row stays.
pub fn dropped_by_call_then_used(v: Vec<u8>) {
    //[o0]~^ NOTE Trust verification: 0 proved, 1 failed, 1 unknown, 0 timed out, 1 runtime-checked, 2 skipped out of 5 obligation(s)
    //[o0]~^^ ERROR Trust Level 0 safety verification incomplete for `addr_of_straight_run_storage_markers::dropped_by_call_then_used`: 3 obligation(s) were not proved
    //[o0]~^^^ ERROR Trust strict verification failed for `addr_of_straight_run_storage_markers::dropped_by_call_then_used`: 3 obligation(s) were not fully verified
    //[o1]~^^^^ NOTE Trust verification: 0 proved, 1 failed, 1 unknown, 0 timed out, 1 runtime-checked, 2 skipped out of 5 obligation(s)
    //[o1]~^^^^^ ERROR Trust Level 0 safety verification incomplete for `addr_of_straight_run_storage_markers::dropped_by_call_then_used`: 3 obligation(s) were not proved
    //[o1]~^^^^^^ ERROR Trust strict verification failed for `addr_of_straight_run_storage_markers::dropped_by_call_then_used`: 3 obligation(s) were not fully verified
    let s = Owned(v);
    let p = &raw const s;
    core::mem::drop(s);
    // SAFETY: deliberately after the source was dropped (negative control).
    unsafe { take_ptr(p as *const [u8; 32]) };
}
