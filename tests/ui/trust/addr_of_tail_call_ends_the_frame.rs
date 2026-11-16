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
//! REVIEW-A4C4-MINORS-1 (2026-11-02, 2026-11-07): a `become` tail call ENDS the caller's
//! frame before the callee runs, so the address of any caller local — an ARGUMENT
//! included — dangles in the callee. The `[unsafe:sep:addr_of] … (source liveness
//! unverified)` row of a pointer passed to `become` must stay
//! (`trust_vcgen::sep_engine::call_arg_confined_addr_of_locals`; docs/DECISION_QUEUE.md
//! "REVIEW-A4C4-MINORS-1").
//!
//! The generation entry hands the sep engine the tail-call PROJECTION
//! (`VerifiableFunction::with_tail_calls_expanded`), in which `become take(..)` is an
//! ordinary `_0 = take(..) -> bbN; bbN: return`: the shape of `caller_ordinary`'s
//! `take(..)`. So the straight-run confinement (G1, 2026-10-27; see
//! `addr_of_straight_run_storage_markers.rs`) credited the tail call as an in-frame use
//! and discharged the row of `caller` (the pointer taken one call, `mk()`, before the
//! tail call; `n` is an argument, so the run crosses `mk()`'s block) and of
//! `caller_same_block`. Each function's only unsafe surface is that `&raw const n`, so
//! it compiles clean exactly when the row is (wrongly) discharged; the errors below are
//! that row, failed closed, in both revisions.
//!
//! `caller_ordinary` is the control: the same pointer passed to an ORDINARY call, during
//! which the caller's frame is live. Its row is discharged (it reports no obligations),
//! so it is not annotated; `caller` and `caller_same_block` differ from it only in
//! `become`.
//!
//! Measured on a stage 1 of this fix (2026-11-07, both revisions): each tail-call caller
//! has one obligation, "[unsafe:sep:addr_of] &raw const on `_2` (source liveness
//! unverified)", failed by `structural-unsafe-demand-finding`. Before it, on a stage 1
//! of the first cut (which changed only the `TailCall` arm, never reached in the
//! projection), this file failed with "ui test did not emit an error" in both revisions:
//! no function here reported a row.

#![feature(explicit_tail_calls)]
#![expect(incomplete_features)]

#[inline(never)]
fn mk() -> u32 {
    7
}

/// Ignores the pointer, so that its own body verifies (a `p as usize` read is an
/// unsupported opaque scalar today, which would make `take` itself an error). The
/// rows this file pins are the CALLER's: whether the caller's `&raw const n` is live
/// at its use, which does not depend on what the callee does with it.
#[inline(never)]
fn take(_p: *const u32, n: u32) -> u32 {
    n
}

/// The pointer is taken one call (`mk()`) before the tail call that takes it.
pub fn caller(_x: *const u32, n: u32) -> u32 {
    //~^ ERROR Trust Level 0 safety verification incomplete for `addr_of_tail_call_ends_the_frame::caller`: 1 obligation(s) were not proved
    //~| ERROR Trust strict verification failed for `addr_of_tail_call_ends_the_frame::caller`: 1 obligation(s) were not fully verified
    become take(&raw const n, mk())
}

/// The pointer is taken in the tail call's own block.
pub fn caller_same_block(_x: *const u32, n: u32) -> u32 {
    //~^ ERROR Trust Level 0 safety verification incomplete for `addr_of_tail_call_ends_the_frame::caller_same_block`: 1 obligation(s) were not proved
    //~| ERROR Trust strict verification failed for `addr_of_tail_call_ends_the_frame::caller_same_block`: 1 obligation(s) were not fully verified
    become take(&raw const n, 5)
}

/// Control: an ordinary call, during which `n`'s storage is live.
pub fn caller_ordinary(n: u32) -> u32 {
    take(&raw const n, mk())
}
