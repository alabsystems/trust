//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
//~? RAW Trust
//@ forbid-output: memory copy side effects require explicit memory-model lowering
//! `copy_nonoverlapping` must reach the native lane as a MODELED memory effect,
//! never as a whole-function lowering abort.
//!
//! rustc's `LowerIntrinsics` pass rewrites `copy_nonoverlapping(src, dst, count)`
//! from a `Call` into `NonDivergingIntrinsic::CopyNonOverlapping` before Trust
//! sees a body, so the statement spelling is what every std body carries
//! (`ptr::read`, `MaybeUninit::assume_init`, `mem::replace`,
//! `RawVecInner::with_capacity_in`, `alloc::fmt::format`, …). The extractor used
//! to mark it `Unsupported`, which aborted the ENTIRE function's TrustIr
//! lowering with
//!
//!     failed to lower `…` into typed TrustIr NativeVerificationBundle input:
//!     unsupported operation: unsupported MIR statement
//!     NonDivergingIntrinsic::CopyNonOverlapping: memory copy side effects
//!     require explicit memory-model lowering
//!
//! poisoning every obligation in the body, not just the copy's own. What this
//! fixture pins is that that message is GONE — the copy now lowers into the
//! ordinary `GEP`/`Load`/`Store` model, so the rest of the function is verifiable
//! on its own merits.
//!
//! It is still `check-fail`, and deliberately so: the copy's UB preconditions
//! (both regions in bounds, and non-overlapping) are real obligations that these
//! raw pointers cannot discharge. Modeling the EFFECT must never be mistaken for
//! discharging the PRECONDITION — if this fixture ever starts passing, the
//! bounds/overlap obligations stopped being emitted and that is a fail-OPEN.

#![crate_type = "lib"]
#![feature(core_intrinsics)]
#![allow(internal_features)]

/// The pervasive `count == 1` shape — this is what `ptr::read` compiles to.
pub unsafe fn read_one(src: *const u32, dst: *mut u32) {
    unsafe { core::intrinsics::copy_nonoverlapping(src, dst, 1) }
}

/// A small constant count, unrolled element-wise.
pub unsafe fn copy_four(src: *const u8, dst: *mut u8) {
    unsafe { core::intrinsics::copy_nonoverlapping(src, dst, 4) }
}

/// A SYMBOLIC count must keep failing closed. Neither backend has a bulk
/// region-havoc primitive, and modeling fewer elements than are written would
/// let a later read of the destination return a stale value.
pub unsafe fn copy_n(src: *const u8, dst: *mut u8, n: usize) {
    unsafe { core::intrinsics::copy_nonoverlapping(src, dst, n) }
}
