//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ dont-require-annotations: HELP
//@ check-fail
//@ forbid-output: memory copy side effects require explicit memory-model lowering
//@ forbid-output: native typed-TrustIr lowering did not complete
//! THE FALSE-PROOF DETECTOR for the modeled `copy_nonoverlapping` statement —
//! the acceptance test demanded by the 810baa6c4c revert, which found that an
//! earlier version of this feature let exactly this body VERIFY SILENTLY: a
//! 64-byte copy into an 8-byte destination produced no Trust diagnostics at
//! all, because the extractor flip removed the fail-closed `Unsupported`
//! obligation while the sep engine's reachability gates never let the copy's
//! own bounds obligations be minted.
//!
//! What this fixture pins, and how each pin detects a regression:
//!
//!   * `check-fail` + the anchored ERROR: if verification of `tracked_oob`
//!     ever goes silent again, the compile succeeds and the annotation is
//!     unmatched — the test fails on both counts. The ERROR names the exact
//!     function path, so an unrelated failure elsewhere cannot satisfy it.
//!   * the anchored HELP (the `CopyBoundsViolation` agentic guidance, emitted
//!     only for that obligation kind): the failure must include a NOT-PROVED
//!     copy-bounds row for this copy — a `MalformedTrustIr` marker or any
//!     other stand-in obligation does NOT print this guidance. This closes the
//!     revert's misread ("1 obligation NOT PROVED" that was a malformed-IR
//!     marker, not a memory-safety row).
//!   * `forbid-output: native typed-TrustIr lowering did not complete`: the
//!     refutation must come from the minted obligation rows over the MODELED
//!     copy, not from a whole-function lowering abort. Failing closed here
//!     would also be "an error", but it is the wrong mechanism and would mask
//!     a broken obligation path the moment lowering starts succeeding.
//!   * `forbid-output: memory copy side effects …`: the extractor must emit
//!     the modeled statement, never the old `Unsupported` spelling, for a
//!     copy whose element type is determinable.
//!
//! The copy is 64 elements of `u8` — exactly the bridge's precise-unroll
//! budget, and exactly the revert's fixture — into an 8-byte stack array whose
//! size the sep engine tracks concretely (`Rvalue::Ref` on `[u8; 8]` records
//! an 8-byte allocation, carried through the unsize cast and `as_ptr`), so the
//! dst bounds obligation is the ground violation `0 + 64 > 8`.

#![crate_type = "lib"]
#![feature(core_intrinsics)]
#![allow(internal_features)]

pub unsafe fn tracked_oob() {
    //~^ ERROR Trust Level 0 safety verification incomplete for `copy_nonoverlapping_oob_refuted::tracked_oob`
    //~| HELP the element/byte count of `core::intrinsics::copy_nonoverlapping` must be provably
    let a = [0u8; 8];
    let mut b = [0u8; 8];
    // 64 bytes into an 8-byte destination: must REFUTE, never silently verify.
    unsafe { core::intrinsics::copy_nonoverlapping(a.as_ptr(), b.as_mut_ptr(), 64) };
}
