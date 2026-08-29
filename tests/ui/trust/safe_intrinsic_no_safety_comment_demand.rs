//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=certify --crate-type lib
//@ edition: 2021
//@ dont-check-compiler-stderr
//@ check-fail
#![feature(core_intrinsics)]
#![allow(internal_features)]
//! **A SAFE INTRINSIC IS NOT AN UNSAFE BLOCK.**
//!
//! # What was wrong
//!
//! `trust_vcgen`'s unsafe-block name fallback carried a bare `"intrinsics::"`
//! entry — a MODULE-path substring standing in for a function identity, the
//! same defect T5A had already deleted for `"::ffi::"`. Every call to a
//! `core::intrinsics::*` item was therefore treated as an unsafe block and
//! charged `[unsafe] missing SAFETY comment`, an obligation whose formula is
//! `Formula::Bool(true)`: a documentation lint that can never be discharged.
//!
//! `ctpop`, `ctlz`, `cttz`, `bswap`, `bitreverse`, `rotate_left`,
//! `wrapping_*`, `saturating_*`, `likely`/`unlikely` are all declared SAFE in
//! `library/core` — `unlikely`'s own doc comment says *"unlike most intrinsics,
//! this is safe to call; it does not require an `unsafe` block"* — and rustc
//! records that faithfully: measured, `ctpop` extracts as `is_unsafe_sig=false`
//! and `ctlz_nonzero` as `is_unsafe_sig=true`. The name fallback simply
//! disagreed with the authoritative signal.
//!
//! Measured on the `core::num` leaf slice: **21 of 43 failing obligations**, 30 %
//! of the whole histogram
//! (`docs/design/2026-08-20-core-slice-blocker-histogram.md` §2.1 row 1). With
//! the pre-fix stage2 `trustc`, `pub fn f(a: u32) -> u32 { intrinsics::ctpop(a) }`
//! compiled to `rc=1` with exactly one obligation: the lint.
//!
//! # What this fixture pins
//!
//! Under the STRICT `certify` policy, NO function below is charged
//! `[unsafe] missing SAFETY comment`. Measured at HEAD with `advisory`
//! substituted for `certify` so every row is visible: seven of the eight report
//! "function has no panic obligations (trivially panic-free)", and `rotl`
//! carries exactly one row — "[trust-absent-callee-assumption] call to absent
//! callee `core::intrinsics::rotate_left::<u32>` (body not in the lowered
//! bundle) may panic". That is a lowering gap, not the doc lint: of the eight,
//! `rotate_left` is the only callee whose body the diagnostic reports as absent
//! from the lowered bundle. It lands `runtime-checked`, and `certify` refuses
//! runtime-checked rows, so it is a build error and is pinned on `rotl` below.
//! Every other function stays silent, so a returning unsafe lint would surface
//! as an unannotated error and fail this test.
//!
//! The opposite direction — that a genuinely-`unsafe`
//! intrinsic (`transmute`, `unchecked_shl`, `ctlz_nonzero`, `copy`, `assume`,
//! …) is STILL charged, and still opens the separation-engine gate — is pinned
//! unit-level by `trust_vcgen::generate::safe_intrinsic_lint_tests`, in both
//! directions and over the whole transcribed leaf set.

use core::intrinsics;

pub fn count_ones(a: u32) -> u32 {
    intrinsics::ctpop(a)
}

pub fn leading_zeros(a: u32) -> u32 {
    intrinsics::ctlz(a)
}

pub fn trailing_zeros(a: u32) -> u32 {
    intrinsics::cttz(a)
}

pub fn swap_bytes(a: u32) -> u32 {
    intrinsics::bswap(a)
}

pub fn reverse_bits(a: u32) -> u32 {
    intrinsics::bitreverse(a)
}

pub fn rotl(a: u32, b: u32) -> u32 {
    //~^ ERROR Trust Level 0 safety verification incomplete for `safe_intrinsic_no_safety_comment_demand::rotl`
    //~| ERROR Trust strict verification failed for `safe_intrinsic_no_safety_comment_demand::rotl`
    intrinsics::rotate_left(a, b)
}

pub fn saturating(a: u32, b: u32) -> u32 {
    intrinsics::saturating_add(a, b)
}

pub fn hinted(c: bool) -> bool {
    intrinsics::likely(c)
}
