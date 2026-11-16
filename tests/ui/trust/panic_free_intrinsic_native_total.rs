//@ edition: 2021
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=certify --crate-type lib
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//! **std-call-summaries P2: the nondeterministic and fallback-bodied float
//! intrinsics are PANIC-FREE in the native lane.**
//!
//! rustc's extractor stamps a direct call to one of the listed `core` intrinsics
//! (`trust_types::PANIC_FREE_RUSTC_INTRINSICS`) with
//! `@trust-rustc-panic-free-intrinsic::` only after `TyCtxt` shows a genuine
//! `#[rustc_intrinsic]` of the real `core`, `#[rustc_nounwind]`, a safe
//! signature and, for the fallback-bodied `minimum*`/`maximum*` selections, a
//! fallback body pinned panic-free (`tcx_marked_panic_free_intrinsic_path`).
//! Before P2 these calls took the absent-callee arm and charged an
//! undischargeable `[trust-absent-callee-assumption] … may panic` row (29 rows
//! in the 2026-10-07 ALab survey: 18 `nsz` min/max, 11 `powif64`/`sinf64`).
//!
//! The bridge now lowers the stamped call with no panic row and a fresh float
//! result (`FreshSymbolicHavoc`): panic-freedom ONLY, no value fact, and in a
//! namespace the facet and determinism gates never read.
//!
//! `check-pass` under `-Ztrust-policy=certify`, under which any runtime-checked
//! row is a build error, so this fixture states that none of the calls below
//! carries one. The negatives are `panic_free_intrinsic_negatives.rs`; the
//! forged-metadata, width and arity refusals are unit-level in `trust_ir_bridge`
//! (`test_panic_free_intrinsic_stamp_metadata_and_shape_fail_closed`).

#![feature(core_intrinsics)]
#![allow(internal_features)]

use std::intrinsics;

// The nondeterministic `nsz` selections: fallback-bodied, and the fallback body
// (`x.is_nan() || y <= x`) is what the pin reads.
pub fn nsz_max(x: f64, y: f64) -> f64 {
    intrinsics::maximum_number_nsz_f64(x, y)
}

pub fn nsz_min(x: f64, y: f64) -> f64 {
    intrinsics::minimum_number_nsz_f64(x, y)
}

pub fn nsz_max32(x: f32, y: f32) -> f32 {
    intrinsics::maximum_number_nsz_f32(x, y)
}

pub fn nsz_min32(x: f32, y: f32) -> f32 {
    intrinsics::minimum_number_nsz_f32(x, y)
}

// The deterministic but fallback-bodied IEEE selections.
pub fn ieee_min(x: f64, y: f64) -> f64 {
    intrinsics::minimumf64(x, y)
}

pub fn ieee_max(x: f64, y: f64) -> f64 {
    intrinsics::maximumf64(x, y)
}

// Upstream 1.101: `integer_power` (`powif64`) moved to
// `panic_free_intrinsic_transcendental_refused.rs` with `sine`. The generic
// `powi` item carries a dispatch fallback body into the `libm` crate, which
// the mint's fallback pin cannot follow, so under `certify` it is refused.

// Upstream 1.101: `sine` moved to
// `panic_free_intrinsic_transcendental_refused.rs`. The generic `sin` item
// carries a dispatch fallback body into the `libm` crate, which the mint's
// fallback pin cannot follow, so under `certify` it is now refused.

// Upstream 1.101: `power32` (`powf32`) moved to the refused fixture with
// `sine` — `powf` is now one generic item with a `libm` dispatch fallback
// body, like `powi` above.

// The result feeds a real bounds obligation that holds whatever the havoc value
// is, so the body carries a published row and a pinned verdict.
pub fn max_then_index(x: f64, y: f64) -> u8 {
    //~^ NOTE Trust verification: 1 proved, 0 failed, 0 unknown, 0 timed out, 0 runtime-checked out of 1
    let t = [1u8, 2];
    t[(intrinsics::maximum_number_nsz_f64(x, y) > 0.0) as usize]
}
