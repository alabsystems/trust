//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-pass
//! The EXACT IEEE-754 float methods verify panic-free.
//!
//! Each body below is a single compiler intrinsic. Until 2026-09-18 every one of
//! them was refused: `trust-ir-bridge` had listed the float intrinsic family as
//! total since it was written, but that list is only ever consulted on a path
//! the extractor stamped `@trust-rustc-intrinsic::`, and the extractor stamped
//! eight integer names. So the float entries were dead, `intrinsics::fabs` took
//! the fail-soft absent-callee encoding, and `x.abs()` failed the strict lane
//! with an unprovable panic row.
//!
//! `float_inexact_intrinsic_methods_stay_refused.rs` is the other half: the
//! transcendentals are panic-free too, and are deliberately NOT marked, because
//! the same marker is read as a DETERMINISM claim and std documents their
//! precision as varying "within the same execution from one invocation to the
//! next".

pub fn absolute(x: f64) -> f64 { x.abs() }
pub fn absolute32(x: f32) -> f32 { x.abs() }
pub fn floored(x: f64) -> f64 { x.floor() }
pub fn ceiled(x: f64) -> f64 { x.ceil() }
pub fn truncated(x: f64) -> f64 { x.trunc() }
pub fn rounded(x: f64) -> f64 { x.round() }
pub fn root(x: f64) -> f64 { x.sqrt() }
pub fn root32(x: f32) -> f32 { x.sqrt() }
pub fn sign_of(x: f64, y: f64) -> f64 { x.copysign(y) }
pub fn fused(a: f64, b: f64, c: f64) -> f64 { a.mul_add(b, c) }
