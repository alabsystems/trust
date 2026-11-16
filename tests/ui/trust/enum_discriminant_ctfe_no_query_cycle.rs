//@ revisions: verify lower
//@ needs-trust-verify
//@ build-pass
//@ edition: 2021
//@[verify] compile-flags: --crate-type=lib -Ztrust-verify=on -Ztrust-policy=advisory
//@[lower] compile-flags: --crate-type=lib -Ztrust-verify=off -Ztrust-ir-lower=on
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE

//! **Regression (fix11, CTFE-IN-MIR-BUILT-1): `layout_of` of a local enum evaluates its explicit
//! discriminants, which no field type shows; the layout funnel must not let that evaluation
//! start from inside `mir_built`.**
//!
//! MEASURED on the stage 1 of the pre-L2 tree (`3213329a3a` with fix11's L2 commits reverted)
//! and of the fix11 WIP, both revisions' flags: `error[E0391]: cycle detected when simplifying
//! constant for the type system E::A::{constant#0}` — wfcheck of `E` evaluates `f()`, which
//! builds `f`'s MIR, whose hook converted `W` (it holds an `E`) and computed `E`'s discriminants,
//! evaluating `f()` again (the MIR oracle's `discriminant_for_variant`). Stock rustc
//! (nightly-2026-04-20) accepts the crate. Inside the freeze every site that computes a local
//! enum's discriminants — the layout funnel, the oracle's enum lowering and the producer's
//! `enum_discriminants` — now asks `ctfe_reentrancy::discriminants_may_be_evaluated` first;
//! `f()` is a call, so `E` (and `W`) stay layout-less and lower `Unsupported`. The
//! literal-discriminant enum `L` still lays out. `build-pass` in both revisions is the assertion.

pub enum E { A = f(), B }
pub struct W { n: u8, e: E }
pub const fn f() -> isize { let _w: Option<&W> = None; 1 }
pub fn w(x: &W) -> u8 { x.n }
pub fn wv(x: W) -> W { x }
pub fn ev(x: E) -> E { x }

pub enum L { A = 3, B = -1, C }
pub struct WL { n: u8, l: L }
pub const fn fl() -> isize { let _w: Option<&WL> = None; 2 }
pub fn wl(x: WL) -> WL { x }
