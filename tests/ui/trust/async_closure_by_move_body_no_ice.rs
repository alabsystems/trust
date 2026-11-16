//@ needs-trust-verify
//@ edition: 2024
//@ revisions: default advisory o2plain
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[advisory] compile-flags: -Ztrust-policy=advisory
//@[o2plain] compile-flags: -Copt-level=2
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@[default] check-fail
//@[advisory] check-pass
//@[o2plain] check-fail
//! Regression for an ICE (measured 2026-09-23, stage-1 `96f2019566`): calling an
//! async closure through `AsyncFnOnce` makes rustc synthesize a BY-MOVE body
//! (`DefKind::SyntheticCoroutineBody`, `{closure#0}::{closure#0}::{synthetic#0}`),
//! and that body has no HIR. `def_uses_unsafe_source_impl`
//! (`rustc_mir_transform/src/trust_verify.rs`) walked `hir_body_owned_by` on it:
//!
//!     body_owned_by: HirId(.. scalar_capture::{closure#0}::{closure#0}::{synthetic#0})
//!     (synthetic (Clean-origin) `value`) has no associated body
//!
//! exit 101, once per function below, under the default policy, under
//! `-Ztrust-policy=advisory` and at `-Copt-level=2` alike. The shapes are the
//! live-compiler fixtures of `crates/trust-thir-lower/src/generated_coroutine/
//! fixtures/` (`scalar_capture.rs` plus the three negative controls of
//! `refusals.rs`); each one ICEd on its own.
//!
//! THE FIX answers for a synthetic by-move body from its parent coroutine's
//! source, of which the body is a by-move copy.
//!
//! The assertion is "no ICE", stated per lane:
//!
//!   * `default` / `opt` — `check-fail`, and compiletest requires exit status
//!     EXACTLY 1, so an ICE's 101 fails the test. The ordinary refusal is real and
//!     independent of the ICE: `consume::{closure#0}` is refused ("coroutine
//!     executor-protocol premise is unproved") even in a crate that never passes
//!     it a closure, where no by-move body exists (measured: exit 1, no ICE).
//!   * `advisory` — `check-pass`, the convention of the other `*_no_ice.rs`
//!     fixtures: on the baseline the ONLY errors under advisory were the four
//!     ICEs, so the compile must now run to completion.
//!
//! Not a verdict pin: which rows these bodies get is the verifier's business.
//! Do not add error annotations here to make it one.

async fn consume<F: AsyncFnOnce() -> u32>(function: F) -> u32 { function().await }

/// `generated_coroutine/fixtures/scalar_capture.rs`.
pub async fn scalar_capture(value: u32) -> u32 {
    let closure = async move || value;
    consume(closure).await
}

/// `refusals.rs`: a real call in the generated body.
pub async fn real_call(value: u32) -> u32 {
    let closure = async move || value.wrapping_add(1);
    consume(closure).await
}

/// `refusals.rs`: a borrowed capture moved into the generated body.
pub async fn borrowed_capture(value: &u32) -> u32 {
    let closure = async move || *value;
    consume(closure).await
}

/// `refusals.rs`: a real suspension point in the generated body.
pub async fn real_suspend(value: u32) -> u32 {
    let closure = async move || { async {}.await; value };
    consume(closure).await
}
