//@ revisions: off adv strict
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: --crate-type lib
//@[off] compile-flags: -Ztrust-verify=off
//@[adv] compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory
//@[strict] compile-flags: -Ztrust-verify=on -Ztrust-policy=strict
//@[off] check-pass
//@[adv] check-pass
//@[strict] check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ forbid-output: E0391
//@ forbid-output: E0733
//@ forbid-output: cycle detected
//! Boxed mutually recursive async fns plus a layout-dependent signature
//! (probe k8; before: E0391).
//!
//! Drop-in (release gate): `off` and `adv` accept this valid Rust crate;
//! `strict` pins the verifier refusals below. Before 2026-09-29 the verified
//! lanes rejected it with a query cycle: a coroutine's layout,
//! demanded from inside the type system, read the coroutine's `optimized_mir`,
//! which Trust makes depend on other bodies (the crate call-graph oracles,
//! TrustVerify's callee bundling and operand evaluation). The layout is now read
//! from the coroutine's pre-steal elaborated MIR (`trust_local_coroutine_layout`).
//! The strict lane still refuses unproved coroutine premises and the explicit
//! panic placeholder below. The annotations pin those verifier refusals while
//! every lane forbids layout/type-query cycles.
//!
//! Re-pinned 2026-10-04: each `{closure#0}` no longer carries a `Trust Level 0
//! safety verification incomplete` error. Its one failed Level 0 row was the
//! `[unsafe] missing SAFETY comment` stand-in charged on the `Pin::new_unchecked`
//! of rustc's own `.await` lowering, which AW-1 (`d46ddcc8b2`, docs/DECISION_QUEUE.md)
//! stopped charging. Measured on a stage 1 of `1ab78ed8e8` (before AW-1): that
//! `hardened_unsafe_operation` row is `failed` in all three closures; on a stage 1
//! with AW-1 it is absent, and every other row and error is unchanged. Each
//! closure is still refused here on its executor-protocol premise and its
//! incomplete native lowering.

use core::{future::Future, pin::Pin};
pub fn a(n: u8) -> Pin<Box<dyn Future<Output = u8>>> {
//[strict]~^ ERROR Trust Level 0 safety verification incomplete for `boxed_async_recursion_plus_layout_signature::a`: 1 obligation(s) were not proved
//[strict]~| ERROR Trust full verification failed for `boxed_async_recursion_plus_layout_signature::a`: native typed-TrustIr lowering did not complete, so the panic-freedom of an unmodeled construct could not be established
    Box::pin(async move { if n == 0 { 0 } else { b(n - 1).await } })
//[strict]~^ ERROR Trust strict verification failed for `boxed_async_recursion_plus_layout_signature::a::{closure#0}`: coroutine executor-protocol premise is unproved
//[strict]~| ERROR Trust full verification failed for `boxed_async_recursion_plus_layout_signature::a::{closure#0}`: native typed-TrustIr lowering did not complete, so the panic-freedom of an unmodeled construct could not be established
}
pub fn b(n: u8) -> Pin<Box<dyn Future<Output = u8>>> { Box::pin(async move { a(n).await }) }
//[strict]~^ ERROR Trust Level 0 safety verification incomplete for `boxed_async_recursion_plus_layout_signature::b`: 1 obligation(s) were not proved
//[strict]~| ERROR Trust full verification failed for `boxed_async_recursion_plus_layout_signature::b`: native typed-TrustIr lowering did not complete, so the panic-freedom of an unmodeled construct could not be established
//[strict]~| ERROR Trust strict verification failed for `boxed_async_recursion_plus_layout_signature::b::{closure#0}`: coroutine executor-protocol premise is unproved
//[strict]~| ERROR Trust full verification failed for `boxed_async_recursion_plus_layout_signature::b::{closure#0}`: native typed-TrustIr lowering did not complete, so the panic-freedom of an unmodeled construct could not be established
pub async fn work() -> u8 { a(3).await }
//[strict]~^ ERROR Trust strict verification failed for `boxed_async_recursion_plus_layout_signature::work::{closure#0}`: coroutine executor-protocol premise is unproved
//[strict]~| ERROR Trust full verification failed for `boxed_async_recursion_plus_layout_signature::work::{closure#0}`: native typed-TrustIr lowering did not complete, so the panic-freedom of an unmodeled construct could not be established
pub const fn size_of_ret<F: Fn() -> R, R>(_: &F) -> usize { core::mem::size_of::<R>() }
pub fn g() -> [u8; size_of_ret(&work)] { unimplemented!() }
//[strict]~^ ERROR Trust Level 0 safety verification incomplete for `boxed_async_recursion_plus_layout_signature::g`: 2 obligation(s) were not proved
//[strict]~| ERROR Trust strict verification failed for `boxed_async_recursion_plus_layout_signature::g`: 2 obligation(s) were not fully verified
