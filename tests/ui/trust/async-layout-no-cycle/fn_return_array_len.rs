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
//! A fn SIGNATURE sized by a future: wfcheck of `g` evaluates the
//! array length, which needs the layout of `work`'s future (probe g2b;
//! before: `E0391 cycle detected when evaluating type-level constant`).
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

pub async fn work() -> u8 { 1 }
//[strict]~^ ERROR Trust strict verification failed for `fn_return_array_len::work::{closure#0}`: coroutine executor-protocol premise is unproved
pub const fn size_of_ret<F: Fn() -> R, R>(_: &F) -> usize { core::mem::size_of::<R>() }
pub fn g() -> [u8; size_of_ret(&work)] { unimplemented!() }
//[strict]~^ ERROR Trust Level 0 safety verification incomplete for `fn_return_array_len::g`: 2 obligation(s) were not proved
//[strict]~| ERROR Trust strict verification failed for `fn_return_array_len::g`: 2 obligation(s) were not fully verified
