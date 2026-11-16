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
//! A PARAMETER type sized by a future (probe pc1; before: E0391).
//!
//! Drop-in (release gate): stock rustc accepts this crate, and so does every
//! revision here. Before 2026-09-29 the verified lanes (`adv`, and `strict`, the
//! shipping default) rejected it with a query cycle: a coroutine's layout,
//! demanded from inside the type system, read the coroutine's `optimized_mir`,
//! which Trust makes depend on other bodies (the crate call-graph oracles,
//! TrustVerify's callee bundling and operand evaluation). The layout is now read
//! from the coroutine's pre-steal elaborated MIR (`trust_local_coroutine_layout`).
//! `strict` may still refuse `async` bodies — Trust verdicts, which drop-in
//! permits — and nothing else.

pub async fn work() -> u8 { 1 }
//[strict]~^ ERROR Trust strict verification failed for `param_type_array_len::work::{closure#0}`: coroutine executor-protocol premise is unproved
pub const fn size_of_ret<F: Fn() -> R, R>(_: &F) -> usize { core::mem::size_of::<R>() }
pub fn user(x: &[u8; size_of_ret(&work)]) -> u8 { x[0] }
