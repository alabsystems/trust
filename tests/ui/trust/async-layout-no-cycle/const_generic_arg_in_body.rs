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
//! A const generic ARGUMENT inside a fn body: typeck of `h` evaluates it
//! (probe k1; before: `E0391 cycle detected when type-checking h`, through
//! layout -> optimized_mir(work::{closure#0}) -> SCC oracle -> typeck(h)).
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
//[strict]~^ ERROR Trust strict verification failed for `const_generic_arg_in_body::work::{closure#0}`: coroutine executor-protocol premise is unproved
pub const fn size_of_ret<F: Fn() -> R, R>(_: &F) -> usize { core::mem::size_of::<R>() }
pub fn g<const N: usize>() -> usize { N }
// ZERO-ROW-GATE (2026-10-10) refused `h` here; R43-ZERO-ROW-PARITY (2026-10-13): accepted again: `g::<K>` is
// discharged by the R43 parametric premises (`g`'s body is `N`, no panic-capable terminator).
pub fn h() -> usize { g::<{ size_of_ret(&work) }>() }
