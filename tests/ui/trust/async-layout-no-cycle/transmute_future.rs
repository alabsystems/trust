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
//! `transmute` of a future: `check_transmutes` computes the coroutine's
//! layout (probe k2). Before, the cycle closed at `layout_of`, whose cycle
//! handler printed a FALSE `E0733 recursion in an async fn requires boxing`
//! (analysis -> layout_of -> optimized_mir(work::{closure#0}) -> SCC oracle ->
//! elaborated(t) -> check_transmutes(t) -> layout_of).
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
//[strict]~^ ERROR Trust strict verification failed for `transmute_future::work::{closure#0}`: coroutine executor-protocol premise is unproved
pub unsafe fn t() -> u8 { unsafe { core::mem::transmute::<_, u8>(work()) } }
//[strict]~^ ERROR Trust Level 0 safety verification incomplete for `transmute_future::t`: 1 obligation(s) were not proved
//[strict]~| ERROR Trust full verification failed for `transmute_future::t`: native typed-TrustIr lowering did not complete, so the panic-freedom of an unmodeled construct could not be established
