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
//! A real mutual-recursion SCC the oracle MUST see, plus a layout-dependent
//! signature elsewhere (probe pe1; before: E0391). That the `ping`/`pong`
//! rows are unchanged by `g` is pinned byte-for-byte by
//! `tests/run-make/trust-coroutine-verdict-order-independent`.
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
//[strict]~^ ERROR Trust strict verification failed for `real_scc_plus_layout_signature::work::{closure#0}`: coroutine executor-protocol premise is unproved
pub const fn size_of_ret<F: Fn() -> R, R>(_: &F) -> usize { core::mem::size_of::<R>() }
pub fn ping(n: u32) -> u32 { if n == 0 { 0 } else { pong(n - 1) } }
//[strict]~^ ERROR Trust strict verification failed for `real_scc_plus_layout_signature::ping`: 2 obligation(s) were not fully verified
pub fn pong(n: u32) -> u32 { if n == 0 { 1 } else { ping(n - 1) } }
//[strict]~^ ERROR Trust strict verification failed for `real_scc_plus_layout_signature::pong`: 2 obligation(s) were not fully verified
pub fn g() -> [u8; size_of_ret(&work)] { unimplemented!() }
//[strict]~^ ERROR Trust Level 0 safety verification incomplete for `real_scc_plus_layout_signature::g`: 2 obligation(s) were not proved
//[strict]~| ERROR Trust strict verification failed for `real_scc_plus_layout_signature::g`: 2 obligation(s) were not fully verified
