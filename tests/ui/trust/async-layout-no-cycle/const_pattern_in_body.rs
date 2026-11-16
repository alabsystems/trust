//@ revisions: off adv strict
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: --crate-type lib
//@[off] compile-flags: -Ztrust-verify=off
//@[adv] compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory
//@[strict] compile-flags: -Ztrust-verify=on -Ztrust-policy=strict
//@[off] check-fail
//@[adv] check-fail
//@[strict] check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ forbid-output: E0391
//@ forbid-output: E0733
//@ forbid-output: cycle detected
//! A const used as a PATTERN: building THIR for `f` evaluates it (probe k4;
//! before: `E0391 cycle detected when const-evaluating + checking N`).
//!
//! Drop-in (release gate): stock rustc 1.99/1.100 accepted this crate; stock
//! 1.101 rejects the pattern with E0158 (measured 2026-10-17 on a stage1 built
//! from the bf9448e4 pin tree: evaluating `<Coroutine as
//! SizedTypeProperties>::SIZE` inside pattern const-eval now answers
//! TooGeneric). Drop-in is matching stock, so every revision now fails with
//! that same stock error — and still never with a cycle. Before 2026-09-29 the verified lanes (`adv`, and `strict`, the
//! shipping default) rejected it with a query cycle: a coroutine's layout,
//! demanded from inside the type system, read the coroutine's `optimized_mir`,
//! which Trust makes depend on other bodies (the crate call-graph oracles,
//! TrustVerify's callee bundling and operand evaluation). The layout is now read
//! from the coroutine's pre-steal elaborated MIR (`trust_local_coroutine_layout`).
//! `strict` may still refuse `async` bodies — Trust verdicts, which drop-in
//! permits — and nothing else.

pub async fn work() -> u8 { 1 }
//[strict]~^ ERROR Trust strict verification failed for `const_pattern_in_body::work::{closure#0}`: coroutine executor-protocol premise is unproved
pub const fn size_of_ret<F: Fn() -> R, R>(_: &F) -> usize { core::mem::size_of::<R>() }
pub const N: usize = size_of_ret(&work);
pub fn f(x: usize) -> bool { match x { N => true, _ => false } }
//[off]~^ ERROR constant pattern cannot depend on generic parameters
//[adv]~^^ ERROR constant pattern cannot depend on generic parameters
//[strict]~^^^ ERROR constant pattern cannot depend on generic parameters
