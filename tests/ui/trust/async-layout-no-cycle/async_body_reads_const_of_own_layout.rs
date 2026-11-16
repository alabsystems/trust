//@ revisions: off adv strict adv_o strict_o
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: --crate-type lib
//@[off] compile-flags: -Ztrust-verify=off
//@[adv] compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory
//@[strict] compile-flags: -Ztrust-verify=on -Ztrust-policy=strict
//@[adv_o] compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory -O
//@[strict_o] compile-flags: -Ztrust-verify=on -Ztrust-policy=strict -O
//@[adv_o] check-pass
//@[strict_o] check-fail
//@[off] check-pass
//@[adv] check-pass
//@[strict] check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ forbid-output: E0391
//@ forbid-output: E0733
//@ forbid-output: cycle detected
//! The async body READS a const whose value needs its OWN layout (probe o1;
//! before: `E0391 cycle detected when const-evaluating + checking N`, also at
//! `-O` and `-Zmir-opt-level=3`). This one discriminates against fixes that only
//! RELOCATE where the call-graph oracles are forced: the cycle closed through
//! TrustVerify's evaluation of the coroutine's own operand `N`
//! (`const_operand_value` -> `eval_to_valtree`), with no oracle frame at all.
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

pub const fn size_of_ret<F: Fn() -> R, R>(_: &F) -> usize { core::mem::size_of::<R>() }
pub const N: usize = size_of_ret(&work);
pub async fn work() -> usize { let x = N; x + 1 }
//[strict,strict_o]~^ ERROR Trust strict verification failed for `async_body_reads_const_of_own_layout::work::{closure#0}`: coroutine executor-protocol premise is unproved
