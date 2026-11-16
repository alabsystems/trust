//@ revisions: off adv strict
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: --crate-type=lib
//@[off] compile-flags: -Ztrust-verify=off
//@[adv] compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory
//@[strict] compile-flags: -Ztrust-verify=on -Ztrust-policy=strict
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! Diagnostic parity for `tests/ui/force-inlining/deny-async.rs` in the verified
//! lanes. Its two "could not be inlined into `async_caller::{closure#0}`" errors
//! come from the coroutine's `optimized_mir`, which upstream demands for every
//! coroutine in the eager layout check of `run_required_analyses` — the only
//! demand, since the crate has front-end errors (the two "incompatible" errors)
//! and never reaches codegen. With verification enabled the layout is read
//! pre-steal (`trust_local_coroutine_layout`) and no longer optimizes the
//! coroutine; `analysis` restores the demand with a top-level sweep
//! (`trust_ensure_coroutine_optimized_mir`). Without it both lanes would lose
//! these two errors. All three revisions report the same four.

#![allow(internal_features)]
#![feature(rustc_attrs)]

#[rustc_no_mir_inline]
#[rustc_force_inline]
//~^ ERROR `callee` is incompatible with `#[rustc_force_inline]`
pub fn callee() {
}

#[rustc_no_mir_inline]
#[rustc_force_inline = "the test requires it"]
//~^ ERROR `callee_justified` is incompatible with `#[rustc_force_inline]`
pub fn callee_justified() {
}

async fn async_caller() {
//[strict]~^ ERROR Trust strict verification failed for `force_inline_refusal_in_async_body::async_caller::{closure#0}`: coroutine executor-protocol premise is unproved
    callee();
    //~^ ERROR `callee` could not be inlined
    callee_justified();
    //~^ ERROR `callee_justified` could not be inlined
}
