//@ revisions: sync_caller async_caller
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory -Ztrust-verify-output=json --crate-type lib
//@ compile-flags: --error-format=human
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//@ forbid-output: Trust Level 0 safety verification incomplete for `adapter_yield_premise_for_async_callee::all_zero::{closure#0}`
//! D2 tier 1's ADAPTER_YIELD premise for a plain fn that an `async fn` calls.
//! The premise initializer borrows the parent's pre-steal elaborated MIR and
//! admits nothing for a stolen parent. Before 2026-09-29, `caller`'s coroutine
//! was optimized during `run_required_analyses` (its layout was read from
//! `optimized_mir`), and its TrustVerify pass bundled `all_zero` —
//! `optimized_mir(all_zero)` — stealing `all_zero`'s elaborated MIR before the
//! seam: the closure got no premise and its `a[i]` bound stayed unproved, only
//! in the `async_caller` revision (measured on stage 1 `638784cafa`). The
//! layout is now read pre-steal, so both revisions carry the premise.

pub fn all_zero(a: &[u8; 8]) -> bool {
    (0..8).all(|i| a[i] == 0)
}

#[cfg(sync_caller)]
pub fn caller(a: [u8; 8]) -> bool {
    all_zero(&a)
}

#[cfg(async_caller)]
pub async fn caller(a: [u8; 8]) -> bool {
    all_zero(&a)
}

//~? RAW "modeled_facts":["ADAPTER_YIELD: core `Iterator::all` over `0..8` invokes this closure only on items it yields; assumed: item parameter `_2` has value in [0, 8)
