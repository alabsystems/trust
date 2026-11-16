//@ revisions: off adv strict
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: --crate-type=lib
//@[off] compile-flags: -Ztrust-verify=off
//@[adv] compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory
//@[strict] compile-flags: -Ztrust-verify=on -Ztrust-policy=strict
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ forbid-output: rec_fut::{closure#0}
//@ forbid-output: awaits_error_output::{closure#0}
//@ forbid-output: create_complex_future::{closure#0}
//@ forbid-output: Trust Verification Report
//! Diagnostic parity for a crate with front-end errors whose coroutines'
//! types reference those errors (shapes of
//! `tests/ui/impl-trait/recursive-impl-trait-type-indirect.rs` and
//! `tests/ui/impl-trait/auto-trait-leakage/auto-trait-contains-err.rs`).
//!
//! Upstream's eager coroutine layout check (`run_required_analyses`) reaches
//! `optimized_mir` only through `ordinary_coroutine_layout`, and `layout_of`
//! returns `ReferencesError` before that when the normalized coroutine type
//! references an error — here an opaque whose hidden type is an error after
//! E0720, and an awaited output that is an error after E0277. So no lane ever
//! optimizes, or verifies, these coroutines. The verified lanes' replacement
//! sweep (`trust_ensure_coroutine_optimized_mir`) once demanded `optimized_mir`
//! of EVERY coroutine, so TrustVerify ran on them: strict added "Trust full
//! verification skipped `…::rec_fut::{closure#0}`" and three more errors, and
//! advisory a verification report. It now demands only the coroutines the
//! eager check reaches (`upstream_layout_check_reaches_coroutine_body`), so
//! every revision reports exactly the front-end errors. The sweep's positive
//! case (a coroutine the check does reach, in an erroring crate) is
//! `force_inline_refusal_in_async_body.rs`.

use std::future::Future;

pub fn rec_fut() -> impl Sized {
    //~^ ERROR cannot resolve opaque type
    async { rec_fut() }
}

fn invalid_future() -> impl Future {}
//~^ ERROR `()` is not a future

pub fn awaits_error_output() -> impl Future<Output = impl Sized> {
    async { invalid_future().await }
}

fn create_complex_future() -> impl Future<Output = impl ReturnsSend> {
    async { &|| async { invalid_future().await } }
}

pub fn coerce_impl_trait() -> impl Future<Output = impl Send> {
    create_complex_future()
}

trait ReturnsSend {}

impl<F, R> ReturnsSend for F
where
    F: Fn() -> R,
    R: Send,
{
}
