//@ build-pass
//@ edition: 2024
//@ revisions: o2 o3
//@ compile-flags: -Ztrust-verify=off --crate-type lib
//@[o2] compile-flags: -Copt-level=2
//@[o3] compile-flags: -Copt-level=3
//! Trust (2026-11-09): regression for the ICE that 69d2b4c9a91 introduced and
//! 42e51ea486 fixed. `is_inline_valid_on_fn` (`compiler/rustc_mir_transform/src/
//! check_inline.rs`) asked whether a callee is C-variadic. Its `DefKind::Closure`
//! arm assumed every such def has a `ty::Closure` type, but an `async` closure is
//! a coroutine-closure (`ty::CoroutineClosure`) and its body a coroutine, both of
//! `DefKind::Closure`. At `-Copt-level=2` and `3` the MIR inliner reaches that arm
//! for the closures below and the `let ... else { unreachable!() }` panicked:
//!
//!     internal error: entered unreachable code
//!     (compiler/rustc_mir_transform/src/check_inline.rs:55)
//!
//! MEASURED with the stage-1 compiler of `fab64fd279` (before 42e51ea486): exit 101
//! on this file at `-Copt-level=2` and at `3`, exit 0 at `0`. A plain closure or an
//! `async` block did not ICE. The fix answers `false` for any non-`ty::Closure`
//! type, as the code did before 69d2b4c9a91. No verification is involved, so
//! `-Ztrust-verify=off` keeps the test about codegen.

pub fn call_async_closure() -> u32 {
    let c = async || 3u32;
    let _f = c();
    0
}

pub fn call_async_closure_with_capture(x: u32) -> u32 {
    let c = async move || x + 1;
    let _f = c();
    x
}
