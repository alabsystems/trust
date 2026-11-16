//@ revisions: callee_first caller_first layout_first
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ forbid-output: E0391
//@ forbid-output: cycle detected
//! W11 transitive spawn census: the verdict is a function of the program, not
//! of item (and so `DefIndex`/query) order. The bounded walk it replaced read
//! callee bodies through `optimized_mir` and could answer differently depending
//! on which bodies were already cached or on the stack. Both revisions compile
//! the SAME three functions, declared callee-first or caller-first, and both
//! must refuse `wrapper` and `caller` transitively and `launch` directly.
//!
//! `layout_first` (2026-09-29) is `callee_first` behind a signature whose array
//! length needs an `async fn`'s future size, declared FIRST. wfcheck of that
//! signature demands the coroutine's layout from inside type computation. The
//! census used to be forced by the first `optimized_mir` — which that layout
//! demanded — and so from inside `wfcheck`: E0391. The layout is now read
//! pre-steal and the census is forced at the analysis seam, so the verdicts
//! are the other revisions' verdicts.

#![allow(dead_code)]

#[cfg(layout_first)]
pub const fn size_of_ret<F: Fn() -> R, R>(_: &F) -> usize { core::mem::size_of::<R>() }

#[cfg(layout_first)]
pub fn sized() -> [u8; size_of_ret(&work)] { unimplemented!() }

#[cfg(layout_first)]
pub async fn work() -> u8 { 1 }

#[cfg(any(callee_first, layout_first))]
pub fn launch() { //[callee_first,layout_first]~ NOTE direct std thread spawn lacks an authenticated execution and race model
    let _handle = std::thread::spawn(|| {});
}

#[cfg(any(callee_first, layout_first))]
pub fn wrapper() { //[callee_first,layout_first]~ NOTE local callee reaches a std thread spawn through calls and drops; caller effect is unmodeled
    launch();
}

pub fn caller() {
    //~^ NOTE local callee reaches a std thread spawn through calls and drops; caller effect is unmodeled
    wrapper();
}

#[cfg(caller_first)]
pub fn wrapper() { //[caller_first]~ NOTE local callee reaches a std thread spawn through calls and drops; caller effect is unmodeled
    launch();
}

#[cfg(caller_first)]
pub fn launch() { //[caller_first]~ NOTE direct std thread spawn lacks an authenticated execution and race model
    let _handle = std::thread::spawn(|| {});
}
