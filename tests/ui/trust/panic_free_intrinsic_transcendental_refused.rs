//@ edition: 2021
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=certify --crate-type lib
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//! CAPABILITY LOSS (upstream 1.101, recorded in docs/DECISION_QUEUE.md):
//! the transcendental intrinsics are now ONE generic item per family
//! (`sin<T: FloatPrimitive>`), declared by `intrinsic_dispatch_on_type!`
//! with a fallback body that dispatches per width into the `libm` crate.
//! The panic-freedom mint pins a fallback body only when every callee is a
//! safe, non-generic, non-trait `core` function, so the dispatch body is
//! not pinnable and no `@trust-rustc-panic-free-intrinsic::` stamp is
//! minted. Under `certify` the call therefore keeps its absent-callee row
//! and is refused — fail-closed, never proved. The body-less per-width
//! items this fixture's predecessors used (`sinf64` in
//! `panic_free_intrinsic_native_total.rs` before 1.101) no longer exist.
//! Flip back when the mint can pin the dispatch fallback (or upstream
//! restores body-less items).

#![feature(core_intrinsics)]
#![allow(internal_features)]

use std::intrinsics;

pub fn sine(x: f64) -> f64 {
    //~^ ERROR Trust Level 0 safety verification incomplete for `panic_free_intrinsic_transcendental_refused::sine`
    //~| ERROR Trust strict verification failed for `panic_free_intrinsic_transcendental_refused::sine`
    intrinsics::sin(x)
}

// The same loss for the power families: `powf` and `powi` are ONE generic
// item each in 1.101, with `libm` dispatch fallback bodies. The per-width
// items (`powf32`, `powif64`) no longer exist.
pub fn power32(x: f32, y: f32) -> f32 {
    //~^ ERROR Trust Level 0 safety verification incomplete for `panic_free_intrinsic_transcendental_refused::power32`
    //~| ERROR Trust strict verification failed for `panic_free_intrinsic_transcendental_refused::power32`
    intrinsics::powf(x, y)
}

pub fn integer_power(x: f64, n: i32) -> f64 {
    //~^ ERROR Trust Level 0 safety verification incomplete for `panic_free_intrinsic_transcendental_refused::integer_power`
    //~| ERROR Trust strict verification failed for `panic_free_intrinsic_transcendental_refused::integer_power`
    intrinsics::powi(x, n)
}
