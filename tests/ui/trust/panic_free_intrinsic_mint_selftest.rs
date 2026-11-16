//@ edition: 2021
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ rustc-env:TRUST_PANIC_FREE_MINT_SELFTEST=1
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! **std-call-summaries P2 review: negative coverage of the panic-free intrinsic
//! mint and its fallback-body walker.**
//!
//! Every real list entry passes every gate of `tcx_marked_panic_free_intrinsic_path`,
//! so no ordinary program can show that a gate is load-bearing. With
//! `TRUST_PANIC_FREE_MINT_SELFTEST=1` the compiler runs
//! `trust_mir_extract::panic_free_intrinsic_mint_selftest`, which drives each gate in
//! isolation with a real `core` item that passes the others and must fail that one
//! (`rotate_left` for the walker, `ub_checks` for `#[rustc_nounwind]`,
//! `unchecked_add` for safety, `minimum_number_nsz_f64` under a wrong body shape),
//! plus the local lookalike intrinsic below for the residency gate, and two
//! positive controls. Every failing case is a compile error, so deleting a gate or
//! making the walker answer `true` turns this fixture red.

#![feature(intrinsics, rustc_attrs)]
#![allow(internal_features)]

/// A LOCAL `#[rustc_intrinsic]` with a listed name, `#[rustc_nounwind]`, a safe
/// signature and a panic-free fallback body: it passes every gate but residency.
#[rustc_intrinsic]
#[rustc_nounwind]
pub const fn maximum_number_nsz_f64(x: f64, y: f64) -> f64 {
    if y >= x { y } else { x }
}

pub fn calls_the_local_lookalike(x: f64, y: f64) -> f64 {
    maximum_number_nsz_f64(x, y)
}
