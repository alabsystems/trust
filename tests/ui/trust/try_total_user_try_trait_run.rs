//@ run-fail
//@ needs-trust-verify
//@ edition: 2021
//@ aux-build: try_total_user_try_trait_dep.rs
//@ compile-flags: -Ztrust-verify=off
//@ error-pattern: boom branch
//@ ignore-emscripten no processes
//! The WITNESS for `try_total_user_try_trait.rs` (TRY-TOTAL-ANCHOR-1): the call that
//! file's BEFORE compiler credited as a total `?`-desugar `Try::branch` panics. The
//! dependency's own `Try::branch` for `Option<u32>` panics on every call.
//!
//! Built with verification OFF, so it passes before and after the fix alike: it pins
//! that the call really panics, not the verdict. Measured 2026-10-05 on the stage 1
//! at `scratchpad/stage1-w14`: the aux built with its own flags and this file built
//! `-Ztrust-verify=off` exits 101 with the message above.

extern crate try_total_user_try_trait_dep as dep;

#[inline(never)]
fn a(x: Option<u32>) -> u32 {
    dep::Try::branch(x)
}

fn main() {
    println!("{}", a(std::hint::black_box(Some(1))));
}
