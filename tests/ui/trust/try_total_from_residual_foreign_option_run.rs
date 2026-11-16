//@ run-fail
//@ needs-trust-verify
//@ edition: 2021
//@ aux-build: try_total_from_residual_foreign_option_dep.rs
//@ compile-flags: -Ztrust-verify=off
//@ error-pattern: boom option from_residual
//@ ignore-emscripten no processes
//! The WITNESS for `try_total_from_residual_foreign_option.rs` (TRY-TOTAL-ANCHOR-1):
//! the `from_residual` that file's BEFORE compiler credited as core's total
//! `Option` re-wrap is the dependency's impl for its own residual type, and it
//! panics.
//!
//! Built with verification OFF, so it passes before and after the fix alike: it pins
//! that the call really panics, not the verdict. Measured 2026-10-05 on the stage 1
//! at `scratchpad/stage1-w14`: the aux built with its own flags and this file built
//! `-Ztrust-verify=off` exits 101 with the message above.

#![feature(try_trait_v2)]

extern crate try_total_from_residual_foreign_option_dep as dep;

use std::ops::FromResidual;

#[inline(never)]
fn d() -> Option<u32> {
    <Option<u32> as FromResidual<dep::Res>>::from_residual(dep::Res)
}

fn main() {
    println!("{:?}", d());
}
