//@ revisions: slice const_generic
//@ run-fail
//@ needs-trust-verify
//@ edition: 2021
//@ only-64bit
//@ aux-build: zst_enum_slice_len_dep.rs
//@ compile-flags: -Ztrust-verify=off
//@ error-pattern: attempt to multiply with overflow
//@ ignore-emscripten no processes
//! The WITNESS for `zst_enum_slice_len.rs` (ZST-ENUM-SLICE-LEN-1).
//!
//! The dependency is built with verification ON under the advisory policy, with
//! overflow checks on. `One` is a zero-sized enum, so a `&[One]` can be `2^63`
//! long, and `twice_len` doubles that length. This file is built
//! `-Ztrust-verify=off` and is safe code: `slice` passes a `2^63`-long slice
//! (`[[One::A; 1 << 31]; 1 << 32]`, flattened), and `const_generic` instantiates
//! `twice_n::<{ 1 << 63 }>` from the dependency's MIR.
//!
//! BEFORE (the stage 1 of `origin/main` `2bf0ad72e3`, a copy at
//! `scratchpad/stage1-w22probe`, measured 2026-10-11): the dependency build
//! reported `[overflow:mul]` proved and kernel-certified and printed
//! `TRUST_ELIDE: elided 1 kernel-certified overflow checks` for each function,
//! and both revisions printed `twice = 0` and exited 0. Against the same
//! dependency built `-Ztrust-verify=off`, both panicked with this pattern (101).
//!
//! AFTER (measured 2026-10-11, stage 1 of `618d7bd287`): the row is refuted (a
//! warning under advisory), nothing is elided, and each revision panics with `attempt to
//! multiply with overflow` (exit 101), as it does against a `-Ztrust-verify=off` dependency.

extern crate zst_enum_slice_len_dep as dep;

#[cfg(slice)]
fn twice() -> usize {
    let big = [[dep::One::A; 1 << 31]; 1 << 32];
    let flat: &[dep::One] = big.as_flattened();
    dep::twice_len(flat)
}

#[cfg(const_generic)]
fn twice() -> usize {
    dep::twice_n::<{ 1usize << 63 }>()
}

fn main() {
    println!("twice = {}", twice());
}
