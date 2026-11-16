//@ needs-trust-verify
//@ edition: 2021
//@ check-pass
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//! **A large array repeat is verified in linear time (Trust, 2026-09-29).**
//!
//! `[0u8; 65536]` lowers to a 65 536-step `InsertElement` chain over an `Undef`
//! seed. The THIR-lowering differential's dead-seed proof walked that chain and, at
//! every step, rescanned the whole function with a clone-and-rewrite probe per
//! instruction: this program took 152 s and 26 GB before verification began, and a
//! 4 MiB buffer ran out of memory (ordinary-Rust completeness sweep). The proof now
//! builds one use map per function (`differential::SeedUses`), so this builds in
//! about a second. There is no timeout here; a regression shows as a UI run that
//! stalls on this file.

pub fn buf() -> u8 {
    let b = [0u8; 65536];
    b[0]
}
