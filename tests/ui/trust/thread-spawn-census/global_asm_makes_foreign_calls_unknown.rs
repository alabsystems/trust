//@ revisions: asm plain
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory --crate-type lib
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@[plain] forbid-output:UnmodeledThreadSpawnEffect
//! Spawn census (P2 review, probe h17): module-level assembly is foreign code
//! that may call any function it names by `sym` (the probe's trampoline jumped
//! to a crate-private spawner), and Rust reaches it through an `extern`
//! declaration, so no body holds inline assembly and no UNKNOWN sink existed:
//! `fire` was QUIET, and it spawned. Design §14 refuses crates using assembly
//! wholesale: with a `global_asm!` item, every call into foreign code reaches an
//! UNKNOWN sink. `plain`, without the item: no row.

#![allow(dead_code)]

#[cfg(asm)]
core::arch::global_asm!("");

unsafe extern "C" {
    fn probe_trampoline();
}

pub fn fire() { unsafe { probe_trampoline() } } //[asm]~ NOTE not enumerated (no spawn was found)
