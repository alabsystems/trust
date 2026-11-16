//@ revisions: guard neg strict
//@ run-fail
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=off -Coverflow-checks=on
//@ error-pattern: attempt to exponentiate with overflow
//@ ignore-emscripten no processes
//@ dont-check-compiler-stderr
//! The run twin of `pow_symbolic_exponent_overflow.rs` (POW-SYMEXP-1): three of its
//! liars, whose `overflow:mul` row was PROVED and kernel-certified, panic on a
//! concrete argument.
//!
//! * `guard`: `if e < 32 { b.pow(e) }` (u32) at `(3, 21)` — `3^21 > u32::MAX`;
//! * `neg`: `(-2i32).pow(e)` at `e = 32` — `(-2)^32 == 2^32`;
//! * `strict`: `if e < 32 { b.strict_pow(e) }` (u32) at `(3, 21)`.
//!
//! The panic does not depend on the verifier (this twin is built verify-off); it
//! is the witness that the rows the fix refutes are real. Measured 2026-10-05 on
//! the stage 1 of `ec03f72395` (`scratchpad/stage1-w15r`): each revision
//! built with these flags exits 0, and its binary panics "attempt to exponentiate
//! with overflow" (exit 101). The scout measured the same panic for `upow(3, 21)`
//! built on the DEFAULT verifying lane (`-Ztrust-verify=on`, exit 0 before the fix).

use std::hint::black_box;

#[inline(never)]
pub fn upow(b: u32, e: u32) -> u32 {
    if e < 32 { b.pow(e) } else { 0 }
}

#[inline(never)]
pub fn n2(e: u32) -> i32 {
    (-2i32).pow(e)
}

#[inline(never)]
pub fn spg(b: u32, e: u32) -> u32 {
    if e < 32 { b.strict_pow(e) } else { 0 }
}

fn main() {
    #[cfg(guard)]
    {
        let (b, e) = black_box((3u32, 21u32));
        println!("upow(3, 21) = {}", upow(b, e));
    }
    #[cfg(neg)]
    {
        let e = black_box(32u32);
        println!("n2(32) = {}", n2(e));
    }
    #[cfg(strict)]
    {
        let (b, e) = black_box((3u32, 21u32));
        println!("spg(3, 21) = {}", spg(b, e));
    }
}
