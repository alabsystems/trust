//@ run-fail
//@ needs-trust-verify
//@ revisions: atomic deref ffi
//@[atomic] edition: 2021
//@[deref] edition: 2021
//@[ffi] edition: 2024
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory -Coverflow-checks=on
//@ error-pattern: attempt to add with overflow
//@ ignore-emscripten no processes
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
#![allow(unused_mut)]
//! INT-RAWCONST-HAVOC-1 (docs/KNOWN_HAZARDS.md, docs/DECISION_QUEUE.md): the run twin.
//! `let mut x: u8 = 5; let p = &raw const x;`, then a write of 255 through `p`, then
//! `x + 1`. Vanilla Rust (and `-Ztrust-verify=off`) panics "attempt to add with
//! overflow". The write is defined under Tree Borrows (UF-1(c)) and needs no `unsafe`
//! at the write site in two of the three revisions:
//!
//! * `atomic` — `AtomicU8::from_ptr(p as *mut u8).store(k, Relaxed)`, a safe call;
//! * `deref`  — `unsafe { *(p as *mut u8) = k; }`;
//! * `ffi`    — an edition-2024 `safe fn memset(p as *mut u8, k as i32, 1)`.
//!
//! vcgen's general havoc list counted `&mut` and `&raw mut` borrows only, so the fact
//! `x == 5` survived the write: the overflow row was proved (clean-kernel certified),
//! TRUST_ELIDE removed the check, and the advisory build printed `0` and exited 0.
//! Measured BEFORE the fix on the stage 1 at `scratchpad/stage1-w17` (2026-10-06):
//! each revision built with exactly these flags exits 0 at run time and prints `0`.
//! The verify-off build of the same source panics (exit 101).
//!
//! AFTER the fix the row is refuted and the check stays, so the run panics. The
//! default policy refuses to build a crate with a refuted row, so this twin uses the
//! advisory policy, which records the row and keeps the check.

#[cfg(atomic)]
#[inline(never)]
fn f(k: u8) -> u8 {
    let mut x: u8 = 5;
    let p = &raw const x;
    let a = unsafe { std::sync::atomic::AtomicU8::from_ptr(p as *mut u8) };
    a.store(k, std::sync::atomic::Ordering::Relaxed);
    x + 1
}

#[cfg(deref)]
#[inline(never)]
fn f(k: u8) -> u8 {
    let mut x: u8 = 5;
    let p = &raw const x;
    unsafe {
        *(p as *mut u8) = k;
    }
    x + 1
}

#[cfg(ffi)]
unsafe extern "C" {
    safe fn memset(s: *mut u8, c: i32, n: usize) -> *mut u8;
}

#[cfg(ffi)]
#[inline(never)]
fn f(k: u8) -> u8 {
    let mut x: u8 = 5;
    let p = &raw const x;
    // SAFETY: `p` points to `x`, which is live, mutable and one byte long.
    memset(p as *mut u8, k as i32, 1);
    x + 1
}

fn main() {
    println!("{}", f(std::hint::black_box(255)));
}
