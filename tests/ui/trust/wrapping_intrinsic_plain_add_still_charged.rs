//@ edition: 2021
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=certify --crate-type lib -Ztrust-verify-timeout-ms=2000
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ dont-require-annotations: ERROR
//@ check-fail
// The 2 s per-obligation budget (default 20 s) removes most of this file's
// cost, because some engine runs out the budget on an obligation it cannot
// decide. It is safe: every per-function verdict was measured identical at
// 0.5 s, 2 s and 20 s (2026-09-23, 96f2019566), and the `Trust verification:`
// NOTE pins fail if the smaller budget ever changes one.
#![feature(core_intrinsics)]
#![allow(internal_features)]
//! **THE OTHER DIRECTION, AND THE ONE THAT MATTERS.**
//!
//! `wrapping_intrinsic_is_modular.rs` pins that
//! `intrinsics::wrapping_{add,sub,mul}` is no longer charged a no-overflow
//! obligation. That fix WITHHOLDS an obligation, so it is exactly the shape
//! that can go wrong quietly: widen it by one inch and ordinary arithmetic
//! stops being checked, with a GREEN build and nothing in the output to say so.
//!
//! This fixture is the tripwire. Every function below must be REFUSED. They are
//! the near neighbours of the certified ops:
//!
//! * an ordinary `a + b` — the operation whose obligation the whole verifier
//!   exists to charge, and which lowers to the *identical* bare
//!   `Rvalue::BinaryOp(Add, ..)` once overflow checks are off;
//! * `unchecked_add` / `unchecked_shl` — the family in the SAME
//!   `LowerIntrinsics` match arm as `wrapping_add`, one `matches!` away from
//!   being flagged. They are UB on overflow, not modular, and must stay
//!   charged.
//!
//! If any of these starts verifying, a real obligation has been removed and
//! this fixture goes red.

use core::intrinsics;

/// Plain checked arithmetic: `a + b` overflows for `a = u32::MAX, b = 1`.
pub fn plain_add(a: u32, b: u32) -> u32 {
    //~^ ERROR Trust
    //~| NOTE Trust verification: 0 proved, 1 failed, 0 unknown
    a + b
}

/// Plain subtraction underflows for `a = 0, b = 1`.
pub fn plain_sub(a: u32, b: u32) -> u32 {
    //~^ ERROR Trust
    //~| NOTE Trust verification: 0 proved, 1 failed, 0 unknown
    a - b
}

/// Plain multiplication overflows.
pub fn plain_mul(a: u32, b: u32) -> u32 {
    //~^ ERROR Trust
    //~| NOTE Trust verification: 0 proved, 1 failed, 0 unknown
    a * b
}

/// `unchecked_add` is UB on overflow, NOT modular. It shares the
/// `LowerIntrinsics` arm with `wrapping_add`; the `matches!` there must keep
/// them apart.
///
/// # Safety
/// Never called; the caller would have to guarantee no overflow.
pub unsafe fn unchecked_add_probe(a: u32, b: u32) -> u32 {
    //~^ ERROR Trust
    //~| NOTE Trust verification: 0 proved, 0 failed, 1 unknown
    unsafe { intrinsics::unchecked_add(a, b) }
}

/// `unchecked_shl` is UB when the shift is out of range — the same arm again,
/// and the one measured reaching vcgen as `BinOp::ShlUnchecked`.
///
/// # Safety
/// Never called; the caller would have to guarantee an in-range shift.
pub unsafe fn unchecked_shl_probe(a: u32, b: u32) -> u32 {
    //~^ ERROR Trust
    //~| NOTE Trust verification: 0 proved, 0 failed, 1 unknown
    unsafe { intrinsics::unchecked_shl(a, b) }
}
