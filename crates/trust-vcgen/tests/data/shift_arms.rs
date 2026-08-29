// Source of the SHIFT-family real-MIR fixtures in this directory. See README.md.
//
//   trustc --edition 2021 --crate-type lib -Ztrust-dump=mir:<dir> \
//          crates/trust-vcgen/tests/data/shift_arms.rs
//
// Every `*.json` beside this file is the dump of one function below, verbatim
// except for `span.file`, rewritten from the absolute compile path to this
// file's repo-relative name. Line numbers are this file's.
#![allow(unconditional_panic, unused)]

/// The canary. `s = x | 64 >= 64 >= 32`, so `1u32 << s` is genuinely UB.
/// Verbatim from `clean/tests/trust_verify/vacuity_sentinel.rs`.
#[inline(never)]
pub fn sentinel_shift_overflow_must_not_prove(x: u32) -> u32 {
    let s = x | 64;
    1u32 << s
}

/// The `Shr` member of the same family — the suppression is per-opcode.
#[inline(never)]
pub fn sentinel_shr_overflow_must_not_prove(x: u32) -> u32 {
    let s = x | 64;
    x >> s
}

/// Two distinct shift amounts, two asserts, two real obligations.
#[inline(never)]
pub fn two_distinct_shift_amounts(x: u32, s: u32, t: u32) -> u32 {
    (x << s) ^ (x << t)
}

/// Genuinely safe: the amount is masked into range, so the surviving
/// obligation is real AND dischargeable.
#[inline(never)]
pub fn provably_safe_shift(x: u32, s: u32) -> u32 {
    x << (s & 31)
}

/// A wholly unconstrained shift amount: neither provable nor refutable, and
/// the obligation must survive.
#[inline(never)]
pub fn unguarded_shift(x: u32, s: u32) -> u32 {
    x << s
}

/// A CONSTANT in-range amount. rustc still emits an assert, but over a cast
/// TEMPORARY (`_2 = 8 as u32; _3 = Lt(_2, 32)`) while the shift statement reads
/// the constant directly — so no exact binding exists and the per-statement row
/// must survive untouched.
#[inline(never)]
pub fn constant_amount_shift(x: u32) -> u32 {
    x << 8
}
