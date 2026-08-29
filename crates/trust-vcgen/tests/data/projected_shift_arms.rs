// Source of the PROJECTED-AMOUNT shift real-MIR fixtures in this directory. See
// README.md.
//
//   trustc --edition 2021 --crate-type lib -Ztrust-dump=mir:<dir> \
//          crates/trust-vcgen/tests/data/projected_shift_arms.rs
//
// Every `projected_*`/`*_projected_*` `*.json` beside this file is the dump of
// one function below, verbatim except for `span.file`, rewritten from the
// absolute compile path to this file's repo-relative name. Line numbers are
// this file's.
#![allow(unconditional_panic, unused)]

/// The canary. `t = (x | 64) + 1 >= 65 >= 32`, so `1u32 << t` is genuinely UB.
/// The `+ 1` is what makes the amount PROJECTED: rustc compares, and shifts by,
/// the value field of the `CheckedAdd` tuple (`_2.0`).
#[inline(never)]
pub fn sentinel_projected_shift_overflow_must_not_prove(x: u32) -> u32 {
    let t = (x | 64) + 1;
    1u32 << t
}

/// The `Shr` member of the same family — the suppression is per-opcode.
#[inline(never)]
pub fn sentinel_projected_shr_overflow_must_not_prove(x: u32) -> u32 {
    let t = (x | 64) + 1;
    x >> t
}

/// Genuinely SAFE: the amount is masked into range before the increment, so the
/// surviving obligation is real AND dischargeable.
#[inline(never)]
pub fn provably_safe_projected_shift(s: u32) -> u32 {
    let t = (s & 15) + 1;
    1u32 << t
}

/// A wholly unconstrained projected amount: neither provable nor refutable, and
/// the obligation must survive.
#[inline(never)]
pub fn unguarded_projected_shift(x: u32, s: u32) -> u32 {
    let t = s + 1;
    x << t
}

/// Two distinct projected amounts, two asserts, two real obligations.
#[inline(never)]
pub fn two_distinct_projected_shift_amounts(x: u32, s: u32, t: u32) -> u32 {
    (x << (s + 1)) ^ (x << (t + 1))
}

/// A field-projected amount read straight out of a parameter tuple: no checked
/// arithmetic anywhere, so the projection is the ONLY non-canonical thing about
/// it.
#[inline(never)]
pub fn tuple_field_projected_shift(p: (u32, u32)) -> u32 {
    1u32 << p.0
}
