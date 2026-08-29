// Source of the SIGNED zero-divisor real-MIR fixtures, consumed by
// `signed_divzero_chain_tests` in `src/generate/checked_vcs.rs`. Same convention
// as `shift_arms.rs` beside it (see README.md for the family as a whole).
//
//   trustc --edition 2021 --crate-type lib -Ztrust-dump=mir:<dir> \
//          crates/trust-vcgen/tests/data/signed_div_arms.rs
//
// One `<fn name>.json` per function below, the compiler's own extracted
// verification input, verbatim except for `span.file` — rewritten from the
// absolute compile path to this file's repo-relative name. Line numbers are this
// file's, so every row re-derives.
//
// MEASURE FROM THIS DUMP, NOT FROM `--emit=mir`. The pretty-printer folds the
// divisor's copy away and shows `_3 = move (_5.0); Div(copy _3, ..)`, which makes
// the projected-operand shape look like a plain local. The extracted input keeps
// it as `Div(Copy{local 3, projections:[Field 0]}, ..)`, and that projection is
// exactly what the chain's compared-value binder has to tolerate.
#![allow(unconditional_panic, unused)]

/// The canary, at the SIGNED width. `n - n` is provably zero, so this is a
/// genuinely-false division by zero. Twin of `vacuity_sentinel.rs`'s `u64` case.
#[inline(never)]
pub fn sentinel_signed_div_by_zero_must_not_prove(x: i64, n: i64) -> i64 {
    x / (n - n)
}

/// The `Rem` member of the same family — the suppression is per-opcode.
#[inline(never)]
pub fn sentinel_signed_rem_by_zero_must_not_prove(x: i64, n: i64) -> i64 {
    x % (n - n)
}

/// A plain unconstrained signed divisor at a narrower width, so the chain's
/// `INT_MIN` recovery is exercised at 32 bits as well as 64.
#[inline(never)]
pub fn unguarded_signed_division(a: i32, b: i32) -> i32 {
    a / b
}

/// Two distinct divisors, two chains, two real obligations. A skip keyed on the
/// BLOCK rather than on the DIVISOR silently drops one of them.
#[inline(never)]
pub fn two_distinct_signed_divisors(x: i32, y: i32, z: i32) -> i32 {
    let p = x / y;
    p / z
}

/// Genuinely safe and genuinely dischargeable: `n | 1` is odd, hence nonzero.
/// The surface must still carry ONE real obligation for it — a suppression that
/// deleted the safe case's obligation instead of proving it is not a fix.
#[inline(never)]
pub fn provably_safe_signed_division(x: i32, n: i32) -> i32 {
    x / (n | 1)
}

/// The UNSIGNED control: no intervening overflow assert, so this must keep going
/// through the one-hop rule untouched by the chain.
#[inline(never)]
pub fn unsigned_control(x: u64, n: u64) -> u64 {
    x / (n - n)
}

/// An unsigned division whose divisor still needs an obligation — pins that the
/// chain's signedness gate did not change the unsigned surface.
#[inline(never)]
pub fn unguarded_unsigned_division(a: u32, b: u32) -> u32 {
    a / b
}

/// THE SAFE CASE THE MANDATE NAMES, in this family: a user-guarded division that
/// yields proved+proved where ONE IS HONEST. rustc cannot discharge `d != 0` at
/// MIR-build time, so it still emits the whole chain — but the surviving
/// assert-lane row sits under the `SwitchInt` guard and IS dischargeable, while
/// the suppressed statement row is the vacuous twin. Deleting the honest one
/// would be a lost recovery, not a fix.
#[inline(never)]
pub fn guarded_signed_division(x: i32, d: i32) -> i32 {
    if d != 0 { x / d } else { 0 }
}
