#![no_std]
#![expect(incomplete_features)]
#![feature(contracts)]
//! CONTROLLED EXPERIMENT — one variable against `pass.rs`.
//!
//! Body is BYTE-IDENTICAL to `pass.rs`, which is measured at
//! `Gate: PASS [strict lane, exit 0]`, `2 proved, 0 unknown (2 total)`.
//! The single change is one added `#[ensures(..)]` clause.
//!
//! The postcondition is TRUE: if `d == 0` the function returns `0`, and
//! `0 <= n` for every `u32`. Otherwise `d >= 1`, and unsigned division by a
//! divisor `>= 1` is non-increasing, so `n / d <= n`. Both arms therefore
//! satisfy `ret <= n`.
//!
//! QUESTION: does adding a true, provable postcondition to a crate that
//! PASSES the strict lane keep it passing?
//!
//! MEASURED HERE: no — THIS fixture goes to exit 1.
//!
//! DO NOT GENERALIZE THAT. An earlier revision of this comment concluded
//! "contracts are structurally incompatible with a strict pass, and 'write
//! more contracts' cannot be the lever for any crate". **That is FALSE and was
//! refuted by `multi.rs` in this same directory**, which carries a grammar
//! `ensures result <= 100` and measures:
//!
//!   exit 0 · Gate: PASS [strict lane] · Coverage 2/2 (complete)
//!   4 proved, 0 failed, 0 runtime-checked, 0 assumed, 0 inconclusive
//!   rows: 2x [PROVED] [postcond] (kernel-rechecked), [PROVED] [divzero],
//!         [PROVED] [hardened_panic_boundary] — ZERO `unreachable`
//!
//! So the `trust-exact-source-clause-discharge` marker DOES discharge; it is
//! absent from the passing run, not UNKNOWN. What fails HERE is narrower: one
//! PER-BRANCH postcondition VC (`n / d <= n`, unsigned-division
//! non-increasing) is Inconclusive on the native trust-mc lane. That is a
//! solver-coverage gap for one shape, not a property of contracts.
//!
//! The general lesson this fixture exists to teach: a single fixture measures
//! a single shape. Reaching from it to "for any crate" is the
//! stated-premise-never-tested error this repo keeps paying for.
use core::contracts::ensures;

#[ensures(move |ret: &u32| *ret <= n)]
pub fn udiv_guarded(n: u32, d: u32) -> u32 {
    if d == 0 {
        return 0;
    }
    n / d
}
