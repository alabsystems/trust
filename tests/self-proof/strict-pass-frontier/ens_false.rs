#![no_std]
#![expect(incomplete_features)]
#![feature(contracts)]
//! MUTATION CONTROL for `ens.rs`. Body byte-identical; the postcondition is
//! negated so it is FALSE.
//!
//! `ens.rs` asserts `ret <= n` and the verifier reports one `[postcondition]
//! PROVED (kernel-rechecked)` row. That row is only evidence if the same
//! machinery REFUTES the false twin. Here the clause is `ret > n`, which the
//! `d == 0` arm falsifies outright (it returns `0`, and `0 > n` is false for
//! every `u32` including `n == 0`), and which `n / d > n` falsifies for every
//! `d >= 1`.
//!
//! EXPECTED: the `[postcondition]` row must NOT be PROVED. If it still proves,
//! the PROVED row in `ens.rs` is a rubber stamp and no postcondition
//! measurement in this directory means anything.
use core::contracts::ensures;

#[ensures(move |ret: &u32| *ret > n)]
pub fn udiv_guarded(n: u32, d: u32) -> u32 {
    if d == 0 {
        return 0;
    }
    n / d
}
