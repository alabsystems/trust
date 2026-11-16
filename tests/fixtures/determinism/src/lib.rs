//! Determinism acceptance fixture (plan
//! `docs/design/2026-09-29-incremental-deterministic-trust-results.md` §3.8).
//!
//! A small library whose obligations cover the stop causes `targo trust
//! stability` must see decided the same way on every axis: arithmetic that
//! proves, an overflow that is refuted, a bounds check that proves from its
//! guard, a nonlinear overflow, a bounded product whose proof needs real
//! search, and a semiprime factorisation that needs more search than the
//! smallest effort scale allows — the obligation the verb's `effort` axis
//! (`[trust] effort = 1`) must see stop on the COUNT (`effort`), identically
//! idle and under load.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

/// Proves: the halves of two `u32`s cannot overflow when added.
pub fn midpoint(a: u32, b: u32) -> u32 {
    a / 2 + b / 2 + (a % 2 + b % 2) / 2
}

/// Refuted: `u8` addition overflows for `a = b = 200`.
pub fn wrapping_hazard(a: u8, b: u8) -> u8 {
    a + b
}

/// Proves from the guard: the index is checked against the length first.
pub fn guarded_get(values: &[u64], index: usize) -> u64 {
    if index < values.len() { values[index] } else { 0 }
}

/// Nonlinear: the product of two unconstrained `u64`s. Whether the solver
/// decides it or stops on the effort budget, it must decide it the same way
/// every run.
pub fn product(a: u64, b: u64) -> u64 {
    a * b
}

/// Needs search: `(x + y) * (x - y)` over 8-bit inputs widened to `u32` never
/// overflows (at most 510 * 255), but no single propagation shows it — the
/// multiplication has to be reasoned through. Either way it must stop the same
/// way on every run.
pub fn square_difference(a: u8, b: u8) -> u32 {
    let (x, y) = (u32::from(a), u32::from(b));
    if x >= y { (x + y) * (x - y) } else { 0 }
}

/// More search than the smallest effort scale allows (plan §3.2a): the guard
/// keeps both factors below 2^16, so the product cannot wrap, and the assertion
/// fails exactly at the factorisation 65_519 · 65_521 = 4_292_870_399. Under
/// `[trust] effort = 1` — one SAT conflict per distinct query term, a few dozen
/// here — the search stops on `effort`, so the effort axis cannot pass
/// vacuously. Whatever the default decides, it must decide the same way every
/// run.
pub fn semiprime_product(a: u32, b: u32) -> u32 {
    if a > 1 && b > 1 && a < 65_536 && b < 65_536 {
        let product = a * b;
        assert!(product != 4_292_870_399);
        product
    } else {
        0
    }
}

/// A loop whose counter stays in range.
pub fn sum_to(n: u32) -> u64 {
    let mut total: u64 = 0;
    let mut i: u32 = 0;
    while i < n {
        total = total.wrapping_add(u64::from(i));
        i += 1;
    }
    total
}
