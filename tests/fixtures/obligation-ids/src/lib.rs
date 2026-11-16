//! Committed-baseline fixture (work item T9). Every obligation here proves, and
//! `checked_div`'s division proves only under its `requires`: removing the
//! clause is the planted loss the acceptance test must catch by key.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

/// Proves: the halves of two `u32`s cannot overflow when added.
pub fn midpoint(a: u32, b: u32) -> u32 {
    a / 2 + b / 2 + (a % 2 + b % 2) / 2
}

/// Proves under its contract: the divisor is never zero.
pub fn checked_div(n: u64, d: u64) -> u64
    requires d > 0
{
    n / d
}

/// Proves from the guard: the index is checked against the length first.
pub fn guarded_get(values: &[u64], index: usize) -> u64 {
    if index < values.len() { values[index] } else { 0 }
}
