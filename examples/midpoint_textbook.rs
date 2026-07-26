// examples/midpoint_textbook.rs — Textbook fix (Bloch 2006) for midpoint overflow.
//
// This is the well-known fix: a/2 + b/2 + (a%2 + b%2)/2.
// Mathematically correct — max value is exactly usize::MAX.
// Before the VC fix (collect_prior_range_facts), Trust falsely rejected this
// because each operation was checked in isolation without value-range context.
// With the fix, Trust should PROVE this safe.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

fn get_midpoint(a: usize, b: usize) -> usize {
    a / 2 + b / 2 + (a % 2 + b % 2) / 2
}

fn main() {
    let _ = get_midpoint(3, 7);
}
