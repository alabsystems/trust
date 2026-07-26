// examples/showcase/safe/safe_midpoint.rs — Safe midpoint calculation.
//
// Safe variant of T1.1 (t1_1_midpoint_overflow.rs).
// Uses the textbook-correct formula: a/2 + b/2 + (a%2 + b%2)/2
// This avoids the (a + b) overflow entirely. The maximum intermediate
// value is MAX/2 + MAX/2 + 1 = MAX, so no overflow is possible.
//
// Trust expected result: PROVED (all VCs satisfied)
//
// Reference: Joshua Bloch, "Extra, Extra — Read All About It: Nearly All
// Binary Searches and Mergesorts are Broken" (2006).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

fn safe_midpoint(a: usize, b: usize) -> usize {
    a / 2 + b / 2 + (a % 2 + b % 2) / 2
}

fn main() {
    println!("midpoint(3, 7) = {}", safe_midpoint(3, 7));
    println!("midpoint(MAX, MAX) = {}", safe_midpoint(usize::MAX, usize::MAX));
    println!("midpoint(0, 0) = {}", safe_midpoint(0, 0));
}
