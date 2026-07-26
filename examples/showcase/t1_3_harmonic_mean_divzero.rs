// examples/showcase/t1_3_harmonic_mean_divzero.rs — Float division by zero.
//
// Trust Showcase T1.3: Division by zero in a mathematical function.
// The harmonic mean formula 2ab/(a+b) divides by zero when a == -b.
// Unlike integer division by zero (which panics), float division by zero
// silently produces Inf or NaN — a subtle source of downstream bugs.
//
// What Trust catches:
//   VcKind::FloatDivisionByZero — on `/ (a + b)`
//   Result: FAILED — counterexample includes a + b == 0.0 (e.g., a = 1.0, b = -1.0)
//
// Caveat: Float verification uses integer approximation. The VC checks
// divisor == 0 using integer encoding, which is numerically correct for this
// case but does not model IEEE 754 rounding, NaN propagation, or signed zero.
//
// Demonstrates: Float division safety detection (with documented precision limits).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

fn harmonic_mean(a: f64, b: f64) -> f64 {
    2.0 * a * b / (a + b) // DIV BY ZERO when a == -b
}

fn main() {
    println!("harmonic_mean(3.0, 6.0) = {}", harmonic_mean(3.0, 6.0));
    // harmonic_mean(1.0, -1.0) would produce Inf
}
