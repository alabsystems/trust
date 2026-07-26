// examples/showcase/safe/safe_harmonic_mean.rs — Safe harmonic mean.
//
// Safe variant of T1.3 (t1_3_harmonic_mean_divzero.rs).
// Checks that the denominator (a + b) is not zero before dividing.
// Returns None when a + b == 0.0 (i.e., when a == -b), avoiding the
// silent production of Inf or NaN from IEEE 754 float division by zero.
//
// Trust expected result: PROVED (FloatDivisionByZero cannot occur)
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

fn harmonic_mean(a: f64, b: f64) -> Option<f64> {
    let denom = a + b;
    if denom == 0.0 {
        None // SAFE: explicitly handle the a == -b case
    } else {
        Some(2.0 * a * b / denom)
    }
}

fn main() {
    println!("harmonic_mean(3.0, 6.0) = {:?}", harmonic_mean(3.0, 6.0));
    println!("harmonic_mean(1.0, -1.0) = {:?}", harmonic_mean(1.0, -1.0));
}
