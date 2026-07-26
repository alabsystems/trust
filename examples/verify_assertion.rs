// Trust test: assertion violation
// VcKind: Assertion { message: "sqrt requires non-negative input" }
// Expected: Assertion FAILED
// Counterexample: x = -1 (or any x < 0)
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

fn checked_sqrt_approx(x: i32) -> i32 {
    assert!(x >= 0, "sqrt requires non-negative input");
    x
}

fn caller(val: i32) -> i32 {
    checked_sqrt_approx(val) // BUG: val may be negative
}

fn main() {
    // Argv-derived (unknown) inputs: safe constants here would let the R1
    // caller-propagation lane prove the whole program safe and discharge the
    // isolated refutation this example exists to demonstrate.
    let n = std::env::args().len() as i32;
    let _ = caller(n);
}
