// examples/showcase/safe/safe_assertion.rs — Safe input validation.
//
// Safe variant of verify_assertion.rs.
// The buggy version passes unchecked input to a function with an
// assert!(x >= 0) precondition. This version validates the input
// at the call site, returning None for negative values instead of
// relying on a runtime assertion panic.
//
// Trust expected result: PROVED (assertion never violated)
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

fn checked_sqrt_approx(x: i32) -> i32 {
    assert!(x >= 0, "sqrt requires non-negative input");
    x // placeholder for actual sqrt computation
}

fn safe_caller(val: i32) -> Option<i32> {
    if val >= 0 {
        Some(checked_sqrt_approx(val)) // SAFE: precondition satisfied
    } else {
        None // SAFE: reject negative input at call site
    }
}

fn main() {
    println!("safe_caller(4) = {:?}", safe_caller(4));
    println!("safe_caller(-1) = {:?}", safe_caller(-1));
    println!("safe_caller(0) = {:?}", safe_caller(0));
}
