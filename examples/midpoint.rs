// examples/midpoint.rs — The golden test for Trust verification.
//
// This function contains a real bug: (a + b) can overflow for large values.
// Trust should detect this and provide a counterexample.
// The division by 2 is trivially safe (no division by zero).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

fn get_midpoint(a: usize, b: usize) -> usize {
    (a + b) / 2
}

fn main() {
    // Named binding: the result is intentionally unused in this driver, and the
    // hardened source audit forbids bare `let _ =` discards (HardenedErrorDiscard).
    let _midpoint = get_midpoint(3, 7);
}
