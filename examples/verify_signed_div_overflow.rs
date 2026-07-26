// Trust test: signed division overflow (i32::MIN / -1)
// VcKind: DivisionByZero; signed division overflow lowering is not emitted on the default compiler path yet
// Expected: DivisionByZero FAILED
// Counterexample: y = 0
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

fn signed_divide(x: i32, y: i32) -> i32 {
    x / y // BUG: panics when y == 0; overflows when x == i32::MIN and y == -1
}

fn main() {
    // Argv-derived (unknown) inputs: safe constants here would let the R1
    // caller-propagation lane prove the whole program safe and discharge the
    // isolated refutation this example exists to demonstrate.
    let n = std::env::args().len() as i32;
    let _ = signed_divide(n, n - 1);
}
