// Trust test: remainder by zero
// VcKind: RemainderByZero
// Expected: RemainderByZero FAILED
// Counterexample: y = 0
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

fn modulo(x: u32, y: u32) -> u32 {
    x % y // BUG: panics when y == 0
}

fn main() {
    // Argv-derived (unknown) inputs: safe constants here would let the R1
    // caller-propagation lane prove the whole program safe and discharge the
    // isolated refutation this example exists to demonstrate.
    let n = std::env::args().len() as u32;
    let _ = modulo(n, n - 1);
}
