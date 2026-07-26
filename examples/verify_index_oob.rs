// Trust test: array index out of bounds
// VcKind: IndexOutOfBounds
// Expected: IndexOutOfBounds FAILED
// Counterexample: any idx >= 10
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

fn lookup(arr: [u32; 10], idx: usize) -> u32 {
    arr[idx] // BUG: panics when idx >= 10
}

fn main() {
    // Argv-derived (unknown) inputs: safe constants here would let the R1
    // caller-propagation lane prove the whole program safe and discharge the
    // isolated refutation this example exists to demonstrate.
    let arr = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9];
    let n = std::env::args().len();
    let _ = lookup(arr, n);
}
