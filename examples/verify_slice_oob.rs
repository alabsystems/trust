// Trust test: slice access on potentially empty slice
// VcKind: SliceBoundsCheck
// Expected: SliceBoundsCheck FAILED
// Counterexample: data with len == 0
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

fn first(data: &[u32]) -> u32 {
    data[0] // BUG: panics when data is empty
}

fn main() {
    // Argv-derived (unknown) inputs: safe constants here would let the R1
    // caller-propagation lane prove the whole program safe and discharge the
    // isolated refutation this example exists to demonstrate.
    let n = std::env::args().len();
    let data = vec![1u32; n];
    let _ = first(&data);
}
