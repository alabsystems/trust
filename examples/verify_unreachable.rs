// Trust test: unreachable code reached
// VcKind: Unreachable
// Expected: Unreachable FAILED
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

fn classify(x: u32) -> &'static str {
    match x {
        0 => "zero",
        1..=100 => "small",
        _ => unreachable!("value too large"), // BUG: reachable for x > 100
    }
}

fn main() {
    // Argv-derived (unknown) inputs: safe constants here would let the R1
    // caller-propagation lane prove the whole program safe and discharge the
    // isolated refutation this example exists to demonstrate.
    let n = std::env::args().len() as u32;
    let _ = classify(n);
}
