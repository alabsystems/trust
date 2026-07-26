// Trust test: precondition violation at call site
// VcKind: Precondition { callee: "reciprocal" }
// Expected: Precondition FAILED
// NOTE: This single-file regression example still uses the legacy contracts
// surface. New crate-based public examples should prefer `trust-spec` and
// `#[trust::requires(...)]`.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

#![feature(contracts)]

extern crate core;

use core::contracts::requires;

#[requires(n > 0)]
fn reciprocal(n: u32) -> f64 {
    1.0 / (n as f64)
}

fn caller(x: u32) -> f64 {
    reciprocal(x) // BUG: caller does not check x > 0
}

fn main() {
    // Argv-derived (unknown) inputs: safe constants here would let the R1
    // caller-propagation lane prove the whole program safe and discharge the
    // isolated refutation this example exists to demonstrate.
    let n = std::env::args().len() as u32;
    let _ = caller(n);
}
