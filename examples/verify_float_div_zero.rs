// Trust test: float division by zero is TOTAL (no obligation)
// VcKind: FloatDivisionByZero
// Expected: FloatDivisionByZero ABSENT
// IEEE-754 float division never traps: x/0.0 yields +/-inf or NaN — defined
// behavior carries no L0 safety obligation (DESIGN_PHILOSOPHY §9; emitting the
// refutation rejected ubiquitous valid Rust). Only INTEGER division keeps its
// division-by-zero obligation (see verify_div_zero.rs).
// ABSENT is a generation assertion: it forbids a FloatDivisionByZero transport
// row; it does not relabel absence as a proof.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

fn float_divide(x: f64, y: f64) -> f64 {
    x / y // BUG: produces +/-Inf when y == 0.0
}

fn main() {
    let _ = float_divide(10.0, 3.0);
}
