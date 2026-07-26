// Trust test: multiple bug types in one function
// VcKind: DivisionByZero, ArithmeticOverflow(Add), IndexOutOfBounds
// Expected: DivisionByZero FAILED, ArithmeticOverflow(Add) FAILED, IndexOutOfBounds FAILED
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

fn statistics(data: &[u32; 1], i: usize, denom: u32, x: u32, y: u32) -> u32 {
    let sum = x + y; // BUG 1: ArithmeticOverflow if x + y exceeds u32::MAX
    let scaled = sum / denom; // BUG 2: DivisionByZero when denom == 0
    scaled + data[i] // BUG 3: IndexOutOfBounds when i >= 1
}

fn main() {
    // Argv-derived (unknown) inputs: safe constants here would let the R1
    // caller-propagation lane prove the whole program safe and discharge the
    // isolated refutations this example exists to demonstrate.
    let data = [1];
    let n = std::env::args().len();
    let _ = statistics(&data, n, n as u32 - 1, n as u32, n as u32);
}
