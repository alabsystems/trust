// Trust test: unsigned subtraction underflow
// VcKind: ArithmeticOverflow { op: BinOp::Sub, operand_tys: (Ty::u32(), Ty::u32()) }
// Expected: ArithmeticOverflow(Sub) FAILED
// Counterexample: any pair where a < b (e.g., a = 0, b = 1)
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

fn unsigned_subtract(a: u32, b: u32) -> u32 {
    a - b // BUG: underflows when a < b
}

fn main() {
    // Argv-derived (unknown) inputs: safe constants here would let the R1
    // caller-propagation lane prove the whole program safe and discharge the
    // isolated refutation this example exists to demonstrate.
    let n = std::env::args().len() as u32;
    let _ = unsigned_subtract(n, n + 1);
}
