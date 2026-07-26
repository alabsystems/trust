// Trust test: integer multiplication overflow
// VcKind: ArithmeticOverflow { op: BinOp::Mul, operand_tys: (Ty::u32(), Ty::u32()) }
// Expected: ArithmeticOverflow(Mul) FAILED
// Counterexample: any pair where width * height > u32::MAX
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

fn area(width: u32, height: u32) -> u32 {
    width * height // BUG: overflows for large dimensions
}

fn main() {
    // Argv-derived (unknown) inputs: safe constants here would let the R1
    // caller-propagation lane prove the whole program safe and discharge the
    // isolated refutation this example exists to demonstrate.
    let n = std::env::args().len() as u32;
    let _ = area(n, n);
}
