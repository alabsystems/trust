// Trust test: left shift overflow
// VcKind: ShiftOverflow { op: BinOp::Shl, operand_ty: Ty::u32(), shift_ty: Ty::u32() }
// Expected: ShiftOverflow(Shl) FAILED
// Counterexample: any shift >= 32 for u32
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

fn shift_left(x: u32, shift: u32) -> u32 {
    x << shift // BUG: panics in debug mode / wraps in release when shift >= 32
}

fn main() {
    // Argv-derived (unknown) inputs: safe constants here would let the R1
    // caller-propagation lane prove the whole program safe and discharge the
    // isolated refutation this example exists to demonstrate.
    let n = std::env::args().len() as u32;
    let _ = shift_left(n, n + 3);
}
