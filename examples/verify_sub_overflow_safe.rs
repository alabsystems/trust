// Trust test: unsigned subtraction -- safe variant
// VcKind: ArithmeticOverflow { op: BinOp::Sub, operand_tys: (Ty::u32(), Ty::u32()) }
// Expected: ArithmeticOverflow(Sub) PROVED (guard proves no underflow)
// Safe pattern: if-guard `a >= b` ensures a - b cannot underflow
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

fn unsigned_subtract_safe(a: u32, b: u32) -> u32 {
    if a >= b {
        a - b // SAFE: guard ensures a >= b, so no underflow
    } else {
        0 // fallback for underflow case
    }
}

fn main() {
    let _ = unsigned_subtract_safe(5, 3);
    let _ = unsigned_subtract_safe(1, 10); // takes else branch
}
