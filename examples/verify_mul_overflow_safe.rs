// Trust test: integer multiplication -- safe variant
// VcKind: ArithmeticOverflow { op: BinOp::Mul, operand_tys: (Ty::u32(), Ty::u32()) }
// Expected: ArithmeticOverflow(Mul) PROVED (literal product fits in u32)
// Safe pattern: finite literals keep the multiplication VC focused on a
// statically-provable non-overflowing operation.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

fn area_safe() -> u32 {
    100u32 * 200u32 // SAFE: literal product fits in u32
}

fn main() {
    let _ = area_safe();
}
