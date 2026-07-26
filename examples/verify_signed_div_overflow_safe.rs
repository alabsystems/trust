// Trust test: signed division overflow -- safe variant
// VcKind: DivisionByZero AND ArithmeticOverflow { op: BinOp::Div }
// Expected: DivisionByZero PROVED AND ArithmeticOverflow(Div) PROVED
//           (guards prove both zero-divisor and MIN/-1 cases unreachable)
// Safe pattern: if-guard checks both y == 0 and (x == i32::MIN && y == -1)
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

fn signed_divide_safe(x: i32, y: i32) -> i32 {
    if y == 0 || (x == i32::MIN && y == -1) {
        0 // fallback for div-by-zero or overflow
    } else {
        x / y // SAFE: guard prevents both failure modes
    }
}

fn main() {
    let _ = signed_divide_safe(10, 3);
    let _ = signed_divide_safe(10, 0); // div-by-zero fallback
    let _ = signed_divide_safe(i32::MIN, -1); // overflow fallback
}
