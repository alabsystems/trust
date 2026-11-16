// Trust test: finite float division with a nonzero divisor.
// VcKind: FloatDivisionByZero
// Expected: FloatDivisionByZero ABSENT
// IEEE-754 division by zero is defined, so absence of this obligation is a
// generation assertion, not a proof. Constant finite operands also avoid the
// separate float-overflow case exercised by verify_float_div_zero.rs.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

fn float_divide_safe() -> f64 {
    10.0 / 2.0
}

fn main() {
    let _ = float_divide_safe();
}
