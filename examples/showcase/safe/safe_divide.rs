// examples/showcase/safe/safe_divide.rs — Safe integer division.
//
// Safe variant of verify_div_zero.rs and verify_signed_div_overflow.rs.
// Handles both failure modes of signed integer division:
//   1. Division by zero (y == 0) — panics at runtime
//   2. Signed overflow (x == i32::MIN, y == -1) — result unrepresentable
//
// Uses i32::checked_div() which returns None for both cases.
//
// Trust expected result: PROVED (no DivisionByZero, no ArithmeticOverflow)
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

fn safe_divide(x: i32, y: i32) -> Option<i32> {
    x.checked_div(y) // SAFE: returns None for y==0 and MIN/-1
}

fn main() {
    println!("10 / 3 = {:?}", safe_divide(10, 3));
    println!("10 / 0 = {:?}", safe_divide(10, 0));
    println!("MIN / -1 = {:?}", safe_divide(i32::MIN, -1));
}
