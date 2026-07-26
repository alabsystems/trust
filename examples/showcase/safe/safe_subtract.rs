// examples/showcase/safe/safe_subtract.rs — Safe unsigned subtraction.
//
// Safe variant of verify_sub_overflow.rs.
// Unsigned subtraction underflows when a < b (e.g., 0u32 - 1 wraps to
// 4294967295). Uses u32::checked_sub() which returns None on underflow.
//
// Trust expected result: PROVED (no ArithmeticOverflow on Sub)
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

fn safe_subtract(a: u32, b: u32) -> Option<u32> {
    a.checked_sub(b) // SAFE: returns None when a < b
}

fn main() {
    println!("5 - 3 = {:?}", safe_subtract(5, 3));
    println!("0 - 1 = {:?}", safe_subtract(0, 1));
    println!("3 - 3 = {:?}", safe_subtract(3, 3));
}
