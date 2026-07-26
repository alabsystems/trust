// examples/showcase/safe/safe_negate.rs — Safe signed negation.
//
// Safe variant of verify_neg_overflow.rs.
// Negation of i32::MIN (-2147483648) overflows because 2147483648 > i32::MAX.
// Uses i32::checked_neg() which returns None for i32::MIN.
//
// Trust expected result: PROVED (no NegationOverflow)
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

fn safe_negate(x: i32) -> Option<i32> {
    x.checked_neg() // SAFE: returns None when x == i32::MIN
}

fn main() {
    println!("negate(42) = {:?}", safe_negate(42));
    println!("negate(MIN) = {:?}", safe_negate(i32::MIN));
    println!("negate(0) = {:?}", safe_negate(0));
}
