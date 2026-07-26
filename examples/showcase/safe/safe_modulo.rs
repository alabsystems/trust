// examples/showcase/safe/safe_modulo.rs — Safe remainder operation.
//
// Safe variant of verify_rem_zero.rs.
// The remainder operator `%` panics when the divisor is zero.
// Uses u32::checked_rem() which returns None for zero divisor.
//
// Trust expected result: PROVED (no RemainderByZero)
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

fn safe_modulo(x: u32, y: u32) -> Option<u32> {
    x.checked_rem(y) // SAFE: returns None when y == 0
}

fn main() {
    println!("10 % 3 = {:?}", safe_modulo(10, 3));
    println!("10 % 0 = {:?}", safe_modulo(10, 0));
    println!("7 % 1 = {:?}", safe_modulo(7, 1));
}
