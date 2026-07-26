// examples/showcase/safe/safe_shift.rs — Safe bit shift.
//
// Safe variant of verify_shift_overflow.rs.
// Shifting a u32 by >= 32 bits is undefined behavior in C and panics
// in Rust debug mode (wraps in release). Uses u32::checked_shl()
// which returns None when the shift amount exceeds the bit width.
//
// Trust expected result: PROVED (no ShiftOverflow)
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

fn safe_shift_left(x: u32, shift: u32) -> Option<u32> {
    x.checked_shl(shift) // SAFE: returns None when shift >= 32
}

fn main() {
    println!("1 << 4 = {:?}", safe_shift_left(1, 4));
    println!("1 << 31 = {:?}", safe_shift_left(1, 31));
    println!("1 << 32 = {:?}", safe_shift_left(1, 32));
}
