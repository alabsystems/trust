// examples/showcase/safe/safe_narrow_cast.rs — Safe narrowing cast.
//
// Safe variant of T1.5 (t1_5_narrow_cast_overflow.rs) and verify_cast_overflow.rs.
// Uses u8::try_from() instead of `as u8`, which returns Err when the
// value exceeds the target type's range. This replaces silent truncation
// with an explicit, handleable error.
//
// Trust expected result: PROVED (no CastOverflow possible)
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

fn safe_narrow(x: u64) -> Option<u8> {
    u8::try_from(x).ok() // SAFE: returns None when x > 255
}

fn main() {
    println!("narrow(42) = {:?}", safe_narrow(42));
    println!("narrow(256) = {:?}", safe_narrow(256));
    println!("narrow(1000) = {:?}", safe_narrow(1000));
}
