// examples/showcase/t1_5_narrow_cast_overflow.rs — Cast overflow detection.
//
// Trust Showcase T1.5: Narrowing cast from u64 to u8.
// Rust's `as` casts are always truncating in both debug and release mode
// (unlike arithmetic overflow, which panics in debug). The value is silently
// reduced to the low 8 bits. This is well-defined but often unintentional.
//
// What Trust catches:
//   VcKind::CastOverflow { from_ty: u64, to_ty: u8 }
//   Result: FAILED — counterexample: x = 256
//   Any input > 255 triggers silent truncation.
//
// Demonstrates: Narrowing cast safety — catching a class of bugs that Rust's
// built-in overflow checks do not cover.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

fn narrow_cast(x: u64) -> u8 {
    x as u8 // TRUNCATION: silently drops high bits when x > 255
}

fn main() {
    println!("narrow_cast(42) = {}", narrow_cast(42));
    println!("narrow_cast(256) = {}", narrow_cast(256)); // prints 0!
    println!("narrow_cast(1000) = {}", narrow_cast(1000)); // prints 232!
}
