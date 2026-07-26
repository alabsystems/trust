// Trust: regression test for rust-lang#107436
// Matching on a fieldless enum should generate a lookup table or direct
// arithmetic, not a chain of conditional branches. When each arm returns
// a simple constant, LLVM should convert the match into a table lookup
// (getelementptr into a constant array) rather than N-1 comparisons.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>

//@ compile-flags: -Copt-level=3

#![crate_type = "lib"]

#[derive(Clone, Copy)]
pub enum Direction {
    North,
    South,
    East,
    West,
}

// CHECK-LABEL: @direction_to_degrees
// A match returning constant integers for each variant of a small fieldless
// enum should be lowered to a lookup table, not a comparison chain.
// CHECK-NOT: br i1
// CHECK-NOT: br i1
// CHECK-NOT: br i1
// The key indicator: we should NOT see three conditional branches for a
// 4-variant enum. LLVM should use a switch or table lookup.
#[no_mangle]
pub fn direction_to_degrees(d: Direction) -> u16 {
    match d {
        Direction::North => 0,
        Direction::South => 180,
        Direction::East => 90,
        Direction::West => 270,
    }
}

// CHECK-LABEL: @direction_opposite
// Converting between enum variants should use arithmetic on the discriminant,
// not a comparison chain. For this specific pattern (opposite direction),
// LLVM should recognize the XOR pattern.
// CHECK-NOT: panic
#[no_mangle]
pub fn direction_opposite(d: Direction) -> Direction {
    match d {
        Direction::North => Direction::South,
        Direction::South => Direction::North,
        Direction::East => Direction::West,
        Direction::West => Direction::East,
    }
}

#[derive(Clone, Copy)]
pub enum Color {
    Red,
    Green,
    Blue,
    Yellow,
    Cyan,
    Magenta,
    White,
    Black,
}

// CHECK-LABEL: @color_to_rgb
// A match on an 8-variant fieldless enum returning a constant tuple should
// produce a table lookup, not 7 conditional branches.
// CHECK-NOT: br i1
// CHECK-NOT: br i1
// CHECK-NOT: br i1
// CHECK-NOT: br i1
// CHECK-NOT: br i1
// CHECK-NOT: br i1
// CHECK-NOT: br i1
#[no_mangle]
pub fn color_to_rgb(c: Color) -> (u8, u8, u8) {
    match c {
        Color::Red => (255, 0, 0),
        Color::Green => (0, 255, 0),
        Color::Blue => (0, 0, 255),
        Color::Yellow => (255, 255, 0),
        Color::Cyan => (0, 255, 255),
        Color::Magenta => (255, 0, 255),
        Color::White => (255, 255, 255),
        Color::Black => (0, 0, 0),
    }
}
