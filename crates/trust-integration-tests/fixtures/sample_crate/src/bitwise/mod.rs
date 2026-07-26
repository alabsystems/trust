// Bitwise operations: shifts, masks, bit counting.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

pub fn count_ones(x: u32) -> u32 {
    x.count_ones()
}

pub fn count_zeros_u32(x: u32) -> u32 {
    x.count_zeros()
}

pub fn leading_zeros(x: u32) -> u32 {
    x.leading_zeros()
}

pub fn trailing_zeros(x: u32) -> u32 {
    x.trailing_zeros()
}

pub fn rotate_left(x: u32, n: u32) -> u32 {
    x.rotate_left(n)
}

pub fn rotate_right(x: u32, n: u32) -> u32 {
    x.rotate_right(n)
}

pub fn set_bit(x: u32, bit: u32) -> u32 {
    x | (1 << bit)
}

pub fn clear_bit(x: u32, bit: u32) -> u32 {
    x & !(1 << bit)
}

pub fn test_bit(x: u32, bit: u32) -> bool {
    (x >> bit) & 1 == 1
}
