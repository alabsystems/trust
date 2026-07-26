// Type conversion and casting operations.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

pub fn u32_to_u64(x: u32) -> u64 {
    x as u64
}

pub fn i32_to_i64(x: i32) -> i64 {
    x as i64
}

pub fn u64_to_usize(x: u64) -> usize {
    x as usize
}

pub fn f64_to_i64(x: f64) -> i64 {
    x as i64
}

pub fn bool_to_u8(b: bool) -> u8 {
    if b { 1 } else { 0 }
}

pub fn char_to_u32(c: char) -> u32 {
    c as u32
}
