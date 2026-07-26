// Const functions: compile-time evaluable operations.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

pub const fn const_add(a: u32, b: u32) -> u32 {
    a.wrapping_add(b)
}

pub const fn const_max(a: u32, b: u32) -> u32 {
    if a > b { a } else { b }
}

pub const fn const_min(a: u32, b: u32) -> u32 {
    if a < b { a } else { b }
}

pub const fn const_clamp(val: u32, lo: u32, hi: u32) -> u32 {
    if val < lo {
        lo
    } else if val > hi {
        hi
    } else {
        val
    }
}

pub const fn const_is_zero(x: u32) -> bool {
    x == 0
}

pub const fn const_abs_i32(x: i32) -> i32 {
    if x < 0 { -x } else { x }
}

const fn internal_const_helper(x: u32) -> u32 {
    x + 1
}

pub const fn const_inc(x: u32) -> u32 {
    internal_const_helper(x)
}
