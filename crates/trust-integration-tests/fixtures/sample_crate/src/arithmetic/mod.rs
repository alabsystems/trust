// Arithmetic operations: wrapping, checked, saturating, division.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

pub fn wrapping_add(a: u64, b: u64) -> u64 {
    a.wrapping_add(b)
}

pub fn wrapping_sub(a: u64, b: u64) -> u64 {
    a.wrapping_sub(b)
}

pub fn wrapping_mul(a: u64, b: u64) -> u64 {
    a.wrapping_mul(b)
}

pub fn checked_add(a: u64, b: u64) -> Option<u64> {
    a.checked_add(b)
}

pub fn checked_sub(a: u64, b: u64) -> Option<u64> {
    a.checked_sub(b)
}

pub fn checked_mul(a: u64, b: u64) -> Option<u64> {
    a.checked_mul(b)
}

pub fn saturating_add(a: u32, b: u32) -> u32 {
    a.saturating_add(b)
}

pub fn saturating_mul(a: u32, b: u32) -> u32 {
    a.saturating_mul(b)
}

pub fn safe_divide(dividend: u32, divisor: u32) -> Option<u32> {
    if divisor == 0 {
        None
    } else {
        Some(dividend / divisor)
    }
}

pub fn safe_rem(n: u32, m: u32) -> Option<u32> {
    if m == 0 {
        None
    } else {
        Some(n % m)
    }
}

pub fn abs_diff(a: i64, b: i64) -> u64 {
    if a > b {
        (a - b) as u64
    } else {
        (b - a) as u64
    }
}

pub fn midpoint(a: usize, b: usize) -> usize {
    a / 2 + b / 2 + (a % 2 + b % 2) / 2
}

pub fn clamp_u32(val: u32, lo: u32, hi: u32) -> u32 {
    if val < lo {
        lo
    } else if val > hi {
        hi
    } else {
        val
    }
}

pub fn is_power_of_two(n: u32) -> bool {
    n != 0 && (n & (n - 1)) == 0
}

fn helper_square(x: u32) -> u64 {
    (x as u64) * (x as u64)
}

pub fn sum_of_squares(a: u32, b: u32) -> u64 {
    helper_square(a) + helper_square(b)
}
