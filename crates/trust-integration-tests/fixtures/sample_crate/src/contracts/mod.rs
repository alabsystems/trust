// Functions with specification contracts (#[requires], #[ensures]).
//
// These are the key functions for verification -- they have
// preconditions and postconditions that the verifier checks.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

#[requires(lo <= hi)]
#[ensures(result >= lo)]
#[ensures(result <= hi)]
pub fn clamp(val: i32, lo: i32, hi: i32) -> i32 {
    if val < lo {
        lo
    } else if val > hi {
        hi
    } else {
        val
    }
}

#[ensures(result >= 0)]
pub fn abs(x: i32) -> i32 {
    if x < 0 { -x } else { x }
}

#[ensures(result >= a)]
#[ensures(result >= b)]
pub fn max_i32(a: i32, b: i32) -> i32 {
    if a > b { a } else { b }
}

#[ensures(result <= a)]
#[ensures(result <= b)]
pub fn min_i32(a: i32, b: i32) -> i32 {
    if a < b { a } else { b }
}

#[requires(n <= 20)]
pub fn factorial(n: u64) -> u64 {
    if n == 0 { 1 } else { n * factorial(n - 1) }
}

#[requires(lo <= hi)]
pub fn in_range(val: i32, lo: i32, hi: i32) -> bool {
    val >= lo && val <= hi
}

#[ensures(result > 0)]
pub fn always_positive() -> u32 {
    42
}

#[requires(x != 0)]
#[ensures(result != 0)]
pub fn double_nonzero(x: i32) -> i32 {
    x * 2
}
