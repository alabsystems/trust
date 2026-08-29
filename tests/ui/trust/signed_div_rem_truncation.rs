//@ needs-trust-verify
//@ proc-macro: trust.rs
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on --crate-type=lib
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE

// Rust signed `/` and `%` truncate toward zero.  The typed-CHC transport must
// not silently give them Euclidean integer semantics: doing so previously
// false-PROVED both deliberately false postconditions below.

extern crate trust;

/// `-1 % 2 == -1`, so signed remainder is not always non-negative.
#[trust::ensures(result >= 0)]
pub fn signed_remainder_is_not_non_negative(x: i32) -> i32 {
    x % 2
}
//~^^^ ERROR Trust Level 0 safety verification incomplete

/// Positive control: Rust's `x % 2` is always in `[-1, 1]`.
#[trust::ensures(result >= -1)]
#[trust::ensures(result <= 1)]
pub fn signed_remainder_bounds_are_true(x: i32) -> i32 {
    x % 2
}

/// Euclidean division gives `-3 div 2 == -2`, but Rust truncates toward zero
/// and returns `-1`.  The old typed-CHC lowering therefore proved this false
/// result equality.
#[trust::requires(x == -3)]
#[trust::ensures(result == -2)]
pub fn signed_division_is_not_floor_division(x: i32) -> i32 {
    x / 2
}
//~^^^ ERROR Trust Level 0 safety verification incomplete

/// Positive control: at the same input the Rust result is exactly `-1`.
#[trust::requires(x == -3)]
#[trust::ensures(result == -1)]
pub fn signed_division_truncation_result_is_true(x: i32) -> i32 {
    x / 2
}
