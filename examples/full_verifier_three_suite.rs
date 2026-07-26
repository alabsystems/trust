#![allow(dead_code)]
#![expect(incomplete_features)]
#![feature(contracts)]
#![crate_type = "staticlib"]

extern crate core;

use core::contracts::{ensures, requires};

#[requires(numerator >= 0 && denominator > 0)]
#[ensures(|ret| *ret >= 0)]
#[unsafe(no_mangle)]
pub fn nonnegative_divide(numerator: i32, denominator: i32) -> i32 {
    numerator / denominator
}

#[requires(low <= high)]
#[ensures(move |ret| *ret >= low)]
#[unsafe(no_mangle)]
pub fn midpoint_no_underflow(low: u32, high: u32) -> u32 {
    low + (high - low) / 2
}

#[unsafe(no_mangle)]
pub fn read_fixed_array_value(values: [i32; 4]) -> i32 {
    values[0]
}
