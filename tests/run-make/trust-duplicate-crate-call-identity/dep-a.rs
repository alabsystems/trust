#![feature(contracts)]

extern crate core;
use core::contracts::requires;

#[derive(Copy, Clone)]
pub struct Marker(pub i32);

#[inline(never)]
#[requires(x > 0)]
pub fn contracted(x: i32) -> i32 {
    x
}

#[inline(never)]
pub fn generic<T: Copy>(x: T) -> T {
    x
}

#[inline(never)]
pub fn arg_identity<T: Copy>(x: T) -> T {
    x
}

#[inline(never)]
#[requires(true)]
pub fn contracted_generic<T: Copy>(x: T) -> T {
    x
}
