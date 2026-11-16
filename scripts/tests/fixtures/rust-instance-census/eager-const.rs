#![no_std]
#![allow(dead_code)]

#[inline(never)]
fn identity<T>(value: T) -> T {
    value
}

// With no use_root, this is the only source of identity::<u8> in eager collection.
const ROOT: fn(u8) -> u8 = identity::<u8>;

#[cfg(empty_root)]
const EMPTY_ROOT: u8 = 9;

#[cfg(alias_root)]
const ALIAS_ROOT: fn(u8) -> u8 = identity::<u8>;

pub fn anchor(value: u8) -> u8 {
    #[cfg(use_root)]
    {
        ROOT(value)
    }
    #[cfg(not(use_root))]
    {
        value
    }
}
