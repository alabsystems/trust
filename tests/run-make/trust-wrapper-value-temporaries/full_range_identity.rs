#![crate_type = "lib"]
use std::ops::RangeFull;

pub fn builtin_literal() -> usize {
    let array = [7u32];
    let slice = &array[..];
    slice.len()
}

pub fn builtin_bound() -> usize {
    let array = [7u32];
    let full = ..;
    let slice = &array[full];
    slice.len()
}

fn custom<'a>(_: &'a [u32; 1], _: RangeFull) -> &'a [u32] { &[] }

pub fn custom_call_is_not_index() -> usize {
    let value = [7u32];
    let slice = &*custom(&value, ..);
    slice.len()
}

pub fn effectful_range_is_not_erased() -> u32 {
    let mut count = 0u32;
    let array = [7u32];
    let _slice = &array[{ count += 1; .. }];
    count
}

pub fn effectful_callee_is_not_erased() -> u32 {
    let value = [7u32];
    let mut count = 0u32;
    let _slice = &*({ count += 1; custom })(&value, ..);
    count
}
