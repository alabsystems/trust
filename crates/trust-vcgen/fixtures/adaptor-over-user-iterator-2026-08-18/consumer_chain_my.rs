#![no_std]
extern crate alloc;
extern crate mycrate;
#[inline(never)]
pub fn boom(v: &mycrate::vec::Vec<u8>) -> alloc::vec::Vec<u64> { v.into_iter().collect() }
