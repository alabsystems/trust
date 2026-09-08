#![allow(dead_code)]
pub fn sh_safe(a: u32, k: u32) -> u32 { a << (k & 31) }
