#![allow(dead_code)]
pub fn arith(a: i32, b: i32) -> i32 { let s = a + b; let d = a / b; s * d }
pub fn remu(a: u32, b: u32) -> u32 { a % b }
pub fn remu_safe(a: u32, b: u32) -> u32 { a % (b | 1) }
pub fn divu_safe(a: u32, b: u32) -> u32 { a / (b | 1) }
pub fn sh(a: u32, k: u32) -> u32 { a << k }
