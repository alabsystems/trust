#![allow(dead_code)]
pub fn pick(a: [i32; 7], i: usize) -> i32 { a[i] }
pub fn pick_safe(a: [i32; 7], i: usize) -> i32 { a[i & 3] }
