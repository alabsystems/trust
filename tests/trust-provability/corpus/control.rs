//! Branching, loops and matching over ordinary scalars.
pub fn sign(x: i32) -> i32 { if x > 0 { 1 } else if x < 0 { -1 } else { 0 } }
pub fn classify(b: u8) -> u8 { match b { 0 => 0, 1..=9 => 1, 10..=99 => 2, _ => 3 } }
pub fn countdown(mut n: u32) -> u32 { let mut steps = 0; while n > 0 { n -= 1; steps += 1; } steps }
pub fn accumulate(n: u32) -> u32 { let mut s = 0u32; let mut i = 0u32; while i < n && i < 100 { s = s.wrapping_add(i); i += 1; } s }
