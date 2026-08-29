#![no_std]
pub fn clamp100(n: u32) -> u32 requires n <= 1000000 {
    if n > 100 { 100 } else { n }
}
