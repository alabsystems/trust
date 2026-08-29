#![no_std]
//! MUTATION CONTROL A for clamp.rs: clause mutated to be FALSE (n=100 returns 100).
pub fn clamp100(n: u32) -> u32 ensures result <= 99 {
    if n > 100 { 100 } else { n }
}
