#![no_std]
//! Two functions: one carrying a grammar postcondition, one carrying the
//! division safety obligation from pass.rs. If this passes, a crate can hold
//! BOTH a real safety obligation and a proved functional contract at exit 0.
pub fn clamp100(n: u32) -> u32 ensures result <= 100 {
    if n > 100 { 100 } else { n }
}

pub fn udiv_guarded(n: u32, d: u32) -> u32 {
    if d == 0 { return 0; }
    n / d
}
