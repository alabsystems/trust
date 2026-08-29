#![no_std]
//! Does the DIVISION body — the one the claim used — admit ANY provable
//! postcondition, or is it the predicate `n/d <= n` specifically?
pub fn udiv_guarded(n: u32, d: u32) -> u32 ensures d != 0 || result == 0 {
    if d == 0 { return 0; }
    n / d
}
