#![no_std]
//! ADVERSARIAL PROBE: a grammar postcondition with NO division in the body,
//! so every per-branch VC is within reach of the native lane.
pub fn clamp100(n: u32) -> u32 ensures result <= 100 {
    if n > 100 { 100 } else { n }
}
