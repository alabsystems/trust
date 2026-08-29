#![no_std]
//! ADVERSARIAL PROBE: the GRAMMAR form of the same postcondition.
//! Body byte-identical to pass.rs. No feature gate, no import, no attribute.
pub fn udiv_guarded(n: u32, d: u32) -> u32 ensures result <= n {
    if d == 0 { return 0; }
    n / d
}
