#![no_std]
//! MUTATION CONTROL for `pass.rs`: the `d == 0` guard is deleted, so the
//! division really can trap. Must NOT pass. Measured: exit 1,
//! `Verdict: HAS VIOLATIONS`, `Summary: 0 proved, 2 failed`.
//!
//! A strict pass that has never been seen to fail is not evidence.
pub fn udiv_guarded(n: u32, d: u32) -> u32 {
    n / d
}
