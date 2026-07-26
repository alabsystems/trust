#![crate_type = "lib"]
// MUTANT of proved/frame_average_period.rs: the `frames > 0` guard is
// dropped, so the division panics when frames == 0. The verifier MUST refuse
// this (exit 1).
pub fn frame_average_period(total_ms: u32, frames: u32) -> u32 {
    total_ms / frames
}
