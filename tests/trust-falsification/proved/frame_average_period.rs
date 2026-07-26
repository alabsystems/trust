#![crate_type = "lib"]
// Guarded division: the average frame period is only computed when at least
// one frame was rendered, so division by zero is unreachable. The
// division-safety obligation must be PROVED.
pub fn frame_average_period(total_ms: u32, frames: u32) -> u32 {
    if frames > 0 { total_ms / frames } else { 0 }
}
