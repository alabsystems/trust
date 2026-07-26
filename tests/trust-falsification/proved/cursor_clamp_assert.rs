#![crate_type = "lib"]
// Guarded explicit assertion: the caller-facing invariant is established by
// the guard, so the assert is unreachable-failing and must be PROVED.
pub fn cursor_clamp_assert(col: u32, width: u32) -> u32 {
    let clamped = if col < width { col } else if width > 0 { width - 1 } else { 0 };
    assert!(width == 0 || clamped < width);
    clamped
}
