#![crate_type = "lib"]
// MUTANT of proved/cursor_clamp_assert.rs: clamping to `width` (not width-1)
// makes `clamped == width` reachable, violating the asserted invariant
// `clamped < width`. The verifier MUST refuse this (exit 1). (The mutant has
// no `width - 1`, so the ONLY failing obligation is the assert's
// panic-freedom — a clean test of the explicit-assert lane.)
pub fn cursor_clamp_assert(col: u32, width: u32) -> u32 {
    let clamped = if col < width { col } else { width };
    assert!(width == 0 || clamped < width);
    clamped
}
