#![crate_type = "lib"]
// MUTANT (grid soundness twin): the same flattened index `y*4+x` reaches 2*4+3 = 11, which is OUT
// OF BOUNDS for a length-11 array (valid 0..=10). The flattened-index bound `idx <= 11` is SOUND but
// COMPATIBLE with the violation `idx >= 11`, so the access stays unproven and panics at runtime
// (CORRECT_REJECT). Pins that the index bound is the ACTUAL max and self-limiting.
pub fn g(grid: &[u8; 11]) -> u8 {
    let mut s = 0u8;
    for y in 0..3 {
        for x in 0..4 {
            s = s.wrapping_add(grid[y * 4 + x]);
        }
    }
    s
}
