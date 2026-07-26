#![crate_type = "lib"]
// COMPLETENESS (hunt-frontier 2026-06-24): a non-square 2D grid flattened index `g[y*W+x]` over
// nested const-range loops. y in [0,3), x in [0,4), so y*4+x in [0, 11] — in bounds for [u8;12].
// Three obligations: [bounds] g[y*4+x] and [overflow:add] y*4+x discharge from the flattened-index
// global facts (`y*4 <= 8`, `y*4+x <= 11`); the BV-encoded [overflow:mul] y*4 discharges from the
// loop-var yield bound rendered in BV (`y < 3`).
pub fn g(grid: &[u8; 12]) -> u8 {
    let mut s = 0u8;
    for y in 0..3 {
        for x in 0..4 {
            s = s.wrapping_add(grid[y * 4 + x]);
        }
    }
    s
}
