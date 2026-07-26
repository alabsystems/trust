#![crate_type = "lib"]
// MUTANT: `+` (real add) overflows on a free running sum. MUST be refused (exit 1) —
// guards each grid cell `c` is a real unconstrained value across the nested loops.
pub fn foreach_2d_grid(g: &[[u32; 4]]) -> u32 {
    let mut t = 0u32;
    for row in g {
        for &c in row {
            t = t + c;
        }
    }
    t
}
