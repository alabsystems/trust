#![crate_type = "lib"]
// MUTANT of superiority/proved/nested_2d_min.rs: drops the `min(g.len())`, so the
// outer index runs to the bare `n`, unbounded by `g.len()`. `g[i]` is OUT OF BOUNDS
// whenever `n > g.len()`, so default mode must NOT eliminate the outer bounds check.
pub fn nested_2d_min(g: &[[u8; 4]], n: usize) -> u8 {
    let mut t = 0u8;
    for i in 0..n {
        for j in 0..4 {
            t ^= g[i][j];
        }
    }
    t
}
