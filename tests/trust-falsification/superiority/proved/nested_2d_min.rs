#![crate_type = "lib"]
// 2D iteration over a slice-of-arrays with a min-bounded outer index: `g: &[[u8;4]]`,
// `m = n.min(g.len())`, then `g[i][j]` for `i in 0..m`, `j in 0..4`. The outer index
// is bounded by the loop-invariant `m <= g.len()` (one arg of the min is the bare
// param `n`, which does not resolve — but `g.len()` does, and `min(n, g.len()) <=
// g.len()` holds regardless), and the inner by the constant array length 4. Default
// mode discharges both.
pub fn nested_2d_min(g: &[[u8; 4]], n: usize) -> u8 {
    let mut t = 0u8;
    let m = n.min(g.len());
    for i in 0..m {
        for j in 0..4 {
            t ^= g[i][j];
        }
    }
    t
}
