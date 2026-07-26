#![crate_type = "lib"]
// 2D modulo-guarded indexing: both `i % 4` and `j % 4` are in 0..4, so indexing a
// [[u32;4];4] is provably in-bounds on BOTH dimensions.
pub fn two_d_modulo_index(m: &[[u32; 4]; 4], i: usize, j: usize) -> u32 {
    m[i % 4][j % 4]
}
