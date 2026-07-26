#![crate_type = "lib"]
// Clamp-guarded indexing: `n.min(3)` is always in 0..4, so indexing a [_; 4] is
// provably in-bounds. The vcgen models the ordered `Ord::min` result bound
// (min(n,3) <= 3), so the bounds check proves instead of being falsely refuted.
pub fn min_clamp_index_bound(arr: &[u32; 4], n: usize) -> u32 {
    arr[n.min(3)]
}
