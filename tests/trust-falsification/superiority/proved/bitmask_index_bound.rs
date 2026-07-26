#![crate_type = "lib"]
// Bitmask (power-of-2) indexing: `n & 3` is always in 0..4, so indexing a [_; 4]
// is provably in-bounds — the ubiquitous ring-buffer / hash-table idiom. The
// interval backend proves `n & 3 ∈ [0, 3] ⊆ [0, len)`.
pub fn bitmask_index_bound(arr: &[u32; 4], n: usize) -> u32 {
    arr[n & 3]
}
