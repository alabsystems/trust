#![crate_type = "lib"]
// Modulo-guarded indexing: `n % 4` is always in 0..4, so indexing a [_; 4] is
// provably in-bounds — the bounds check is statically discharged (no OOB panic
// reachable). The interval backend proves `n % 4 ∈ [0, 4) ⊆ [0, len)`.
pub fn modulo_index_bound(arr: &[u32; 4], n: usize) -> u32 {
    arr[n % 4]
}
