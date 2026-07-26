#![crate_type = "lib"]
// MUTANT of proved/bitmask_index_bound.rs: `n & 7` reaches 7 > 3, so `arr[n & 7]`
// on a 4-element array is OUT OF BOUNDS. MUST be refused (the interval over-approx
// [0,7] is NOT ⊆ [0,4)); fail-closed. MUST fail (exit 1).
pub fn bitmask_index_bound(arr: &[u32; 4], n: usize) -> u32 {
    arr[n & 7]
}
