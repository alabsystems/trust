#![crate_type = "lib"]
// MUTANT of superiority/proved/bitmask_index_bound.rs: `n & 7` reaches index 7 on
// a `[u32; 4]` (OUT OF BOUNDS). Default mode must NOT eliminate the check.
pub fn bitmask_index_bound(arr: &[u32; 4], n: usize) -> u32 {
    arr[n & 7]
}
