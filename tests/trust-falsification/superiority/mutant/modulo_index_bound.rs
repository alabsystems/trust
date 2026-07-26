#![crate_type = "lib"]
// MUTANT of superiority/proved/modulo_index_bound.rs: `n % 5` reaches index 4 on
// a `[u32; 4]` (OUT OF BOUNDS). Default mode must NOT eliminate the check.
pub fn modulo_index_bound(arr: &[u32; 4], n: usize) -> u32 {
    arr[n % 5]
}
