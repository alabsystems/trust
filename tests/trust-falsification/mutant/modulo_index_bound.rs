#![crate_type = "lib"]
// MUTANT of proved/modulo_index_bound.rs: `n % 5` reaches 4, but the array has
// only 4 elements — `arr[4]` is OUT OF BOUNDS. The verifier MUST refuse to prove
// it safe (the interval over-approx [0,5) is NOT ⊆ [0,4); falls through and the
// genuine OOB is refuted). MUST fail (exit 1).
pub fn modulo_index_bound(arr: &[u32; 4], n: usize) -> u32 {
    arr[n % 5]
}
