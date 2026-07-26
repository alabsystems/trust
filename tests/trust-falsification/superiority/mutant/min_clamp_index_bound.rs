#![crate_type = "lib"]
// MUTANT of proved/min_clamp_index_bound.rs: `n.min(5)` returns up to 5, and for
// n == 4 it returns 4 — `arr[4]` is OUT OF BOUNDS on a 4-element array. The
// modeled bound `min(n,5) <= 5` is too weak to prove `< 4`, so the genuine OOB
// is refuted. MUST fail (exit 1).
pub fn min_clamp_index_bound(arr: &[u32; 4], n: usize) -> u32 {
    arr[n.min(5)]
}
