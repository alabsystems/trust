#![crate_type = "lib"]
// MUTANT of proved/vec_scalar_index_write_guarded.rs: the `i < v.len()` guard is
// dropped, so `v[i] = x` panics for any `i >= v.len()`. The verifier MUST refuse
// this (exit 1). Pre-fix this was the WRITE-path silent false-accept: the
// `index_mut` reborrow tripped the coarse mut-borrow gate, the length recovery
// declined, and the OOB write produced ZERO obligations (vacuously verified).
pub fn set_at(v: &mut Vec<i32>, i: usize, x: i32) {
    v[i] = x;
}
