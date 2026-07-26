#![crate_type = "lib"]
// TRAP (#7c owned-Vec scalar index, soundness): the UNGUARDED twin of
// `proved/vec_scalar_index_lenchecked.rs`. An arbitrary `usize` index `v[i]` on a borrowed
// `&Vec<i32>` with NO `i < v.len()` guard CAN be out of bounds (panics at runtime), so the
// `i >= len` OOB obligation is SATISFIABLE and MUST be refused (exit 1) under
// the default strict policy. If Trust modeled the `Vec` scalar index as a clean total call (no
// obligation) — the pre-#7c behavior, which reported this vacuously "safe" — this mutant
// would SURVIVE (verify) and flip the gate RED. The abstract length is UNCONSTRAINED here
// (no guard, no `.len()` tie), so `i >= len` is trivially SAT and the access is refuted.
pub fn vec_scalar_index_unguarded_oob(v: &Vec<i32>, i: usize) -> i32 {
    v[i]
}
