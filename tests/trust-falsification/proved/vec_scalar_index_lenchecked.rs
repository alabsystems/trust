#![crate_type = "lib"]
// WIN (#7c owned-Vec scalar index, completeness): a `usize`-scalar index `v[i]` on a
// borrowed `&Vec<i32>` dominated by an `if i < v.len()` guard is provably in bounds and
// MUST verify (exit 0). Unlike a slice `s[i]` (whose bounds check rustc bakes into a MIR
// `Assert(Lt(i, Len))`), the `Vec` index lowers to `<Vec<T> as Index<usize>>::index(&v,
// i)` — the bounds check lives inside the opaque stdlib `index`. Trust now emits the real
// `i >= len` OOB obligation against the container's ABSTRACT length (`coll_len_var`, the
// same symbol `v.len()` ties to), so the guard `i < v.len()` DISCHARGES it.
//
// TWIN of `mutant/vec_scalar_index_unguarded_oob.rs` (the SAME `v[i]` with the guard
// REMOVED — an unconstrained `i` is `i >= len`-satisfiable, so it REFUTES). If Trust ever
// stopped emitting the scalar-index obligation, the mutant would survive and flip the gate.
pub fn vec_scalar_index_lenchecked(v: &Vec<i32>, i: usize) -> i32 {
    if i < v.len() { v[i] } else { 0 }
}
