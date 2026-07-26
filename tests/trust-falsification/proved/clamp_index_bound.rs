#![crate_type = "lib"]
// COMPLETENESS (fuzzer-revealed 2026-06-24, `sr_clamp_index_safe`): `arr[n.clamp(0,3)]`
// over `[u8;4]`. `n.clamp(0,3)` is in `[0,3] < 4`, so the index is provably in bounds.
// The clamp result bound was emitted as `(lo>hi) ∨ (lo<=r<=hi)`, relying on the solver
// to fold the constant `Gt(0,3)` to false — but ay does NOT fold a constant comparison,
// so the disjunction stayed vacuously satisfiable and the bound never discharged the
// index. Fixed by folding the constant `Gt(lo,hi)` at clamp-fact emission (a constant
// `lo<=hi` clamp emits the UNCONDITIONAL bound `lo<=r<=hi`). Verifies (exit 0).
pub fn f(n: usize, arr: &[u8; 4]) -> u8 {
    arr[n.clamp(0, 3)]
}
