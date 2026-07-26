#![crate_type = "lib"]
// COMPLETENESS (hunt-frontier 2026-06-24): `if a >= b { a - b }` over unsigned cannot
// underflow — the `[overflow:sub]` violation `Sub(a,b) < 0` with the guard `a >= b` is
// UNSAT (a≥b ⟹ a−b≥0), but ay leaves it Unknown. Closed by extending the structural
// arithmetic discharge (`term_nonneg` recognizes `Sub(A,B) ≥ 0` from a `Ge(A,B)` guard).
// An UNGUARDED `a - b` keeps no `Ge(a,b)` conjunct, so it stays refutable (mutant below).
pub fn f(a: u8, b: u8) -> u8 {
    if a >= b { a - b } else { 0 }
}
