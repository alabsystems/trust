#![crate_type = "lib"]
// COMPLETENESS (`[unreach]` nested-loop, fuzzer-revealed 2026-06-24): a 2D grid
// reduction `for i { for j { t += a[i][j] as u16 } }` over `&[[u8;M];N]`. The
// accumulator is bounded (`t <= N*M*255 = 4080 < u16::MAX`, via the product trip
// count K=N*M in `build_accumulator_bound_facts`), so `[overflow:add]` proves. The
// residual was the NESTED iterator-exhaustion `[unreach]`: the trap is reached via
// `Or([outer_loop_exhausted, inner_loop_exhausted])`, each branch UNSAT by a
// DIFFERENT range discriminant — the flat single-loop discharge missed the
// disjunction. `formula_is_unsat_by_exhaustive_discriminant` now recurses (`Or`
// UNSAT iff every branch UNSAT), proving both nested traps dead. All five
// obligations (2 bounds + 1 overflow + 2 unreach) are now static proofs; this
// verifies (exit 0). The soundness twin remains `mutant/enum_partial_unreachable.rs`.
pub fn f(a: &[[u8; 4]; 4]) -> u16 {
    let mut t: u16 = 0;
    for i in 0..4 {
        for j in 0..4 {
            t += a[i][j] as u16;
        }
    }
    t
}
