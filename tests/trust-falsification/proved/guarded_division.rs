#![crate_type = "lib"]
// COMPLETENESS (fuzzer-revealed 2026-06-24, `div_guarded`): `if b != 0 { a / b }`. The
// `[divzero]` violation is the complementary pair `(b ≠ 0) ∧ (b = 0)` — propositionally
// UNSAT, but ay cannot STRICT-prove a trivial equality contradiction (only linear-arith
// Farkas), so the safe guarded division stayed runtime-checked. On the legacy/full-
// verification lowering path the violation is the bool temp `_4` with a block-def
// `_4 ⟺ (b=0)`, conjoined with the guard. Fixed by the propositional structural
// discharge (complementary-pair + bool-temp biconditional) in
// `formula_is_propositionally_unsat`, promoted in the results path. An UNGUARDED `a / b`
// has no `b ≠ 0` conjunct, so it stays runtime-checked (mutant below). Verifies (exit 0).
pub fn f(a: u32, b: u32) -> u32 {
    if b != 0 { a / b } else { 0 }
}
