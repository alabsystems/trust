#![crate_type = "lib"]
// MUTANT (guarded-division soundness twin): an UNGUARDED `a / b` is division-by-zero
// whenever `b == 0`. Genuinely violable, so `-full` MUST refute it (exit 1). This pins
// the soundness of the guarded-division structural discharge: the discharge fires ONLY
// when the violation `b = 0` is contradicted by a `b ≠ 0` guard conjunct; without the
// guard the violation is satisfiable and must never be proved.
pub fn f(a: u32, b: u32) -> u32 {
    a / b
}
