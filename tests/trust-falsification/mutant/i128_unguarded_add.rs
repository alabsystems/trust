#![crate_type = "lib"]
// MUTANT (i128 BV-bound discharge soundness twin): an UNGUARDED i128 add `a + b` can
// overflow (`i128::MAX + 1`). The operands carry only the `[i128::MIN, i128::MAX]` type
// range, whose sum overflows i128 — the structural BV bound-propagation does NOT fire
// (checked_add is None) — so the overflow stays refutable. `-full` MUST refute (exit 1).
pub fn f(a: i128, b: i128) -> i128 {
    a + b
}
