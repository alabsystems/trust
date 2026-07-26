#![crate_type = "lib"]
// COMPLETENESS (fuzzer-revealed 2026-06-24, `sr_i128_add_guarded_safe`): a compound-
// guarded i128 add `if a>-1000 && a<1000 && b>-1000 && b<1000 { a+b }`. The operands
// are bounded to (-1000,1000), so `a+b` is in (-1998,1998), well within i128 — no
// overflow. The signed-128 overflow is BV-modeled and the dominating guards ARE
// threaded onto the BV operands (`BvSLt(-1000, bv_a)` …), but ay's QF_BV solver leaves
// the bounded 128-bit sign-bit overflow test Unknown. Fixed by a structural BV
// bound-propagation discharge (conjuncts_carry_bv_overflow_safe): bounded operands whose
// result-range fits [i128::MIN, i128::MAX] cannot overflow. Verifies (exit 0).
pub fn f(a: i128, b: i128) -> i128 {
    if a > -1000 && a < 1000 && b > -1000 && b < 1000 { a + b } else { 0 }
}
