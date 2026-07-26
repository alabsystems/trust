#![crate_type = "lib"]
// The bare-cast for-each reduction `for &x in a { t += x as ACC }` over a FIXED
// array `&[u8; 16]` accumulating into u32. The checked-add overflow obligation
// `t + (x as u32) <= u32::MAX` is PROVED by default (no `wrapping_add`): the
// accumulator is bounded `t <= 0 + 16 * MAX(u8) = 4080` (`build_accumulator_bound_facts`,
// via `addend_per_iteration_bound` case (a) — the bare widened element), and the
// addend is bounded `x as u32 <= 255` (`build_additive_bound_facts`), so
// `4080 + 255 = 4335 < u32::MAX` and the overflow VC is UNSAT. This is the formal
// gate's guard for fuzzer gap 2 (`[overflow:add]`, the `sum_foreach` family) — the
// SAFE bare-cast accumulator that must stay PROVED, not runtime-checked. Pairs with
// mutant/foreach_cast_sum.rs (the same shape whose `N*MAX(ELEM)` exceeds the
// accumulator type, so the bound is self-limiting and the overflow stays refutable).
pub fn foreach_cast_sum(a: &[u8; 16]) -> u32 {
    let mut t: u32 = 0;
    for &x in a {
        t += x as u32;
    }
    t
}
