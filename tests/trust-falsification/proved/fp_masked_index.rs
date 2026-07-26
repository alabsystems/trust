#![crate_type = "lib"]
// COMPLETENESS (fuzzer-revealed 2026-06-24, `fp_masked_index_safe`):
// `arr[((a + b) as usize) & 3]` over `[u8;4]`. The masked index `& 3` is in [0,3] < 4
// (PROVED). The only other obligation was `[float_overflow_to_infinity]` on `a + b`,
// which is genuinely violable (unconstrained f64 can overflow) — but BENIGN: float
// overflow to infinity is non-trapping (IEEE-754 defined `±inf`), and `inf as usize`
// SATURATES to usize::MAX (no panic). Since `a + b`'s ONLY use is that float→int cast,
// the overflow cannot reach a trap; the saturated integer is bounds-checked by the
// masked index. Fixed by suppressing the float-overflow obligation when the result's
// sole use is a float→int cast (v2_float_result_only_feeds_int_cast). Now fully proved.
pub fn f(a: f64, b: f64, arr: &[u8; 4]) -> u8 {
    arr[((a + b) as usize) & 3]
}
