#![crate_type = "lib"]
// T5 (float intervals — clamp-bounded Add): the aterm-types contrast-ratio
// shape (crates/aterm-types/src/lib.rs:265, gate-logs-w3/aterm-types.log
// "float overflow to infinity (Add)" FAILED/UNKNOWN). BUG: the vcgen
// arithmetic-safety lane refused f64 Add even when BOTH operands were
// `.clamp(0.0, 1.0)`-bounded — `float_exp_bound` knew int->f64 casts and
// `as_secs_f64` but neither float LITERALS nor the std `f64::clamp` with
// literal bounds, so the `FloatOverflowToInfinity` VC stayed minted and the
// native lane wedged it at Unsupported/Unknown. FIX: `f64::clamp(lo, hi)`
// with literal, finite, ordered bounds now yields the NaN-or-bounded exponent
// fact max(|lo|, |hi|) (NaN passes through clamp but a NaN result is not an
// overflow TO INFINITY; the Add witness requires finite operands), and float
// literals carry their own exponent — so `l + d` with both operands in
// [0, 1] ∪ {NaN} provably cannot overflow and the VC is DISCHARGED at vcgen.
// MUST PROVE (exit 0). FLIP: mutant/float_clamp_bounded_add.rs drops the
// clamps — two unconstrained f64 params CAN genuinely overflow to +inf
// (f64::MAX + f64::MAX), so the obligation must be minted and REFUTE (exit 1).
pub fn contrast_sum(l: f64, d: f64) -> f64 {
    // Clamp at the arithmetic site: the bounds are the literals the T5
    // recognizer requires, so the Add's operands are provably in [0, 1] (or
    // NaN, which cannot produce an infinity under Add).
    let l = l.clamp(0.0, 1.0);
    let d = d.clamp(0.0, 1.0);
    l + d
}
