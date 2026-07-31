// DIRECTION 3 — the load-bearing one. An unproved obligation whose kind has NO
// runtime fallback must STILL fail the build under the default policy.
//
// `Postcondition` classifies `has_runtime_fallback == false`
// (`trust-types/src/formula/vc_kind.rs`): rustc emits no check for an `ensures`
// clause, so accepting an unproved one would ship unverified behaviour with
// nothing catching it. That is precisely what separates policy B from "accept
// anything unproved".
//
// WHY THIS EXACT BODY. The clause `result <= x` is TRUE for every u32 — masking
// with a right-shift of itself can only clear bits — but the verifier does not
// discharge it, so the row lands `unknown`. That combination is the whole point:
//
//   * A postcondition that is FALSE would be REFUTED, and a refuted row already
//     fails under `refutation.rs`. This fixture would then be a duplicate and
//     would pin nothing about the no-fallback class. (An earlier draft used
//     `ensures result >= x` over `x.wrapping_mul(x)`, which is false at
//     x = 65536 — it would have made exactly that mistake.)
//   * A postcondition that PROVES obviously pins nothing either. `x / 3` and
//     `x.saturating_mul(2)` under `result <= x` / `result >= x` both prove, so
//     neither can serve here.
//
// Measured at stage2 `2d87b63cc`: two `postcond` rows, `outcome=unknown`,
// `typed_kind=Postcondition`, build rejected. The battery re-checks all three of
// those facts, so if a future prover improvement DISCHARGES this clause the
// battery fails loudly and asks for a new fixture rather than silently passing.
pub fn masked_is_no_larger(x: u32) -> u32
    ensures result <= x
{
    x & (x >> 1)
}
