#![crate_type = "lib"]
// SOUNDNESS mutant (T5A unsafe-demand class, sibling-obligation shape). The
// undocumented unsafe-sig call from mutant/undocumented_unsafe_sig_call.rs, but
// in a caller that ALSO carries a provable arithmetic op (`a as u32 + 1` — a
// defined cast, then a widened add that cannot overflow), so the function's
// translated Horn rule set is non-trivial and solves SAFE.
//
// The unsafe-call demand is a fail-closed FINDING, not a modelled property: its
// violation is the ground `Bool(true)` "there is no model of this construct's
// effects", which no CHC encoding can express and which SAT witnesses trivially.
// It therefore contributes nothing to the rule set the sibling arithmetic makes
// non-trivial. A lane that credits the whole function's obligations from that
// one solve reports the demand `Proved` — reading "the solver found no
// counterexample to a question it was not asked" as a proof, which is how
// `undocumented_unsafe_sig_call` first regressed from REFUTE to a false PROVE.
//
// MUST refute (exit 1): the demand carries no witness in the solved rules, and a
// missing-SAFETY finding is unprovable by construction, so
// `refute_unsafe_demand_findings` locks it to the structural verdict whatever a
// backend claims.
//
// Pairs with mutant/undocumented_unsafe_sig_call.rs (same call, no sibling).

/// Callee contract: caller must ensure `x != 0` (documented but unverified —
/// the point is the SIGNATURE is unsafe, not what the body does).
///
/// # Safety
/// `x` must be nonzero.
pub unsafe fn danger(x: u32) -> u32 {
    x.wrapping_mul(3)
}

/// The injected bug: an unsafe-sig call with NO preceding SAFETY comment,
/// sharing a body with an arithmetic obligation that genuinely proves.
#[must_use]
pub fn call_beside_provable_arithmetic(x: u32, a: u8) -> (u32, u32) {
    (unsafe { danger(x) }, a as u32 + 1)
}
