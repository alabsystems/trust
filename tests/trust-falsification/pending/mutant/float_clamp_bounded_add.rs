#![crate_type = "lib"]
// MUTANT of proved/float_clamp_bounded_add.rs: the clamps are dropped, so
// both Add operands are unconstrained f64 — `contrast_sum(f64::MAX, f64::MAX)`
// genuinely overflows to +inf at runtime. The T5 clamp-bounded discharge must
// NOT fire without the clamp facts (no literal-bounded operand exists), so the
// `FloatOverflowToInfinity` obligation is minted with its real semantic
// witness (both magnitudes above f64::MAX/2, finite exponents, same sign —
// satisfiable here) and the verifier must REFUSE this (exit 1). If this ever
// proves, the T5 fact leaked past its literal-clamp gate.
pub fn contrast_sum(l: f64, d: f64) -> f64 {
    l + d
}
