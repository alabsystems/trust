#![crate_type = "lib"]
// MUTANT (wide-accumulator soundness twin): summing `[u128; 16]` elements (each up to
// u128::MAX) GENUINELY OVERFLOWS — the per-element bound is u128::MAX, so the sum bound
// `16 * u128::MAX` exceeds u128::MAX. `-full` MUST refute (exit 1). Pins that the UInt
// threshold discharge is SELF-LIMITING (the sum bound itself must fit).
pub fn f(a: &[u128; 16]) -> u128 { let mut t: u128 = 0; for &x in a { t += x; } t }
