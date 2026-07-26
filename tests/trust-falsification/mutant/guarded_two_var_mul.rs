#![crate_type = "lib"]
// MUTANT + DISCRIMINATING guard of proved/guarded_two_var_mul.rs: the bound is
// widened `< 1000` -> `< 100000`. Now `a * b` can reach `99999 * 99999 ≈ 1.0e10`,
// which EXCEEDS `u32::MAX ≈ 4.29e9` — the multiply overflows. The guard no longer
// rules out the overflow disjunct, so it cannot be discharged and the verifier MUST
// fail closed (`[overflow:mul] FAILED` with a verified counterexample, exit 1).
// Guards that the bounded-multiply discharge uses the ACTUAL bound magnitude (a model
// that ignored the bound value would falsely prove this real overflow).
pub fn guarded_two_var_mul(a: u32, b: u32) -> u32 {
    if a < 100000 && b < 100000 {
        a * b
    } else {
        0
    }
}
