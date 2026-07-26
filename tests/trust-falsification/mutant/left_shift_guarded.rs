#![crate_type = "lib"]
// MUTANT of proved/left_shift_guarded.rs: the `k < 64` guard is dropped, so
// `1u64 << k` can shift by >= the bit width — a real shift overflow. The amount
// obligation becomes the SAT formula `k >= 64`; the verifier MUST fail closed
// with a counterexample, never certify.
pub fn left_shift_guarded(k: u32) -> u64 {
    1u64 << k
}
