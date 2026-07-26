#![crate_type = "lib"]
// MUTANT of `proved/signed_shift_const.rs`: the shift amount is now a runtime
// `u32` with NO `< 32` guard, so `a >> n` can shift by at least the bit width —
// a real shift-overflow. The closed-constant contradiction becomes the SAT
// obligation `n >= 32`, so neither the in-process kernel nor the native CHC/PDR
// runner can prove it; the verifier MUST fail closed (`[shift:right] FAILED`
// with a verified counterexample), never certify.
pub fn signed_shift_const(a: i32, n: u32) -> i32 {
    a >> n
}
