#![crate_type = "lib"]
// MUTANT (native total-call soundness twin): `trailing_zeros(0) == 32` is OUT OF BOUNDS for a
// length-32 array (valid 0..=31). The `Inst::Assume(result <= 32)` the native bridge emits is the
// TRUE postcondition and is COMPATIBLE with the violation `result >= 32` (32 is reachable), so the
// access is NOT proved and `-full` MUST refute (exit 1). Pins that the assumed bound is the
// intrinsic's ACTUAL max (the receiver width, inclusive) and is self-limiting — a too-loose Assume
// (or modeling the result as `< width`) would FALSE-PROVE this guaranteed OOB.
pub fn f(n: u32, arr: &[u8; 32]) -> u8 {
    arr[n.trailing_zeros() as usize]
}
