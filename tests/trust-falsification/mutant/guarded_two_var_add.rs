#![crate_type = "lib"]
// MUTANT of `proved/guarded_two_var_add.rs`: the guards are removed, so `a + b`
// overflows `u32` whenever `a + b > u32::MAX` (e.g. both near MAX). The overflow
// disjunct `a+b > u32::MAX` is now SAT (no guard bounds the summands), so the
// additive lift cannot close it; the verifier MUST fail closed.
pub fn guarded_two_var_add(a: u32, b: u32) -> u32 {
    a + b
}
