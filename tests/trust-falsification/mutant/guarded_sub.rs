#![crate_type = "lib"]
// MUTANT of `proved/guarded_sub.rs`: the subtrahend is now a runtime `u32` with
// NO guard, so `x - y` underflows whenever `y > x`. The underflow disjunct
// `x - y < 0` is SAT (no guard contradicts it), so the disjunctive case-split
// cannot close it; the verifier MUST fail closed (`[overflow] FAILED`).
pub fn guarded_sub(x: u32, y: u32) -> u32 {
    x - y
}
