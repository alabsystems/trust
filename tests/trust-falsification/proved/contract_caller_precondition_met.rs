#![crate_type = "lib"]
#![feature(contracts)]
#![allow(incomplete_features)]
// PROVED (#5-PRE-A WIN — a caller that ESTABLISHES a linear precondition still
// verifies): `helper` requires `x < 10`; `caller` calls it with the constant 5,
// so the caller-side precondition VC is `!(5 < 10)` = `5 >= 10`, which the
// in-process ay backend refutes (UNSAT) -> PROVED. This is the regression guard
// for #5-PRE-A: the fail-closed reclassify must NOT reject a caller that
// genuinely discharges a decidable precondition (the ay re-solve proves it).
#[core::contracts::requires(true)]
pub fn caller() -> i32 {
    helper(5)
}

#[core::contracts::requires(x < 10)]
pub fn helper(x: i32) -> i32 {
    x
}
