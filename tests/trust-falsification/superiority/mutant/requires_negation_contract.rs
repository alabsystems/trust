#![crate_type = "lib"]
#![feature(contracts)]
#![allow(incomplete_features)]
// MUTANT of superiority/proved/requires_negation_contract.rs: returns `x` instead of
// `-x`. Under `requires(x > 0)` the result is positive, so `*r == -x` (negative) is
// FALSE — default mode must NOT discharge the negation postcondition.
#[core::contracts::requires(x > 0)]
#[core::contracts::ensures(move |r: &i32| *r == -x)]
pub fn requires_negation_contract(x: i32) -> i32 {
    x
}
