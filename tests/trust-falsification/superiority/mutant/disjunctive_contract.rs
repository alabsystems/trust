#![crate_type = "lib"]
#![feature(contracts)]
#![allow(incomplete_features)]
// MUTANT of superiority/proved/disjunctive_contract.rs: shifts the first disjunct to
// `*r == x + 1`. On the `x > 0` branch the result is `x`, so BOTH `x == x + 1` and
// `x == 0` are false — the disjunction is violated. Default mode must NOT prove it.
#[core::contracts::ensures(move |r: &u32| *r == x + 1 || *r == 0)]
pub fn disjunctive_contract(x: u32) -> u32 {
    if x > 0 {
        x
    } else {
        0
    }
}
