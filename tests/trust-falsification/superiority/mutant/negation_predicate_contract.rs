#![crate_type = "lib"]
#![feature(contracts)]
#![allow(incomplete_features)]
// MUTANT of superiority/proved/negation_predicate_contract.rs: shifts the negated
// disjunct to `*r == -2`. On the `b == true` branch the result is `-1`, so both
// `-1 == -2` and `-1 == 1` are false — the disjunction is violated and default mode
// must NOT prove it.
#[core::contracts::ensures(move |r: &i32| *r == -2 || *r == 1)]
pub fn negation_predicate_contract(b: bool) -> i32 {
    if b {
        -1
    } else {
        1
    }
}
