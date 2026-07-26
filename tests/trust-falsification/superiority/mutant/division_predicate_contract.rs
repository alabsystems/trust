#![crate_type = "lib"]
#![feature(contracts)]
#![allow(incomplete_features)]
// MUTANT of superiority/proved/division_predicate_contract.rs: claims `*r == x / 2 + 1`
// while the body returns `x / 2`. `x / 2 != x / 2 + 1` always, so the postcondition is
// FALSE — default mode must NOT discharge it (it stays unknown / not falsely proved).
#[core::contracts::ensures(move |r: &i32| *r == x / 2 + 1)]
pub fn division_predicate_contract(x: i32) -> i32 {
    x / 2
}
