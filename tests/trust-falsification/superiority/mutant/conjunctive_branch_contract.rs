#![crate_type = "lib"]
#![feature(contracts)]
#![allow(incomplete_features)]
// MUTANT of superiority/proved/conjunctive_branch_contract.rs: strengthens the upper
// conjunct to STRICT `r < hi`. On the `x > hi` branch the result is exactly `hi`, so
// `r < hi` is FALSE — the conjunction is violated and default mode must NOT prove it.
#[core::contracts::requires(lo <= hi)]
#[core::contracts::ensures(move |r: &u32| *r >= lo && *r < hi)]
pub fn clamp_contract(x: u32, lo: u32, hi: u32) -> u32 {
    if x < lo {
        lo
    } else if x > hi {
        hi
    } else {
        x
    }
}
