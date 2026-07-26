#![crate_type = "lib"]
#![feature(contracts)]
#![allow(incomplete_features)]
// MUTANT of superiority/proved/contract_inc.rs: returns `x`, so `ret == x` and
// the postcondition `ret > x` is VIOLATED. Default mode must NOT discharge it
// (the postcondition fails) — proving the contract verification is non-vacuous.
#[core::contracts::requires(x < 100)]
#[core::contracts::ensures(move |ret: &u32| *ret > x)]
pub fn contract_inc(x: u32) -> u32 { x }
