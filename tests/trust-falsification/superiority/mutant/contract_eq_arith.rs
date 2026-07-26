#![crate_type = "lib"]
#![feature(contracts)]
#![allow(incomplete_features)]
// MUTANT of superiority/proved/contract_eq_arith.rs: returns `x + 2`, so
// `ret == x + 1` is VIOLATED (ret = x+2). Default mode must NOT discharge the
// postcondition — proving the equality-arithmetic contract check is non-vacuous.
#[core::contracts::requires(x < 100)]
#[core::contracts::ensures(move |ret: &u32| *ret == x + 1)]
pub fn contract_eq_arith(x: u32) -> u32 { x + 2 }
