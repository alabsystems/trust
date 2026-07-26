#![crate_type = "lib"]
#![feature(contracts)]
#![allow(incomplete_features)]
// MUTANT: the body computes `x >= 0` but the contract claims `ret == (x > 0)`.
// They DISAGREE at x == 0 (body true, spec false), so Trust must NOT statically
// discharge the postcondition — it stays unproved (sound: the re-sort fix
// connects the names, it does not make a wrong implementation verify).
#[core::contracts::ensures(move |r: &bool| *r == (x > 0))]
pub fn is_positive(x: i32) -> bool { x >= 0 }
