#![crate_type = "lib"]
#![feature(contracts)]
#![allow(incomplete_features)]
// MUTANT: `ret > x` is FALSE for the identity body (x is not > x). Trust must
// NOT statically discharge it — the postcondition is refuted (sound: the
// param-name fix connects `x` to the body, it does not make false specs pass).
#[core::contracts::requires(x < 100)]
#[core::contracts::ensures(move |ret: &u32| *ret > x)]
pub fn identity_contract(x: u32) -> u32 { x }
