#![crate_type = "lib"]
#![feature(contracts)]
#![allow(incomplete_features)]
// SUPERIORITY: an EQUALITY postcondition over ARITHMETIC — `ensures(ret == x + 1)`.
// rustc only enforces this at runtime; Trust statically PROVES it (the
// contract-predicate lowering now handles `+`/`-`, and the postcondition VC pins
// the return value to the body). Default mode must report it fully proved.
#[core::contracts::requires(x < 100)]
#[core::contracts::ensures(move |ret: &u32| *ret == x + 1)]
pub fn contract_eq_arith(x: u32) -> u32 { x + 1 }
