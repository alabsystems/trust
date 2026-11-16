//@ trust-ladder-xcrate: refuses
//! THE QUANTIFIER INVERSION, MEASURED. This crate never names the contract; it
//! inherits it by naming the trait. A panicking impl does not compile.
extern crate libt;
pub struct A;
impl libt::T for A { fn m(&self) -> u32 { panic!("boom") } }
fn main() { use libt::T; let a = A; let _ = a.m(); }
