//@ trust-ladder-xcrate: verifies
//! A conforming downstream impl of a DEPENDENCY's Phi-carrying trait.
extern crate libt;
pub struct A;
impl libt::T for A { fn m(&self) -> u32 { 7 } }
fn main() { use libt::T; let a = A; let _ = a.m(); }
