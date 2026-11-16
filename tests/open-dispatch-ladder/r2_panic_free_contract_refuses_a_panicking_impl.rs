//@ trust-ladder: refuses
//@ trust-ladder-row: is not proved panic-free
//@ trust-ladder-crate-type: bin
//! NEGATIVE CONTROL FOR r1. Without this, r1's rc=0 would be indistinguishable
//! from the lane silently dropping the row. The refusal must land AT THE IMPL.
#![feature(register_tool)]
#![register_tool(trust)]
pub trait T { #[trust::panic_free] fn m(&self) -> u32; }
pub struct A;
impl T for A { fn m(&self) -> u32 { panic!("boom") } }
pub fn f(x: &dyn T) -> u32 { x.m() }
fn main() { let a = A; let _ = f(&a); }
