//@ trust-ladder: verifies
//@ trust-ladder-crate-type: bin
//! THE DISCHARGE, AND WHY THIS IS NOT A MISSING PROOF. h5's shape plus
//! `#[trust::panic_free]` on the trait DEFINITION verifies: the lattice in
//! `trust_verify/trait_panic_free.rs` discharges Phi at each impl and relies on
//! it at the `dyn` call. `f` carries no row because the reliance certificate
//! discharged its only obligation — a designed discharge (docs/KNOWN_HAZARDS.md),
//! which r2 is the control for.
#![feature(register_tool)]
#![register_tool(trust)]
pub trait T { #[trust::panic_free] fn m(&self) -> u32; }
pub struct A;
impl T for A { fn m(&self) -> u32 { 7 } }
pub fn f(x: &dyn T) -> u32 { x.m() }
fn main() { let a = A; let _ = f(&a); }
