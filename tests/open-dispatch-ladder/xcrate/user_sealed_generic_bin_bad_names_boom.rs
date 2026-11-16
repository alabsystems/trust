//@ trust-ladder-xcrate: refuses
//@ trust-ladder-xcrate-dep: libs
//@ trust-ladder-xcrate-declare: libs
//@ trust-ladder-row: Trust instance discharge not established for `user_sealed_generic_bin_bad_names_boom::main`
//! THE RAIL `user_sealed_generic_bin_bad_declared` NOW LEANS ON (added
//! 2026-10-05): the same program, but `main` names `f::<Boom>`, and
//! `<Boom as Shape>::area` panics. The OD-1 instance hypothesis on `f` is charged
//! per named instance, so that instance's discharge must fail and strict must
//! refuse. Going green is a FALSE PROOF.
extern crate libs;
use libs::{Boom, Shape};
pub struct Mine;
impl Shape for Mine { fn area(&self) -> u32 { 1 } }
fn f<X: Shape>(x: &X) -> u32 { x.area() }
fn main() { let _ = f(&Mine); let _ = f(&Boom); }
