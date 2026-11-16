//@ trust-ladder-xcrate: refuses
//@ trust-ladder-xcrate-dep: libs
//@ trust-ladder-xcrate-declare: libs
//! GUARD RAIL for D4-A: a `dyn`-bearing root parameter poisons the trait for
//! C-FLOW, and a FOREIGN trait gets no impl-set certificate at a virtual site
//! (a vtable can be minted in dependency bodies nobody walked). Declaring the
//! crate changes neither.
extern crate libs;
use libs::Shape;
pub fn g(x: &dyn Shape) -> u32 { x.area() }
fn main() { let _ = g(&libs::Sq(3)); }
