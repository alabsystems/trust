//@ trust-ladder-xcrate: verifies
//@ trust-ladder-xcrate-dep: libss
//@ trust-ladder-xcrate-declare: libss
//! D4 increment B (2026-09-25): rung 2 for a FOREIGN trait with no Phi, at a
//! GENERIC call site in a binary. No seal is visible for a foreign trait, so the
//! impl set is closed by enumeration: `libss::Sq` (re-derived here) and the
//! local `Mine` (its own verdict), no blanket impl.
extern crate libss;
use libss::Shape;
pub struct Mine;
impl Shape for Mine { fn area(&self) -> u32 { 1 } }
fn f<X: Shape>(x: &X) -> u32 { x.area() }
fn main() { let _ = f(&Mine); }
