//@ trust-ladder-xcrate: verifies
//@ trust-ladder-xcrate-dep: libs
//@ trust-ladder-xcrate-declare: libs
//! D4-A (2026-09-24): C-FLOW over a dependency's trait. The only coercion to
//! `dyn Shape` is in `main`, and its one `Self` (`Sq`) is re-derived panic-free
//! here from the declared dependency's encoded MIR.
extern crate libs;
use libs::Shape;
fn main() { let s: &dyn Shape = &libs::Sq(3); let _ = s.area(); }
