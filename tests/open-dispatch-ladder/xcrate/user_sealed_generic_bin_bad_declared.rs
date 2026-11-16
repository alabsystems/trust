//@ trust-ladder-xcrate: conditional
//@ trust-ladder-xcrate-dep: libs
//@ trust-ladder-xcrate-declare: libs
//@ trust-ladder-row: Trust verification advisory for `user_sealed_generic_bin_bad_declared::f`: 1 instance hypothesis row(s)
//! RE-RECORDED 2026-10-05 as `conditional` (measured on the stage 1 of
//! `f8220714f0`, OD-1 open shapes on main, and of `754201766a`). OD-1 phase 1
//! (main `c77d7678cf`) admits an OPEN generic call as one
//! `assumption:instance-hypothesis` row, so under this ladder's (strict) flags
//! `user_sealed_generic_bin_bad_declared::f` now exits 0 with a CONDITIONAL result and the warning above instead of
//! failing; `-Ztrust-policy=certify` exits 1 (`Trust certify verification failed
//! for `user_sealed_generic_bin_bad_declared::f`: 1 instance hypothesis row(s)`), which the `conditional` disposition
//! re-measures on every run. The refusal this row protected is not lost:
//! this binary instantiates only `f::<Mine>`, discharged by `Mine::area`'s own
//! body; `Boom` is never instantiated, so the program is panic-free. Naming
//! `f(&Boom)` refuses with `Trust instance discharge not established` (with or
//! without the declare flag): the new rail
//! `user_sealed_generic_bin_bad_names_boom`. A local panicking impl named at `f`
//! refuses at its own body and at the discharge.
//! The text below is the row as first written; its `refuses` predates OD-1.
//! GUARD RAIL for D4 increment B: rung 2 over `libs::Shape`, whose impl set
//! includes `Boom`, which panics and is never constructed here. Going green is a
//! FALSE PROOF until shown otherwise.
extern crate libs;
use libs::Shape;
pub struct Mine;
impl Shape for Mine { fn area(&self) -> u32 { 1 } }
fn f<X: Shape>(x: &X) -> u32 { x.area() }
fn main() { let _ = f(&Mine); }
