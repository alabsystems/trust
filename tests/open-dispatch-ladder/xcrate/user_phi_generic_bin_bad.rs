//@ trust-ladder-xcrate: conditional
//@ trust-ladder-xcrate-dep: libtbad
//@ trust-ladder-xcrate-declare: libtbad
//@ trust-ladder-row: Trust verification advisory for `user_phi_generic_bin_bad::f`: 1 instance hypothesis row(s)
//! RE-RECORDED 2026-10-05 as `conditional` (measured on the stage 1 of
//! `f8220714f0`, OD-1 open shapes on main, and of `754201766a`). OD-1 phase 1
//! (main `c77d7678cf`) admits an OPEN generic call as one
//! `assumption:instance-hypothesis` row, so under this ladder's (strict) flags
//! `user_phi_generic_bin_bad::f` now exits 0 with a CONDITIONAL result and the warning above instead of
//! failing; `-Ztrust-policy=certify` exits 1 (`Trust certify verification failed
//! for `user_phi_generic_bin_bad::f`: 1 instance hypothesis row(s)`), which the `conditional` disposition
//! re-measures on every run. The refusal this row protected is not lost:
//! this binary instantiates only `f::<Mine>`, whose `instance-hypothesis:discharge`
//! row resolves to `<Mine as T>::m` and is proved by that body; `Bad` is never
//! instantiated, so the program is panic-free. Naming `f(&Bad)` refuses with
//! `Trust instance discharge not established` (with or without the declare flag):
//! the new rail `user_phi_generic_bin_bad_names_bad`.
//! The text below is the row as first written; its `refuses` predates OD-1.
//! GUARD RAIL for D4 increment B: the declared dependency ALSO has `Bad`, which
//! panics and which this program never constructs. The closure is over the impl
//! set, not over the types a program uses. Going green is a FALSE PROOF until
//! shown otherwise.
extern crate libtbad;
use libtbad::T;
pub struct Mine;
impl T for Mine { fn m(&self) -> u32 { 1 } }
fn f<X: T>(x: &X) -> u32 { x.m() }
fn main() { let _ = f(&Mine); }
