//@ trust-ladder-xcrate: conditional
//@ trust-ladder-xcrate-dep: libtimpl
//@ trust-ladder-row: Trust verification advisory for `user_phi_generic_bin_undeclared::f`: 1 instance hypothesis row(s)
//! RE-RECORDED 2026-10-05 as `conditional` (measured on the stage 1 of
//! `f8220714f0`, OD-1 open shapes on main, and of `754201766a`). OD-1 phase 1
//! (main `c77d7678cf`) admits an OPEN generic call as one
//! `assumption:instance-hypothesis` row, so under this ladder's (strict) flags
//! `user_phi_generic_bin_undeclared::f` now exits 0 with a CONDITIONAL result and the warning above instead of
//! failing; `-Ztrust-policy=certify` exits 1 (`Trust certify verification failed
//! for `user_phi_generic_bin_undeclared::f`: 1 instance hypothesis row(s)`), which the `conditional` disposition
//! re-measures on every run. The refusal this row protected is not lost:
//! only `f::<Mine>` is instantiated and discharged by `Mine::m`'s own body. Naming
//! the undeclared dependency's `f(&Good)` still refuses (`Trust instance discharge
//! not established`), because `Good` cannot be re-derived — an incompleteness,
//! fail-closed.
//! The text below is the row as first written; its `refuses` predates OD-1.
//! GUARD RAIL for D4 increment B: `user_phi_generic_bin_declared` with the
//! dependency NOT declared. Its impl `Good` cannot be re-derived, so the closure
//! over the impl set is incomplete and the generic call keeps its fatal row.
extern crate libtimpl;
use libtimpl::T;
pub struct Mine;
impl T for Mine { fn m(&self) -> u32 { 1 } }
fn f<X: T>(x: &X) -> u32 { x.m() }
fn main() { let _ = f(&Mine); }
