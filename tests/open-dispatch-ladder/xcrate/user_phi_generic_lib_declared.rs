//@ trust-ladder-xcrate: conditional
//@ trust-ladder-xcrate-dep: libtimpl
//@ trust-ladder-xcrate-declare: libtimpl
//@ trust-ladder-crate-type: lib
//@ trust-ladder-row: Trust verification advisory for `user_phi_generic_lib_declared::f`: 1 instance hypothesis row(s)
//! RE-RECORDED 2026-10-05 as `conditional` (measured on the stage 1 of
//! `f8220714f0`, OD-1 open shapes on main, and of `754201766a`). OD-1 phase 1
//! (main `c77d7678cf`) admits an OPEN generic call as one
//! `assumption:instance-hypothesis` row, so under this ladder's (strict) flags
//! `user_phi_generic_lib_declared::f` now exits 0 with a CONDITIONAL result and the warning above instead of
//! failing; `-Ztrust-policy=certify` exits 1 (`Trust certify verification failed
//! for `user_phi_generic_lib_declared::f`: 1 instance hypothesis row(s)`), which the `conditional` disposition
//! re-measures on every run. The refusal this row protected is not lost:
//! no closed-world enumeration is claimed for the library; the dispatch is a
//! disclosed hypothesis. A downstream binary with `impl T for Theirs { panic!() }`
//! calling `u::f(&Theirs)` exits 1 under strict (`this implementation of
//! `#[trust::panic_free]` trait method `libtimpl::T::m` is not proved panic-free`,
//! plus `main`'s generic absent callee).
//! The text below is the row as first written; its `refuses` predates OD-1.
//! GUARD RAIL for D4 increment B: `user_phi_generic_bin_declared`'s `f` in a
//! LIBRARY. A crate compiled later can add a panicking impl of the foreign
//! trait, so no enumeration made here is complete — the `w10` premise, for a
//! foreign trait.
extern crate libtimpl;
use libtimpl::T;
pub struct Mine;
impl T for Mine { fn m(&self) -> u32 { 1 } }
pub fn f<X: T>(x: &X) -> u32 { x.m() }
