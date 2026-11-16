//@ trust-ladder-xcrate: verifies
//@ trust-ladder-xcrate-dep: libtimpl
//@ trust-ladder-xcrate-declare: libtimpl
//! D4 increment B (2026-09-25): rung 1 for a FOREIGN Phi trait at a GENERIC call
//! site in a binary. The impl set is `libtimpl::Good` (re-derived here from the
//! declared crate's encoded MIR) and the local `Mine` (held to Phi at its impl by
//! this compilation). `main` calls `f` at a LOCAL type only: a concrete call into
//! a dependency's trait impl is a separate, pre-existing bundling gap.
extern crate libtimpl;
use libtimpl::T;
pub struct Mine;
impl T for Mine { fn m(&self) -> u32 { 1 } }
fn f<X: T>(x: &X) -> u32 { x.m() }
fn main() { let _ = f(&Mine); }
