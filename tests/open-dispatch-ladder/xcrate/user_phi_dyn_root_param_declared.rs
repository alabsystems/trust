//@ trust-ladder-xcrate: refuses
//@ trust-ladder-xcrate-dep: libtimpl
//@ trust-ladder-xcrate-declare: libtimpl
//! GUARD RAIL for D4 increment B: the SAME impl set as
//! `user_phi_generic_bin_declared`, reached through `&dyn T` at a root
//! parameter. The foreign-trait closure serves the generic shape only: a
//! monomorphization cannot be forged, a vtable can, and for a foreign trait it
//! can be minted in dependency bodies no walk of this compilation sees.
extern crate libtimpl;
use libtimpl::T;
pub struct Mine;
impl T for Mine { fn m(&self) -> u32 { 1 } }
pub fn g(x: &dyn T) -> u32 { x.m() }
fn main() { let _ = g(&Mine); }
