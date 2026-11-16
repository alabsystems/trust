//@ trust-ladder-xcrate: refuses
//@ trust-ladder-xcrate-dep: libtbad
//@ trust-ladder-xcrate-declare: libtbad
//@ trust-ladder-row: Trust instance discharge not established for `user_phi_generic_bin_bad_names_bad::main`
//! THE RAIL `user_phi_generic_bin_bad` NOW LEANS ON (added 2026-10-05). Since
//! OD-1 phase 1 that row is `conditional`: `f`'s open dispatch is an
//! `assumption:instance-hypothesis`, and soundness moves to each instance this
//! compilation names. Here `main` names `f::<Bad>` as well as `f::<Mine>`, and
//! `<Bad as T>::m` panics, so the `instance-hypothesis:discharge` row for that
//! instance must fail and strict must refuse. Going green — or refusing for any
//! reason other than the discharge — means a named panicking instance escaped
//! the per-instance obligation: a FALSE PROOF.
extern crate libtbad;
use libtbad::{Bad, T};
pub struct Mine;
impl T for Mine { fn m(&self) -> u32 { 1 } }
fn f<X: T>(x: &X) -> u32 { x.m() }
fn main() { let _ = f(&Mine); let _ = f(&Bad); }
