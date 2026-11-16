//@ trust-ladder: conditional
//@ trust-ladder-row: Trust verification advisory for `w3_exported_trait_in_an_rlib_is_not_sealed::S::feed`: 1 instance hypothesis row(s)
//! RE-RECORDED 2026-10-05 as `conditional` (measured on the stage 1 of
//! `f8220714f0`, OD-1 open shapes on main, and of `754201766a`). OD-1 phase 1
//! (main `c77d7678cf`) admits an OPEN generic call as one
//! `assumption:instance-hypothesis` row, so under this ladder's (strict) flags
//! `w3_exported_trait_in_an_rlib_is_not_sealed::S::feed` now exits 0 with a CONDITIONAL result and the warning above instead of
//! failing; `-Ztrust-policy=certify` exits 1 (`Trust certify verification failed
//! for `w3_exported_trait_in_an_rlib_is_not_sealed::S::feed`: 1 instance hypothesis row(s)`), which the `conditional` disposition
//! re-measures on every run. The refusal this row protected is not lost:
//! `Sink` is still Open (no enumeration is made), and the obligation moves to
//! each instance. A downstream binary with `impl Sink for Theirs { panic!() }`
//! calling `S(7).feed(&mut Theirs)` exits 1 under strict (the impl's own L0 rows,
//! and `main`'s call into the dependency's generic `feed` as a generic absent
//! callee). The same-crate instance at a panicking impl is the new rail
//! `w3b_exported_trait_lib_names_a_panicking_instance_refuses`.
//! The text below is the row as first written; its `refuses` predates OD-1.
//! GUARD RAIL for the sealedness premise itself. Same shape as w1/w2 but an
//! rlib: a downstream crate can still add an impl, so `dyn_trait_sealedness`
//! is Open and no enumeration is sound. This is the sweep's t09 shape, and it
//! is why t09 is a correct refusal in a library and not a bug.
pub trait Sink { fn put(&mut self, v: u32); }
pub struct S(pub u32);
impl S { pub fn feed<K: Sink>(&self, k: &mut K) { k.put(self.0); } }
pub struct A(pub u32);
impl Sink for A { fn put(&mut self, v: u32) { self.0 = v; } }
