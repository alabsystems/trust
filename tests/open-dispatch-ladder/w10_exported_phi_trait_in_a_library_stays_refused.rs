//@ trust-ladder: conditional
//@ trust-ladder-row: Trust verification advisory for `w10_exported_phi_trait_in_a_library_stays_refused::feed`: 1 instance hypothesis row(s)
//! RE-RECORDED 2026-10-05 as `conditional` (measured on the stage 1 of
//! `f8220714f0`, OD-1 open shapes on main, and of `754201766a`). OD-1 phase 1
//! (main `c77d7678cf`) admits an OPEN generic call as one
//! `assumption:instance-hypothesis` row, so under this ladder's (strict) flags
//! `w10_exported_phi_trait_in_a_library_stays_refused::feed` now exits 0 with a CONDITIONAL result and the warning above instead of
//! failing; `-Ztrust-policy=certify` exits 1 (`Trust certify verification failed
//! for `w10_exported_phi_trait_in_a_library_stays_refused::feed`: 1 instance hypothesis row(s)`), which the `conditional` disposition
//! re-measures on every run. The refusal this row protected is not lost:
//! rung 1 still does NOT rely on Φ for this exported trait — no Φ-closure row is
//! minted; the dispatch is a disclosed hypothesis. A downstream binary with
//! `impl Sink for Theirs { panic!() }` calling `feed(&mut Theirs, 7)` exits 1
//! under strict (`this implementation of `#[trust::panic_free]` trait method ...
//! is not proved panic-free`, plus its L0 rows and `main`'s generic absent
//! callee).
//! The text below is the row as first written; its `refuses` predates OD-1.
//! THE RAIL FOR `w9`, and the reason the widened gate is still a gate.
//!
//! Byte-for-byte `w9` with `pub` on the trait and its impl. Now the trait IS
//! exported, so a downstream crate can name it and write
//! `impl Sink for Theirs { fn put(&mut self, _) { panic!() } }`. The impl set is
//! genuinely OPEN and no visibility route closes it, so rung 1 must refuse —
//! `crate_types_are_whole_program` is false for a library and neither
//! `not_exported` nor `has_private_supertrait` holds.
//!
//! If this row ever goes green, rung 1 has stopped asking WHICH closed-world
//! route applies and started relying on Φ for traits anyone can implement.
#![feature(register_tool)]
#![register_tool(trust)]

pub trait Sink {
    #[trust::panic_free]
    fn put(&mut self, v: u32);
}
pub struct A(pub u32);
impl Sink for A {
    fn put(&mut self, v: u32) {
        self.0 = v;
    }
}
pub fn feed<K: Sink>(k: &mut K, v: u32) {
    k.put(v);
}
