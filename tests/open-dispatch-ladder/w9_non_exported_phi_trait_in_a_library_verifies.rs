//@ trust-ladder: verifies
//! THE ROUTE RUNG 1 HAD DROPPED. This is a LIBRARY — not a whole-program
//! artifact — so `crate_types_are_whole_program` is false and rung 1 refused it
//! until 2026-09-20.
//!
//! `generic_call_relies_on_panic_free_contract`'s own doc says its closed-world
//! gate is "the `dyn_trait_sealedness` U6 route, reused verbatim rather than
//! reinvented". It was not verbatim: that route is a THREE-way disjunction —
//! `whole_program || not_exported || has_private_supertrait` — and two disjuncts
//! were dropped in the reuse.
//!
//! `Sink` here is NOT exported. A downstream crate cannot name it, so it cannot
//! implement it, so the impl set is closed by LANGUAGE VISIBILITY — which holds
//! in an rlib exactly as in an executable. `w8` already rails the same route
//! green for the `dyn` lane; this is its generic twin.
//!
//! Its rail is `w10`, the same program with `pub` on the trait, which must stay
//! REFUSED because there the impl set genuinely is open.
#![feature(register_tool)]
#![register_tool(trust)]

trait Sink {
    #[trust::panic_free]
    fn put(&mut self, v: u32);
}
struct A(u32);
impl Sink for A {
    fn put(&mut self, v: u32) {
        self.0 = v;
    }
}
fn feed<K: Sink>(k: &mut K, v: u32) {
    k.put(v);
}
pub fn drive(v: u32) {
    let mut a = A(0);
    feed(&mut a, v);
}
