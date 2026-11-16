//@ trust-ladder: refuses
//@ trust-ladder-crate-type: bin
//! GUARD RAIL, the harder direction: rung 2 must check EVERY member of the
//! enumerated set, not just the one the call site happens to reach. `B` is
//! never constructed, yet its impl is in the set, so the conjunction fails.
pub trait Sink { fn put(&mut self, v: u32); }
pub struct S(pub u32);
impl S { pub fn feed<K: Sink>(&self, k: &mut K) { k.put(self.0); } }
pub struct A(pub u32);
impl Sink for A { fn put(&mut self, v: u32) { self.0 = v; } }
pub struct B(pub u32);
impl Sink for B { fn put(&mut self, _v: u32) { panic!("boom") } }
fn main() { let s = S(1); let mut a = A(0); s.feed(&mut a); }
