//@ trust-ladder: refuses
//@ trust-ladder-crate-type: bin
//! GUARD RAIL for any widening that lets rung 2's sealed-enumeration verdict
//! reach the absent-callee tolerance. The trait IS sealed here (local, no
//! blanket impl, whole-program artifact) and the impl set IS fully enumerated —
//! but the single impl PANICS, so rung 2 must decline and the call must stay
//! refused. If this row ever goes green, a false proof shipped.
pub trait Sink { fn put(&mut self, v: u32); }
pub struct S(pub u32);
impl S { pub fn feed<K: Sink>(&self, k: &mut K) { k.put(self.0); } }
pub struct A(pub u32);
impl Sink for A { fn put(&mut self, _v: u32) { panic!("boom") } }
fn main() { let s = S(1); let mut a = A(0); s.feed(&mut a); }
