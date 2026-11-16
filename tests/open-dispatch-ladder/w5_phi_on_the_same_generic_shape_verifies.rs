//@ trust-ladder: verifies
//@ trust-ladder-crate-type: bin
//! w4's twin with rung 1 instead of rung 2. Byte-for-byte the same program plus
//! `#[trust::panic_free]` on the trait method. This verifies. The pair w4/w5 IS
//! the wiring gap: the lattice discharges the same call two ways and only one
//! of them reaches the row that fails the build.
#![feature(register_tool)]
#![register_tool(trust)]
pub trait Sink { #[trust::panic_free] fn put(&mut self, v: u32); }
pub struct S(pub u32);
impl S { pub fn feed<K: Sink>(&self, k: &mut K) { k.put(self.0); } }
pub struct A(pub u32);
impl Sink for A { fn put(&mut self, v: u32) { self.0 = v; } }
fn main() { let s = S(1); let mut a = A(0); s.feed(&mut a); }
