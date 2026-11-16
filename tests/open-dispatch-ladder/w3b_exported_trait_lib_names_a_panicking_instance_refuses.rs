//@ trust-ladder: refuses
//@ trust-ladder-row: Trust instance discharge not established for `w3b_exported_trait_lib_names_a_panicking_instance_refuses::g`
//! THE RAIL `w3` NOW LEANS ON (added 2026-10-05). `w3` is `conditional`: the
//! exported `Sink` is Open, so `S::feed`'s dispatch is an OD-1
//! `assumption:instance-hypothesis` charged per instance. This library names
//! `feed::<Bad>` itself, at an impl that panics, so the discharge for that
//! instance must fail (alongside `Bad::put`'s own L0 rows). Going green, or
//! losing the discharge row, means the per-instance obligation no longer reaches
//! an instance the crate builds.
pub trait Sink { fn put(&mut self, v: u32); }
pub struct S(pub u32);
impl S { pub fn feed<K: Sink>(&self, k: &mut K) { k.put(self.0); } }
pub struct A(pub u32);
impl Sink for A { fn put(&mut self, v: u32) { self.0 = v; } }
pub struct Bad;
impl Sink for Bad { fn put(&mut self, _v: u32) { panic!("bad") } }
pub fn g() { S(1).feed(&mut Bad); }
