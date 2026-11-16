//@ trust-ladder: verifies
//@ trust-ladder-crate-type: bin
//! THE RUNG-2 ROW, CLOSED 2026-09-19. Rung 2 sealed this trait, enumerated its
//! one impl and found it verified — `TRUST_RUNG2_PROBE` prints
//! `sealedness=Sealed`, `impl_count=1`, `=> verified=true` — and that verdict
//! used to reach nothing, for TWO reasons, both measured here:
//!   1. it filed under `safe_def_path_str` of the TRAIT METHOD (`Sink::put`)
//!      while the row carries `func_operand_name` (`<K as Sink>::put`), so the
//!      key never matched; and
//!   2. even once it matched, `out` is the EXPECTED-ABSENT set, whose row is
//!      still an assumption-panic row and still fail-closed. Rung 1 files into
//!      `compiler_total_out`, the arm that emits no obligation at all.
//! Rung 1's own comment says it SUBSUMES rung 2, so the two rungs assert the
//! same proposition and must land in the same channel. w5 is this program with
//! rung 1 instead. This row verifies only while w1/w2/w3 stay red.
pub trait Sink { fn put(&mut self, v: u32); }
pub struct S(pub u32);
impl S { pub fn feed<K: Sink>(&self, k: &mut K) { k.put(self.0); } }
pub struct A(pub u32);
impl Sink for A { fn put(&mut self, v: u32) { self.0 = v; } }
fn main() { let s = S(1); let mut a = A(0); s.feed(&mut a); }
