//@ slice-facts: verifies
//! CONTROL. Indexing INSIDE a loop is fine when the slice is the loop-invariant
//! outer one. So neither "guards" nor "loops" is the discriminator on its own.
pub fn f(v: &[u32]) -> u32 { let mut s=0u32; let mut i=0usize; while i < v.len() { s = s.wrapping_add(v[i]); i += 1; } s }
