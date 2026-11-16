//@ slice-facts: refuses
//! THE ROW THAT GENERALISES IT. No `windows`, no `chunks`, no iterator
//! postcondition of any kind — just a slice of slices, iterated, with an
//! explicit guard. It refutes too.
//!
//! So the class is not "the slice-chunking yield fact fails to connect". It is:
//! a slice value REBOUND EACH ITERATION carries no length knowledge to a bounds
//! check in the body, and an explicit in-body guard does not supply it either.
//! `g1` (same guard, no loop) and `g2` (loop, but a loop-INVARIANT slice) are the
//! two controls that isolate "rebound each iteration" as the discriminator.
pub fn f(v: &[&[u32]]) -> u32 { let mut s=0u32; for w in v { if !w.is_empty() { s = s.wrapping_add(w[0]); } } s }
