//@ vec-lowering: verifies
//! A SECOND WORKING EQUIVALENT. Two spellings of the same construction verify
//! while the idiomatic one does not, which is what makes this a lowering gap
//! rather than anything about Vec's semantics.
fn main() { let v: Vec<u32> = Vec::from([1u32, 2, 3]); let _ = v.len(); }
