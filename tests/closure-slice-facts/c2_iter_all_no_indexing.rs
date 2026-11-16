//@ slice-facts: verifies
//! CONTROL. A closure is not refused for BEING a closure — these all verify.
//! What the failing rows have in common is INDEXING a slice whose length
//! comes from the iterator that produced it.
pub fn f(v: &[u32]) -> bool { v.iter().all(|x| *x > 0) }
