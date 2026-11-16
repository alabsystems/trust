//@ slice-facts: verifies
//! THE CONTROL THAT NAMES THE DEFECT. Structurally identical to h1 — a `while`
//! loop, a local assigned every iteration, an explicit guard on that local one
//! statement before the index — except the guarded quantity is an INTEGER
//! (`k < v.len()`) rather than the LENGTH OF A SLICE (`!w.is_empty()`).
//!
//! This verifies. h1 refutes.
//!
//! So it is not "guards are killed when their free variable is reassigned in a
//! loop" — that rule exists (safety.rs, the stale-dominating-guard kill) and it
//! would hit `k` here just as hard. The loss is specific to the LENGTH TERM of a
//! slice local that is assigned inside a loop.
pub fn f(v: &[u32]) -> u32 {
    let mut s = 0u32; let mut i = 0usize;
    while i < v.len() { let k = i; if k < v.len() { s = s.wrapping_add(v[k]); } i += 1; }
    s
}
