//@ slice-facts: refuses
//! THE LAST DOOR, and it is shut. h5 shows a guard on a loop-assigned INTEGER
//! survives, so the obvious repair from user code is to route the length through
//! one: `let n = w.len(); if n >= 1 { w[0] }`. It does not help — this refutes,
//! and so does the `w.len() >= 1` form and the `windows` form of the same shape.
//!
//! `w.len()` is itself `PtrMetadata(w)`, so binding it to an integer produces the
//! same disconnected term rather than a new one. Therefore:
//!
//!   for a slice local ASSIGNED INSIDE A LOOP, NO user-expressible fact about
//!   its length reaches the bounds check.
//!
//! That is the complete black-box characterisation, and it is where measurement
//! from outside stops: the next step is instrumenting the VC generator to print
//! which length term the guard constrains and which one the `assert` reads. Three
//! attributions of mine died on reading one more file, so that step should not be
//! guessed at.
pub fn f(v: &[u32]) -> u32 {
    let mut s = 0u32; let mut i = 0usize;
    while i < v.len() { let w = &v[i..]; let n = w.len(); if n >= 1 { s = s.wrapping_add(w[0]); } i += 1; }
    s
}
