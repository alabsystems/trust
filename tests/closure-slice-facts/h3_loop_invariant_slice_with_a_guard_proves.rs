//@ slice-facts: verifies
//! CONTROL — a loop is not enough. Same guard, same index, inside a loop, but
//! `w` is a PARAMETER and so is loop-invariant. Verifies.
pub fn f(w: &[u32]) -> u32 {
    let mut s = 0u32; let mut k = 0usize;
    while k < 1 { if !w.is_empty() { s = s.wrapping_add(w[0]); } k += 1; }
    s
}
