//@ slice-facts: refuses
//! NO ITERATOR AT ALL. A `while` loop, a plain subslice binding, and an explicit
//! guard one statement before the index. Refutes. This is what finally fixes the
//! class's name: it is not `windows`, not `chunks`, not iterators, and not
//! closures — it is a slice local ASSIGNED INSIDE A LOOP.
pub fn f(v: &[u32]) -> u32 {
    let mut s = 0u32; let mut i = 0usize;
    while i < v.len() { let w = &v[i..]; if !w.is_empty() { s = s.wrapping_add(w[0]); } i += 1; }
    s
}
