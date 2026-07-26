#![crate_type = "lib"]
// PROVED analog of mutant/slice_shadow_name_collision.rs: a single slice re-bound
// (`let s = inner`) and indexed under its OWN length guard — safe, and the
// collision-safe naming must still UNIFY the (same-slice) guard and bounds lengths so it
// PROVES (the fix distinguishes only DISTINCT locals that share a name).
pub fn slice_shadow_name_collision(outer: &[u32], inner: &[u32], i: usize) -> u32 {
    let _ = outer;
    let s = inner;
    if i < s.len() { s[i] } else { 0 }
}
