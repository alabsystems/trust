#![crate_type = "lib"]
// PROVED analog of mutant/nondominating_bool_guard.rs: the guard `i < s.len()` is the
// discriminant's UNIQUE (single, dominating) definition, so it genuinely bounds the
// access and PROVES — confirming the single-assignment requirement does not over-reject
// the legitimately-guarded shape.
pub fn nondominating_bool_guard(s: &[u32], i: usize) -> u32 {
    if i < s.len() { s[i] } else { 0 }
}
