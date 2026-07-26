#![crate_type = "lib"]
// Guard-bounded SLICE indexing (symbolic length): the `i < s.len()` guard makes
// `s[i]` provably in-bounds — verified against the threaded path condition, not a
// constant length.
pub fn guarded_slice_bound(s: &[u32], i: usize) -> u32 {
    if i < s.len() { s[i] } else { 0 }
}
