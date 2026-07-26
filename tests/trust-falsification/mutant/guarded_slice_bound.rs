#![crate_type = "lib"]
// MUTANT of proved/guarded_slice_bound.rs: drops the `i < s.len()` guard, so
// `s[i]` can be OUT OF BOUNDS for any i >= len. MUST be refused (exit 1).
pub fn guarded_slice_bound(s: &[u32], i: usize) -> u32 {
    s[i]
}
