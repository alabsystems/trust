#![crate_type = "lib"]
// MUTANT of superiority/proved/guarded_slice_bound.rs: drops the `i < s.len()`
// guard. `s[i]` can be OUT OF BOUNDS for any i >= len, so default mode must NOT
// eliminate the check.
pub fn guarded_slice_bound(s: &[u32], i: usize) -> u32 {
    s[i]
}
