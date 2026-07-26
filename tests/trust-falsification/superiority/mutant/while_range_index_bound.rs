#![crate_type = "lib"]
// MUTANT of superiority/proved/while_range_index_bound.rs: off-by-one `<=` guard.
// When i == s.len() the access `s[i]` is OUT OF BOUNDS, so default mode must NOT
// statically eliminate the bounds check (it stays runtime-checked / fails).
pub fn while_range_index_bound(s: &[u32]) -> u32 {
    let mut acc = 0u32;
    let mut i = 0usize;
    while i <= s.len() {
        acc ^= s[i];
        i += 1;
    }
    acc
}
