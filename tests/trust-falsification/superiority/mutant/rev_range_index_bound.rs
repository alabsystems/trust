#![crate_type = "lib"]
// MUTANT of superiority/proved/rev_range_index_bound.rs: off-by-one `s[i + 1]`.
// In reverse, the first yielded i is s.len()-1, so s[i+1] = s[s.len()] — OUT OF
// BOUNDS. The yield invariant bounds i < len, NOT i+1, so default mode must NOT
// statically eliminate this check.
pub fn rev_range_index_bound(s: &[u32]) -> u32 {
    let mut acc = 0u32;
    for i in (0..s.len()).rev() {
        acc ^= s[i + 1];
    }
    acc
}
