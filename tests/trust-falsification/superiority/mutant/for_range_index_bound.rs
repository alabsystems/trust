#![crate_type = "lib"]
// MUTANT of superiority/proved/for_range_index_bound.rs: off-by-one `s[i + 1]`.
// When i == s.len()-1 the access is s[s.len()] — OUT OF BOUNDS. The yield
// invariant bounds `i < len`, NOT `i + 1`, so default mode must NOT statically
// eliminate this check (it stays runtime-checked / fails) — proving Trust is
// sound, not vacuously proving every range index.
pub fn for_range_index_bound(s: &[u32]) -> u32 {
    let mut acc = 0u32;
    for i in 0..s.len() {
        acc ^= s[i + 1];
    }
    acc
}
