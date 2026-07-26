#![crate_type = "lib"]
// MUTANT of superiority/proved/chunks_index_bound.rs: c[4] can be OUT OF BOUNDS —
// a chunks(4) sub-slice has length in [1, 4], so index 4 never exists. Default
// mode must NOT eliminate the check.
pub fn chunks_index_bound(s: &[u32]) -> u32 {
    let mut acc = 0u32;
    for c in s.chunks(4) {
        acc ^= c[4];
    }
    acc
}
