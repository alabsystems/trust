#![crate_type = "lib"]
// MUTANT of superiority/proved/chunks_exact_index.rs: indexes c[4], past the
// exact-length-4 chunk. `c[4]` is always OUT OF BOUNDS, so default mode must NOT
// eliminate the check.
pub fn chunks_exact_index(s: &[u8]) -> u8 {
    let mut t = 0u8;
    for c in s.chunks_exact(4) {
        t ^= c[0] ^ c[4];
    }
    t
}
