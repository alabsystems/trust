#![crate_type = "lib"]
// `for c in s.chunks_exact(4)` yields sub-slices of length EXACTLY 4 (the short
// remainder is dropped), so c[0]..c[3] are all in bounds. Default mode must fully
// discharge all four index checks.
pub fn chunks_exact_index(s: &[u8]) -> u8 {
    let mut t = 0u8;
    for c in s.chunks_exact(4) {
        t ^= c[0] ^ c[1] ^ c[2] ^ c[3];
    }
    t
}
