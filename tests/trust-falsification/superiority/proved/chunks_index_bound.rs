#![crate_type = "lib"]
// SUPERIORITY: `for c in s.chunks(4) { c[0] }` — `<[T]>::chunks(4)` yields only
// NON-EMPTY sub-slices (length in [1, 4]), so c[0] is provably in bounds. vcgen
// models the yielded slice's length (1 <= len <= n) and eliminates the runtime
// bounds check rustc retains.
pub fn chunks_index_bound(s: &[u32]) -> u32 {
    let mut acc = 0u32;
    for c in s.chunks(4) {
        acc ^= c[0];
    }
    acc
}
