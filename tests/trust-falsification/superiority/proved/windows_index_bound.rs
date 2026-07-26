#![crate_type = "lib"]
// SUPERIORITY: `for w in s.windows(2) { w[0] ^ w[1] }` — rustc retains a runtime
// bounds check on every w[0]/w[1]. `<[T]>::windows(2)` yields sub-slices of length
// EXACTLY 2, so w[0] and w[1] are provably in bounds; vcgen models the yielded
// slice's length (== n) and statically eliminates the checks.
pub fn windows_index_bound(s: &[u32]) -> u32 {
    let mut acc = 0u32;
    for w in s.windows(2) {
        acc ^= w[0] ^ w[1];
    }
    acc
}
