#![crate_type = "lib"]
// SUPERIORITY: `for i in (0..s.len()).rev() { s[i] }` — a reverse range loop.
// `Rev<Range>::next` yields exactly the values of `0..s.len()` in reverse, so
// every index is in [0, s.len()) and `s[i]` is provably in bounds. vcgen treats
// `.rev()` as transparent for the yield invariant (Rev<Range> over a traced Range
// has the same value set), eliminating the runtime bounds check rustc retains.
pub fn rev_range_index_bound(s: &[u32]) -> u32 {
    let mut acc = 0u32;
    for i in (0..s.len()).rev() {
        acc ^= s[i];
    }
    acc
}
