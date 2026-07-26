#![crate_type = "lib"]
// The ubiquitous bounded-copy idiom: `n = min(src.len(), dst.len())` then a
// `for i in 0..n` loop copying `src[i]` into `dst[i]`. BOTH indexes are provably
// in bounds — the range-yield invariant gives `i < n`, and the loop-invariant
// `Ord::min` bound gives `n <= src.len()` AND `n <= dst.len()`, so `i < src.len()`
// and `i < dst.len()`. Exercises three modeled facts at once: range-yield, the
// `&mut [T]` metadata slice-length tie, and the global min result bound. Default
// mode must FULLY discharge both bounds checks (superior to rustc's two panics).
pub fn bounded_copy(dst: &mut [u8], src: &[u8]) {
    let n = src.len().min(dst.len());
    for i in 0..n {
        dst[i] = src[i];
    }
}
