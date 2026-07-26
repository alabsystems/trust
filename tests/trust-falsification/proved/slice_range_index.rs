#![crate_type = "lib"]
// `&s[..b]` (`RangeTo<usize>` SliceIndex on a runtime-length &[T]) under the
// CORRECT end-bound guard `b <= s.len()`. The `<[T] as Index<RangeTo>>::index`
// panic (`b > len`) is unreachable, and Trust now models the call's bounds
// obligation (`b > s.len()`) with the bound resolved to the param `b` and the
// length to `s__slice_len`, so the guard DISCHARGES it. Proves non-vacuously —
// the no-guard mutant (slice_range_index) is refused.
pub fn slice_rangeto_index(s: &[u8], b: usize) -> u8 {
    if b <= s.len() {
        let t = &s[..b];
        t.iter().copied().fold(0u8, |acc, x| acc.wrapping_add(x))
    } else {
        0
    }
}
