#![crate_type = "lib"]
// `for (i, _) in s.iter().enumerate()` yields the index `i` with the loop-invariant
// `0 <= i < s.len()` (the enumerate count over a slice iterator runs 0..len), so
// `s[i]` is provably in bounds. Default mode must FULLY discharge the check.
pub fn enumerate_index(s: &[u32]) -> u32 {
    let mut acc = 0u32;
    for (i, _) in s.iter().enumerate() {
        acc = acc.wrapping_add(s[i]);
    }
    acc
}
