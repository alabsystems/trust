#![crate_type = "lib"]
// Chained `Ord::min`: `n = a.len().min(b.len()).min(c.len())` bounds `n` by all
// three slice lengths (the outer min's `n <= inner` chains through the inner min's
// `inner <= a.len()`/`<= b.len()`). With the range-yield `i < n`, all three indexes
// a[i]/b[i]/c[i] are provably in bounds — default mode discharges every check.
pub fn min_three(a: &[u8], b: &[u8], c: &[u8]) -> u8 {
    let n = a.len().min(b.len()).min(c.len());
    let mut t = 0u8;
    for i in 0..n {
        t ^= a[i] ^ b[i] ^ c[i];
    }
    t
}
