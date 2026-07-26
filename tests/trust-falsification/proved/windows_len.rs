#![crate_type = "lib"]
// `for w in s.windows(2)` — the #46 sub-slice-iterator lane. `<[T]>::windows(n)`
// CONSTRUCTS a `Windows` iterator yielding `&[T]` sub-slices; its `next` is
// unconditionally total (the ONLY panic in the API is the constructor's
// `assert!(n != 0)`, discharged here because `2` is a literal `>= 1`). The body
// reads `w.len()` (a total `::slice::len` summary → fresh-symbolic usize) and sums
// with `wrapping_add` (no overflow obligation), so the loop proves panic-free under
// the default strict policy. Pairs with mutant/windows_len.rs (overflow value-tracking)
// and mutant/chunks_zero.rs (the panic-on-zero soundness guard).
pub fn windows_len(s: &[u32]) -> u32 {
    let mut t = 0u32;
    for w in s.windows(2) {
        t = t.wrapping_add(w.len() as u32);
    }
    t
}
