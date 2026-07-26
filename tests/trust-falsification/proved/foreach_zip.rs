#![crate_type = "lib"]
// `for (&x, &y) in a.iter().zip(b.iter())` — the zip desugar yields
// `Option<(&u32, &u32)>` (a nested aggregate, tracked) and `Zip<slice::Iter,
// slice::Iter>::next` is total (both inner iterators are slice-backed — the #46
// adapter recognizer requires BOTH, the soundness gate). The body sums with
// `wrapping_add` (no overflow obligation), so the loop proves panic-free under
// the default strict policy.
pub fn foreach_zip(a: &[u32], b: &[u32]) -> u32 {
    let mut t = 0u32;
    for (&x, &y) in a.iter().zip(b.iter()) {
        t = t.wrapping_add(x).wrapping_add(y);
    }
    t
}
