#![crate_type = "lib"]
// `for &x in s.iter().take(2)` — the `take` total adapter over a slice iterator.
// Yielded elements are real unconstrained u32; `wrapping_add` has no overflow
// obligation, so it proves under the default strict policy.
pub fn foreach_take(s: &[u32]) -> u32 {
    let mut t = 0u32;
    for &x in s.iter().take(2) {
        t = t.wrapping_add(x);
    }
    t
}
