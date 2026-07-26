#![crate_type = "lib"]
// `for (i, &x) in s.iter().enumerate()` — the enumerate desugar yields
// `Option<(usize, &T)>`, a nested aggregate now tracked in the CHC (#46). The body
// sums with `wrapping_add` (no overflow obligation), so the loop proves panic-free
// under the default strict policy.
pub fn foreach_enumerate(s: &[u32]) -> u32 {
    let mut t = 0u32;
    for (_i, &x) in s.iter().enumerate() {
        t = t.wrapping_add(x);
    }
    t
}
