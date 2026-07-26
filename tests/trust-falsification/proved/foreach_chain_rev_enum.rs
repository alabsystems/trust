#![crate_type = "lib"]
// CHAINED total adapters: `s.iter().rev().enumerate()`. Both `Rev` and `Enumerate`
// wrap a slice-backed iterator (recursively recognized), and the yielded
// `Option<(usize, &T)>` is a nested aggregate (tracked, #46). `wrapping_add` has no
// overflow obligation, so the loop proves under the default strict policy.
pub fn foreach_chain_rev_enum(s: &[u32]) -> u32 {
    let mut t = 0u32;
    for (_i, &x) in s.iter().rev().enumerate() {
        t = t.wrapping_add(x);
    }
    t
}
