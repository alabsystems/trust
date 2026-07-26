#![crate_type = "lib"]
// NESTED for-each loops over two slices — both iterator-modeled, the inner loop's
// CHC nested inside the outer. `wrapping_add` is panic-free, so it proves under
// the default strict policy.
pub fn nested_for_loops(a: &[u32], b: &[u32]) -> u32 {
    let mut t = 0u32;
    for &x in a {
        for &y in b {
            t = t.wrapping_add(x).wrapping_add(y);
        }
    }
    t
}
