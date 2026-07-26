#![crate_type = "lib"]
// MUTANT: `+` (real add) overflows in the inner loop. MUST be refused (exit 1) —
// guards both nested-loop-yielded elements are real unconstrained values.
pub fn nested_for_loops(a: &[u32], b: &[u32]) -> u32 {
    let mut t = 0u32;
    for &x in a {
        for &y in b {
            t = t + x + y;
        }
    }
    t
}
