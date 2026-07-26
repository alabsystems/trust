#![crate_type = "lib"]
// MUTANT: `+` (real add) overflows on a free running sum. MUST be refused (exit 1) —
// guards the chained-adapter-yielded element is a real unconstrained value.
pub fn foreach_chain_rev_enum(s: &[u32]) -> u32 {
    let mut t = 0u32;
    for (_i, &x) in s.iter().rev().enumerate() {
        t = t + x;
    }
    t
}
