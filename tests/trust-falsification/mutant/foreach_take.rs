#![crate_type = "lib"]
// MUTANT + DISCRIMINATING guard: `+` (real add) overflows on a free running sum plus
// the yielded element. MUST be refused (exit 1) — guards that the `take`-yielded
// element is a real unconstrained value.
pub fn foreach_take(s: &[u32]) -> u32 {
    let mut t = 0u32;
    for &x in s.iter().take(2) {
        t = t + x;
    }
    t
}
