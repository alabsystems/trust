#![crate_type = "lib"]
// MUTANT + DISCRIMINATING guard: `+` (real add) overflows on a free running sum plus
// the yielded element. MUST be refused (exit 1) — guards that the `skip`-yielded
// element is a real unconstrained value.
pub fn foreach_skip(s: &[u32]) -> u32 {
    let mut t = 0u32;
    for &x in s.iter().skip(2) {
        t = t + x;
    }
    t
}
