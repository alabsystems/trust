#![crate_type = "lib"]
// MUTANT + DISCRIMINATING guard: replace `wrapping_add` with `+`, which overflows
// when the running sum plus the yielded element exceeds u32::MAX. MUST be refused
// (exit 1). This guards that the enumerate-YIELDED element `x` is a real unconstrained
// u32 — if it were mis-modeled (e.g. aliased to 0), `t + x` could not overflow and
// the mutant would falsely prove.
pub fn foreach_enumerate(s: &[u32]) -> u32 {
    let mut t = 0u32;
    for (_i, &x) in s.iter().enumerate() {
        t = t + x;
    }
    t
}
