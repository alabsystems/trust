#![crate_type = "lib"]
// MUTANT + DISCRIMINATING guard: replace `wrapping_add` with `+`, which overflows on
// a free running sum plus the two zipped elements. MUST be refused (exit 1). Guards
// that BOTH zip-yielded elements `x` and `y` are real unconstrained values — if the
// zip model mis-resolved them (e.g. aliased to 0), `t + x + y` could not overflow and
// the mutant would falsely prove.
pub fn foreach_zip(a: &[u32], b: &[u32]) -> u32 {
    let mut t = 0u32;
    for (&x, &y) in a.iter().zip(b.iter()) {
        t = t + x + y;
    }
    t
}
