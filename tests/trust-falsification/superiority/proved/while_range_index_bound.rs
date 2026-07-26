#![crate_type = "lib"]
// SUPERIORITY: `while i < s.len() { s[i]; i += 1 }` — rustc retains BOTH a runtime
// bounds check on `s[i]` AND an overflow check on `i += 1`. Trust proves both:
// the `i < s.len()` guard bounds the index, and the slice-length invariant
// `s.len() <= isize::MAX` proves `i + 1` cannot overflow (without it the SMT lane
// false-refutes with an impossible `s.len() = 2^64` counterexample). Default mode
// must report this fully proved (0 runtime-checked).
pub fn while_range_index_bound(s: &[u32]) -> u32 {
    let mut acc = 0u32;
    let mut i = 0usize;
    while i < s.len() {
        acc ^= s[i];
        i += 1;
    }
    acc
}
