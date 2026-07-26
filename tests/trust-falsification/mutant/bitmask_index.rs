#![crate_type = "lib"]
// MUTANT of `proved/bitmask_index.rs`: the mask is now 31, but the array length
// is still 16, so `i & 31` ranges over 0..=31 and can be >= 16 — out of bounds.
// The result bound is `i&31 <= 31`, which does NOT contradict the violation
// `i&31 >= 16` (e.g. i&31 = 20), so the verifier MUST fail closed.
pub fn bitmask_index(s: &[i32; 16], i: usize) -> i32 {
    s[i & 31]
}
