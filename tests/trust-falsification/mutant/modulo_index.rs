#![crate_type = "lib"]
// MUTANT of `proved/modulo_index.rs`: the modulus is now 9 but the array length
// is still 8, so `i % 9 ∈ 0..9` can be 8 — out of bounds. The result-bound fact
// is `i%9 < 9`, which does NOT contradict the violation `i%9 >= 8` (e.g. i%9 = 8),
// so the case-split cannot close it; the verifier MUST fail closed.
pub fn modulo_index(s: &[i32; 8], i: usize) -> i32 {
    s[i % 9]
}
