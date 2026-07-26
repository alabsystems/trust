#![crate_type = "lib"]
// The CORRECT strict bounds guard: `i < s.len()` makes `s[i]` provably in-bounds,
// so Trust discharges the bounds check STATICALLY (superior to rustc, which keeps
// the runtime panic). Pairs with the mutant, which weakens `<` to `<=` — the
// classic off-by-one. Guards that the verifier distinguishes `i < len` (safe) from
// `i <= len` (out-of-bounds at `i == len`) at the boundary.
pub fn offbyone_len_guard(s: &[u32], i: usize) -> u32 {
    if i < s.len() { s[i] } else { 0 }
}
