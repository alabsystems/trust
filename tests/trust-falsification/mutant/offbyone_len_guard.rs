#![crate_type = "lib"]
// MUTANT of proved/offbyone_len_guard.rs: the one-token off-by-one `<` → `<=`.
// `if i <= s.len() { s[i] }` indexes `s[len]` when `i == s.len()` — one past the
// end, an out-of-bounds read. The verifier MUST refuse this (exit 1): the guard
// `i <= len` does NOT imply `i < len`, so the bounds obligation `i < len` is not
// discharged. A surviving mutant would mean the verifier conflates `<` and `<=` at
// the boundary — a soundness hole.
pub fn offbyone_len_guard(s: &[u32], i: usize) -> u32 {
    if i <= s.len() { s[i] } else { 0 }
}
