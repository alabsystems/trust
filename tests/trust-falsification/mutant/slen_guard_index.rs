#![crate_type = "lib"]
// MUTANT of `proved/slen_guard_index.rs`: the index is now `7`, but the guard
// `len > 5` only ensures `len >= 6`, so `s[7]` is out of bounds when `len` is 6
// or 7. The transitive chain `5 < len <= _5 <= _4 <= 7` does NOT yield a false
// constant (`5 < 7` is true), so the obligation is SAT and neither the chain nor
// the solver can discharge it; the verifier MUST fail closed (`[bounds] FAILED`).
pub fn slen_guard_index(s: &[i32]) -> i32 {
    if s.len() > 5 { s[7] } else { 0 }
}
