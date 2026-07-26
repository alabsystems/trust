#![crate_type = "lib"]
// MUTANT + DISCRIMINATING guard of proved/conj_guard_two_index.rs: the ONLY change
// drops the second conjunct, so only `i` is guarded while `s[j]` is still indexed.
// `s[j]` is now an unbounded access (`j` can be >= s.len()) — the bounds obligation
// for `s[j]` is SAT, cannot be closed, and the verifier MUST fail closed
// (`[bounds] FAILED`, exit 1). This is the critical multi-guard soundness guard: a
// model that tracked "some guard exists" rather than "this index's guard exists"
// would falsely prove the unguarded `s[j]` access.
pub fn conj_guard_two_index(s: &[u32], i: usize, j: usize) -> u32 {
    if i < s.len() {
        s[i].wrapping_add(s[j])
    } else {
        0
    }
}
