#![crate_type = "lib"]
// A CONJUNCTIVE-guard two-index slice access: BOTH `i` and `j` are bounded by the
// same `&&` guard before indexing. rustc inserts two runtime bounds-panic checks;
// Trust discharges BOTH statically under the default strict policy (the dominating-guard
// enrichment threads each conjunct `i < s.len()` / `j < s.len()` to its access). The
// body uses `wrapping_add` so the ONLY obligations are the two bounds checks — this
// is the multi-guard case, where a guard-tracking bug (forgetting one conjunct) would
// most likely hide. Pairs with mutant/conj_guard_two_index.rs (the j-guard dropped).
pub fn conj_guard_two_index(s: &[u32], i: usize, j: usize) -> u32 {
    if i < s.len() && j < s.len() {
        s[i].wrapping_add(s[j])
    } else {
        0
    }
}
