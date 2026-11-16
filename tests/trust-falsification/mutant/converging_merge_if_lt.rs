#![crate_type = "lib"]
// MUTANT, a FALSE PROOF on origin/main (CONVERGING-MERGE-1): `s[lo]` runs at the
// merge after `if lo < hi { .. }`, which the guard's FALSE edge also reaches.
// `build_converging_pointer_facts` gave every block reachable from the TRUE target
// the fact `lo < s.len()`, the merge included. `c3(&mut [0], 5)` indexes `s[5]`
// (runtime oracle, verify off: "the len is 1 but the index is 5").
//
// BEFORE (the gate's flags, measured 2026-10-10): exit 0, `3 proved, 0 failed` —
// SURVIVING MUTANT — on `scratchpad/stage1-w21base` (origin/main `32b6ef82d6`; 2
// kernel-certified, the false `s[lo]` `[bounds]` row among them) and on the stage 1
// of `5ccf66a518` (`integ/wave21`; all 3 kernel-certified). AFTER (the stage 1 of the
// fix): exit 1, `2 proved, 1 failed`, `[bounds]` refuted at `lo = 0, s.len() = 0` —
// the fact stops at blocks the true edge certifies (`TrueEdgeReach::certifies`).
pub fn c3(s: &mut [u8], lo: usize) {
    let mut hi = s.len();
    if lo < hi {
        hi -= 1;
        s[hi] = 0;
    }
    s[lo] = 1;
}
