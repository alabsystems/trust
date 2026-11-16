#![crate_type = "lib"]
// MUTANT (CONVERGING-MERGE-1): `converging_merge_break_lt.rs` with the guard spelled
// `hi > lo`. `c2(&mut [7])` indexes `s[1]`.
//
// BEFORE (the gate's flags, measured 2026-10-10): `scratchpad/stage1-w21base`
// (origin/main `32b6ef82d6`) exit 1, `2 proved, 2 failed` (`[bounds]` on `s[lo]`,
// `[slice]` on `s[hi]`);
// the stage 1 of `5ccf66a518` (`integ/wave21`) exit 0, `4 proved, 0 failed`, all
// kernel-certified — SURVIVING MUTANT. AFTER: `[bounds]` refutes on `s[lo]`.
pub fn c2(s: &mut [u8]) {
    let mut lo = 0;
    let mut hi = s.len();
    while hi > lo {
        hi -= 1;
        if s[hi] == 0 {
            break;
        }
        lo += 1;
    }
    s[lo] = 1;
}
