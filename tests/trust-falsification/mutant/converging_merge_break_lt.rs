#![crate_type = "lib"]
// MUTANT (CONVERGING-MERGE-1): `s[lo]` runs at the loop exit, which both the
// guard's FALSE edge and the `break` reach. On origin/main the relational guard did
// not certify `hi -= 1`, so `s[hi]` refuted and masked the false `s[lo]` row; the
// relational certificate of TWO-POINTER-FALSE-REFUTE removed that refutation.
// `c1(&mut [7])` indexes `s[1]`, `c1(&mut [])` `s[0]`.
//
// BEFORE (the gate's flags, measured 2026-10-10): `scratchpad/stage1-w21base`
// (origin/main `32b6ef82d6`) exit 1, `3 proved, 1 failed` (`[slice]` on `s[hi]`);
// the stage 1 of `5ccf66a518` (`integ/wave21`) exit 0, `4 proved, 0 failed`, all
// kernel-certified — SURVIVING MUTANT. AFTER: `[bounds]` refutes on `s[lo]`.
pub fn c1(s: &mut [u8]) {
    let mut lo = 0;
    let mut hi = s.len();
    while lo < hi {
        hi -= 1;
        if s[hi] == 0 {
            break;
        }
        lo += 1;
    }
    s[lo] = 1;
}
