#![crate_type = "lib"]
// FALSE-REFUTATION GUARD (TWO-POINTER-FALSE-REFUTE): the two-pointer reverse with
// its guard spelled `hi > lo`. MIR keeps the spelling (`Gt(hi, lo)`), and neither
// the downward-induction certificate nor the converging `lo < s.len()` fact read
// it before; both now treat it as `lo < hi`.
//
// BEFORE (`scratchpad/stage1-w21before`, the gate's flags, measured 2026-10-06, again 2026-10-09):
// exit 1, `3 proved, 3 failed` — `[bounds]` on `s[hi]` and `[slice]` on both
// `s[lo]`. AFTER (predicted, not built): 6/6 proved.
pub fn tpr_gt(s: &mut [u8]) {
    let mut lo = 0;
    let mut hi = s.len();
    while hi > lo {
        hi -= 1;
        let t = s[lo];
        s[lo] = s[hi];
        s[hi] = t;
        lo += 1;
    }
}
