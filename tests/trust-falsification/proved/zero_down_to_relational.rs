#![crate_type = "lib"]
// FALSE-REFUTATION GUARD (TWO-POINTER-FALSE-REFUTE): a downward loop whose guard is
// RELATIONAL — `while lo < hi { hi -= 1; s[hi] = 0 }` with `lo` an unsigned
// PARAMETER. `lo < hi` and `lo >= 0` give `hi >= 1`, so `hi - 1` never wraps and
// `hi - 1 < s.len()` (`hi <= s.len()` is the downward invariant).
//
// Runtime oracle (verify off, overflow checks on): every length 0..63 and every
// `lo` in 0..=len+2 zeroes exactly `s[lo..]`, no panic.
//
// BEFORE (`scratchpad/stage1-w21before`, the gate's flags, measured 2026-10-06, again 2026-10-09):
// exit 1, `1 proved, 1 failed` — `[bounds]` on `s[hi]`. AFTER (predicted, not
// built): 2/2 proved.
pub fn zero_down_to(s: &mut [u8], lo: usize) {
    let mut hi = s.len();
    while lo < hi {
        hi -= 1;
        s[hi] = 0;
    }
}
