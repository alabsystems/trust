#![crate_type = "lib"]
// MUTANT of `proved/two_pointer_reverse.rs` (TWO-POINTER-FALSE-REFUTE twin): the
// accesses run BEFORE `hi -= 1`, so `s[hi]` reads at `hi == s.len()`. Runtime
// oracle: `tpr_late(&mut [1])` panics "index out of bounds: the len is 1 but the
// index is 1".
//
// The relational guard DOES certify this function's decrement (`hi >= 1` there),
// and the fact it gains, `_26.0 < s.len()`, is true. It is a fact about the
// decrement's RESULT; the out-of-bounds reads index the loop-head `hi`.
//
// BEFORE (`scratchpad/stage1-w21before`, the gate's flags, measured 2026-10-06, again 2026-10-09):
// exit 1, `4 proved, 2 failed` (`[bounds]`, `[slice]`). AFTER (predicted): refuted.
pub fn tpr_late(s: &mut [u8]) {
    let mut lo = 0;
    let mut hi = s.len();
    while lo < hi {
        let t = s[lo];
        s[lo] = s[hi];
        s[hi] = t;
        hi -= 1;
        lo += 1;
    }
}
