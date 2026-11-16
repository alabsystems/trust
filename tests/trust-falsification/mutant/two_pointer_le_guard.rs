#![crate_type = "lib"]
// MUTANT of `proved/two_pointer_reverse.rs` (TWO-POINTER-FALSE-REFUTE twin): the
// guard is `lo <= hi`. `Le` is never an underflow certificate — at
// `lo == hi == 0` (an empty slice) `hi -= 1` underflows. Runtime oracle: `tpr_le(&mut
// [])` panics "attempt to subtract with overflow".
//
// BEFORE (`scratchpad/stage1-w21before`, the gate's flags, measured 2026-10-06, again 2026-10-09):
// exit 1, `2 proved, 4 failed` incl. `[overflow:sub]`. AFTER (predicted): unchanged.
pub fn tpr_le(s: &mut [u8]) {
    let mut lo = 0;
    let mut hi = s.len();
    while lo <= hi {
        hi -= 1;
        let t = s[lo];
        s[lo] = s[hi];
        s[hi] = t;
        lo += 1;
    }
}
