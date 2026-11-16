#![crate_type = "lib"]
// MUTANT (TWO-POINTER-FALSE-REFUTE twin): stride 2 under the relational guard
// `lo < hi`. The guard gives `hi >= 1`, never `hi >= 2`, so it certifies `K = 0`
// and `k + 1 >= c` fails for `c = 2`: at `lo = 0, hi = 1` `hi -= 2` underflows.
//
// BEFORE (`scratchpad/stage1-w21before`, the gate's flags, measured 2026-10-06, again 2026-10-09):
// exit 1, `0 proved, 2 failed` (`[bounds]`, `[overflow:sub]`). AFTER (predicted):
// unchanged.
pub fn rel_dec2(s: &mut [u8], lo: usize) {
    let mut hi = s.len();
    while lo < hi {
        hi -= 2;
        s[hi] = 0;
    }
}
