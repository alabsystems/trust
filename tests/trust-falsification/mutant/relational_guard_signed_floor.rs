#![crate_type = "lib"]
// MUTANT (TWO-POINTER-FALSE-REFUTE twin): a SIGNED floor. `lo: i64` can be
// negative, so `lo < hi` does not give `hi >= 1`: with `lo = -1` the loop drives
// `hi` to -1 and `a[hi as usize]` indexes `a[usize::MAX]`. Only an UNSIGNED `x`
// in `x < hi` is a relational guard.
//
// BEFORE (`scratchpad/stage1-w21before`, the gate's flags, measured 2026-10-06, again 2026-10-09):
// exit 1, `1 proved, 1 failed` (`[bounds]`). AFTER (predicted): unchanged.
pub fn signed_rel(a: &mut [u8; 8], lo: i64) {
    let mut hi: i64 = 8;
    while lo < hi {
        hi -= 1;
        a[hi as usize] = 0;
    }
}
