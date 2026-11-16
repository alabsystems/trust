#![crate_type = "lib"]
// MUTANT (TWO-POINTER-FALSE-REFUTE twin): two decrements under one `lo < hi`.
// The second sees `hi - 1`, which can be 0: at `lo = 0, hi = 1` it underflows. The
// guard certifies only the FIRST decrement (`GuardReach::certifies`: no write of the
// cursor between the guard and the decrement).
//
// BEFORE (`scratchpad/stage1-w21before`, the gate's flags, measured 2026-10-06, again 2026-10-09):
// exit 1, `1 proved, 2 failed` (`[bounds]`, `[overflow:sub]`). AFTER (predicted):
// refuted on the second decrement's `[overflow:sub]`.
pub fn rel_twice(s: &mut [u8], lo: usize) {
    let mut hi = s.len();
    while lo < hi {
        hi -= 1;
        hi -= 1;
        s[hi] = 0;
    }
}
