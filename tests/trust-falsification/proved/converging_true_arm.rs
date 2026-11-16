#![crate_type = "lib"]
// FALSE-REFUTATION GUARD (CONVERGING-MERGE-1 control): `s[lo]` inside the TRUE arm
// of `if hi > lo`, the block the guard's true edge certifies. The fix withdraws the
// converging `lo < s.len()` fact only from blocks the false edge (or the entry) also
// reaches, so this access keeps it.
//
// BEFORE (the gate's flags, measured 2026-10-10): exit 0, `3 proved, 0 failed`, on
// `scratchpad/stage1-w21base` (origin/main `32b6ef82d6`) and on the stage 1 of
// `5ccf66a518` (`integ/wave21`). AFTER: unchanged.
pub fn inside(s: &mut [u8], lo: usize) {
    let mut hi = s.len();
    if hi > lo {
        hi -= 1;
        s[hi] = 0;
        s[lo] = 1;
    }
}
