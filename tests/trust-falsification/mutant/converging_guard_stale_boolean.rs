#![crate_type = "lib"]
// MUTANT, a FALSE PROOF before its fix (CONVERGING-GUARD-STALE-1): `c = lo < hi`
// is computed BEFORE `lo += 1`, and the call to `tick` puts the increment in a block
// of its own before the switch on `c`. The converging fact `lo < s.len()` holds of
// the COMPARED `lo`, but was emitted in the body of the INCREMENTED one (both of the
// builder's walks start at the switch, after the increment). `conv_stale3(&mut [0])`
// indexes `s[1]` (runtime oracle, verify off). `lo > 1000 -> break` keeps the
// increment's own overflow row provable, so nothing else refuted the function.
//
// BEFORE (`scratchpad/stage1-w21before`, the gate's flags, measured 2026-10-06, again 2026-10-09):
// exit 0, `3 proved, 0 failed`, all kernel-certified — SURVIVING MUTANT. AFTER
// (predicted, not built): the comparison and the read of `lo` must sit in the switch
// block with no later write of `lo`, so no fact is emitted and `[bounds]` refutes.
#[inline(never)]
fn tick() {}

pub fn conv_stale3(s: &mut [u8]) {
    let mut lo = 0;
    let mut hi = s.len();
    loop {
        if lo > 1000 {
            break;
        }
        let c = lo < hi;
        lo += 1;
        tick();
        if c {
            hi -= 1;
            s[lo] = 0;
        } else {
            break;
        }
    }
}
