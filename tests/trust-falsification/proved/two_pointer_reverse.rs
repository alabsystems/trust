#![crate_type = "lib"]
// FALSE-REFUTATION GUARD (TWO-POINTER-FALSE-REFUTE): in-place reversal by
// converging pointers — `lo` rises from 0, `hi` falls from `s.len()`, loop while
// `lo < hi`. BOTH `s[lo]` and `s[hi]` are in bounds and `hi -= 1` cannot underflow
// (`lo < hi` with `lo: usize >= 0` gives `hi >= 1`). The twin of
// `superiority/proved/two_pointer_reverse.rs`, which the gate does not scan.
//
// `s[hi]` rides the downward-induction fact `hi - 1 < s.len()`, which needs an
// underflow certificate for the decrement: since 7180f666c3 only a CONSTANT guard
// (`while i > 0`) gave one, so this function was refuted with `hi = 2 > s.len() = 1`
// at the loop head — a state it cannot reach. The relational guard over an
// unsigned `lo` now certifies `hi >= 1` (`induction::downward_guards`).
//
// Runtime oracle (verify off, overflow checks on): every length 0..63 reverses
// correctly, no panic.
//
// BEFORE (`scratchpad/stage1-w21before`, the stage 1 of 46e9afaf95; the gate's
// flags, measured 2026-10-06, again 2026-10-09): exit 1, `4 proved, 2 failed` — `[bounds]` and
// `[slice]` on the two `s[hi]` accesses. AFTER (predicted, not built): 6/6 proved.
pub fn two_pointer_reverse(s: &mut [u8]) {
    let mut lo = 0;
    let mut hi = s.len();
    while lo < hi {
        hi -= 1;
        let t = s[lo];
        s[lo] = s[hi];
        s[hi] = t;
        lo += 1;
    }
}
