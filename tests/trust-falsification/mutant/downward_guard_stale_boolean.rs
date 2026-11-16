#![crate_type = "lib"]
// MUTANT, a FALSE PROOF before its fix (DOWNWARD-GUARD-STALE-1): `c` compares `i`
// BEFORE the first decrement, and the switch on `c` came after it. Read as a guard
// `i > 1` on the cursor at the switch, it gave the second decrement `_t.0 >= 1`,
// discharging the `i - 1` underflow. At `a.len() == 2` the body sees `i == 1`, the
// second decrement leaves 0, and `a[i - 1]` panics "attempt to subtract with
// overflow" (runtime oracle, verify off; built with verification the check was
// elided and the bounds check caught the wrapped index instead).
//
// BEFORE (`scratchpad/stage1-w21before`, the gate's flags, measured 2026-10-06, again 2026-10-09):
// exit 0, `4 proved, 0 failed` — SURVIVING MUTANT. AFTER (predicted, not built):
// a guard's comparison and its read of the cursor must sit in the switch block
// with no later write of the cursor (`induction::downward_guards`), so `c` is no
// guard and the `[overflow:sub]` row refutes.
pub fn stale(a: &mut [u8]) {
    let mut i = a.len();
    if i != 0 {
        let c = i > 1;
        i -= 1;
        if c {
            i -= 1;
            a[i - 1] = 0;
        }
    }
}
