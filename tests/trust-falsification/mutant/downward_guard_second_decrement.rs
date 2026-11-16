#![crate_type = "lib"]
// MUTANT, a FALSE PROOF before its fix (DOWNWARD-GUARD-SECOND-DEC-1): the guard
// `i > 1` gives the FIRST decrement's result `_t.0 >= 1`. The SECOND decrement sees
// `i - 1`, so its result can be 0 — but it inherited the same `>= 1`, which
// discharged the `i - 1` underflow below. At `a.len() == 2`: `i = 2 -> 1 -> 0`, and
// `a[i - 1]` panics "attempt to subtract with overflow" (runtime oracle, verify off).
// Built WITH verification, the false proof ELIDED that check: the subtraction
// wrapped and the program died on the bounds check instead (`index ... is
// 18446744073709551615`).
//
// BEFORE (`scratchpad/stage1-w21before`, the gate's flags, measured 2026-10-06, again 2026-10-09):
// exit 0, `4 proved, 0 failed` — SURVIVING MUTANT. AFTER (predicted, not built):
// a guard certifies a decrement only if the cursor is unwritten between the guard
// and it (`GuardReach::certifies`), so the second decrement gets no bound and the
// `[overflow:sub]` row refutes.
pub fn ge_twice(a: &mut [u8]) {
    let mut i = a.len();
    while i > 1 {
        i -= 1;
        i -= 1;
        a[i - 1] = 0;
    }
}
