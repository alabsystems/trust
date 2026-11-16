#![crate_type = "lib"]
// MUTANT (DOWNWARD-PARAM-CURSOR-1): the downward cursor is a `mut` PARAMETER,
// re-initialised to `s.len()` only when `c`. A parameter is defined at entry by
// no statement, so the def scan read "one init, `s.len()`" and emitted
// `i - 1 < s.len()`; the `s[i]` row was proved and kernel-certified although
// `param_cursor(&mut [0; 4], 9, false)` indexes `s[8]` (runtime oracle, verify off).
//
// BEFORE (`scratchpad/stage1-w21before`, the gate's flags, measured 2026-10-06, again 2026-10-09):
// exit 1, `2 proved, 0 failed, 1 unknown` — refused only by the unrelated
// `[termination]` UNKNOWN, which the gate scores `incomplete` (UNCAUGHT MUTANT), not
// refuted. AFTER (predicted, not built): a parameter cursor qualifies only if its
// entry value reaches no decrement; here the `!c` path reaches it without an init,
// so `i` gets no downward facts and `[bounds]` refutes.
pub fn param_cursor(s: &mut [u8], mut i: usize, c: bool) {
    if c {
        i = s.len();
    }
    while i > 0 {
        i -= 1;
        s[i] = 0;
    }
}
