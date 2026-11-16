#![crate_type = "lib"]
// MUTANT (CONVERGING-MERGE-1): `converging_merge_if_lt.rs` with the guard spelled
// `hi > lo`. The `Gt(hi, lo)` spelling reached `build_converging_pointer_facts` with
// TWO-POINTER-FALSE-REFUTE, which made this shape a new false proof on
// `integ/wave21`. `c4(&mut [0], 5)` indexes `s[5]`.
//
// BEFORE (the gate's flags, measured 2026-10-10): `scratchpad/stage1-w21base`
// (origin/main `32b6ef82d6`) exit 1, `2 proved, 1 failed` (`[bounds]` on `s[lo]`, which
// main's converging builder did not read under `Gt`); the stage 1
// of `5ccf66a518` (`integ/wave21`) exit 0, `3 proved, 0 failed`, all kernel-certified
// — SURVIVING MUTANT. AFTER: `[bounds]` refutes.
pub fn c4(s: &mut [u8], lo: usize) {
    let mut hi = s.len();
    if hi > lo {
        hi -= 1;
        s[hi] = 0;
    }
    s[lo] = 1;
}
