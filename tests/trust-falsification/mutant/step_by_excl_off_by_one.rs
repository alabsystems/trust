#![crate_type = "lib"]
// MUTANT (-full StepBy<Range> EXCLUSIVE-bound off-by-one — the RED-TEAM guard):
// inside `for i in (0..8).step_by(1)` over a `[u8; 8]`, index `arr[i + 1]`. The
// native yield model gives `i < 8` (EXCLUSIVE), so `i` can be 7 and `i + 1` can be
// 8 == the exclusive end == the FIRST out-of-bounds index. This is genuinely
// violable (rc=101 at i=7), so `-full` MUST refute (exit 1).
//
// This is THE soundness pin for the `hi_is_exclusive` flag: with the EXCLUSIVE
// upper (`i < 8`, Ult) the solver cannot prove `i + 1 < 8` (i=7 is a real
// counterexample) and refutes. With the OLD hard-coded INCLUSIVE upper (`i <= 8`,
// Ule — the pre-fix behavior shared with the bit-count caller) the model would
// admit `i <= 8` but STILL not prove `i + 1 < 8`; the decisive companion is the
// `proved/step_by_step1_full` twin, where `arr[i]` (i<8) PROVES — together they
// show the bound is EXACTLY `[0, 8)`, neither too loose nor too tight.
pub fn f(arr: &[u8; 8]) -> u8 {
    let mut s = 0u8;
    for i in (0..8).step_by(1) {
        s = s.wrapping_add(arr[i + 1]);
    }
    s
}
