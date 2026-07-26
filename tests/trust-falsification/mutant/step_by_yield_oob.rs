#![crate_type = "lib"]
// MUTANT (-full StepBy<Range> yield out of bounds): `for i in (0..9).step_by(1)`
// over a `[u8; 8]` yields i in {0, 1, …, 8} — the yield i can be 8 == len, which
// is OUT OF BOUNDS for an 8-element array. The native model bounds the yield by
// the EXCLUSIVE range end (`i < 9`), which does NOT imply `i < 8`, so the precise
// path finds the real counterexample (i=8). Genuinely violable (rc=101 at i=8),
// so `-full` MUST refute (exit 1). Pins that the yield bound tracks the ACTUAL
// range end (9), never the array length.
pub fn f(arr: &[u8; 8]) -> u8 {
    let mut s = 0u8;
    for i in (0..9).step_by(1) {
        s = s.wrapping_add(arr[i]);
    }
    s
}
