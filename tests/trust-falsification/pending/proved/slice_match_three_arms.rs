#![crate_type = "lib"]
// QUARANTINED — CAPABILITY GAP on the branch, over-refutation at the base.
// A three-arm slice pattern: `[] => 0`, `[x] => *x`, `[x, .., y] => x + y`
// (wrapping). IT DOES NOT FAULT: the arms partition every possible length and
// each binding is a pattern binding, so no index can be out of range and the
// addition wraps by construction.
// Runtime oracle (stock rustc, -O -C debug-assertions=on, #[inline(never)],
// black_box, catch_unwind, silent hook): 0 panics / 65 runs, sweep = every
// slice length 0..=64, which reaches all three arms.
//
// Measured under `-Ztrust-policy=certify`: pristine `70a7534fd1` answers
// `refuted`; `campaign-integration` answers `incomplete` with
// `0 failed, 1 unknown, 1 runtime-checked` and three rows the native lane
// reports as unsupported (`the proof certificate is replayable but not
// release-admissible`, and a PDR candidate that `require[s] fresh private
// consumer replay before proof-grade admission`). The branch therefore moved
// this shape off a wrong answer and onto an honest coverage gap, which is
// progress but is not a proof — so it cannot be a `proved/` fixture yet.
// Move it to `proved/` when the admissibility lane closes.
pub fn slice_match_three_arms(a: &[u8]) -> u8 {
    match a {
        [] => 0u8,
        [x] => *x,
        [x, .., y] => x.wrapping_add(*y),
    }
}
