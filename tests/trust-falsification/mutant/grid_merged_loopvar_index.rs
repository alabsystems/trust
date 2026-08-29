#![crate_type = "lib"]
// MERGED LOCAL INSIDE A NESTED LOOP. Two nested `for` loops walk a 2x3 grid; the
// index is `let i = if c { y * 3 + x } else { b }`, where `b` is an unconstrained
// parameter, and the body reads `g[i]` on a `[u8; 6]`. IT FAULTS: whenever
// `c == false` and `b >= 6` the first read is out of bounds and the body panics.
// Runtime oracle (stock rustc, -O -C debug-assertions=on, #[inline(never)],
// black_box, catch_unwind, silent hook): 6 panics / 24 runs, sweep
// `c in {true, false}` x `b in 0..=11` (2*12) — the 6 are exactly
// `c == false, b in 6..=11`.
//
// *** THIS FIXTURE IS RED ON BOTH COLUMNS. IT IS A LIVE FALSE PROOF, NOT A
// *** FIXTURE DEFECT. Measured under `-Ztrust-policy=certify`: pristine
// *** `70a7534fd1` answers `proved` and `campaign-integration` ALSO answers
// *** `proved`, reporting "4 proved, 0 failed, 0 unknown, 0 timed out,
// *** 0 runtime-checked out of 4 obligation(s)" and "4 kernel-certified by the
// *** clean CIC kernel". The compiler certifies a program the oracle panics on
// *** in 6 of 24 sampled inputs. The gate must therefore report
// *** "SURVIVING MUTANT" here until the defect is fixed; that row is the point
// *** of the fixture. It is in the GATED lane rather than `pending/` because
// *** `pending/` is documented as quarantine for CAPABILITY GAPS, and this is
// *** neither a decline nor an unknown — it is an affirmative proof of a false
// *** statement.
//
// THE SHAPE IS NARROWER THAN "a merged local". Measured on both columns, all of
// these near-neighbours are correctly `refuted` and so do NOT reproduce it:
// the flat merge (`let i = if c { 1 } else { b }; g[i]`), the same merge inside
// ONE `for` loop, a loop-carried `while` variant, a merge reseated through
// `&mut`, an `enum`-match merge, and a written-once PARAMETER merge. So does the
// nested-loop version whose taken branch is a CONSTANT rather than a loop
// expression. What survives is the conjunction: nested loops AND a merged local
// whose taken branch is an arithmetic expression over both loop variables.
// A second instance of the same conjunction — the identical body with the `bool`
// parameter replaced by the guard `b > 100` — also answers `proved` on both
// columns, so the surviving shape is not a one-off of this exact source.
//
// The safe control that must keep proving is `proved/grid_unmerged_loopvar_index.rs`:
// the same nested loops and the same `y * 3 + x`, without the merge.
pub fn grid_merged_loopvar_index(g: &[u8; 6], c: bool, b: usize) -> u8 {
    let mut acc = 0u8;
    for y in 0..2usize {
        for x in 0..3usize {
            let i = if c { y * 3 + x } else { b };
            acc = acc.wrapping_add(g[i]);
        }
    }
    acc
}
