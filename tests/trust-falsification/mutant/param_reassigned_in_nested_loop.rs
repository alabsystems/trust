#![crate_type = "lib"]
// A PARAMETER REASSIGNED INSIDE A NESTED LOOP, WITH ITS ENTRY VALUE READ ON THE
// OTHER BRANCH. `i` is a `usize` parameter. When `c` holds, two nested `for`
// loops overwrite it with `y * 3 + x` (0..=5) and read `g[i]` on a `[u8; 6]`;
// when `c` is false the function instead reads `g[i]` at the value the CALLER
// passed, which is unconstrained. IT FAULTS: `c == false` with `i >= 6` indexes
// out of bounds.
// Runtime oracle (stock rustc, -O -C debug-assertions=on, #[inline(never)],
// black_box, catch_unwind, silent hook): 6 panics / 24 runs, sweep
// `c in {true, false}` x `i in 0..=11` (2*12) — the 6 are exactly
// `c == false, i in 6..=11`.
//
// *** RED ON BOTH COLUMNS. A LIVE FALSE PROOF, NOT A FIXTURE DEFECT.
// *** Under `-Ztrust-policy=certify`, pristine `70a7534fd1` answers `proved`,
// *** reporting "5 proved, 0 failed, 0 unknown, 0 timed out, 0 runtime-checked
// *** out of 5 obligation(s)" and "5 kernel-certified by the clean CIC kernel".
// *** `campaign-integration` answers the same: the branch carries no fix for
// *** this class. The gate must report "SURVIVING MUTANT" here until one lands.
// *** Gated lane rather than `pending/` for the same reason as
// *** `grid_merged_loopvar_index.rs`: `pending/` quarantines CAPABILITY GAPS,
// *** and this is an affirmative proof of a false statement.
//
// DISTINCT FROM THE NEIGHBOURS ALREADY RULED OUT. `grid_merged_loopvar_index.rs`
// lists a "written-once PARAMETER merge" among shapes that refute correctly —
// that is `let i = if c { .. } else { param }`, where the parameter is only READ.
// Here the parameter is WRITTEN, and the surviving value on the other branch is
// its ENTRY value. The two are different channels and only this one survives.
//
// WHY IT MATTERS FOR THE FIX. A single-assignment gate keyed on explicit
// definitions does NOT close this: `i = y * 3 + x` lowers to
// `_t = AddWithOverflow(..); _2 = move (_t.0)` with `_2` the parameter, so the
// parameter has exactly ONE explicit def and scores as single-assignment while
// holding two distinct values — the entry value and the loop value. The repo
// already documents this asymmetry twice and names the predicate that does hold
// for parameters (`local_is_never_written`): see the `root_is_never_reseated`
// doc in `crates/trust-vcgen/src/generate/value_facts.rs` and
// `local_versions_collapse_to_bare` in
// `crates/trust-vcgen/src/generate/discharge.rs`. A fix that adopts the
// def-counting predicate instead will leave this fixture red, which is exactly
// what the fixture is for.

pub fn param_flat(g: &[u8; 6], mut i: usize, c: bool) -> u8 {
    let mut s = 0u8;
    if c {
        for y in 0..2 {
            for x in 0..3 {
                i = y * 3 + x;
                s = s.wrapping_add(g[i]);
            }
        }
    } else {
        s = g[i];
    }
    s
}
