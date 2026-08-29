#![crate_type = "lib"]
// CONTROL (class B, must PASS on BOTH columns). The safe twin of
// `mutant/grid_merged_loopvar_index.rs`: the same two nested `for` loops over a
// 2x3 grid and the same `y * 3 + x`, WITHOUT the merge — no second branch, no
// free parameter. IT DOES NOT FAULT: `y in 0..2` and `x in 0..3` give
// `y * 3 + x in 0..=5`, in bounds for the `[u8; 6]`.
// Runtime oracle (stock rustc, -O -C debug-assertions=on, #[inline(never)],
// black_box, catch_unwind, silent hook): 0 panics / 1 run — the body takes no
// input beyond the array, so one run IS the whole input domain.
//
// WHY IT IS HERE. Its obligations include the `[overflow:mul]` on `y * 3` and
// the `[overflow:add]` on `y * 3 + x` — the mul-result add. Any fix that
// tightens merged-local handling in nested loops must not cost this discharge,
// so the control is what says the tightening was surgical.
//
// Two-column measurement, `-Ztrust-policy=certify`: `proved` on pristine
// `70a7534fd1` and `proved` on `campaign-integration`. Non-discriminating BY
// DESIGN — that is what a control is.
pub fn grid_unmerged_loopvar_index(g: &[u8; 6]) -> u8 {
    let mut acc = 0u8;
    for y in 0..2usize {
        for x in 0..3usize {
            let i = y * 3 + x;
            acc = acc.wrapping_add(g[i]);
        }
    }
    acc
}
