#![crate_type = "lib"]
// CONTROL (class B, must PASS on BOTH columns). A WRITTEN PARAMETER: the
// incoming `i` is overwritten on both sides of an `if`, so the value that
// reaches `g[i]` is the merge of two in-bounds constants and never the caller's.
// IT DOES NOT FAULT: `i in {0, 5}` at the read, both in bounds for the
// `[u8; 6]`.
// Runtime oracle (stock rustc, -O -C debug-assertions=on, #[inline(never)],
// black_box, catch_unwind, silent hook): 0 panics / 24 runs, sweep
// `c in {true, false}` x incoming `i in 0..=11` (2*12) — including the six
// incoming values that WOULD be out of bounds if the writes were dropped.
//
// WHY IT IS HERE. A parameter is written by the ABI at entry and then again in
// the body, so it is exactly the local that a single-assignment merge rule
// mishandles in one direction or the other. This control pins the SAFE
// direction: the writes must be seen, so the merge is `{0, 5}` and not the
// caller's free value.
//
// Two-column measurement, `-Ztrust-policy=certify`: `proved` on pristine
// `70a7534fd1` and `proved` on `campaign-integration`. Non-discriminating BY
// DESIGN — that is what a control is.
pub fn param_write_merged_bounded(g: &[u8; 6], c: bool, mut i: usize) -> u8 {
    if c {
        i = 0usize;
    } else {
        i = 5usize;
    }
    g[i]
}
