#![crate_type = "lib"]
// CONTROL (class A, must PASS on BOTH columns). A safe three-arm
// `match a.cmp(&b)` in which each arm divides by a distinct NONZERO literal.
// IT DOES NOT FAULT: no arm can divide by zero, and unsigned division cannot
// overflow, so the body is total.
// Runtime oracle (stock rustc, -O -C debug-assertions=on, #[inline(never)],
// black_box, catch_unwind, silent hook): 0 panics / 6400 runs, sweep
// `a, b in -2..=2` x `x in 0..=255` (5*5*256), which covers all three arms.
//
// WHY IT IS HERE. The companion to `ord_cmp_arm_direct_index.rs` on the other
// Level 0 kind: it guards that signed arm-label decoding does not cost the
// division-by-zero discharge on an ordinary `Ordering` match.
//
// Two-column measurement, `-Ztrust-policy=certify`: `proved` on pristine
// `70a7534fd1` and `proved` on `campaign-integration`. Non-discriminating BY
// DESIGN — that is what a control is.
use core::cmp::Ordering;
pub fn ord_cmp_arm_direct_div(a: i32, b: i32, x: u32) -> u32 {
    match a.cmp(&b) {
        Ordering::Less => x / 1,
        Ordering::Equal => x / 2,
        Ordering::Greater => x / 4,
    }
}
