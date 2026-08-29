#![crate_type = "lib"]
// CONTROL (class A, must PASS on BOTH columns). A safe three-arm
// `match a.cmp(&b)` in which each arm reads a CONSTANT slot of a `[u32; 4]`.
// IT DOES NOT FAULT: every index is a literal below the array length, so the
// body is total.
// Runtime oracle (stock rustc, -O -C debug-assertions=on, #[inline(never)],
// black_box, catch_unwind, silent hook): 0 panics / 25 runs, sweep
// `a, b in -2..=2` (5*5), which covers all three arms.
//
// WHY IT IS HERE. `Ordering::Less` has discriminant -1, so decoding the arm
// labels signed is a change to how EVERY `cmp` match is translated. This fixture
// is the guard against an over-eager decode: an ordinary, plainly-safe
// `Ordering` match must keep verifying.
//
// Two-column measurement, `-Ztrust-policy=certify`: `proved` on pristine
// `70a7534fd1` and `proved` on `campaign-integration`. Non-discriminating BY
// DESIGN — that is what a control is.
use core::cmp::Ordering;
pub fn ord_cmp_arm_direct_index(a: i32, b: i32, t: &[u32; 4]) -> u32 {
    match a.cmp(&b) {
        Ordering::Less => t[0],
        Ordering::Equal => t[1],
        Ordering::Greater => t[2],
    }
}
