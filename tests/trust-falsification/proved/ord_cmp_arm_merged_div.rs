#![crate_type = "lib"]
// SAFE `Ordering` MATCH WHOSE ARM CONSTANT SUPPLIES THE NONZERO DIVISOR. The
// three arms bind `d` to 1, 2 and 4; the merged `d` is then the divisor.
// IT DOES NOT FAULT: nothing else can write `d`, so `d in {1, 2, 4}` and the
// division is always defined.
// Runtime oracle (stock rustc, -O -C debug-assertions=on, #[inline(never)],
// black_box, catch_unwind, silent hook): 0 panics / 6400 runs, sweep
// `a, b in -2..=2` x `x in 0..=255` (5*5*256), which covers all three arms.
//
// WHY IT IS A GATE FIXTURE. The same claim as `ord_cmp_arm_merged_index.rs` on
// the division-by-zero kind: the arm constants are the only thing keeping the
// divisor away from 0, so the `Less` arm must be tied to 1 and not left free.
//
// Two-column measurement, `-Ztrust-policy=certify`: pristine `70a7534fd1`
// answers `refuted` with `[divzero] FAILED`, and its counterexample binds the
// merged `d` to 0 while the match discriminant is 0 — a combination no arm can
// produce, since the discriminant-0 (`Equal`) arm binds `d` to 2. The merged
// local is simply not tied to any arm's value, so a total function is accused.
// `campaign-integration` answers `proved`. The fixture discriminates.
use core::cmp::Ordering;
pub fn ord_cmp_arm_merged_div(a: i32, b: i32, x: u32) -> u32 {
    let d = match a.cmp(&b) {
        Ordering::Less => 1u32,
        Ordering::Equal => 2u32,
        Ordering::Greater => 4u32,
    };
    x / d
}
