#![crate_type = "lib"]
// SAFE `Ordering` MATCH WHOSE ARM CONSTANT SUPPLIES THE INDEX BOUND. The three
// arms bind `i` to 0, 1 and 2; the merged `i` then indexes a `[u32; 4]`.
// IT DOES NOT FAULT: nothing else can write `i`, so `i in {0, 1, 2}` and every
// read is in bounds.
// Runtime oracle (stock rustc, -O -C debug-assertions=on, #[inline(never)],
// black_box, catch_unwind, silent hook): 0 panics / 25 runs, sweep
// `a, b in -2..=2` (5*5), which covers all three arms.
//
// WHY IT IS A GATE FIXTURE. Here the arm constants are the ONLY thing that
// bounds the index, so the fixture fails unless the three arms are each tied to
// their value — including the `Less` arm, whose discriminant is -1.
//
// Two-column measurement, `-Ztrust-policy=certify`: pristine `70a7534fd1`
// answers `refuted` with `[bounds] FAILED`, and its counterexample binds the
// merged `i` to 4 while the match discriminant is 0 — a combination no arm can
// produce, since the discriminant-0 (`Equal`) arm binds `i` to 1. The merged
// local is simply not tied to any arm's value, so a total function is accused.
// `campaign-integration` answers `proved`. The fixture discriminates.
use core::cmp::Ordering;
pub fn ord_cmp_arm_merged_index(a: i32, b: i32, t: &[u32; 4]) -> u32 {
    let i = match a.cmp(&b) {
        Ordering::Less => 0usize,
        Ordering::Equal => 1usize,
        Ordering::Greater => 2usize,
    };
    t[i]
}
