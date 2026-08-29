#![crate_type = "lib"]
// SIGNED SWITCH LABEL, THE ORDINARY SPELLING. `core::cmp::Ordering::Less` has
// discriminant -1, so `match a.cmp(&b) { Less => .., _ => .. }` is the SAME
// negative-arm shape as a literal `-1` pattern — it just does not look like one.
// This body adds 1 to a `u8` on the `Less` arm. IT FAULTS: at `a < b` and
// `x == 255` the `x + 1` overflows and panics under debug assertions.
// Runtime oracle (stock rustc, -O -C debug-assertions=on, #[inline(never)],
// black_box, catch_unwind, silent hook): 10 panics / 6400 runs, sweep
// `a, b in -2..=2` x `x in 0..=255` (5*5*256) — the 10 are the 10 ordered pairs
// with `a < b`, each at `x == 255`.
//
// WHY IT IS A GATE FIXTURE. Unsign-extended, the `Less` arm's raw label is
// 2^8-1 (or the wider spelling) against a signed discriminant, so the arm is
// UNSAT and everything on it discharges vacuously. Every `match a.cmp(&b)` in
// the language carries this arm. The verifier MUST refute this.
//
// Two-column measurement, `-Ztrust-policy=certify`: pristine `70a7534fd1`
// answers `proved` (SURVIVING MUTANT); `campaign-integration` answers
// `refuted`. The fixture discriminates.
use core::cmp::Ordering;
pub fn ord_cmp_less_arm_add(a: i32, b: i32, x: u8) -> u8 {
    match a.cmp(&b) {
        Ordering::Less => x + 1,
        _ => 0,
    }
}
