#![crate_type = "lib"]
// SAFE ENUM MATCH WHOSE ARM CONSTANTS SUPPLY THE INDEX BOUND. Two arms bind `i`
// to 0 and to 5; the merged `i` then indexes a `[u8; 6]`. IT DOES NOT FAULT:
// nothing else can write `i`, so `i in {0, 5}` and both reads are in bounds —
// 5 is the LAST slot, so the bound is exact rather than slack.
// Runtime oracle (stock rustc, -O -C debug-assertions=on, #[inline(never)],
// black_box, catch_unwind, silent hook): 0 panics / 2 runs, sweep = both
// variants of `SelP`, which is the whole input domain of `s`.
//
// WHY IT IS A GATE FIXTURE. The arm constants are the only thing that bounds the
// index, so the fixture fails unless each arm is tied to its own value.
//
// Two-column measurement, `-Ztrust-policy=certify`: pristine `70a7534fd1`
// answers `refuted`, with the counterexample binding the merged `i` to 6 while
// the discriminant is the `Lo` arm's — a FALSE REFUTATION of a total function,
// and it needs no negative discriminant to happen. `campaign-integration`
// answers `proved`. The fixture discriminates.
pub enum SelP {
    Lo,
    Hi,
}
pub fn enum_arm_merged_index(g: &[u8; 6], s: SelP) -> u8 {
    let i = match s {
        SelP::Lo => 0usize,
        SelP::Hi => 5usize,
    };
    g[i]
}
