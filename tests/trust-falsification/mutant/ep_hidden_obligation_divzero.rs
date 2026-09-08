#![crate_type = "lib"]
// A SECOND ASSERT BEHIND A BRANCH, HIDDEN BY A DISCHARGED FIRST ONE. `member` carries TWO
// division obligations:
//   entry prefix : `a / b`       -> DivisionByZero(b)      CHARGEABLE to the caller
//   NON-prefix   : `a / (b - 1)` -> DivisionByZero(b - 1)   behind `if flag`
// The caller passes `b = 1`, which DISCHARGES the prefix obligation and says nothing about
// the second. If a relaxation of the all-or-nothing entry-prefix rule DROPS the non-prefix
// assert rather than charging it, the caller certifies while the callee panics: the
// hidden-obligation class that rule exists to prevent. Every non-prefix assert must be
// independently discharged IN BUNDLE, or the member refused.
//
// Runtime oracle (stock rustc 1.96.0, -O -C overflow-checks=on -C debug-assertions=on,
// #[inline(never)], black_box, catch_unwind, silent hook): 32 panics / 64 runs, sweep
// `a in 1..33` x `flag in {false, true}`. Every panic is exactly `flag == true`.
//
// The verifier MUST refuse this (exit 1, division-by-zero violation with a counterexample).
pub fn ep_hidden_obligation_divzero(a: u64, flag: bool) -> u64 { member(a, 1, flag) }
#[inline(never)]
fn member(a: u64, b: u64, flag: bool) -> u64 {
    let q = a / b;
    if flag { q + a / (b - 1) } else { q }
}
