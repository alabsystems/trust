//@ needs-trust-verify
//@ revisions: tripped control
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=strict --crate-name=t
//@[tripped] compile-flags: -Ztrust-verify-function-budget-steps=52
//@[control] check-pass
//@ rustc-env: TRUST_R1_TRACE=1
//@ normalize-stderr: "formula=.* freevars=\{[^}]*\}" -> "formula=$$FORMULA freevars=$$FREEVARS"
//@ normalize-stderr: "sealed [0-9a-f]{64}" -> "sealed $$DIGEST"
//@ normalize-stderr: "elapsed_ms=\d+" -> "elapsed_ms=$$TIME"
//@ normalize-stderr: "sha256:[0-9a-f]{64}" -> "sha256:$$DIGEST"
//@ normalize-stderr: "trust-mc@\d+\.\d+\.\d+" -> "trust-mc@$$ENGINE"
//
// R1 (caller-propagation flips) under a TRIPPED verification budget mints NOTHING.
//
// Once the per-function budget trips it stays tripped for the rest of the harvest (the step
// counter saturates at zero; a passed deadline stays passed), and a VC generated after the
// trip may have been built on a truncated statement-version oracle, whose reads render BARE.
// The main pass discards such an inventory at its post-generation checkpoint; the R1
// harvesters now read `exhausted_readonly()` after every VC generation and before every
// certificate and mint (`r1_budget_tripped` in trust_verify.rs), so a tripped harvest stops
// at the first read and returns no flip.
//
// `tripped`: 52 steps are enough for the MAIN pass of `helper` and `main` to finish (so the
// report below is the real per-function verdict, not a budget error), and not enough for the
// harvest, which also builds the strengthened VC and the caller's site VC under ONE budget.
// The trace must show the harvest stopping at the trip and no `ADMITTED FLIP`; `helper`'s
// division then stays unproved and strict fails it.
//
// The step count is a WINDOW, re-measured 2026-09-28 on a stage1 at 3230a2055c3 after the SSA
// statement-version oracle (WS-E steps 1-4) replaced the polled entry-version fixpoint, so F's
// VC generation charges far fewer steps than it used to (this revision was 200 before): below
// 75 steps the main pass itself reports a budget error; from 150 the harvest finishes F's VC
// generation, proposes P, and trips one checkpoint later ("after the strengthened VC's
// generation"). 110 is the middle of the 75..=145 window in which the trip lands after F's VC
// generation, the checkpoint this revision pins.
//
// RE-MEASURED 2026-11-08 on a stage1 at d59a1ff978: the window is now 39..=66 (below 39 the main
// pass reports `exceeded its per-function budget ... during VC generation of helper`; from 67
// the trip lands after the strengthened VC's generation). main's 2026-11-07 vcgen memoization
// waves (PERF-COMPILER-VCGEN-64..82, e.g. 25cd76a6d9) charge a budget step only on a cache
// miss, so the same walk charges about half the steps (the old compiler, ad3c581466, still
// measures 76..=145). The revision pins the same checkpoint at the new middle, 52.
//
// `control`: the same program at the default budget admits the flip — every caller passes a
// nonzero divisor — so the `tripped` refusal is the budget's doing, not the program's.
//
// MEASURED on the pre-fix compiler (a stage1 of this commit's parent), same flags: the budget
// has already tripped by the end of F's VC generation (the fixed harvest stops right there,
// see the `tripped` stderr). Pre-fix, the harvest took its Failed VC and proposed P from that
// post-trip generation, went on into the strengthened VC's generation, and stopped only
// because that produced no matching row (`no strengthened VC matching V`). No flip was
// minted in this program either way: the pre-fix difference this revision's stderr pins is
// that the harvest kept going past the trip on VCs built after it, not an admitted flip. The
// unobserved-trip half of the fix is pinned in trust-vcgen:
// `a_trip_no_later_poll_observes_still_marks_the_walk_truncated`.
#![allow(dead_code)]

fn helper(x: u32, divisor: u32) -> u32 {
//[tripped]~^ ERROR safety verification incomplete
//[tripped]~| ERROR strict verification failed
    x / divisor
}

fn main() {
    let _ = helper(10, 5);
}
