#![crate_type = "lib"]
// ============================================================================
// KNOWN RED — and the red is CORRECT. Do not "fix" this by moving the fixture.
// ============================================================================
// Everything below this banner describes the design as it was intended, and it
// is still an accurate description of the CONTRACT. What it gets wrong is the
// conclusion "So this VERIFIES (exit 0)". It does not, and it should not today.
//
// `0e9090f03b` (2026-08-20, "close a live false PROVE at the Certified tier —
// coroutine resume premise") withdrew the capability that made this green,
// because that capability was minting a FALSE PROVE. This fixture's brief green
// window was a single gate run (6819d58406, 277/2); before that it was red for
// the ordinary reason (see reports/2026-08-16-falsification-gate-88b99d6812.md,
// which records "2/2 obligations proved; fails only on `coroutine
// executor-protocol premise is unproved`"), and after it, red again — now
// reporting "3 conditionally discharged (NOT proved), 1 skipped out of 4".
//
// ATTRIBUTION, measured across FOUR toolchains rather than argued:
//   stage2 88b99d6812  "2 proved out of 2" + ASSUMPTION        rc=1  incomplete
//   stage1 716725c5e9  "3 proved out of 3" + CONTRACT ... ∈{0}  rc=0  proved
//   stage1 d6f6dd3e1f  "3 cond. discharged, 1 skipped of 4"     rc=1  incomplete
//   stage2 f24fdb2fdb  byte-identical to the row above          rc=1  incomplete
// Rows 3 and 4 being byte-identical places the whole delta BEFORE the CTFE
// query-cycle guards and the safe-intrinsic lint fix — so neither of those, nor
// the intrinsic value semantics, nor the per-variant drop glue, caused it. All
// were checked and cleared.
//
// WHY IT IS NOT MOVED TO pending/. A proposed fix relocated this file there.
// `pending/` is not a gate category — the gate globs only `proved/` and
// `mutant/` at the top level — so moving it deletes the row from the corpus
// rather than resolving it. That is the same laundering this campaign already
// rejected once for the `must_not_verify/` proposal. An honest red stays where
// the gate can see it.
//
// WHAT WOULD LEGITIMATELY CLOSE IT: a caller that DISCHARGES the resume-state
// contract, so the premise is satisfied rather than assumed. The contract is
// real and is charged to callers (it sits in no demotion allowlist, and
// `register_proven_panic_free` is blocked for such bodies so a conditional
// proof cannot leak into the interprocedural registry). What is missing is a
// discharging caller in this fixture, not the machinery.
//
// ---------------------------------------------------------------------------
// Trust: piece #13 step-3 (coroutine resume-state contract). A SAFE ZERO-AWAIT
// `async fn`: the coroutine RESUME body reads the captured arg `x` back from the
// opaque frame (havoc'd u8), widens it and adds 1. `(x as u16) + 1` cannot
// overflow for any u8 x (max 255+1 = 256 < 65536), so the body's real overflow
// obligation is PROVED by ay (kernel-certified). The executor-protocol premise
// is a PUBLISHED CONTRACT, not an assumption: the bridge constrains the resume
// ENTRY dispatch read to the LIVE state set — the dispatch SwitchInt's own
// case set (rustc's otherwise→Unreachable exhaustiveness certificate) minus
// the reserved RETURNED=1/POISONED=2 ABI discriminants, here exactly {0} — and
// re-emits the `ResumedAfter*` sentinels as REFUTABLE asserts the solver must
// prove unreachable under that precondition. So this VERIFIES (exit 0) under
// strict `-full` with every sentinel obligation PROVED (not skipped) and ONE
// `contract:coroutine-resume-state` row naming {0} (and NO
// `assumption:coroutine` row). A regression that fails to lower the coroutine,
// prunes the sentinels by construction while claiming contract backing, leaks
// the state constraint into frame data, or false-fails the termination
// self-loops re-reddens this. NON-VACUOUS twice over: the mutant sibling
// (async_zero_await_widen) overflows on the SAME havoc'd frame read and MUST
// refute with x = 255 — proving the entry contract constrained only the
// resume-state selector — and a wrong live set makes the sentinel proof FAIL.
pub async fn f(x: u8) -> u16 {
    (x as u16) + 1
}
