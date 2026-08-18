#![crate_type = "lib"]
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
