// Trust (D2): THE FALSE-PROVE EXHIBIT, as a standing regression test.
//
// This is the test the lane that introduced the defect owed and did not write.
// `ca53846043` ("coroutine resume as a CHECKED caller contract", Lane B) ended
// its own commit message with "NOT MEASURED: the end-to-end fixture flips —
// needs a stage2 rebuild + gate run". The fixtures it never ran were failing.
//
// WHAT WAS MEASURED, on HEAD, at the DEFAULT strict policy with no unusual
// flags — one line of library code:
//
//     $ trustc --edition 2021 -Ztrust-verify=on --crate-type=lib exlib.rs
//     note: Trust verification: 2 proved, 0 failed, 0 unknown, 0 timed out,
//           0 runtime-checked out of 2 obligation(s)
//       = note: of which 2 kernel-certified by the clean CIC kernel
//     >>> exit: 0
//
// and then, from a driver compiled `-Ztrust-verify=off` (exactly how Targo
// compiles a dependency, which is where a real executor lives) polling it twice
// with a safe `Waker::noop()`:
//
//     first poll: Ready(7)
//     thread 'main' panicked at exlib.rs:1:34:
//     `async fn` resumed after completion
//     >>> program exit: 101
//
// `exlib.rs:1:34` is the span of the row that had just been certified "panic
// freedom: no assertion, `unreachable!`, or panic is reachable".
//
// THE MECHANISM. The bridge injects an entry `Assume(resume_state == 0)`, which
// DOMINATES every block, and the `ResumedAfterReturn` sentinel sits on the
// `resume_state == 1` arm. The certified CIC term decodes to
// `resume_state = 0 ∧ resume_state = 1 ⊢ False` — ex falso. The kernel was
// faithful; the violation formula it was handed already carried the
// executor-protocol premise in its hypothesis CONTEXT. `axiom_closure: Empty`
// is LITERALLY TRUE of that term (ex falso needs no axiom) and MATERIALLY
// MISLEADING about the obligation. Measured: the whole-function panic-freedom
// row's term and context were BYTE-IDENTICAL to the sentinel row's, yet it
// reported bare `proved` / `Certified` / `KernelRechecked`, while the
// conditionality lived only on a SIBLING `contract:coroutine-resume-state` row
// with `outcome: skipped`.
//
// WHY NO CALLER CAUGHT IT: the callsite charge in the bridge fires only for an
// in-bundle direct `Call` whose callee signature carries
// `coroutine_resume_contract`. The real resumer is the generated `Future::poll`
// shim plus an executor in a dependency crate, which Targo compiles with
// `-Ztrust-verify=off`. Measured: a cross-crate consumer under strict gets NO
// resume-precondition obligation, and an in-crate `async fn` caller gets none
// either. There is no caller-side discharge lane — the bridge says so in the
// obligation text it mints.
//
// THE PIN. Under a fail-closed lane this crate must NOT compile clean. The
// contract row is now explicit-advisory-only, so the executor-protocol premise
// is once again published as an unproved assumption and rejected. If this file
// ever compiles successfully again, a body whose sentinel is reachable at
// runtime is being certified panic-free.
//
// Sibling `full_lane_abort_unchanged.rs` pins the same abort as a policy
// contract; this file exists to carry the exhibit and its runtime evidence, so
// the reason the abort must stay can never be lost again.
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ edition: 2021
//@ compile-flags: --crate-type=lib
//@ check-fail
//@ dont-check-compiler-stderr
pub async fn tick(x: u32) -> u32 { x } //~ ERROR coroutine executor-protocol premise is unproved
//~? RAW Trust: ASSUMPTION [coroutine]
