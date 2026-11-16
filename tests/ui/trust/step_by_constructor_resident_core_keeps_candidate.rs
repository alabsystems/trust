//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on --crate-type lib -Ztrust-policy=strict
//@ rustc-env:TRUST_NATIVE_DEBUG=1
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-pass
//~? RAW [STEP_BY_CANDIDATE] fn=step_by_constructor_resident_core_keeps_candidate::control role=iterator-step-by
//! HONEST CONTROL for the 2026-09-28 residency conjunct in
//! `step_by_constructor::candidate` (see
//! `step_by_constructor_no_core_range_lang_item_impostor_refuted.rs`).
//!
//! The same call, `<Range<u32> as Iterator>::step_by`, on this compiler's own
//! resident `core`: the classification must still answer `iterator-step-by`, so
//! the StepBy constructor lane keeps its input. The verdict is pinned too, and is
//! unrelated to the conjunct: the lane charges `step_by`'s own safety sites and
//! the bundled body now lowers, so both preconditions and the panic-freedom row
//! prove and the function builds.
//!
//! History: first measured at `246ceb451e5` (stage-1 `trustc`, with and without
//! the residency conjunct), where the call was REFUSED because the bundled body
//! did not lower ("native typed-TrustIr lowering did not complete"). Re-measured
//! 2026-09-28 at `5f8066c410` on stage 1 and stage 2: the bundle builds and the
//! report reads "3 proved, 0 failed" (the synthetic `trust_mc_default_function`
//! admission row is excluded from that count by design). Which later change made
//! the body lower was not bisected. The only commits in between that touch the
//! lowering crates are the v50 uniform-array cohort (`27c75be420`,
//! `6fc5ee102e`, `db547a7256`).
#![no_std]

pub fn control() {
    let _s = (0u32..10).step_by(2);
}
