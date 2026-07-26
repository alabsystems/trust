// Typed reactor refusals.
//
// The only failure the drain loop can surface is a budget trip: the reactor is
// otherwise total (it never blocks, never touches a real clock, never panics on
// well-formed input). The budget makes runaway rescheduling — an interval that
// re-arms at delay 0, a `.then` that re-queues itself forever — terminate
// DETERMINISTICALLY, mirroring the M0 trace driver's TIMER_CAP: the same input
// trips at the same step count on every run and every machine.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

/// A typed reactor refusal. Fail-closed: a drain that would not quiesce returns
/// this rather than looping forever or approximating.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum ReactorError {
    /// The step budget was exhausted before both queues drained. `limit` is the
    /// configured ceiling (default `Reactor::DEFAULT_STEP_BUDGET`). Deterministic:
    /// the same enqueue/resolve sequence trips at the same step count every run.
    #[error(
        "reactor step budget exhausted after {limit} steps: the microtask/timer graph \
         never quiesces (runaway rescheduling)"
    )]
    Budget {
        /// The configured step ceiling that was hit.
        limit: u64,
    },
}
