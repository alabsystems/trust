//! Ambient per-function verification budget — a **step** bound, not just a clock.
//!
//! The per-function verification budget (`verify_fn_deadline` / the step budget
//! in the compiler) is cooperative: it cannot preempt synchronous in-process
//! work. Historically it was consulted ONLY at solver dispatch, so the whole
//! synchronous preprocessing phase — MIR→VF extraction, VC generation, spec
//! inference — ran outside it and a single non-terminating loop there could spin
//! unbounded (a vendored `memchr(std)` body hung `trustc` for 4h+ this way).
//!
//! This module makes the *existing* budget ambient so every preprocessing choke
//! point across the verifier crates can consult it with no signature churn — the
//! same RAII + `thread_local!` shape already used for `FAITHFUL_SCALARS` in
//! `trust-mir-extract`. The compiler installs the budget once, at function entry,
//! before any preprocessing; the choke points (`convert_ty_inner`, the
//! VC-generation walks, the driver worklists, the widening fixpoint) call
//! [`budget_exhausted`] once per iteration and fail closed on overrun. A trip
//! costs only completeness — an `Unsupported` type, an `Unknown` obligation, a
//! dropped strengthening — never soundness: an over-budget result is NEVER
//! `Proved`.
//!
//! # Termination guarantee (why this is a *proof*, not just a timeout)
//!
//! [`budget_exhausted`] carries two independent bounds:
//!
//! * a **step counter** — a `u64` `remaining` that STRICTLY DECREASES by one on
//!   every call and reports exhaustion at zero. Any loop whose body calls
//!   `budget_exhausted()` once per iteration therefore performs at most
//!   `remaining` iterations before the guard fires — a textbook well-founded
//!   descent on `remaining : nat`. This bound is **deadline-independent**: it
//!   holds even when the wall-clock budget is disabled, and unlike wall-clock
//!   time it is a real ranking function, so it is what makes termination
//!   *provable* rather than merely *observed*.
//! * a **wall-clock deadline** — polled amortized (only every
//!   [`WALL_POLL_INTERVAL`] steps) to also cap loops whose per-iteration work is
//!   itself super-polynomial (e.g. a symbolic-execution walk that doubles a
//!   state formula each step): the step counter bounds the iteration *count*, the
//!   clock bounds the *work*.
//!
//! Together they give: every instrumented pre-dispatch loop halts within
//! `min(remaining steps, deadline)` and fails closed. The step half is the
//! provable core (Tier-1 of the design's termination guarantee); the clock half
//! is the operational backstop for exponential-per-step work.

use std::cell::Cell;
use std::time::Instant;

/// Poll the wall clock only every this-many steps (amortized: one `Instant::now()`
/// per 4096 cheap decrements). Purely a performance knob — the step counter is
/// checked on every call, so termination never depends on this interval.
pub const WALL_POLL_INTERVAL: u64 = 4096;

thread_local! {
    /// The ambient deadline for the function currently being verified on this
    /// thread. `None` = no wall-clock budget in force. Each parallel `mir_built`
    /// worker owns its own.
    static VERIFY_DEADLINE: Cell<Option<Instant>> = const { Cell::new(None) };
    /// Remaining preprocessing steps for the current function. `u64::MAX` = the
    /// step budget is disabled. Strictly decremented by every `budget_exhausted`
    /// call; zero = exhausted.
    static VERIFY_STEPS: Cell<u64> = const { Cell::new(u64::MAX) };
}

/// RAII scope installing the ambient per-function verification budget.
///
/// Install it at function entry, before any preprocessing; the previous values
/// are restored on drop (normal return OR unwind), so a synchronously-forced
/// nested proof query cannot leak this frame's budget into the caller.
#[must_use]
pub struct VerifyBudgetGuard {
    prev_deadline: Option<Instant>,
    prev_steps: u64,
}

impl VerifyBudgetGuard {
    /// Install `deadline` (wall-clock) and `step_budget` (`0` = disabled →
    /// `u64::MAX`) as the ambient budget for the current scope.
    pub fn install(deadline: Option<Instant>, step_budget: u64) -> Self {
        let steps = if step_budget == 0 { u64::MAX } else { step_budget };
        VerifyBudgetGuard {
            prev_deadline: VERIFY_DEADLINE.with(|d| d.replace(deadline)),
            prev_steps: VERIFY_STEPS.with(|s| s.replace(steps)),
        }
    }
}

impl Drop for VerifyBudgetGuard {
    fn drop(&mut self) {
        VERIFY_DEADLINE.with(|d| d.set(self.prev_deadline));
        VERIFY_STEPS.with(|s| s.set(self.prev_steps));
    }
}

/// The ambient wall-clock deadline, if one is installed.
#[inline]
pub fn current_deadline() -> Option<Instant> {
    VERIFY_DEADLINE.with(|d| d.get())
}

/// Charge one preprocessing step and report whether the ambient per-function
/// budget is now exhausted — by the **step** counter (a strictly-decreasing
/// `nat`, checked every call, deadline-independent) or, amortized, by the
/// wall-clock deadline.
///
/// Callers MUST treat `true` as fail-closed — return `Unsupported` / `Unknown` /
/// a partial or dropped result — and NEVER as a proof. Because the step counter
/// strictly decreases on every call, any loop that calls this once per iteration
/// performs at most `remaining` iterations: termination is by well-founded
/// descent on `remaining`, independent of the clock.
#[inline]
pub fn budget_exhausted() -> bool {
    let remaining = VERIFY_STEPS.with(|s| {
        let n = s.get();
        // Saturating so a disabled budget (u64::MAX) never wraps; a live budget
        // strictly decreases toward the zero floor.
        s.set(n.saturating_sub(1));
        n
    });
    if remaining == 0 {
        return true; // step budget spent — deadline-independent, always fires
    }
    // Amortized wall-clock backstop for super-polynomial per-step work.
    if remaining % WALL_POLL_INTERVAL == 0 {
        if let Some(at) = VERIFY_DEADLINE.with(|d| d.get()) {
            if Instant::now() >= at {
                return true;
            }
        }
    }
    false
}

/// Non-charging query: is the ambient budget already exhausted — by the step
/// counter reaching zero, or by the wall-clock deadline passing? Used by the
/// compiler's phase-boundary checkpoints (after extraction, after VC
/// generation), which report a hard error rather than a degraded value. Does
/// NOT charge a step (a checkpoint is not a loop iteration).
#[inline]
pub fn exhausted_readonly() -> bool {
    if VERIFY_STEPS.with(|s| s.get()) == 0 {
        return true;
    }
    VERIFY_DEADLINE.with(|d| match d.get() {
        Some(at) => Instant::now() >= at,
        None => false,
    })
}
