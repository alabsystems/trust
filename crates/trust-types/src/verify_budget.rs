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
//! point across the verifier crates CAN consult it with no signature churn — the
//! same RAII + `thread_local!` shape already used for `FAITHFUL_SCALARS` in
//! `trust-mir-extract`. A trip costs only completeness — an `Unsupported` type,
//! an `Unknown` obligation, a dropped strengthening — never soundness: an
//! over-budget result is NEVER `Proved`.
//!
//! # What actually polls this — read this before relying on the bound
//!
//! This paragraph used to assert that "the choke points (`convert_ty_inner`, the
//! VC-generation walks, the driver worklists, the widening fixpoint) call
//! [`budget_exhausted`] once per iteration". **That was FALSE, and it was the
//! stated premise under which an unbounded verifier was believed bounded.**
//! MEASURED 2026-08-31 by counting call sites: `budget_exhausted()` appeared in
//! ONE file of `trust-vcgen` (`contracts.rs`) and in NONE of `generate/mod.rs`,
//! `generate/path_defs.rs`, `generate/safety.rs`, `generate/checked_vcs.rs`,
//! `generate/overflow_vc.rs` or `termination.rs` — that is, in none of "the
//! VC-generation walks". On `trust-spec-elab` the verifier spent >=99.7% of its
//! time in walks that polled nothing, and no timeout could bound it.
//!
//! Two independent defects produced that outcome, and BOTH are needed for the
//! bound to hold:
//!
//! 1. **The polls were missing.** Now added at the walk loops whose degradation
//!    is already proven sound and pinned by tests.
//! 2. **No budget was INSTALLED over the whole-crate R1 pre-pass.** The only
//!    production `VerifyBudgetGuard::install` sat inside the PER-BODY pass, so
//!    the pre-pass ran at `VERIFY_STEPS = u64::MAX` with no deadline and every
//!    poll reachable from it was DEAD CODE. A poll bounds nothing unless a guard
//!    is installed above it.
//!
//! The honest current statement is therefore: **the bound holds exactly at the
//! loops enumerated by `grep -rn 'budget_exhausted()' crates/ compiler/`, and
//! only under a scope that installed a guard.**
//!
//! # A trip is fail-closed only where a consumer DISCARDS what followed it
//!
//! A poll that trips does not stop generation; it makes the walk that polled hand
//! back LESS — fewer path guards, fewer path definitions, fewer extracted block
//! definitions. Each such degradation is chosen to drop HYPOTHESES only, but a VC
//! generated after a trip is still not the VC the program deserves, so every
//! consumer of generated VCs must discard what followed a trip:
//!
//! * the main pass: its post-generation checkpoint
//!   (`preprocessing_budget_exceeded` in `rustc_mir_transform::trust_verify`)
//!   discards the function's whole inventory;
//! * the R1 harvesters (`try_harvest_flip`, `try_harvest_generic_mono_flip`,
//!   `try_harvest_recursive_flip`): [`exhausted_readonly`] after every VC
//!   generation, before every certificate and around every mint — a tripped
//!   harvest mints nothing;
//! * the overflow-elision join table (the consumed generation's origin inventory,
//!   T3 C05, built on `generate_v2_safety_vcs_impl_with_origins_checked`): the same
//!   read is OR-ed into the walk's `truncated` flag and read again when the
//!   generation returns, so the table is refused. The second read is also what
//!   covers the interval environment the rows are discharged and augmented with:
//!   the interval fixpoint polls the ambient budget and answers a trip with Top
//!   everywhere.
//!
//! A NEW consumer of generated VCs must read [`exhausted_readonly`] after
//! generation and discard on `true`.
//!
//! The statement-version oracle is no longer a polled walk, but it is BUILT FROM
//! one, and that is not the same as being immune to a trip. It used to poll:
//! `entry_versions_fixpoint` and its gen-set precompute handed back a PARTIAL or
//! EMPTY reaching-version map on a trip, under which every inter-block read rendered
//! BARE — the false-ACCEPT direction, sound only because of the discards above. Its
//! replacement (the query-driven SSA oracle, `trust-vcgen/src/generate/version_ssa.rs`)
//! has no truncated state of its OWN and consults no budget; but its gen-sets and its
//! write index's synthetic-name superset (`generate/block_writes.rs`) are extracted by
//! `guards::extract_block_definitions` / `extract_statement_definitions_isolated`,
//! which poll per statement and silently return FEWER names on a trip. An oracle
//! built after a trip can therefore version too few reads — the same false-accept
//! direction, narrower. It fails closed where it can see the trip (its `#e` mint gate
//! answers `false`, and its statement gate recomputes the exact prefix, for an index
//! extracted after one); everything else rests on the discards above. So those
//! discards must stay for as long as any extraction polls — the SSA oracle landing
//! is NOT a reason to remove one.
//!
//! One read suffices because a trip LATCHES for [`exhausted_readonly`]: the step
//! counter saturates at zero and a passed deadline stays passed. It does NOT
//! latch for [`budget_exhausted`] on the clock half — the clock is read only
//! every [`WALL_POLL_INTERVAL`] steps, so after a clock trip up to 4095 later
//! polls answer `false` and generation carries on — so no consumer may rely on
//! a LATER poll having observed an earlier trip.
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
//!
//! # Which half tripped (the stop cause)
//!
//! The two halves are not interchangeable to a reader of the result. A step
//! trip is a COUNT: the same inputs trip it at the same poll on every host, so
//! the degraded result it leaves is reproducible (`StopCause::Steps`). A clock
//! trip depends on machine speed and load, so the result it leaves is not
//! (`StopCause::WallBackstop`). The FIRST trip in a guarded scope is latched
//! and [`exhaustion_cause`] reports it: once a trip has degraded a walk,
//! everything generated afterwards descends from that degradation, so a later
//! trip of the other half cannot change which bound decided the output. A
//! consumer that discards or reports an over-budget result stamps the reason
//! with this cause (see `crate::determinism`), so a clock-degraded function can
//! never pass as a deterministic one.
//!
//! # Another function's verification is not this function's time
//!
//! Verification runs inside each body's `optimized_mir` query, so a function's
//! verification can force ANOTHER body's whole verification synchronously, on the
//! same thread, inside its own scope: reading a callee's optimized MIR for tracing,
//! for a bundled member, or a callee's proof results. The nested verification
//! installs its own guard, and on drop the guard restores this module's state.
//! The STEP half was always per function (the nested scope gets its own counter
//! and the caller's is restored untouched), but the CLOCK half was not: a deadline
//! is an absolute instant, so the caller's clock kept running while the callee was
//! verified, and a caller whose callee spent its own whole clock found its clock
//! spent too. Measured on the candidate gate 20261016T202952Z-7f3690ed73
//! (atpkg-publish, re-run alone): `mirror::one` took 362.7 s, and its five
//! transitive callers verified around it (`mirror_in`, `mirror`, `publish_quad`,
//! `publish_with`, `<Index as Indexer>::publish`) each published ONE
//! `TrustPreprocessingBudget` row in place of their obligations, within 3 s of
//! `one` finishing.
//!
//! So a guard installed with [`VerifyBudgetGuard::install_function`] (a FUNCTION
//! scope: one body's verification) CREDITS its whole wall time to every enclosing
//! scope on the thread when it ends: every guard restores the deadline it saved
//! moved later by the credit earned while it was installed, and a deadline a
//! consumer captured by value is moved the same way through [`credited`] and a
//! [`ClockCreditMark`] taken when it was captured. Each function's own work is
//! still bounded by its own clock, and the nested verification by its own, so a
//! stack of nested verifications ends within the sum of its functions' budgets —
//! the bound it would have had verified one after another.
//!
//! # A clock that fired in a scope is reported when the scope ends
//!
//! A stamped row covers only the result that consumer builds. The same scope
//! also runs work whose outcome is consumed without becoming a row — the R1
//! harvest mints no flip, a refutation attempt is abandoned, a late strict
//! revalidation is discarded — and those lanes test the deadline themselves as
//! well as through these polls. So when a [`VerifyBudgetGuard`] drops, it
//! reports to the determinism backstop ledger
//! ([`crate::determinism::note_stop`], lane [`BUDGET_CLOCK_LANE`]) if its clock
//! half tripped OR its deadline has passed: in either case some lane in the
//! scope may have stopped on the clock, and the unit is not reproducible. The
//! step half needs no report: a step trip is a count.
//!
//! # Solver work is bounded per query, not here
//!
//! The step budget bounds preprocessing. Solver work is bounded by ONE count
//! per query — `min(C, max(1, k · size))` conflicts, sent to ay as `:rlimit`
//! before every check-sat (`crate::determinism::EffortScale`, plan §3.2a) —
//! and by nothing per function: a second, per-function count would be a
//! second budget, and it made a query's stop depend on the queries before it.

use std::cell::Cell;
use std::time::{Duration, Instant};

use crate::determinism::StopCause;

/// Poll the wall clock only every this-many steps (amortized: one `Instant::now()`
/// per 4096 cheap decrements). Purely a performance knob — the step counter is
/// checked on every call, so termination never depends on this interval.
pub const WALL_POLL_INTERVAL: u64 = 4096;

/// The backstop-ledger lane a [`VerifyBudgetGuard`] reports a fired clock under.
pub const BUDGET_CLOCK_LANE: &str = "per-function budget clock";

thread_local! {
    /// The ambient deadline for the function currently being verified on this
    /// thread. `None` = no wall-clock budget in force. Each parallel `mir_built`
    /// worker owns its own.
    static VERIFY_DEADLINE: Cell<Option<Instant>> = const { Cell::new(None) };
    /// Remaining preprocessing steps for the current function. Strictly
    /// decremented by every `budget_exhausted` call; zero = exhausted. Outside
    /// any guarded scope it is `u64::MAX`: no budget is installed, so nothing
    /// polls against one (see the module doc's precondition).
    static VERIFY_STEPS: Cell<u64> = const { Cell::new(u64::MAX) };
    /// The first bound that tripped in the current guarded scope, latched.
    static VERIFY_TRIP: Cell<Option<BudgetTrip>> = const { Cell::new(None) };
    /// The wall time FUNCTION scopes on this thread have credited to the scopes
    /// enclosing them (module doc: "Another function's verification is not this
    /// function's time"). Only ever grows; a scope reads the difference since it
    /// was installed ([`ClockCreditMark`]).
    static NESTED_FUNCTION_CREDIT: Cell<Duration> = const { Cell::new(Duration::ZERO) };
}

/// The complete ambient function state, including credit earned by nested
/// function verification. A stack hop itself earns no such credit.
#[derive(Clone, Copy)]
struct BudgetState {
    deadline: Option<Instant>,
    steps: u64,
    trip: Option<BudgetTrip>,
    nested_credit: Duration,
}

impl BudgetState {
    fn current() -> Self {
        Self {
            deadline: VERIFY_DEADLINE.with(Cell::get),
            steps: VERIFY_STEPS.with(Cell::get),
            trip: VERIFY_TRIP.with(Cell::get),
            nested_credit: NESTED_FUNCTION_CREDIT.with(Cell::get),
        }
    }

    fn restore(self) {
        VERIFY_DEADLINE.with(|value| value.set(self.deadline));
        VERIFY_STEPS.with(|value| value.set(self.steps));
        VERIFY_TRIP.with(|value| value.set(self.trip));
        NESTED_FUNCTION_CREDIT.with(|value| value.set(self.nested_credit));
    }
}

/// Borrow the current function budget for one synchronous worker dispatch.
///
/// `dispatch` must only spawn/join the worker, not perform budgeted work on
/// the caller concurrently. Its non-Clone worker token cannot outlive this
/// call: a scoped thread must join before dispatch returns or unwinds. The
/// original absolute deadline, remaining count, first trip and nested-function
/// credit return to the caller even when spawning fails or the worker panics.
/// No fresh guard, allowance or clock is installed over the borrowed work.
/// This carries resource accounting only, never proof authority.
pub fn with_worker_budget<R>(
    dispatch: impl for<'scope> FnOnce(VerifyBudgetWorker<'scope>) -> R,
) -> R {
    let state = std::sync::Mutex::new(BudgetState::current());
    struct RestoreCaller<'a>(&'a std::sync::Mutex<BudgetState>);
    impl Drop for RestoreCaller<'_> {
        fn drop(&mut self) {
            self.0.lock().unwrap_or_else(std::sync::PoisonError::into_inner).restore();
        }
    }
    let _restore = RestoreCaller(&state);
    dispatch(VerifyBudgetWorker { state: &state })
}

/// One lifetime-bound, non-Clone worker side of [`with_worker_budget`].
/// Its state has no serialized representation and cannot grant a new budget.
pub struct VerifyBudgetWorker<'scope> {
    state: &'scope std::sync::Mutex<BudgetState>,
}

impl VerifyBudgetWorker<'_> {
    /// Run with the caller's exact budget. An unwind exports consumed work and
    /// the first trip before crossing the join, and restores the worker's prior
    /// TLS state just as normal return does. Balanced nested function/share
    /// scopes retain their existing credit and first-trip rules.
    pub fn run<R>(self, work: impl FnOnce() -> R) -> R {
        let previous = BudgetState::current();
        self.state.lock().unwrap_or_else(std::sync::PoisonError::into_inner).restore();
        struct ReturnBudget<'a> {
            shared: &'a std::sync::Mutex<BudgetState>,
            previous: BudgetState,
        }
        impl Drop for ReturnBudget<'_> {
            fn drop(&mut self) {
                *self.shared.lock().unwrap_or_else(std::sync::PoisonError::into_inner) =
                    BudgetState::current();
                self.previous.restore();
            }
        }
        let _return_budget = ReturnBudget { shared: self.state, previous };
        work()
    }
}

/// A reading of this thread's nested-function clock credit, taken when a deadline is
/// captured, so the deadline can later be moved by the credit earned since
/// ([`credited`]).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ClockCreditMark(Duration);

/// The current nested-function clock credit of this thread.
#[must_use]
pub fn clock_credit_mark() -> ClockCreditMark {
    ClockCreditMark(NESTED_FUNCTION_CREDIT.with(Cell::get))
}

/// The wall time function scopes nested in the current one credited since `mark`.
#[must_use]
pub fn clock_credit_since(mark: ClockCreditMark) -> Duration {
    NESTED_FUNCTION_CREDIT.with(Cell::get).saturating_sub(mark.0)
}

/// `deadline`, captured when `mark` was taken, moved later by the time this thread
/// spent since then verifying OTHER functions (nested function scopes): the deadline
/// the capturing scope would hold had those verifications run before it. `None`
/// stays `None`; an instant that cannot be represented stays where it was.
#[must_use]
pub fn credited(deadline: Option<Instant>, mark: ClockCreditMark) -> Option<Instant> {
    shifted(deadline, clock_credit_since(mark))
}

fn shifted(deadline: Option<Instant>, by: Duration) -> Option<Instant> {
    deadline.map(|at| at.checked_add(by).unwrap_or(at))
}

/// Which half of the ambient budget tripped first.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BudgetTrip {
    /// The step counter reached zero: a count, reproducible.
    Steps,
    /// The wall-clock deadline passed: load-dependent, not reproducible.
    Clock,
}

impl BudgetTrip {
    /// The stop cause this trip stamps on what it degraded.
    #[must_use]
    pub const fn stop_cause(self) -> StopCause {
        match self {
            Self::Steps => StopCause::Steps,
            Self::Clock => StopCause::WallBackstop,
        }
    }
}

fn latch_trip(trip: BudgetTrip) {
    VERIFY_TRIP.with(|t| {
        if t.get().is_none() {
            t.set(Some(trip));
        }
    });
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
    prev_trip: Option<BudgetTrip>,
    /// The nested-function clock credit when the scope was installed.
    credit_at_install: ClockCreditMark,
    /// `Some(entry instant)` for a FUNCTION scope ([`Self::install_function`]).
    function_entered: Option<Instant>,
}

impl VerifyBudgetGuard {
    /// Install `deadline` (wall-clock) and `step_budget` as the ambient budget
    /// for the current scope, with no trip latched yet.
    ///
    /// `step_budget` is a COUNT, taken literally: `0` is spent before the
    /// first poll. There is no "disabled" value: the compiler's step budget
    /// (`-Ztrust-verify-function-budget-steps`) refuses `0`, because a
    /// function with no step bound can only be stopped by the clock, and a
    /// clock stop is not reproducible.
    pub fn install(deadline: Option<Instant>, step_budget: u64) -> Self {
        Self::install_scope(deadline, step_budget, None)
    }

    /// [`Self::install`] for a FUNCTION scope — one body's whole verification. When
    /// it ends, its wall time is credited to every scope enclosing it on this thread
    /// (module doc: "Another function's verification is not this function's time"),
    /// so a verification forced synchronously from inside another function's does
    /// not spend that function's clock.
    pub fn install_function(deadline: Option<Instant>, step_budget: u64) -> Self {
        Self::install_scope(deadline, step_budget, Some(Instant::now()))
    }

    fn install_scope(
        deadline: Option<Instant>,
        step_budget: u64,
        function_entered: Option<Instant>,
    ) -> Self {
        VerifyBudgetGuard {
            prev_deadline: VERIFY_DEADLINE.with(|d| d.replace(deadline)),
            prev_steps: VERIFY_STEPS.with(|s| s.replace(step_budget)),
            prev_trip: VERIFY_TRIP.with(|t| t.replace(None)),
            credit_at_install: clock_credit_mark(),
            function_entered,
        }
    }
}

impl Drop for VerifyBudgetGuard {
    fn drop(&mut self) {
        // Report a clock that may have decided something in this scope BEFORE
        // the outer scope's state is restored (module doc: "A clock that fired
        // in a scope is reported when the scope ends").
        let clock_tripped = VERIFY_TRIP.with(|t| t.get()) == Some(BudgetTrip::Clock);
        let deadline_passed =
            VERIFY_DEADLINE.with(|d| d.get()).is_some_and(|at| Instant::now() >= at);
        if clock_tripped || deadline_passed {
            crate::determinism::note_stop(BUDGET_CLOCK_LANE, StopCause::WallBackstop);
        }
        // What the enclosing scope's saved deadline moves by: the credit function
        // scopes nested in this one earned while it was installed, and, when this is a
        // function scope itself, the rest of its own wall time, which it credits to
        // the scopes enclosing it (the nested part is already in the credit).
        let nested = clock_credit_since(self.credit_at_install);
        let shift = match self.function_entered {
            Some(entered) => {
                let elapsed = entered.elapsed().max(nested);
                NESTED_FUNCTION_CREDIT.with(|c| c.set(c.get().saturating_add(elapsed - nested)));
                elapsed
            }
            None => nested,
        };
        VERIFY_DEADLINE.with(|d| d.set(shifted(self.prev_deadline, shift)));
        VERIFY_STEPS.with(|s| s.set(self.prev_steps));
        VERIFY_TRIP.with(|t| t.set(self.prev_trip));
    }
}

/// The earlier of two optional instants (`None` = no bound).
#[must_use]
pub fn earliest(a: Option<Instant>, b: Option<Instant>) -> Option<Instant> {
    match (a, b) {
        (Some(a), Some(b)) => Some(a.min(b)),
        (a, b) => a.or(b),
    }
}

/// RAII scope that TIGHTENS only the ambient wall-clock deadline, for a phase that may
/// spend only a share of the function's clock, and shares everything else with the
/// enclosing [`VerifyBudgetGuard`] scope.
///
/// Trust: 2026-10-17 (gate-rca deadline). The compiler gives the native TrustIr lane
/// (bundle construction, then the live dispatch) a share of what is left of the
/// function's clock, so the cheap certifying lanes that run after it (the in-process ay
/// bridge, the structural and clean-kernel promotions, certification and S1) are never
/// left with nothing. Construction is synchronous vcgen work whose loops poll this
/// module, so its share has to be the AMBIENT deadline while it runs. A fresh
/// [`VerifyBudgetGuard`] cannot do that: it installs a new step counter, so the steps
/// the phase spends would not be charged to the function, and the phase could not be
/// bounded by what the function has left of its count.
///
/// * The STEP COUNTER is shared: every poll inside charges the function's count, and a
///   step trip inside stays latched after the scope (it is a count of the function).
/// * The DEADLINE inside is the earlier of the enclosing one and `share`.
/// * A CLOCK trip latched inside, when nothing had tripped before the scope, was a trip
///   of the share: the scope's consumer discards what followed it (the compiler
///   declines the native bundle when the share has passed), and the enclosing scope's
///   clock is its own. So the latch is cleared when the scope ends. If the enclosing
///   deadline had passed too, the next [`exhausted_readonly`] re-reads that clock and
///   latches it again.
/// * When the scope ends with its clock tripped or its share passed, it reports to the
///   determinism ledger exactly as a [`VerifyBudgetGuard`] does: a lane in the scope
///   may have stopped on a clock, so the unit is not reproducible.
#[must_use]
pub struct DeadlineShareGuard {
    prev_deadline: Option<Instant>,
    prev_trip: Option<BudgetTrip>,
    share: Option<Instant>,
    /// The nested-function clock credit when the scope was installed: a function
    /// verified inside the share moves the share and the restored deadline alike.
    credit_at_install: ClockCreditMark,
}

impl DeadlineShareGuard {
    /// Tighten the ambient deadline to `share` (when it is earlier) until the guard drops.
    pub fn narrow(share: Option<Instant>) -> Self {
        let prev_deadline = VERIFY_DEADLINE.with(Cell::get);
        let narrowed = earliest(prev_deadline, share);
        VERIFY_DEADLINE.with(|d| d.set(narrowed));
        DeadlineShareGuard {
            prev_deadline,
            prev_trip: VERIFY_TRIP.with(Cell::get),
            share: narrowed,
            credit_at_install: clock_credit_mark(),
        }
    }
}

impl Drop for DeadlineShareGuard {
    fn drop(&mut self) {
        let trip = VERIFY_TRIP.with(Cell::get);
        let clock_tripped_here = self.prev_trip.is_none() && trip == Some(BudgetTrip::Clock);
        let nested = clock_credit_since(self.credit_at_install);
        let share_passed = shifted(self.share, nested).is_some_and(|at| Instant::now() >= at);
        if clock_tripped_here || share_passed {
            crate::determinism::note_stop(BUDGET_CLOCK_LANE, StopCause::WallBackstop);
        }
        if clock_tripped_here {
            VERIFY_TRIP.with(|t| t.set(self.prev_trip));
        }
        VERIFY_DEADLINE.with(|d| d.set(shifted(self.prev_deadline, nested)));
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
///
/// **Every `true` this returns is latched, by construction.** The bounds are read
/// only in [`poll_bounds`], which can answer only with a [`BudgetTrip`], and the
/// one exit below latches whatever it answered before returning `true`. So a bound
/// a later change adds must name its own `BudgetTrip` variant (and, through the
/// exhaustive [`BudgetTrip::stop_cause`], its own stop cause), and cannot answer
/// `true` here without [`exhausted_readonly`] and [`exhaustion_cause`] seeing it.
/// The seal `321aaeda7` broke exactly this: its process-memory ceiling was a bare
/// `return true` in this function that latched nothing, so the checkpoints never
/// saw it (blocker 5 of
/// `docs/issues/2026-09-30-verified-lane-blockers-measured-on-alab-repos.md`).
#[inline]
pub fn budget_exhausted() -> bool {
    match poll_bounds() {
        Some(trip) => {
            latch_trip(trip);
            true
        }
        None => false,
    }
}

/// Charge one step and read the bounds: the ONLY place [`budget_exhausted`]
/// reads one. Answers which bound tripped, never a bare `bool`, so the caller's
/// single exit can latch it (see [`budget_exhausted`]).
#[inline]
fn poll_bounds() -> Option<BudgetTrip> {
    let remaining = VERIFY_STEPS.with(|s| {
        let n = s.get();
        // Saturating so a disabled budget (u64::MAX) never wraps; a live budget
        // strictly decreases toward the zero floor.
        s.set(n.saturating_sub(1));
        n
    });
    if remaining == 0 {
        // Step budget spent — deadline-independent, always fires.
        return Some(BudgetTrip::Steps);
    }
    // Amortized wall-clock backstop for super-polynomial per-step work.
    let clock_due = remaining.is_multiple_of(WALL_POLL_INTERVAL);
    if clock_due && VERIFY_DEADLINE.with(|d| d.get()).is_some_and(|at| Instant::now() >= at) {
        return Some(BudgetTrip::Clock);
    }
    None
}

/// Non-charging query: is the ambient budget already exhausted — by the step
/// counter reaching zero, or by the wall-clock deadline passing? Both latch, so
/// one read after a phase observes every trip made during it, including a clock
/// trip no later [`budget_exhausted`] poll saw. Used by the compiler's
/// phase-boundary checkpoints (after extraction, after VC generation), which
/// report a hard error rather than a degraded value, by the R1 harvesters, and
/// by the safety walk's `truncated` flag (see the module doc). Does
/// NOT charge a step (a checkpoint is not a loop iteration).
///
/// A `true` answer latches the half it observed (if nothing tripped earlier),
/// because the caller is about to act on it: [`exhaustion_cause`] then names
/// the bound that decided the checkpoint.
///
/// **Every trip a poll latched answers `true` here, whatever bound made it.**
/// The latched trip is read FIRST, so this checkpoint cannot disagree with a
/// poll about whether the scope was degraded, even for a bound whose own state
/// does not stay tripped (as a clock or a spent counter does). Together with the
/// single latching exit of [`budget_exhausted`] this covers every bound read in
/// [`poll_bounds`]; it does NOT cover a bound read anywhere else. The two
/// disagreed once and it cost a whole crate's coverage without one warning: the
/// seal `321aaeda7` polled a process memory ceiling, read from PEAK resident
/// size, as a bare `return true` that latched nothing and that this function did
/// not read. MEASURED on ny-propagate `--lib` (seal 9192, 2026-09-30): the peak
/// crossed the 16 GiB ceiling after about 6,033 of 32,726 bodies; from then on
/// the first type-lowering poll of every body tripped, so 26,686 functions
/// lowered their return-place local to the "type lowering exceeded the
/// per-function verification budget" marker and got a `MalformedTrustIr` Unknown
/// (26,620 once, 66 also as a wrapped `unsupported_mir` copy: 26,752 rows),
/// while every extraction checkpoint read "not exhausted" (0 extraction-phase
/// overrun warnings in that run). `main` deleted that ceiling (`5aa81ac1683`).
#[inline]
pub fn exhausted_readonly() -> bool {
    if VERIFY_TRIP.with(|t| t.get()).is_some() {
        return true;
    }
    if VERIFY_STEPS.with(|s| s.get()) == 0 {
        latch_trip(BudgetTrip::Steps);
        return true;
    }
    let clock_passed = VERIFY_DEADLINE.with(|d| match d.get() {
        Some(at) => Instant::now() >= at,
        None => false,
    });
    if clock_passed {
        latch_trip(BudgetTrip::Clock);
    }
    clock_passed
}

/// The first bound that tripped in the current guarded scope, as the stop
/// cause a consumer stamps on what the trip degraded. `None` while nothing has
/// tripped. Non-charging.
#[inline]
pub fn exhaustion_cause() -> Option<StopCause> {
    VERIFY_TRIP.with(|t| t.get()).map(BudgetTrip::stop_cause)
}

#[cfg(test)]
mod tests {
    use std::time::Duration;

    use super::*;

    #[test]
    fn a_step_trip_is_a_count_and_is_reported_as_steps() {
        let _guard = VerifyBudgetGuard::install(None, 3);
        assert_eq!(exhaustion_cause(), None);
        assert!(!budget_exhausted());
        assert!(!budget_exhausted());
        assert!(!budget_exhausted());
        assert!(budget_exhausted(), "the fourth poll finds the counter at zero");
        assert_eq!(exhaustion_cause(), Some(StopCause::Steps));
        assert!(exhausted_readonly());
        assert_eq!(exhaustion_cause(), Some(StopCause::Steps));
    }

    #[test]
    fn a_passed_deadline_is_reported_as_the_wall_backstop() {
        let past =
            Instant::now().checked_sub(Duration::from_millis(1)).unwrap_or_else(Instant::now);
        let _guard = VerifyBudgetGuard::install(Some(past), u64::MAX);
        assert_eq!(exhaustion_cause(), None);
        assert!(exhausted_readonly());
        assert_eq!(exhaustion_cause(), Some(StopCause::WallBackstop));
    }

    #[test]
    fn a_zero_step_budget_is_spent_not_disabled() {
        let _guard = VerifyBudgetGuard::install(None, 0);
        assert!(exhausted_readonly(), "zero steps left is an exhausted count");
        assert!(budget_exhausted());
        assert_eq!(exhaustion_cause(), Some(StopCause::Steps));
    }

    fn clock_notes() -> u64 {
        crate::determinism::noted_stops()
            .iter()
            .filter(|stop| stop.lane == BUDGET_CLOCK_LANE && stop.cause == StopCause::WallBackstop)
            .map(|stop| stop.count)
            .sum()
    }

    /// The scope-end report (module doc). The ledger is process-wide, so this
    /// asserts only that ITS scopes added notes; tests that run concurrently
    /// can add more, never fewer.
    #[test]
    fn a_scope_whose_clock_fired_reports_it_when_it_ends() {
        let past =
            Instant::now().checked_sub(Duration::from_millis(1)).unwrap_or_else(Instant::now);
        let before = clock_notes();
        {
            // No poll ever observes the passed deadline: a lane that tests the
            // deadline itself (and not through this module) must still count.
            let _guard = VerifyBudgetGuard::install(Some(past), u64::MAX);
        }
        let after_passed_deadline = clock_notes();
        assert!(after_passed_deadline > before, "a passed deadline is reported on drop");
        {
            let _guard = VerifyBudgetGuard::install(Some(past), u64::MAX);
            assert!(exhausted_readonly());
        }
        assert!(clock_notes() > after_passed_deadline, "a clock trip is reported on drop");
    }

    #[test]
    fn the_first_trip_decides_even_if_the_other_half_trips_later() {
        let past =
            Instant::now().checked_sub(Duration::from_millis(1)).unwrap_or_else(Instant::now);
        let _guard = VerifyBudgetGuard::install(Some(past), 2);
        // The clock is observed first (a checkpoint), then the counter runs out.
        assert!(exhausted_readonly());
        assert!(!budget_exhausted());
        assert!(!budget_exhausted());
        assert!(budget_exhausted(), "the counter is now spent as well");
        assert_eq!(
            exhaustion_cause(),
            Some(StopCause::WallBackstop),
            "a clock-degraded scope stays not-reproducible"
        );
    }

    /// The latch in the POLL, not only in the read-only checkpoint: every
    /// instrumented preprocessing loop calls [`budget_exhausted`], and a clock
    /// trip it observes must be the scope's cause even when the step counter
    /// runs out later in the same scope. Without the latch a walk the clock cut
    /// short would be stamped `steps` once its counter ran out — a clock hiding
    /// behind a count. Nothing here calls [`exhausted_readonly`], which latches
    /// on its own.
    #[test]
    fn a_clock_trip_seen_by_the_poll_is_latched_before_the_counter_runs_out() {
        let past =
            Instant::now().checked_sub(Duration::from_millis(1)).unwrap_or_else(Instant::now);
        let _guard = VerifyBudgetGuard::install(Some(past), 2 * WALL_POLL_INTERVAL);
        let mut trips = 0u64;
        for _ in 0..WALL_POLL_INTERVAL {
            trips += u64::from(budget_exhausted());
        }
        assert_eq!(trips, 1, "the poll reads the clock once per interval, and it has passed");
        assert_eq!(
            exhaustion_cause(),
            Some(StopCause::WallBackstop),
            "the poll latched the clock it observed"
        );
        // 4,096 steps are left: one more interval of polls spends them, and the
        // poll after that finds the counter at zero.
        for _ in 0..=WALL_POLL_INTERVAL {
            budget_exhausted();
        }
        assert!(budget_exhausted(), "the step counter is spent as well");
        assert_eq!(
            exhaustion_cause(),
            Some(StopCause::WallBackstop),
            "the counter running out later does not relabel a clock-cut scope"
        );
    }

    /// The checkpoint sees every trip a poll latched (see [`exhausted_readonly`]),
    /// even when the bound's own state no longer reads as tripped. No current
    /// bound reaches that state (a spent counter and a passed deadline stay so),
    /// so it is set up by hand: a latched trip while both re-read halves are
    /// live. It stands for a bound like the seal's peak-memory ceiling, which the
    /// checkpoint did not re-read; with the latch unread this test fails.
    #[test]
    fn every_trip_a_poll_made_is_seen_by_the_checkpoint() {
        let future = Instant::now().checked_add(Duration::from_secs(3600));
        let _guard = VerifyBudgetGuard::install(future, u64::MAX);
        assert!(!exhausted_readonly(), "nothing has tripped and both halves are live");
        latch_trip(BudgetTrip::Steps);
        assert!(VERIFY_STEPS.with(|s| s.get()) > 0, "the counter is not spent");
        assert!(future.is_some_and(|at| Instant::now() < at), "the deadline has not passed");
        assert!(exhausted_readonly(), "a latched trip is an exhausted scope");
        assert_eq!(exhaustion_cause(), Some(StopCause::Steps), "and keeps its own cause");
        {
            let _inner = VerifyBudgetGuard::install(future, u64::MAX);
            assert!(!exhausted_readonly(), "a fresh nested scope has not tripped");
        }
        assert!(exhausted_readonly(), "the outer trip is restored with the outer scope");
    }

    /// The poll's invariant (see [`budget_exhausted`]): every `true` it answers
    /// has latched a trip BEFORE any checkpoint runs, so [`exhaustion_cause`] names
    /// it and [`exhausted_readonly`] reports it. Swept over both halves: spent
    /// counters, an off-interval and an on-interval step count, no deadline, a
    /// passed deadline and a future one. The cause is read before the checkpoint,
    /// because the checkpoint latches on its own and would hide a poll that did not.
    #[test]
    fn every_true_the_poll_answers_is_latched_before_any_checkpoint() {
        let past =
            Instant::now().checked_sub(Duration::from_millis(1)).unwrap_or_else(Instant::now);
        let future = Instant::now().checked_add(Duration::from_secs(3600));
        let mut trips = [0usize; 2];
        for deadline in [None, Some(past), future] {
            for steps in [1, 2, WALL_POLL_INTERVAL, WALL_POLL_INTERVAL + 1, 3 * WALL_POLL_INTERVAL]
            {
                let _guard = VerifyBudgetGuard::install(deadline, steps);
                for _ in 0..=steps {
                    let cause_before = exhaustion_cause();
                    if budget_exhausted() {
                        let cause = exhaustion_cause();
                        assert!(
                            cause.is_some(),
                            "a `true` poll left no latched trip (deadline {deadline:?}, budget {steps})"
                        );
                        assert!(
                            cause_before.is_none() || cause_before == cause,
                            "the first trip stays latched"
                        );
                        assert!(exhausted_readonly(), "the checkpoint sees the poll's trip");
                        match cause {
                            Some(StopCause::Steps) => trips[0] += 1,
                            Some(StopCause::WallBackstop) => trips[1] += 1,
                            other => panic!("unexpected cause {other:?}"),
                        }
                    }
                }
            }
        }
        assert!(trips[0] > 0 && trips[1] > 0, "the sweep exercised both halves: {trips:?}");
    }

    #[test]
    fn a_nested_guard_starts_clean_and_restores_the_outer_trip() {
        let _outer = VerifyBudgetGuard::install(None, 1);
        assert!(!budget_exhausted());
        assert!(budget_exhausted());
        assert_eq!(exhaustion_cause(), Some(StopCause::Steps));
        {
            let _inner = VerifyBudgetGuard::install(None, u64::MAX);
            assert_eq!(exhaustion_cause(), None, "a fresh scope has not tripped");
            assert!(!budget_exhausted());
        }
        assert_eq!(exhaustion_cause(), Some(StopCause::Steps), "the outer latch is restored");
    }

    /// The share guard (gate-rca deadline, 2026-10-17): a passed SHARE trips the polls
    /// and the checkpoint inside the scope, and does not survive it while the function's
    /// own deadline is live. Negative control: the same passed instant installed as the
    /// FUNCTION deadline does survive (that is what the compiler's later checkpoints must
    /// see), so the test can tell the two apart.
    #[test]
    fn a_passed_share_trips_inside_and_is_cleared_when_the_scope_ends() {
        let past =
            Instant::now().checked_sub(Duration::from_millis(1)).unwrap_or_else(Instant::now);
        let future = Instant::now().checked_add(Duration::from_secs(3600));
        let _function = VerifyBudgetGuard::install(future, u64::MAX);
        {
            let _share = DeadlineShareGuard::narrow(Some(past));
            assert_eq!(current_deadline(), Some(past), "the earlier share is the deadline inside");
            assert!(exhausted_readonly(), "the checkpoint inside sees the passed share");
            assert_eq!(exhaustion_cause(), Some(StopCause::WallBackstop));
        }
        assert_eq!(current_deadline(), future, "the function deadline is restored");
        assert!(!exhausted_readonly(), "the share's clock trip is not the function's");
        assert_eq!(exhaustion_cause(), None);

        // Negative control: a passed FUNCTION deadline is exhausted after the scope too.
        let _passed = VerifyBudgetGuard::install(Some(past), u64::MAX);
        {
            let _share = DeadlineShareGuard::narrow(future);
            assert_eq!(current_deadline(), Some(past), "a later share never loosens the deadline");
            assert!(exhausted_readonly());
        }
        assert!(exhausted_readonly(), "the function's own passed clock is re-read and latched");
    }

    /// The share guard keeps ONE step counter: steps spent inside are the function's,
    /// and a step trip inside stays latched after the scope. Negative control: a fresh
    /// [`VerifyBudgetGuard`] in the same place hands the phase a new counter, and the
    /// function's count is untouched by what it spends.
    #[test]
    fn a_share_scope_charges_and_keeps_the_function_step_counter() {
        let _function = VerifyBudgetGuard::install(None, 3);
        {
            let _share = DeadlineShareGuard::narrow(None);
            assert!(!budget_exhausted());
            assert!(!budget_exhausted());
            assert!(!budget_exhausted());
            assert!(budget_exhausted(), "the fourth poll in the share spends the function's count");
        }
        assert_eq!(exhaustion_cause(), Some(StopCause::Steps), "a step trip is the function's");
        assert!(exhausted_readonly());

        let _control = VerifyBudgetGuard::install(None, 3);
        {
            let _fresh = VerifyBudgetGuard::install(None, 3);
            for _ in 0..4 {
                budget_exhausted();
            }
        }
        assert_eq!(exhaustion_cause(), None, "a fresh guard does not charge the outer count");
        assert!(!budget_exhausted(), "the outer count is untouched");
    }

    #[test]
    fn earliest_takes_the_earlier_bound_and_none_is_unbounded() {
        let now = Instant::now();
        let later = now.checked_add(Duration::from_secs(1));
        assert_eq!(earliest(Some(now), later), Some(now));
        assert_eq!(earliest(later, Some(now)), Some(now));
        assert_eq!(earliest(None, Some(now)), Some(now));
        assert_eq!(earliest(Some(now), None), Some(now));
        assert_eq!(earliest(None, None), None);
    }

    /// A far deadline: these tests read the credit arithmetic, never a trip.
    fn far() -> Instant {
        Instant::now() + Duration::from_secs(3600)
    }

    /// Run `scope` around a short nested piece of work and return the instants the
    /// test saw: (before the scope was installed, inside it at its start, inside it
    /// at its end, after it dropped). The work is a sleep, so `inside_end -
    /// inside_start` is at least `at_least`.
    fn around<G>(scope: impl FnOnce() -> G, at_least: Duration) -> [Instant; 4] {
        let before = Instant::now();
        let guard = scope();
        let inside_start = Instant::now();
        std::thread::sleep(at_least);
        let inside_end = Instant::now();
        drop(guard);
        [before, inside_start, inside_end, Instant::now()]
    }

    /// NESTED-CLOCK (gate-rca deadline, 2026-10-18): a FUNCTION scope nested in
    /// another function's scope credits its whole wall time to the enclosing deadline
    /// when it ends — at least the time seen inside it, at most the time around it.
    /// Negative control: the same nested work in an ordinary scope (`install`) leaves
    /// the enclosing deadline exactly where it was, which is what spent a caller's
    /// clock on its callee's verification before the fix.
    #[test]
    fn a_nested_function_scope_is_credited_to_the_enclosing_deadline() {
        let deadline = far();
        let _caller = VerifyBudgetGuard::install_function(Some(deadline), u64::MAX);
        let mark = clock_credit_mark();
        let [before, start, end, after] = around(
            || VerifyBudgetGuard::install_function(Some(far()), u64::MAX),
            Duration::from_millis(5),
        );
        let moved = current_deadline().expect("the caller's deadline") - deadline;
        assert!(moved >= end - start, "credited {moved:?}, less than the nested work");
        assert!(moved <= after - before, "credited {moved:?}, more than the nested scope");
        assert_eq!(clock_credit_since(mark), moved, "a captured deadline moves alike");
        assert_eq!(credited(Some(deadline), mark), current_deadline());
        assert_eq!(credited(None, mark), None, "no clock stays no clock");

        let restored = current_deadline();
        let mark = clock_credit_mark();
        let _ =
            around(|| VerifyBudgetGuard::install(Some(far()), u64::MAX), Duration::from_millis(5));
        assert_eq!(current_deadline(), restored, "control: an ordinary scope credits nothing");
        assert_eq!(clock_credit_since(mark), Duration::ZERO);
    }

    /// The bug's shape, as a negative control: nested work in an ordinary scope that
    /// outlives the caller's deadline leaves the caller exhausted on the clock. In a
    /// function scope the caller's deadline moves past the nested work instead.
    #[test]
    fn nested_work_past_the_caller_deadline_spends_it_only_outside_a_function_scope() {
        let deadline = Instant::now() + Duration::from_millis(20);
        let _caller = VerifyBudgetGuard::install_function(Some(deadline), u64::MAX);
        {
            let _plain = VerifyBudgetGuard::install(Some(far()), u64::MAX);
            while Instant::now() < deadline {
                std::thread::sleep(Duration::from_millis(1));
            }
        }
        assert!(exhausted_readonly(), "control: the caller's clock ran during the nested work");
        assert_eq!(exhaustion_cause(), Some(StopCause::WallBackstop));

        let deadline = Instant::now() + Duration::from_millis(20);
        let _caller = VerifyBudgetGuard::install_function(Some(deadline), u64::MAX);
        let start;
        let end;
        {
            let _nested = VerifyBudgetGuard::install_function(Some(far()), u64::MAX);
            start = Instant::now();
            while Instant::now() < deadline {
                std::thread::sleep(Duration::from_millis(1));
            }
            end = Instant::now();
        }
        let moved = current_deadline().expect("the caller's deadline") - deadline;
        assert!(moved >= end - start, "the caller keeps the clock the nested work took");
    }

    /// Two levels of nesting: the innermost function's time is credited to the middle
    /// function's deadline when it ends, and the middle function credits its whole
    /// time — the innermost part included once, not twice — to the outer deadline.
    #[test]
    fn nested_function_credit_counts_each_instant_once_through_two_levels() {
        let outer = far();
        let _outer = VerifyBudgetGuard::install_function(Some(outer), u64::MAX);
        let middle = far();
        let before = Instant::now();
        let middle_guard = VerifyBudgetGuard::install_function(Some(middle), u64::MAX);
        let [_, start, end, _] = around(
            || VerifyBudgetGuard::install_function(Some(far()), u64::MAX),
            Duration::from_millis(5),
        );
        let middle_moved = current_deadline().expect("the middle deadline") - middle;
        assert!(middle_moved >= end - start);
        std::thread::sleep(Duration::from_millis(5));
        drop(middle_guard);
        let after = Instant::now();
        let outer_moved = current_deadline().expect("the outer deadline") - outer;
        assert!(outer_moved >= middle_moved + Duration::from_millis(5));
        assert!(
            outer_moved <= after - before,
            "the outer deadline moved {outer_moved:?}, more than the middle scope lasted"
        );
    }

    /// A function verified inside a share scope moves the share (the ambient deadline
    /// inside) and, when the share ends, the deadline it restores.
    #[test]
    fn a_function_verified_inside_a_share_moves_the_share_and_the_restored_deadline() {
        let deadline = far();
        let _caller = VerifyBudgetGuard::install_function(Some(deadline), u64::MAX);
        let share = Instant::now() + Duration::from_secs(1800);
        let share_guard = DeadlineShareGuard::narrow(Some(share));
        let [_, start, end, _] = around(
            || VerifyBudgetGuard::install_function(Some(far()), u64::MAX),
            Duration::from_millis(5),
        );
        let share_moved = current_deadline().expect("the share") - share;
        assert!(share_moved >= end - start);
        drop(share_guard);
        assert_eq!(
            current_deadline(),
            Some(deadline + share_moved),
            "the restored deadline moves by the same credit"
        );
    }

    #[test]
    fn a_budget_larger_than_the_work_never_trips() {
        let _guard = VerifyBudgetGuard::install(None, u64::MAX);
        for _ in 0..(3 * WALL_POLL_INTERVAL) {
            assert!(!budget_exhausted());
        }
        assert!(!exhausted_readonly());
        assert_eq!(exhaustion_cause(), None);
    }
}

#[cfg(test)]
#[path = "verify_budget/worker_tests.rs"]
mod worker_tests;
