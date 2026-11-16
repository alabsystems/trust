//! The deterministic in-process `ay` router trust-vcgen's tests decide their rows
//! with (VCGEN-TEST-BACKSTOP-1, `docs/DECISION_QUEUE.md`).
//!
//! A verdict of [`trust_router::Router::deterministic_in_process_ay`] is meant to be
//! decided by ay's effort count: `:rlimit`, set from the [`EffortScale`]. Its
//! `timeout_ms` is the WALL-CLOCK BACKSTOP for a phase that stops counting
//! (`trust-router`'s `router.rs`). A test that asserts a verdict should not be
//! decided by a clock it does not test: a backstop that fires is the machine, not the
//! verifier. Measured 2026-11-02 under a landing gate at load ~100 on 18 cores: a
//! 30-second backstop turned a PROVED
//! control of `ploss_adv_false_proofs_realmir.rs` into
//! `Unknown { time_ms: 30310, reason: "shared query deadline exhausted before AY
//! dispatch [stop:wall-backstop]; ..." }`, because that clock then started BEFORE the
//! query waited on ay's process-global execution lock, which every libtest thread of
//! the binary shares. Since ROUTER-LOCK-CLOCK-1 (`docs/DECISION_QUEUE.md`) the wait
//! is not charged to the query's clock; only the query's own solving is.
//!
//! The count does not yet decide alone, so a long backstop removes the test's clock
//! and not every effect of load. [`EffortScale`]'s docs
//! (`trust-types/src/determinism.rs`, the T2 dependencies) list what is left:
//! ay-sat's wall-capped restart inprocessing and lookahead, in every SAT solve but
//! the bit-blast ones, move where the count stops a search; `:rlimit` bounds each SAT
//! solve inside a check-sat, not the whole check; and ay's 24,000,000-decision
//! allowance stays in force as a second count. A row near its count's edge can
//! therefore still change verdict under load while this backstop never fires.
//! Measured:
//! `cex_grounding_castu_unminable` VC 2 (`counterexample_grounding_realmir.rs`),
//! refuted at k = 192 alone, came back `incomplete` in 2 of 4 runs of its file at
//! eight threads; at the builtin k = 384 it did so in 0 of 5. Such a stop reads as
//! `effort`, `incomplete` or another ay stop, not `[stop:wall-backstop]`. Before
//! calling one a verifier regression, rerun it on an idle host: a verdict that holds
//! idle and flips under load marks a count-edge row.
//!
//! The backstop here only stops a hang: [`TEST_BACKSTOP_MS`] (ten minutes), which
//! `TRUST_TEST_SOLVER_BACKSTOP_MS` may RAISE and never lower.
//!
//! ONLY FOR A TEST WHOSE EVERY SOLVE THE COUNT ENDS. A test that is about the backstop
//! itself (it expects a clock-ended `Unknown`, measures time, or exercises the deadline
//! plumbing) keeps its own timeout, and so does a test whose fixtures hold a row the
//! count does NOT end: measured 2026-11-02, the disjoint-component refutation retry of
//! an `[unsafe:sep:deref] alignment check` row runs until its share of the clock (300 s
//! of ten minutes, 15 s of thirty seconds), and one `alignment check` solve ran the whole
//! ten minutes at 25,882 conflicts. Such a row holds ay's process-global execution lock
//! for its whole share. Until ROUTER-LOCK-CLOCK-1 every query queued behind it spent
//! ITS clock waiting: with this router that was ten minutes per row and the same
//! `exhausted before AY dispatch` failure (`ffi_pointer_contract_realmir.rs`, 10 queued
//! rows). The queued queries are now solved, but the row itself still ends on the
//! clock, ten minutes at a time under this router, so those files keep their literal
//! clock until ay counts that phase (VCGEN-TEST-BACKSTOP-1 lists them;
//! ROUTER-LOCK-CLOCK-1's residual R1 locates the phase).
//!
//! Two kinds of test keep a clock for what they check, not for a row the count misses:
//! a SPEED GUARD that fails by timeout when a gate widens
//! (`intrinsic_semantics_realmir.rs`'s `cttz` free-argument row keeps its 30 s), and a
//! test that mirrors a SHIPPED lane's router, which builds [`shipped_vc_clock_router`].
//! A test mirrors a lane when it says it solves through the router a named compiler
//! lane builds: then a solve the shipped clock would stop must fail the test too,
//! whatever clock the test had before. A test that says only that it uses the
//! backend the compiler routes to does not mirror a lane's clock.
//!
//! One definition: integration tests include this file with
//! `#[path = "support/test_router.rs"] mod test_router;`, and the library's unit tests
//! reach it as `crate::test_router` (`src/lib.rs`, `cfg(test)`).
#![allow(dead_code)]

use trust_types::determinism::{Backstop, EffortScale};

/// The wall-clock backstop the test router gets: ten minutes. It ends a solve the
/// count fails to stop (ROUTER-LOCK-CLOCK-1's residual R1, ay's QF_NIA split loop),
/// so a hang fails the test rather than the run.
///
/// A wait for ay's execution lock never spends it. Since ROUTER-LOCK-CLOCK-1 a
/// query's wait is credited to its own deadline (`ComponentRetryBudget::note_lock_wait`
/// in `trust-router`, pinned by its `lock_clock_tests`), so a binary's libtest
/// threads queueing behind one another at any load cost none of this backstop. With
/// no enclosing deadline, as here, a wait is bounded only by the lock-wait hang bound,
/// 64 of these clocks (`lock_wait_backstop_ms`: 38,400,000 ms, about 10.7 hours). So
/// raising this value buys room only for the query's own solving, never for its
/// place in the queue.
pub const TEST_BACKSTOP_MS: u64 = 600_000;

/// The ceiling of an override: one day. `ComponentRetryBudget` reads a deadline it
/// cannot represent as one already passed, so an unbounded override would turn
/// every row into a clock-ended `Unknown` — the defect this file exists to remove.
pub const TEST_BACKSTOP_MAX_MS: u64 = 86_400_000;

/// Raises the backstop (milliseconds); a value below [`TEST_BACKSTOP_MS`] is
/// raised to it, one above [`TEST_BACKSTOP_MAX_MS`] lowered to that.
pub const TEST_BACKSTOP_ENV: &str = "TRUST_TEST_SOLVER_BACKSTOP_MS";

/// The deterministic in-process ay router, at the builtin effort scale (the scale
/// every trust-vcgen test site used), with the test backstop: the router a test that
/// solves with ay alone builds.
pub fn deterministic_test_router() -> trust_router::Router {
    trust_router::Router::deterministic_in_process_ay(test_backstop_ms(), EffortScale::BUILTIN)
}

/// The deterministic in-process ay router at the per-query clock `targo trust` ships:
/// [`Backstop::BUILTIN`]'s `vc_clock_ms()`, 5,000 ms, which targo passes as
/// `-Ztrust-verify-timeout-ms`. For a test that mirrors a SHIPPED lane rather than one
/// that only needs a verdict. The per-path refute lane and the BMC bounded-reduction
/// refute lane (`refute_bounded_reduction_bmc_overflows`) in
/// `compiler/rustc_mir_transform/src/trust_verify.rs`, like its other ay lanes, build
/// `deterministic_in_process_ay(timeout_ms, effort_scale(sess))` with `timeout_ms` at
/// most `vc_timeout_ms(sess)`, so the tests that mirror them keep that clock
/// (VCGEN-TEST-BACKSTOP-1, kept sites). Spelled from the production constant so the two
/// cannot drift apart.
pub fn shipped_vc_clock_router() -> trust_router::Router {
    trust_router::Router::deterministic_in_process_ay(
        Backstop::BUILTIN.vc_clock_ms(),
        EffortScale::BUILTIN,
    )
}

/// The in-process ay backend with the test backstop, at the builtin effort scale, for
/// a test that measures the DEPLOYED backend pair (the interval backend, then ay) and
/// so builds its own [`trust_router::Router::with_backends`].
pub fn test_ay_backend() -> trust_router::in_process_ay_backend::InProcessAyBackend {
    trust_router::in_process_ay_backend::InProcessAyBackend::new()
        .with_timeout(test_backstop_ms())
        .with_effort_scale(EffortScale::BUILTIN)
}

/// The backstop in force: [`TEST_BACKSTOP_MS`], or the override.
pub fn test_backstop_ms() -> u64 {
    test_backstop_ms_from(std::env::var(TEST_BACKSTOP_ENV).ok().as_deref())
}

/// The backstop for an override value `raw` (`None`: the variable is unset). A
/// value that is not a whole number of milliseconds panics rather than being
/// ignored, so a mistyped override is never silently the default.
pub fn test_backstop_ms_from(raw: Option<&str>) -> u64 {
    let Some(raw) = raw.map(str::trim).filter(|raw| !raw.is_empty()) else {
        return TEST_BACKSTOP_MS;
    };
    let ms: u64 = raw.parse().unwrap_or_else(|_| {
        panic!("{TEST_BACKSTOP_ENV}={raw:?} must be a whole number of milliseconds")
    });
    ms.clamp(TEST_BACKSTOP_MS, TEST_BACKSTOP_MAX_MS)
}
