// trust-router/in_process_ay_backend/lock_clock_tests.rs: a query's clock is
// charged for its work, not for its wait on AY's process-global execution lock
// (ROUTER-LOCK-CLOCK-1).
//
// Measured 2026-11-02 (VCGEN-TEST-BACKSTOP-1): in `ffi_pointer_contract_realmir`
// ten queries queued behind one slow solve each spent their whole clock waiting
// for the lock and came back `Unknown` ("shared query deadline exhausted before
// AY dispatch") without ever being solved, so a row's verdict depended on the
// load. These tests hold the lock from the test thread, as that slow solve did,
// and pin both halves of the rule: a queued query is still solved under its whole
// clock, and the outer deadline still ends a wait, which then names itself.
//
// What each test asserts is a verdict, a stop cause or an equality, never a
// time. Two of them also check that the run exercised the rule at all (the query
// really waited longer than its whole clock): that check reads the wait the solve
// itself measured ([`LOCK_WAITED`]), and the hold is counted from the moment the
// query thread is about to ask, so how late the scheduler starts that thread does
// not shorten the wait it sees.
//
// Each test holds the one process-global lock for a few seconds, so the other
// tests of this binary that solve in-process wait that long; none of them
// charges the wait to its clock any more, which is the point.
//
// Author: Andrew Yates
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::cell::Cell;
use std::sync::mpsc;
use std::time::{Duration, Instant};

use trust_types::determinism::StopCause;
use trust_types::verify_budget::VerifyBudgetGuard;
use trust_types::{Formula, Sort, VerificationResult};

use super::InProcessAyBackend;

thread_local! {
    /// How long this thread's solves waited for AY's execution lock, in all, as
    /// `lock_ay_exec_until` measured each wait (`solve_and_classify_in` adds
    /// every one, whether the wait ended in the lock or in a bound). Read apart
    /// from the budget the wait is credited to, so a test can tell "the query
    /// did not wait" from "the wait was not credited".
    pub(super) static LOCK_WAITED: Cell<Duration> = const { Cell::new(Duration::ZERO) };
}

/// Run `work` and measure how long its solves waited for the lock.
fn measuring_lock_waits<T>(work: impl FnOnce() -> T) -> (T, Duration) {
    let before = LOCK_WAITED.with(Cell::get);
    let answer = work();
    (answer, LOCK_WAITED.with(Cell::get).saturating_sub(before))
}

/// The queued query's own clock.
const QUERY_CLOCK_MS: u64 = 1_000;
/// The queued query's own clock, as a duration.
const QUERY_CLOCK: Duration = Duration::from_millis(QUERY_CLOCK_MS);
/// How long the test holds the lock once the query is about to ask: three times
/// the query's clock, so a wait charged to the clock spends it, with two whole
/// clocks to spare for the moment between asking and trying the lock.
const HOLD: Duration = Duration::from_millis(3 * QUERY_CLOCK_MS);
/// The longest the test holds the lock for a query a bound must stop: the hold
/// ends as soon as the query answers, so a long one costs nothing when the
/// bound works and leaves room for a slow scheduler when it does.
const LONG_HOLD: Duration = Duration::from_secs(30);
/// The solver threads' stack, as the real-MIR fixtures give theirs.
const SOLVER_STACK_BYTES: usize = 64 * 1024 * 1024;

/// `x > 5` over Int: satisfiable, refuted with a model in a few milliseconds.
fn refutable() -> Formula {
    Formula::Gt(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(5)))
}

/// Hold AY's execution lock while `query` runs on its own thread, for `hold`
/// counted from when that thread is about to call `query` (not from when it
/// was spawned, which the scheduler decides), or until `query` answers; then
/// release it. Answers what `query` returned, and whether it had returned while
/// the lock was still held.
fn while_the_lock_is_held<T: Send + 'static>(
    hold: Duration,
    query: impl FnOnce() -> T + Send + 'static,
) -> (T, bool) {
    let held = trust_types::ay_exec_lock().lock().unwrap_or_else(|e| e.into_inner());
    let (asking, about_to_ask) = mpsc::channel();
    let (sender, receiver) = mpsc::channel();
    let worker = std::thread::Builder::new()
        .stack_size(SOLVER_STACK_BYTES)
        .spawn(move || {
            // The receivers may be gone if the test already failed.
            let _ = asking.send(());
            let _ = sender.send(query());
        })
        .expect("spawn the query thread");
    about_to_ask.recv().expect("the query thread starts");
    let early = receiver.recv_timeout(hold);
    drop(held);
    let answered_while_held = early.is_ok();
    let answer = match early {
        Ok(answer) => answer,
        Err(_) => receiver.recv().expect("the query thread answers once the lock is free"),
    };
    worker.join().expect("the query thread must not panic");
    (answer, answered_while_held)
}

/// THE DEFECT, pinned: a query that waits for the lock longer than its whole
/// clock is still dispatched, and gets the verdict its effort count gives it.
/// Before ROUTER-LOCK-CLOCK-1 the wait spent the clock, and the query answered
/// `Unknown` "shared query deadline exhausted before AY dispatch" as soon as it
/// took the lock.
#[test]
fn a_query_queued_behind_the_lock_longer_than_its_clock_is_still_solved() {
    let backend = InProcessAyBackend::new().with_timeout(QUERY_CLOCK_MS);
    let ((result, waited), answered_while_held) =
        while_the_lock_is_held(HOLD, move || measuring_lock_waits(|| backend.run(&refutable())));
    assert!(!answered_while_held, "no bound may end a wait this short: {result:?}");
    assert!(
        waited > QUERY_CLOCK,
        "the query must have waited for the lock longer than its whole {QUERY_CLOCK_MS} ms clock \
         (it waited {waited:?}), or this test pins nothing: {result:?}"
    );
    assert!(
        matches!(&result, VerificationResult::Failed { counterexample: Some(_), .. }),
        "a query queued behind the lock for {waited:?}, longer than its {QUERY_CLOCK_MS} ms \
         clock, must still be solved and refuted, not stopped on a clock its wait spent: \
         {result:?}"
    );
}

/// The same wait, on a query whose disjoint-component retry runs: every
/// component solve takes the lock again, and none of those waits is charged.
/// `x > 5 ∧ y > 7` splits into two components; the whole query is refuted by
/// the first solve, so this drives the retry directly through its budget.
#[test]
fn a_component_retry_queued_behind_the_lock_is_still_solved() {
    use super::{ComponentRetry, ComponentRetryBudget};
    let backend = InProcessAyBackend::new().with_timeout(QUERY_CLOCK_MS);
    let formula = Formula::And(vec![
        refutable(),
        Formula::Gt(Box::new(Formula::Var("y".into(), Sort::Int)), Box::new(Formula::Int(7))),
    ]);
    let ((result, credited, waited), answered_while_held) =
        while_the_lock_is_held(HOLD, move || {
            let budget = ComponentRetryBudget::new(QUERY_CLOCK_MS);
            let (result, waited) = measuring_lock_waits(|| {
                match backend.try_disjoint_component_refutation(&formula, true, 0, &budget) {
                    ComponentRetry::Refuted(failed) => failed,
                    ComponentRetry::Undecided(cause) => {
                        cause.unknown_result("component retry", 0, "the retry did not refute")
                    }
                    ComponentRetry::NotApplicable => panic!("`x > 5 ∧ y > 7` splits in two"),
                }
            });
            (result, budget.lock_waited(), waited)
        });
    assert!(!answered_while_held, "no bound may end a wait this short: {result:?}");
    assert!(
        waited > QUERY_CLOCK,
        "the retry must have waited for the lock longer than its whole {QUERY_CLOCK_MS} ms clock \
         (it waited {waited:?}), or this test pins nothing: {result:?}"
    );
    assert_eq!(
        credited, waited,
        "every wait the retry's solves made is credited to the query's budget, none charged"
    );
    let VerificationResult::Failed { counterexample: Some(model), .. } = &result else {
        panic!(
            "a component retry queued behind the lock for {waited:?} must still refute both \
             components: {result:?}"
        );
    };
    assert_eq!(model.assignments.len(), 2, "both components' models compose: {model:?}");
}

/// The OUTER bound still holds: a wait cannot outlive the enclosing deadline
/// (the compiler's per-function clock), and the row it ends names the wait.
/// Before ROUTER-LOCK-CLOCK-1 the wait was a plain `lock()`, which no deadline
/// reached: this query would have waited the whole hold out.
#[test]
fn a_wait_past_the_enclosing_deadline_stops_and_names_the_wait() {
    let backend = InProcessAyBackend::new().with_timeout(60_000);
    let (result, answered_while_held) = while_the_lock_is_held(LONG_HOLD, move || {
        let _function = VerifyBudgetGuard::install(
            Some(Instant::now() + Duration::from_millis(QUERY_CLOCK_MS / 2)),
            u64::MAX,
        );
        backend.run(&refutable())
    });
    assert!(
        answered_while_held,
        "the enclosing deadline must end the wait while the lock is still held: {result:?}"
    );
    let VerificationResult::Unknown { reason, .. } = &result else {
        panic!("a query whose wait outlived its enclosing deadline is undecided: {result:?}");
    };
    assert_eq!(StopCause::of_result(&result), StopCause::WallBackstop, "{reason}");
    assert!(
        reason.contains("for AY's process-global execution lock")
            && reason.contains("the enclosing verification deadline passed")
            && reason.contains("no solve was dispatched"),
        "the row must name the wait and the bound that ended it: {reason}"
    );
}

/// Pigeonhole PHP(7,6) over Bool variables named `{prefix}_i_j`: unsatisfiable,
/// and far more than one conflict per term for CDCL.
fn pigeonhole_7_6(prefix: &str) -> Vec<Formula> {
    let holes = 6usize;
    let pigeons = holes + 1;
    let var = |i: usize, j: usize| Formula::Var(format!("{prefix}_{i}_{j}").into(), Sort::Bool);
    let mut conjuncts = Vec::new();
    for i in 0..pigeons {
        conjuncts.push(Formula::Or((0..holes).map(|j| var(i, j)).collect()));
    }
    for j in 0..holes {
        for i in 0..pigeons {
            for k in (i + 1)..pigeons {
                conjuncts.push(Formula::Or(vec![
                    Formula::Not(Box::new(var(i, j))),
                    Formula::Not(Box::new(var(k, j))),
                ]));
            }
        }
    }
    conjuncts
}

/// The retry's solves draw from the effort count of the query's own scale, as
/// the whole query's solve does, so a component whose search the count can end
/// ends on the count (`effort`), the same on every host, never on the clock.
/// Two variable-disjoint PHP(7,6) at one conflict per term, behind a minute's
/// clock: the whole query, each component and the row all stop on `effort`. The
/// stop cause is the assertion, not a time: a clock that ended a solve would
/// read `wall-backstop`, so the test does not depend on the load. (A component
/// whose search ay's count does not bound still ends on the clock:
/// ROUTER-LOCK-CLOCK-1's residual R1, ay's QF_NIA split loop.)
#[test]
fn a_component_retry_ends_on_the_effort_count_not_the_clock() {
    use trust_types::determinism::EffortScale;

    use super::{ComponentRetry, ComponentRetryBudget};
    let starved = InProcessAyBackend::new()
        .with_timeout(60_000)
        .with_effort_scale(EffortScale { conflicts_per_node: 1 });
    let whole = Formula::And(pigeonhole_7_6("a").into_iter().chain(pigeonhole_7_6("b")).collect());
    let retry = starved.try_disjoint_component_refutation(
        &whole,
        true,
        0,
        &ComponentRetryBudget::new(60_000),
    );
    assert!(
        matches!(retry, ComponentRetry::Undecided(StopCause::Effort)),
        "each component's search ends on its share of the count: {retry:?}"
    );
    let row = starved.run(&whole);
    let VerificationResult::Unknown { reason, .. } = &row else {
        panic!("one conflict per term decides neither PHP(7,6): {row:?}");
    };
    assert_eq!(StopCause::of_result(&row), StopCause::Effort, "{reason}");
    assert!(
        !reason.contains("retry stopped"),
        "a retry the count ended leaves the row's own stop as it was: {reason}"
    );
}
