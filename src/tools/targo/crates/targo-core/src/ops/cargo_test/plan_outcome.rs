//! Trust: how a test plan run ended, as its exit status and its closing
//! record say it.
//!
//! A gate reads one number. Cargo's 101 for every failure made three
//! different answers look alike, and a gate must not treat them alike:
//!
//! | status | outcome | what it says |
//! |---|---|---|
//! | 0 | `passed`, `nothing-selected` | every performed request and phase passed, or the selection performs nothing |
//! | 101 | `failed` | red: a test failed that the known-red file does not list, a harness or a build failed, a phase failed, or a known-red row is stale |
//! | 2 | `cannot-judge`, `interrupted` | no verdict: the invocation or the plan was refused, a prerequisite was missing, a requirement that is no test failure was not met, or the run was interrupted |
//! | 3 | `out-of-time` | no verdict: the run's wall bound or a harness's no-progress bound ran out |
//!
//! Red wins over the others where a run shows both: a run with a new failure
//! and an unmet `min-tests` is red. Out of time wins over everything: a run
//! Targo stopped has no verdict, whatever had failed by then.
//!
//! With JSON messages the last record of every plan invocation is
//! `reason="test-plan-result"` and carries the same `outcome` and
//! `exit_status`; a run that ended before it had a verdict writes the short
//! form of `close`.

use std::sync::atomic::{AtomicBool, Ordering};

use serde::Serialize;

use crate::util::GlobalContext;
use crate::util::machine_message::Message;

/// The exit status of a run that judged nothing.
pub const CANNOT_JUDGE: i32 = 2;
/// The exit status of a run Targo stopped for time.
pub const OUT_OF_TIME: i32 = 3;
/// Cargo's status for a failure; here, red tests or a red build.
pub const FAILED: i32 = 101;

/// How a plan run ended.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum Outcome {
    Passed,
    NothingSelected,
    Failed,
    CannotJudge,
    Interrupted,
    OutOfTime,
}

impl Outcome {
    pub fn exit_status(self) -> i32 {
        match self {
            Self::Passed | Self::NothingSelected => 0,
            Self::Failed => FAILED,
            Self::CannotJudge | Self::Interrupted => CANNOT_JUDGE,
            Self::OutOfTime => OUT_OF_TIME,
        }
    }
}

/// Marks an error as one that judged nothing: attached as context, it is
/// what `status` finds, and what the person reads first.
#[derive(Clone, Copy, Debug)]
pub struct CannotJudge;

impl std::fmt::Display for CannotJudge {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "cannot judge (exit status {CANNOT_JUDGE}): this test plan run is no verdict on \
             the tests, neither a pass nor a failure"
        )
    }
}

/// Marks an error as the run having been interrupted.
#[derive(Clone, Copy, Debug)]
pub struct Interrupted;

impl std::fmt::Display for Interrupted {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "interrupted (exit status {CANNOT_JUDGE}): this test plan run was stopped and is \
             no verdict on the tests"
        )
    }
}

/// Marks an error as the run having been stopped for time.
#[derive(Clone, Copy, Debug)]
pub struct OutOfTime;

impl std::fmt::Display for OutOfTime {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "out of time (exit status {OUT_OF_TIME}): Targo stopped this test plan run, which \
             is no verdict on the tests"
        )
    }
}

/// `error`, marked as having judged nothing.
pub fn cannot_judge(error: anyhow::Error) -> anyhow::Error {
    if error.downcast_ref::<CannotJudge>().is_some() {
        return error;
    }
    error.context(CannotJudge)
}

/// The outcome `error` is marked with, if it is marked. An unmarked error
/// keeps the status it was raised with: a failed build or a failed test.
pub fn marked(error: &anyhow::Error) -> Option<Outcome> {
    if error.downcast_ref::<OutOfTime>().is_some() {
        Some(Outcome::OutOfTime)
    } else if error.downcast_ref::<Interrupted>().is_some() {
        Some(Outcome::Interrupted)
    } else if error.downcast_ref::<CannotJudge>().is_some() {
        Some(Outcome::CannotJudge)
    } else {
        None
    }
}

/// How the invocation is ending: the first stop Targo recorded, and whether
/// the run reached its own verdict before any stop came. The two are decided
/// under one lock, so a run has one ending: a stop that comes after the
/// verdict is refused (the run was over, and its record and status say how),
/// and a verdict reached after a stop is the stop's.
pub(crate) struct Ending {
    state: std::sync::Mutex<EndingState>,
}

struct EndingState {
    stopped: Option<(Outcome, String)>,
    concluded: bool,
}

impl Ending {
    pub(crate) const fn new() -> Self {
        Ending {
            state: std::sync::Mutex::new(EndingState {
                stopped: None,
                concluded: false,
            }),
        }
    }

    fn state(&self) -> std::sync::MutexGuard<'_, EndingState> {
        self.state
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
    }

    /// Records a stop, unless the run already has one or has its verdict.
    /// Returns whether this stop is the run's.
    pub(crate) fn stop(&self, outcome: Outcome, why: String) -> bool {
        let mut state = self.state();
        if state.concluded || state.stopped.is_some() {
            return false;
        }
        state.stopped = Some((outcome, why));
        true
    }

    pub(crate) fn stopped(&self) -> Option<(Outcome, String)> {
        self.state().stopped.clone()
    }

    /// The run has its verdict, unless a stop came first: then the stop is
    /// the run's ending, and the verdict is not written.
    pub(crate) fn conclude(&self) -> Result<(), (Outcome, String)> {
        let mut state = self.state();
        if let Some(stop) = &state.stopped {
            return Err(stop.clone());
        }
        state.concluded = true;
        Ok(())
    }

    /// `result`, unless a stop was recorded: a run Targo stopped (a signal, a
    /// bound) never exits 0, though the work under way when the stop came
    /// may have finished in the grace the clock's watcher gives it
    /// (`plan_clock`): a `--unit-graph-parity` check, a `--no-run` build or a
    /// run of nothing starts no job queue that would end it.
    pub(crate) fn ended(&self, result: crate::CliResult) -> crate::CliResult {
        match (result, self.stopped()) {
            (Ok(()), Some((_, why))) => {
                Err(crate::CliError::new(anyhow::anyhow!("{why}"), CANNOT_JUDGE))
            }
            (result, _) => result,
        }
    }
}

/// This invocation's ending.
static ENDING: Ending = Ending::new();

/// Says that Targo stopped the run, as `outcome` and for `why`: a bound that
/// ran out, or a signal. Whatever error the stop then surfaces as (a
/// cancelled build, a killed test), the invocation ends with this outcome
/// and this reason. Returns whether this stop is the run's: it is not when
/// an earlier stop is, or when the run already has its verdict.
pub(crate) fn stop(outcome: Outcome, why: String) -> bool {
    ENDING.stop(outcome, why)
}

/// How and why Targo stopped the run, if it did.
pub fn stopped() -> Option<(Outcome, String)> {
    ENDING.stopped()
}

/// Says that the run has its verdict, before its record is written; from
/// here no stop is the run's. Refused with the stop when one came first.
pub(crate) fn conclude() -> Result<(), (Outcome, String)> {
    ENDING.conclude()
}

/// The plan invocation's result, held to the stop if there was one
/// (`Ending::ended`).
pub fn ended(result: crate::CliResult) -> crate::CliResult {
    ENDING.ended(result)
}

/// Set once the invocation's `test-plan-result` record is written.
static CLOSED: AtomicBool = AtomicBool::new(false);

/// Says that the closing record has been written, by the run's own verdict.
pub(crate) fn closed() {
    CLOSED.store(true, Ordering::Release);
}

pub const TEST_PLAN_RESULT_SCHEMA_V1: &str = "targo.test-plan-result.v1";

/// The closing record of a run that ended without a verdict of its own: a
/// refusal, a failed build, a phase the invocation ended in.
#[derive(Debug, Serialize)]
struct Closing<'a> {
    schema: &'static str,
    plan: &'a str,
    phase: Option<&'a str>,
    passed: bool,
    outcome: Outcome,
    exit_status: i32,
    /// The first line of the error that ended the run.
    why: &'a str,
}

impl Message for Closing<'_> {
    fn reason(&self) -> &str {
        "test-plan-result"
    }
}

/// Ends a plan invocation that failed with `status`: with JSON messages,
/// writes the closing record unless the run's verdict already wrote it.
/// Every plan invocation's JSON then ends in one `test-plan-result`, and a
/// stream without one was cut off.
pub fn close(
    gctx: &GlobalContext,
    json: bool,
    plan: &str,
    outcome: Outcome,
    error: Option<&anyhow::Error>,
) {
    if !json || CLOSED.swap(true, Ordering::AcqRel) {
        return;
    }
    // A run Targo stopped says why it stopped, not what the stop broke.
    let stopped = stopped().map(|(_, why)| why);
    let why = stopped.or_else(|| error.map(|error| {
        // Each cause's first line, outermost first; the marker's own line
        // says only the status.
        error
            .chain()
            .map(|cause| cause.to_string())
            .filter(|line| {
                !line.starts_with("cannot judge (exit status")
                    && !line.starts_with("out of time (exit status")
                    && !line.starts_with("interrupted (exit status")
            })
            .filter_map(|cause| cause.lines().next().map(str::to_owned))
            .collect::<Vec<_>>()
            .join(": ")
    }));
    // An error with no message is a test or a build that failed and said so
    // itself, in a run that stopped there.
    let why = why
        .as_deref()
        .unwrap_or("the run stopped at a failure that its own output reports");
    let _ = writeln!(gctx.shell().out(), "{}", closing_line(plan, outcome, why));
}

/// The closing record of a run that ended as `outcome`, for `why`.
fn closing_line(plan: &str, outcome: Outcome, why: &str) -> String {
    Closing {
        schema: TEST_PLAN_RESULT_SCHEMA_V1,
        plan,
        phase: None,
        passed: false,
        outcome,
        exit_status: outcome.exit_status(),
        why,
    }
    .to_json_string()
}

/// The closing record of a run its clock's watcher ends because no job
/// queue is left to end it (`plan_clock`): the stop's own outcome and why,
/// unless the run's record was already written.
pub(crate) fn closing_of_stopped(plan: &str) -> Option<String> {
    let (outcome, why) = stopped()?;
    if CLOSED.swap(true, Ordering::AcqRel) {
        return None;
    }
    Some(closing_line(plan, outcome, &why))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_mark_survives_the_context_added_above_it() {
        let refused = cannot_judge(anyhow::anyhow!("the plan names no member"));
        assert_eq!(marked(&refused), Some(Outcome::CannotJudge));
        let wrapped = refused.context("workspace `own/Cargo.toml`");
        assert_eq!(marked(&wrapped), Some(Outcome::CannotJudge));
        // Marked once, however often it is asked for.
        let twice = cannot_judge(wrapped);
        assert_eq!(
            twice
                .chain()
                .filter(|cause| cause.to_string().starts_with("cannot judge"))
                .count(),
            1
        );
        assert_eq!(marked(&anyhow::anyhow!("a test failed")), None);
        // A run stopped for time is out of time, whatever else it was.
        let late = cannot_judge(anyhow::anyhow!("stalled").context(OutOfTime));
        assert_eq!(marked(&late), Some(Outcome::OutOfTime));
    }

    #[test]
    fn a_run_has_one_ending_a_stop_or_its_verdict() {
        // A stop, then the work finishes: no verdict, and never exit 0.
        let ending = Ending::new();
        assert!(ending.stop(Outcome::Interrupted, "signal 15 stopped the run".into()));
        assert!(!ending.stop(Outcome::OutOfTime, "a later stop".into()));
        assert_eq!(
            ending.conclude(),
            Err((Outcome::Interrupted, "signal 15 stopped the run".into()))
        );
        let error = ending.ended(Ok(())).unwrap_err();
        assert_eq!(error.exit_code, CANNOT_JUDGE);
        assert_eq!(
            error.error.unwrap().to_string(),
            "signal 15 stopped the run"
        );
        // An error the run raised stays its own.
        let raised = ending.ended(Err(crate::CliError::code(101))).unwrap_err();
        assert_eq!(raised.exit_code, 101);

        // The verdict, then a signal: the run was over, and the stop is not its.
        let ending = Ending::new();
        assert_eq!(ending.conclude(), Ok(()));
        assert!(!ending.stop(Outcome::Interrupted, "signal 2 stopped the run".into()));
        assert_eq!(ending.stopped(), None);
        assert!(ending.ended(Ok(())).is_ok());
    }

    #[test]
    fn each_outcome_has_one_status_and_only_a_pass_is_0() {
        let all = [
            (Outcome::Passed, 0),
            (Outcome::NothingSelected, 0),
            (Outcome::Failed, 101),
            (Outcome::CannotJudge, 2),
            (Outcome::Interrupted, 2),
            (Outcome::OutOfTime, 3),
        ];
        for (outcome, status) in all {
            assert_eq!(outcome.exit_status(), status);
        }
        assert_eq!(
            serde_json::to_string(&Outcome::NothingSelected).unwrap(),
            "\"nothing-selected\""
        );
    }
}
