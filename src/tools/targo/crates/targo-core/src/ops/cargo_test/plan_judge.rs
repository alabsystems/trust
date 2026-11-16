//! Trust: what a `targo test --plan` run judged, beyond each harness's exit.
//!
//! A harness that exits 0 has not shown that it judged anything: libtest
//! exits 0 on `running 0 tests`, and a process may exit 0 before libtest
//! closes its run. A plan run therefore reads each harness's closing
//! `test result:` line and holds it to the exit, counts what the harness
//! reported, and asks of the whole run what the plan asks:
//!
//! * each member of `[default]` reports at least `min-tests` tests over the
//!   default run and its variants;
//! * each variant reports a test;
//! * each test an instrument's `require-pass` names printed
//!   `test <name> ... ok` in one of that instrument's actions;
//! * with `[expect] known-red`, each failure is of a test that file lists,
//!   and no test it lists passed (`plan_expect`);
//! * no `[[workspace]]` phase of the run failed (`plan_phases`).
//!
//! Stdout is shared: a test that writes past libtest's capture, or a child
//! process it starts, prints there too. A closing line therefore stands only
//! as the close of the run the harness announced (`running N tests`, N tests
//! accounted for, nothing printed after it), and a watched name's `ok` line
//! only where the `ok` lines number what the closing line says passed and
//! the name printed no other result. This catches output that is not
//! libtest's own by its disagreement with libtest's; it is not proof against
//! test code written to forge all of it consistently.
//!
//! A reported test is one libtest counted as passed or failed. An ignored or
//! filtered-out test judged nothing. A target with `harness = false` prints
//! no summary: it counts as one test, whose verdict is its exit.

use std::collections::{BTreeMap, BTreeSet};
use std::sync::{Arc, Mutex};

use cargo_util::ProcessError;
use serde::Serialize;

use super::plan::{RequestRole, ResolvedPlan};
use super::plan_expect::KnownRedResult;
use crate::util::CargoResult;
use crate::util::machine_message::{Message, TestCounts};

pub use super::plan_outcome::TEST_PLAN_RESULT_SCHEMA_V1;
use super::plan_outcome::Outcome;

/// A harness's closing `test result:` line: the last one it printed.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Closing {
    /// `ok`, as opposed to `FAILED`.
    pub ok: bool,
    /// Its numbers, when the line is complete and agrees with its own word:
    /// an `ok` line counts no failure.
    pub counts: Option<TestCounts>,
    /// Its `measured` number, which with passed, failed and ignored makes up
    /// the tests the run announced; 0 without `counts`.
    pub measured: u64,
}

impl Closing {
    /// A closing line that said `ok` or `FAILED` and parsed as `numbers`:
    /// its counts and its `measured`.
    pub(crate) fn new(ok: bool, numbers: Option<(TestCounts, u64)>) -> Closing {
        // An `ok` line that counts a failure contradicts itself.
        let numbers = numbers.filter(|(counts, _)| !ok || counts.failed == 0);
        Closing {
            ok,
            counts: numbers.map(|(counts, _)| counts),
            measured: numbers.map_or(0, |(_, measured)| measured),
        }
    }
}

/// What a plan reads of one harness's stdout, line by line.
#[derive(Clone, Debug, Default)]
pub(crate) struct Reading {
    watched: Vec<String>,
    /// N of the first `running N tests` line: the run libtest announced.
    announced: Option<u64>,
    closing: Option<Closing>,
    /// A line that is not blank followed the last closing line.
    trailing: bool,
    /// The `test <name> ... ok` lines printed, whatever their names.
    ok_lines: u64,
    watched_ok: BTreeSet<String>,
    /// The watched names that printed a result other than `ok`.
    contradicted: BTreeSet<String>,
    /// The `test <name> ... FAILED` lines printed, and their names.
    failed_lines: u64,
    failed: BTreeSet<String>,
}

impl Reading {
    /// Also records the result lines of each of `names`.
    pub(crate) fn watching(names: &[String]) -> Reading {
        Reading {
            watched: names.to_vec(),
            ..Reading::default()
        }
    }

    /// The last closing line printed, as read.
    pub(crate) fn closing(&self) -> Option<Closing> {
        self.closing
    }

    /// Reads a `test result:` line.
    pub(crate) fn close(&mut self, closing: Closing) {
        self.closing = Some(closing);
        self.trailing = false;
    }

    /// Reads any other stdout line.
    pub(crate) fn line(&mut self, line: &str) {
        if line.trim().is_empty() {
            return;
        }
        self.trailing = self.closing.is_some();
        let announced = line
            .strip_prefix("running ")
            .and_then(|rest| {
                rest.strip_suffix(" tests")
                    .or_else(|| rest.strip_suffix(" test"))
            })
            .filter(|number| !number.is_empty() && number.bytes().all(|b| b.is_ascii_digit()))
            .and_then(|number| number.parse::<u64>().ok());
        if let Some(announced) = announced {
            // The harness announces its run before any test can print.
            self.announced.get_or_insert(announced);
            return;
        }
        let Some((name, result)) = line
            .strip_prefix("test ")
            .and_then(|result| result.split_once(" ... "))
        else {
            return;
        };
        if result == "ok" {
            self.ok_lines += 1;
        }
        // libtest names a `#[should_panic]` test `<name> - should panic`.
        let name = name.strip_suffix(" - should panic").unwrap_or(name);
        if result == "FAILED" {
            self.failed_lines += 1;
            self.failed.insert(name.to_owned());
        }
        if self.watched.iter().any(|watched| watched == name) {
            if result == "ok" {
                self.watched_ok.insert(name.to_owned());
            } else {
                self.contradicted.insert(name.to_owned());
            }
        }
    }

    /// The closing line's counts, or why the line does not close the run the
    /// harness announced. `None` without a closing line that has counts.
    fn closed(&self) -> Option<Result<TestCounts, String>> {
        let closing = self.closing?;
        let counts = closing.counts?;
        let accounted = counts.passed + counts.failed + counts.ignored + closing.measured;
        let stray = match self.announced {
            None => Some("no `running N tests` line came before it".to_owned()),
            Some(announced) if announced != accounted => Some(format!(
                "it accounts for {accounted} test{} and the harness announced `running \
                 {announced} test{}`",
                if accounted == 1 { "" } else { "s" },
                if announced == 1 { "" } else { "s" },
            )),
            Some(_) if self.trailing => Some("output follows it".to_owned()),
            Some(_) => None,
        };
        Some(stray.map_or(Ok(counts), Err))
    }

    /// The watched names that passed, the watched names that printed another
    /// result, and why no result line of this harness is read, if none is.
    fn names(&self) -> (BTreeSet<String>, BTreeSet<String>, Option<String>) {
        if self.watched.is_empty() {
            return Default::default();
        }
        let Some(Ok(counts)) = self.closed() else {
            // No closing line stands, so the action has failed.
            return Default::default();
        };
        if self.ok_lines != counts.passed {
            let void = format!(
                "the harness printed {} `test <name> ... ok` line{} and closed its run with {} \
                 passed, so its result lines are not read",
                self.ok_lines,
                if self.ok_lines == 1 { "" } else { "s" },
                counts.passed
            );
            return (BTreeSet::new(), BTreeSet::new(), Some(void));
        }
        let passed = self
            .watched_ok
            .difference(&self.contradicted)
            .cloned()
            .collect();
        (passed, self.contradicted.clone(), None)
    }
}

impl Reading {
    /// The tests libtest reported failed, where its report is its own: it
    /// closed the run it announced as failed, and printed one `FAILED` line
    /// per failure and one `ok` line per pass that its closing line counts,
    /// each `FAILED` line for a test of its own name. `None` otherwise: a
    /// harness that ended any other way names no failed test.
    fn failures(&self) -> Result<BTreeSet<String>, String> {
        // A closing line that counts a failure is a `FAILED` one: an `ok`
        // line that counts one has no counts (`Closing::new`).
        let counts = match self.closed() {
            None => {
                return Err(
                    "the harness printed no complete closing `test result:` line, so libtest \
                     did not report its failed tests"
                        .to_owned(),
                );
            }
            Some(Err(stray)) => {
                return Err(format!(
                    "the harness's closing `test result:` line does not close its own run: \
                     {stray}"
                ));
            }
            Some(Ok(counts)) => counts,
        };
        if counts.failed == 0 {
            return Err(
                "the harness's closing `test result:` line counts no failed test".to_owned(),
            );
        }
        let own = self.failed_lines == counts.failed
            && self.failed.len() as u64 == counts.failed
            && self.ok_lines == counts.passed;
        if !own {
            return Err(format!(
                "the harness printed {} `test <name> ... FAILED` line{} naming {} test{} and {} \
                 `test <name> ... ok` line{}, and closed its run with {} failed and {} passed, \
                 so its result lines are not read",
                self.failed_lines,
                if self.failed_lines == 1 { "" } else { "s" },
                self.failed.len(),
                if self.failed.len() == 1 { "" } else { "s" },
                self.ok_lines,
                if self.ok_lines == 1 { "" } else { "s" },
                counts.failed,
                counts.passed
            ));
        }
        Ok(self.failed.clone())
    }
}

/// What one finished action showed.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct Observed {
    /// The tests it reported, where its exit and its closing line agree.
    pub tests: Option<TestCounts>,
    /// The watched names it printed `test <name> ... ok` for, and nothing
    /// else.
    pub passed: BTreeSet<String>,
    /// The watched names it printed some other result for.
    pub contradicted: BTreeSet<String>,
    /// Why none of its result lines is read, if none is.
    pub void: Option<String>,
    /// The tests it reported failed, where it failed by libtest's own
    /// report: it exited with a code after `Reading::failures` read one.
    /// `None` for an action that passed or that failed any other way.
    pub failed: Option<BTreeSet<String>>,
    /// For an action that failed with `failed` unset: why it names no
    /// failed test.
    pub unreported: Option<String>,
}

/// What a plan action's worker watches its harness for, and where it leaves
/// what it saw for the coordinator.
#[derive(Clone, Debug)]
pub(crate) struct Watch {
    harness: bool,
    names: Vec<String>,
    slot: Arc<Mutex<Option<Observed>>>,
    /// When the harness last printed a line, for the run's stall bound.
    progress: super::plan_clock::Progress,
}

impl Watch {
    pub(crate) fn new(harness: bool, names: Vec<String>) -> Watch {
        Watch {
            harness,
            names,
            slot: Arc::default(),
            progress: Default::default(),
        }
    }

    /// When the harness last printed a line: the worker touches it on
    /// each, and the queue reads it against the plan's stall bound.
    pub(crate) fn progress(&self) -> &super::plan_clock::Progress {
        &self.progress
    }

    /// The test names whose result lines the worker records.
    pub(crate) fn names(&self) -> &[String] {
        &self.names
    }

    /// Reads a finished harness: records what it reported and returns why
    /// its successful exit does not stand, if it does not.
    pub(crate) fn conclude<T>(&self, exit: &CargoResult<T>, reading: &Reading) -> Option<String> {
        let (tests, disagreement) = reported(self.harness, Exit::of(exit), reading);
        let (passed, contradicted, void) = reading.names();
        // A target with `harness = false` prints no result line to read, so
        // no watched name of it can be seen to pass.
        let void = void.or_else(|| {
            (!self.harness && !self.names.is_empty()).then(|| {
                "the target has `harness = false`, so it prints no result lines".to_owned()
            })
        });
        // libtest exits with a code when a test fails. A signal, or a
        // process Targo has no exit of, is not libtest reporting a failure.
        let exited = exit.as_ref().err().is_some_and(|error| {
            error
                .downcast_ref::<ProcessError>()
                .is_some_and(|process| process.code.is_some() && process.signal.is_none())
        });
        let (failed, unreported) = if exit.is_ok() {
            // Failed, if at all, by the disagreement of its exit 0, which
            // the action's own error states.
            (None, None)
        } else if !self.harness {
            let why = "the target has `harness = false`, so it names no failed test";
            (None, Some(why.to_owned()))
        } else if !exited {
            let why = "the harness did not exit with a code of its own (a signal ended it, or \
                       Targo has no exit of it), so libtest did not report its failed tests";
            (None, Some(why.to_owned()))
        } else {
            match reading.failures() {
                Ok(failed) => (Some(failed), None),
                Err(why) => (None, Some(why)),
            }
        };
        *self.slot.lock().unwrap() = Some(Observed {
            tests,
            passed,
            contradicted,
            void,
            failed,
            unreported,
        });
        disagreement
    }

    /// What the worker left, once.
    pub(crate) fn take(&self) -> Option<Observed> {
        self.slot.lock().unwrap().take()
    }
}

/// How a harness process ended.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Exit {
    /// It exited 0.
    Success,
    /// It exited by itself with another code, or a signal ended it.
    Failure,
    /// Targo has no exit of its own to read: it never started, or its output
    /// was rejected.
    Unknown,
}

impl Exit {
    fn of<T>(exit: &CargoResult<T>) -> Exit {
        match exit {
            Ok(_) => Exit::Success,
            // A process that could not be started is a `ProcessError` too,
            // one with neither an exit code nor a signal.
            Err(error)
                if error
                    .downcast_ref::<ProcessError>()
                    .is_some_and(|process| process.code.is_some() || process.signal.is_some()) =>
            {
                Exit::Failure
            }
            Err(_) => Exit::Unknown,
        }
    }
}

/// The tests a finished harness reported and, for one that exited 0, why
/// that exit is not a pass.
fn reported(harness: bool, exit: Exit, reading: &Reading) -> (Option<TestCounts>, Option<String>) {
    let one = |passed, failed| TestCounts {
        passed,
        failed,
        ignored: 0,
        filtered_out: 0,
    };
    if !harness {
        // No summary to read: one test, judged by the exit.
        return match exit {
            Exit::Success => (Some(one(1, 0)), None),
            Exit::Failure => (Some(one(0, 1)), None),
            Exit::Unknown => (None, None),
        };
    }
    let closing = reading.closing();
    let closed = reading.closed();
    match (exit, closing) {
        (Exit::Success, Some(Closing { ok: true, .. })) if matches!(closed, Some(Ok(_))) => {
            (closed.and_then(Result::ok), None)
        }
        (Exit::Success, closing) => {
            let saw = match (closing, closed) {
                (None, _) => {
                    "without libtest's closing `test result: ok.` line: it ended mid-run".to_owned()
                }
                (Some(Closing { ok: false, .. }), _) => {
                    "after a closing `test result: FAILED.` line".to_owned()
                }
                (Some(Closing { ok: true, .. }), Some(Err(stray))) => format!(
                    "with a closing `test result: ok.` line that does not close its own run: \
                     {stray}"
                ),
                (Some(Closing { ok: true, .. }), _) => "with a closing `test result: ok.` line \
                                                        that is incomplete or counts a failure"
                    .to_owned(),
            };
            (None, Some(format!("the test harness exited 0 {saw}")))
        }
        // The action fails by its exit. Its counts stand only where libtest
        // closed the run it announced as failed and counted a failure.
        (Exit::Failure, Some(Closing { ok: false, .. })) => match closed {
            Some(Ok(counts)) if counts.failed > 0 => (Some(counts), None),
            _ => (None, None),
        },
        (Exit::Failure | Exit::Unknown, _) => (None, None),
    }
}

impl ResolvedPlan {
    /// Whether the known-red file excuses the failed action `ran`: it failed
    /// only in tests the file lists.
    pub(crate) fn excuses(&self, ran: &Ran) -> bool {
        self.known_red
            .as_ref()
            .is_some_and(|known| known.judge(ran).excused)
    }

    /// Whether a finished run already reports why an action never ran: it
    /// was interrupted, or an action failed and fails the run. A failure the
    /// known-red file excuses fails nothing, so it explains nothing.
    pub(crate) fn explains_unrun(&self, interrupted: bool, ran: &[Ran]) -> bool {
        interrupted || ran.iter().any(|ran| ran.failed && !self.excuses(ran))
    }

    /// The watch for an action that runs the test binary `binary` for the
    /// requests `ids`: the tests their instruments require to pass, and the
    /// tests of that binary the known-red file lists, whose pass is a stale
    /// row.
    pub(crate) fn watch(&self, harness: bool, binary: &str, ids: &[String]) -> Watch {
        let names = self
            .plan
            .instrument
            .iter()
            .filter(|instrument| ids.contains(&instrument.id))
            .flat_map(|instrument| instrument.require_pass.iter().cloned())
            .chain(
                self.known_red
                    .iter()
                    .flat_map(|known| known.tests_of(binary).map(str::to_owned)),
            )
            .collect::<BTreeSet<_>>();
        Watch::new(harness, names.into_iter().collect())
    }
}

/// One finished action, as the plan's verdict reads it.
#[derive(Clone, Debug)]
pub(crate) struct Ran {
    pub package: String,
    /// The test binary as a known-red key names it: the target's crate name.
    pub binary: String,
    pub requests: Vec<String>,
    pub failed: bool,
    pub observed: Option<Observed>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub(crate) struct RequestResult {
    pub id: String,
    /// The actions that ran for this request, and how many of them failed.
    pub actions: usize,
    pub failed: usize,
    /// The failed actions that failed only in tests the known-red file
    /// lists; they do not fail the request.
    pub excused: usize,
    /// The tests those actions reported (passed + failed).
    pub tests: u64,
    pub passed: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub(crate) struct MemberResult {
    pub package: String,
    /// The tests the member's actions reported (passed + failed) over
    /// `[default]` and its variants.
    pub tests: u64,
    pub min_tests: u64,
    pub passed: bool,
}

/// The plan's verdict on a run that ran to its end.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Verdict {
    pub requests: Vec<RequestResult>,
    /// One row per member `min-tests` is judged for; empty when the plan
    /// sets none or `--request` left out part of a member's sum.
    pub members: Vec<MemberResult>,
    /// What the plan requires that the run did not show, beyond the failed
    /// actions themselves.
    pub unmet: Vec<String>,
    /// What the known-red file says of the run; `None` without one.
    pub known_red: Option<KnownRedResult>,
}

impl Verdict {
    pub(crate) fn of(plan: &ResolvedPlan, ran: &[Ran]) -> Verdict {
        let reported = |ran: &Ran| {
            ran.observed
                .as_ref()
                .and_then(|observed| observed.tests)
                .map_or(0, |tests| tests.passed + tests.failed)
        };
        let mut unmet = Vec::new();

        let mut members = Vec::new();
        if let Some(min_tests) = plan.min_tests() {
            // An instrument judges something outside its host, so only the
            // default run and the variants credit a member.
            let credits: BTreeSet<&str> = plan
                .requests
                .iter()
                .filter(|request| request.role != RequestRole::Instrument)
                .map(|request| request.id.as_str())
                .collect();
            let mut tests: BTreeMap<&str, u64> = plan
                .members
                .iter()
                .map(|member| (member.as_str(), 0))
                .collect();
            for ran in ran {
                if ran.requests.iter().any(|id| credits.contains(id.as_str()))
                    && let Some(total) = tests.get_mut(ran.package.as_str())
                {
                    *total += reported(ran);
                }
            }
            for (package, tests) in tests {
                let passed = tests >= min_tests;
                if !passed {
                    unmet.push(format!(
                        "member `{package}` reported {tests} test{} (passed + failed) over \
                         `[default]` and its variants; `min-tests` is {min_tests}. Its tests \
                         are behind a feature no request enables, behind a cfg this host does \
                         not satisfy, all ignored, or absent",
                        if tests == 1 { "" } else { "s" }
                    ));
                }
                members.push(MemberResult {
                    package: package.to_owned(),
                    tests,
                    min_tests,
                    passed,
                });
            }
        }

        let mut requests = Vec::new();
        for request in &plan.requests {
            let own = ran
                .iter()
                .filter(|ran| ran.requests.contains(&request.id))
                .collect::<Vec<_>>();
            let mut passed = true;
            let required = plan
                .plan
                .instrument
                .iter()
                .filter(|instrument| instrument.id == request.id)
                .flat_map(|instrument| &instrument.require_pass);
            let observed = || own.iter().filter_map(|ran| ran.observed.as_ref());
            for name in required {
                if observed().any(|observed| observed.passed.contains(name)) {
                    continue;
                }
                passed = false;
                let why = if observed().any(|observed| observed.contradicted.contains(name)) {
                    "a harness that printed it also printed another result for that test".to_owned()
                } else if let Some(void) = observed().find_map(|observed| observed.void.as_ref()) {
                    void.clone()
                } else {
                    "the test is ignored, filtered out, renamed, compiled out, or it failed"
                        .to_owned()
                };
                unmet.push(format!(
                    "instrument `{}` requires `{name}` to pass, and none of its test \
                     executables printed `test {name} ... ok`: {why}",
                    request.id
                ));
            }
            let failed = own.iter().filter(|ran| ran.failed).count();
            let excused = own.iter().filter(|ran| plan.excuses(ran)).count();
            let tests = own.iter().map(|ran| reported(ran)).sum();
            // A variant exists to run tests a feature set compiles in. One
            // whose executables all exit 0 on `running 0 tests` judged
            // nothing, and its member's `min-tests` may be met elsewhere.
            if request.role == RequestRole::Variant && failed == 0 && tests == 0 {
                passed = false;
                unmet.push(format!(
                    "variant `{}` reported no test (passed + failed): its tests are behind a \
                     feature it does not enable, behind a cfg this host does not satisfy, all \
                     ignored, filtered out, or absent",
                    request.id
                ));
            }
            requests.push(RequestResult {
                id: request.id.clone(),
                actions: own.len(),
                failed,
                excused,
                tests,
                passed: passed && failed == excused,
            });
        }
        let known_red = plan.known_red.as_ref().map(|known| known.result(ran));
        for unjudged in known_red.iter().flat_map(|result| &result.unjudged) {
            // A failed harness fails by its action; one that passed with
            // rows nobody could check has not shown the rows are in force.
            if !unjudged.failed {
                unmet.push(unjudged.unmet(known_red.as_ref().map_or("", |result| &result.file)));
            }
        }
        // A `[[workspace]]` phase that failed fails the plan's run.
        unmet.extend(plan.phases.iter().filter_map(|row| row.unmet()));
        for key in known_red.iter().flat_map(|result| &result.stale) {
            unmet.push(format!(
                "known-red row `{key}` is stale: the test passed. Delete the row from `{}`, or \
                 mark it `[flaky]` if the test may pass or fail",
                known_red.as_ref().map_or("", |result| &result.file)
            ));
        }
        Verdict {
            requests,
            members,
            unmet,
            known_red,
        }
    }

    /// Nothing failed and nothing the plan requires is missing.
    pub(crate) fn passed(&self) -> bool {
        self.unmet.is_empty() && self.requests.iter().all(|request| request.passed)
    }

    /// How a run that ran to its end ended (`plan_outcome`). Red is a
    /// failure the known-red file does not excuse, a failed phase, or a
    /// stale known-red row: something was judged and is wrong. Anything else
    /// the plan requires and the run did not show (a member under
    /// `min-tests`, a `require-pass` test that did not run, a variant or
    /// instrument that judged nothing, known-red rows nobody could check)
    /// is no failed test: the run could not judge.
    pub(crate) fn outcome(&self, plan: &ResolvedPlan) -> Outcome {
        use super::plan_phases::PhaseState;
        let red = self
            .requests
            .iter()
            .any(|request| request.failed != request.excused)
            || plan.phases.iter().any(|row| row.state == PhaseState::Failed)
            || self
                .known_red
                .as_ref()
                .is_some_and(|result| !result.stale.is_empty());
        if red {
            Outcome::Failed
        } else if !self.passed() {
            Outcome::CannotJudge
        } else if plan.requests.is_empty()
            && !plan.phases.iter().any(|row| {
                matches!(
                    row.state,
                    PhaseState::Built | PhaseState::Passed | PhaseState::Started
                )
            })
        {
            Outcome::NothingSelected
        } else {
            Outcome::Passed
        }
    }

    /// The error for what the plan requires and the run did not show.
    pub(crate) fn refusal(&self, plan: &ResolvedPlan) -> Option<String> {
        if self.unmet.is_empty() {
            return None;
        }
        Some(format!(
            "test plan `{}`: {} requirement{} not met:\n    {}",
            plan.path.display(),
            self.unmet.len(),
            if self.unmet.len() == 1 { "" } else { "s" },
            self.unmet.join("\n    ")
        ))
    }

    /// The `test-plan-result` record: the last line of a plan run's JSON.
    pub(crate) fn record(&self, plan: &ResolvedPlan) -> String {
        let outcome = self.outcome(plan);
        if plan.phase.is_none() {
            super::plan_outcome::closed();
        }
        TestPlanResult {
            schema: TEST_PLAN_RESULT_SCHEMA_V1,
            plan: plan.path.to_string_lossy().into_owned(),
            phase: plan.phase.as_ref().map(|phase| phase.manifest.as_str()),
            passed: self.passed(),
            outcome,
            exit_status: outcome.exit_status(),
            narrowed: plan.narrowed,
            min_tests_skipped: plan.min_tests_set() && plan.min_tests().is_none(),
            requests: &self.requests,
            members: &self.members,
            unmet: &self.unmet,
            known_red: self.known_red.as_ref(),
            phases: &plan.phases,
        }
        .to_json_string()
    }
}

/// What a plan run concluded. Written once, after every action's terminal
/// record, and only by a run that ran to its end: one that was interrupted
/// or stopped at its first failure has no verdict.
#[derive(Debug, Serialize)]
struct TestPlanResult<'a> {
    schema: &'static str,
    plan: String,
    /// The `[[workspace]]` manifest this is the verdict of, in the
    /// `test-plan-phase-result` record of one phase's run; `null` in the
    /// plan's own verdict, which is the last record and counts every phase.
    phase: Option<&'a str>,
    passed: bool,
    /// How the run ended, and the exit status that says the same
    /// (`plan_outcome`): `passed` and `nothing-selected` are 0, `failed` is
    /// 101, `cannot-judge` is 2.
    outcome: Outcome,
    exit_status: i32,
    /// `--request` left out some request the selection performs: this is
    /// not the verdict of that selection.
    narrowed: bool,
    /// The plan sets `min-tests` and this run did not judge it.
    min_tests_skipped: bool,
    requests: &'a [RequestResult],
    members: &'a [MemberResult],
    unmet: &'a [String],
    /// The `[expect] known-red` file's verdict: the listed tests that failed
    /// in an excused harness (`excused`) or in one that was not
    /// (`not_excused`), the failed tests it does not list (`new_failures`),
    /// its rows whose test passed (`stale`) and the binaries with rows whose
    /// result lines were not read (`unjudged`). `null` when the plan names
    /// no file.
    known_red: Option<&'a KnownRedResult>,
    /// What became of each `[[tool]]` and `[[workspace]]` entry in this
    /// run; empty in a phase's own record.
    phases: &'a [super::plan_phases::PhaseRow],
}

impl Message for TestPlanResult<'_> {
    fn reason(&self) -> &str {
        // `test-plan-result` stays the one last record of an invocation; a
        // phase's verdict has the same shape under a name of its own.
        if self.phase.is_some() {
            "test-plan-phase-result"
        } else {
            "test-plan-result"
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn counts(passed: u64, failed: u64, ignored: u64, filtered_out: u64) -> TestCounts {
        TestCounts {
            passed,
            failed,
            ignored,
            filtered_out,
        }
    }

    /// A harness that announced `announced` tests (if any) and printed
    /// `closing` last (if any).
    fn reading(announced: Option<u64>, closing: Option<Closing>) -> Reading {
        run(announced, &[], closing)
    }

    /// The same, with `lines` between the two and `m::one` and `m::slow`
    /// watched.
    fn run(announced: Option<u64>, lines: &[&str], closing: Option<Closing>) -> Reading {
        let mut reading = Reading::watching(&["m::one".to_owned(), "m::slow".to_owned()]);
        if let Some(announced) = announced {
            reading.line(&format!(
                "running {announced} test{}",
                if announced == 1 { "" } else { "s" }
            ));
        }
        for line in lines {
            reading.line(line);
        }
        if let Some(closing) = closing {
            reading.close(closing);
        }
        reading
    }

    fn closing(ok: bool, counts: Option<TestCounts>) -> Option<Closing> {
        Some(Closing::new(ok, counts.map(|counts| (counts, 0))))
    }

    #[test]
    fn a_harness_is_held_to_its_closing_line() {
        let three = counts(3, 0, 1, 2);
        assert_eq!(
            reported(
                true,
                Exit::Success,
                &reading(Some(4), closing(true, Some(three)))
            ),
            (Some(three), None)
        );
        // Exit 0 stands only on a complete `ok` line.
        for (closing, saw) in [
            (None, "ended mid-run"),
            (closing(false, Some(counts(1, 1, 0, 0))), "FAILED"),
            (closing(true, None), "incomplete"),
            // An `ok` line that counts a failure has no counts.
            (closing(true, Some(counts(1, 1, 0, 0))), "incomplete"),
        ] {
            let (tests, disagreement) = reported(true, Exit::Success, &reading(Some(2), closing));
            assert_eq!(tests, None, "{closing:?}");
            assert!(disagreement.unwrap().contains(saw), "{closing:?}");
        }
        // A failed exit fails by itself; its counts stand only on a closing
        // FAILED line that counts a failure.
        let failed = counts(2, 1, 0, 0);
        assert_eq!(
            reported(
                true,
                Exit::Failure,
                &reading(Some(3), closing(false, Some(failed)))
            ),
            (Some(failed), None)
        );
        for (announced, closing) in [
            (3, None),
            (4, closing(true, Some(three))),
            (3, closing(false, None)),
            (2, closing(false, Some(counts(2, 0, 0, 0)))),
            // Not the close of the run it announced.
            (9, closing(false, Some(failed))),
        ] {
            assert_eq!(
                reported(true, Exit::Failure, &reading(Some(announced), closing)),
                (None, None)
            );
        }
        assert_eq!(
            reported(
                true,
                Exit::Unknown,
                &reading(Some(4), closing(true, Some(three)))
            ),
            (None, None)
        );
    }

    /// Stdout is shared with whatever the tests start or write past libtest's
    /// capture: an `ok` line stands only as the close of the announced run.
    #[test]
    fn a_closing_line_stands_only_for_the_run_the_harness_announced() {
        let seven = closing(true, Some(counts(7, 0, 0, 0)));
        // The harness announced two tests; a line counting seven is not its.
        let (tests, disagreement) = reported(true, Exit::Success, &reading(Some(2), seven));
        assert_eq!(tests, None);
        assert_eq!(
            disagreement.unwrap(),
            "the test harness exited 0 with a closing `test result: ok.` line that does not \
             close its own run: it accounts for 7 tests and the harness announced `running 2 \
             tests`"
        );
        // Filtered-out tests were never announced; measured ones were.
        let measured = Some(Closing::new(true, Some((counts(1, 0, 1, 5), 2))));
        assert_eq!(
            reported(true, Exit::Success, &reading(Some(4), measured)),
            (Some(counts(1, 0, 1, 5)), None)
        );
        // No announcement at all.
        let (tests, disagreement) = reported(true, Exit::Success, &reading(None, seven));
        assert_eq!(tests, None);
        assert!(
            disagreement
                .unwrap()
                .ends_with("no `running N tests` line came before it")
        );
        // The first announcement is the harness's own; a later one is a
        // child's.
        let mut nested = reading(Some(7), None);
        nested.line("running 2 tests");
        nested.close(seven.unwrap());
        assert_eq!(
            reported(true, Exit::Success, &nested),
            (Some(counts(7, 0, 0, 0)), None)
        );
        // libtest prints nothing after its closing line but blank lines.
        let mut closed = reading(Some(7), seven);
        closed.line("");
        closed.line("  ");
        assert_eq!(
            reported(true, Exit::Success, &closed),
            (Some(counts(7, 0, 0, 0)), None)
        );
        closed.line("test z ... ok");
        let (tests, disagreement) = reported(true, Exit::Success, &closed);
        assert_eq!(tests, None);
        assert!(disagreement.unwrap().ends_with("output follows it"));
        // A closing line after that output is the last one again.
        closed.close(seven.unwrap());
        assert_eq!(
            reported(true, Exit::Success, &closed),
            (Some(counts(7, 0, 0, 0)), None)
        );
    }

    #[test]
    fn a_watched_test_passed_only_on_its_own_ok_line() {
        let ok = |passed, ignored| closing(true, Some(counts(passed, 0, ignored, 2)));
        let names = |reading: &Reading| {
            let (passed, contradicted, void) = reading.names();
            (
                passed.into_iter().collect::<Vec<_>>(),
                contradicted.into_iter().collect::<Vec<_>>(),
                void,
            )
        };
        let none = Vec::<String>::new();
        let reading = run(
            Some(3),
            &[
                "test m::one ... ok",
                "test m::slow ... ignored",
                "test m::other ... ok",
            ],
            ok(2, 1),
        );
        assert_eq!(
            names(&reading),
            (vec!["m::one".to_owned()], vec!["m::slow".to_owned()], None)
        );
        // Each line alone in a run that adds up: none of them passes
        // `m::one`.
        for (line, passed) in [
            ("test m::one ... FAILED", 0),
            ("test m::one ... ignored, slow", 0),
            ("test m::one_more ... ok", 1),
            ("test x::m::one ... ok", 1),
            (" test m::one ... ok", 0),
            ("test m::one ... ok ", 0),
        ] {
            let closing = closing(passed == 1, Some(counts(passed, 1 - passed, 0, 0)));
            let (passed, _, void) = names(&run(Some(1), &[line], closing));
            assert_eq!((passed, void), (none.clone(), None), "{line}");
        }
        // libtest names a `#[should_panic]` test with a suffix.
        let reading = run(Some(1), &["test m::one - should panic ... ok"], ok(1, 0));
        assert_eq!(
            names(&reading),
            (vec!["m::one".to_owned()], none.clone(), None)
        );
        let reading = run(
            Some(1),
            &["test m::one - should panic ... FAILED"],
            closing(false, Some(counts(0, 1, 0, 0))),
        );
        assert_eq!(
            names(&reading),
            (none.clone(), vec!["m::one".to_owned()], None)
        );
    }

    /// A line of a result line's text is not always libtest's: a test may
    /// write one past the capture.
    #[test]
    fn a_result_line_libtest_did_not_print_passes_no_watched_test() {
        let ok = |passed, ignored| closing(true, Some(counts(passed, 0, ignored, 0)));
        // `m::slow` is ignored, and something printed that it passed: the
        // harness counted one pass and two `ok` lines were printed.
        let forged = run(
            Some(2),
            &[
                "test m::slow ... ignored",
                "test m::slow ... ok",
                "test m::one ... ok",
            ],
            ok(1, 1),
        );
        let (passed, contradicted, void) = forged.names();
        assert!(passed.is_empty() && contradicted.is_empty());
        assert_eq!(
            void.unwrap(),
            "the harness printed 2 `test <name> ... ok` lines and closed its run with 1 passed, \
             so its result lines are not read"
        );
        // Where the numbers happen to agree (the forging test's own line is
        // split around its output), the two results for one name still
        // contradict each other, in either order.
        for lines in [
            ["test m::slow ... ignored", "test m::slow ... ok"],
            ["test m::slow ... ok", "test m::slow ... ignored"],
        ] {
            let (passed, contradicted, void) = run(Some(2), &lines, ok(1, 1)).names();
            assert!(passed.is_empty(), "{lines:?}");
            assert_eq!(contradicted.into_iter().collect::<Vec<_>>(), ["m::slow"]);
            assert_eq!(void, None);
        }
        // A harness that prints no result lines (`--quiet`) shows no name.
        let quiet = run(Some(2), &[], ok(2, 0));
        assert!(
            quiet
                .names()
                .2
                .unwrap()
                .contains("printed 0 `test <name> ... ok` lines")
        );
        // Without a closing line that stands the action has failed.
        let open = run(Some(2), &["test m::one ... ok"], None);
        assert_eq!(open.names(), Default::default());
        // Nothing watched, nothing to say.
        let mut unwatched = Reading::default();
        unwatched.line("running 1 test");
        unwatched.close(ok(1, 0).unwrap());
        assert_eq!(unwatched.names(), Default::default());
    }

    #[test]
    fn an_unharnessed_target_counts_one_test_judged_by_its_exit() {
        let nothing = reading(None, None);
        assert_eq!(
            reported(false, Exit::Success, &nothing),
            (Some(counts(1, 0, 0, 0)), None)
        );
        assert_eq!(
            reported(false, Exit::Failure, &nothing),
            (Some(counts(0, 1, 0, 0)), None)
        );
        assert_eq!(reported(false, Exit::Unknown, &nothing), (None, None));
        // Whatever it printed is not a libtest summary.
        assert_eq!(
            reported(false, Exit::Success, &reading(None, closing(false, None))),
            (Some(counts(1, 0, 0, 0)), None)
        );
    }

    /// A process that never started has no exit: it is not a failed test.
    #[test]
    fn only_a_process_that_ended_has_an_exit() {
        let ended = |code, signal| -> CargoResult<()> {
            // What a spawn failure returns, then with an exit of its own.
            let mut error = ProcessError::could_not_execute("harness");
            error.code = code;
            error.signal = signal;
            Err(error.into())
        };
        assert_eq!(Exit::of(&Ok(())), Exit::Success);
        assert_eq!(Exit::of(&ended(Some(3), None)), Exit::Failure);
        assert_eq!(Exit::of(&ended(None, Some(9))), Exit::Failure);
        assert_eq!(Exit::of(&ended(None, None)), Exit::Unknown);
        let other: CargoResult<()> = Err(anyhow::anyhow!("output rejected"));
        assert_eq!(Exit::of(&other), Exit::Unknown);
        // So an unharnessed target that could not be spawned reports nothing.
        let watch = Watch::new(false, Vec::new());
        assert_eq!(
            watch.conclude(&ended(None, None), &Reading::default()),
            None
        );
        assert_eq!(watch.take().unwrap().tests, None);
    }

    #[test]
    fn a_watch_hands_the_coordinator_what_the_worker_saw_once() {
        let watch = Watch::new(true, vec!["m::one".to_owned()]);
        assert_eq!(watch.take(), None);
        let exit: CargoResult<()> = Ok(());
        // Exit 0 mid-run: no closing line, so no result line is read either.
        let open = run(Some(1), &["test m::one ... ok"], None);
        assert_eq!(watch.conclude(&exit, &open).is_some(), true);
        assert_eq!(watch.take(), Some(Observed::default()));
        assert_eq!(watch.take(), None);
        let closed = run(
            Some(1),
            &["test m::one ... ok"],
            closing(true, Some(counts(1, 0, 0, 0))),
        );
        assert_eq!(watch.conclude(&exit, &closed), None);
        assert_eq!(
            watch.take(),
            Some(Observed {
                tests: Some(counts(1, 0, 0, 0)),
                passed: BTreeSet::from(["m::one".to_owned()]),
                ..Observed::default()
            })
        );
        assert_eq!(watch.take(), None);
    }

    const PLAN: &str = r#"
schema = "targo.test-plan.v1"
[select]
members = "default-members"
[default]
targets = "tests"
min-tests = 2
[[variant]]
id = "v"
package = "a"
lib = true
[[instrument]]
id = "i"
package = "a"
lib = true
require-pass = ["m::one", "m::two"]
[[instrument]]
id = "j"
package = "b"
lib = true
"#;

    fn plan() -> ResolvedPlan {
        ResolvedPlan::unbound(
            "p.toml",
            PLAN,
            &[
                ("default", RequestRole::Default),
                ("v", RequestRole::Variant),
                ("i", RequestRole::Instrument),
                ("j", RequestRole::Instrument),
            ],
            &["a", "b"],
        )
    }

    fn ran(package: &str, requests: &[&str], tests: Option<TestCounts>, passed: &[&str]) -> Ran {
        Ran {
            package: package.to_owned(),
            binary: package.to_owned(),
            requests: requests.iter().map(|id| (*id).to_owned()).collect(),
            failed: false,
            observed: Some(Observed {
                tests,
                passed: passed.iter().map(|name| (*name).to_owned()).collect(),
                ..Observed::default()
            }),
        }
    }

    #[test]
    fn a_watch_names_what_its_requests_instruments_require() {
        let plan = plan();
        let ids = |ids: &[&str]| ids.iter().map(|id| (*id).to_owned()).collect::<Vec<_>>();
        assert_eq!(
            plan.watch(true, "a", &ids(&["default", "i"])).names(),
            ["m::one", "m::two"]
        );
        assert!(
            plan.watch(true, "a", &ids(&["default", "v", "j"]))
                .names()
                .is_empty()
        );
    }

    #[test]
    fn min_tests_sums_a_members_default_run_and_variants_and_no_instrument() {
        let mut plan = plan();
        let all = [
            // Ignored and filtered-out tests judged nothing.
            ran("a", &["default"], Some(counts(1, 0, 5, 7)), &[]),
            ran("a", &["v"], Some(counts(0, 1, 0, 0)), &[]),
            // An instrument's own action credits nobody; one it shares with
            // the default run is the default run's.
            ran("b", &["j"], Some(counts(9, 0, 0, 0)), &[]),
            ran("b", &["default", "j"], Some(counts(1, 0, 0, 0)), &[]),
            // A run with no count that stands counts nothing.
            ran("b", &["default"], None, &[]),
            // Not a member of `[default]`.
            ran("c", &["default"], Some(counts(4, 0, 0, 0)), &[]),
            ran("a", &["i"], Some(counts(2, 0, 0, 0)), &["m::one", "m::two"]),
        ];
        let verdict = Verdict::of(&plan, &all);
        let member = |package: &str, tests, passed| MemberResult {
            package: package.to_owned(),
            tests,
            min_tests: 2,
            passed,
        };
        assert_eq!(
            verdict.members,
            [member("a", 2, true), member("b", 1, false)]
        );
        assert_eq!(verdict.unmet.len(), 1, "{:?}", verdict.unmet);
        assert!(
            verdict.unmet[0].starts_with(
                "member `b` reported 1 test (passed + failed) over `[default]` and its \
                 variants; `min-tests` is 2."
            ),
            "{}",
            verdict.unmet[0]
        );
        assert!(!verdict.passed());
        let refusal = verdict.refusal(&plan).unwrap();
        assert!(
            refusal.starts_with("test plan `p.toml`: 1 requirement not met:\n    member `b`"),
            "{refusal}"
        );
        // Every request passed: the member's shortfall is the plan's.
        assert!(verdict.requests.iter().all(|request| request.passed));

        // A run without an instrument still has every member's whole sum.
        plan.narrowed = true;
        let verdict = Verdict::of(&plan, &all);
        assert_eq!(verdict.members.len(), 2);
        assert!(!verdict.passed());
        let record: serde_json::Value = serde_json::from_str(&verdict.record(&plan)).unwrap();
        assert_eq!(record["narrowed"], true);
        assert_eq!(record["min_tests_skipped"], false);
        assert_eq!(record["passed"], false);

        // A run without the default run or a variant has part of the sum and
        // judges none of it; its record says so.
        plan.sum_partial = true;
        let verdict = Verdict::of(&plan, &all);
        assert_eq!(verdict.members, []);
        assert_eq!(verdict.refusal(&plan), None);
        assert!(verdict.passed());
        let record: serde_json::Value = serde_json::from_str(&verdict.record(&plan)).unwrap();
        assert_eq!(record["narrowed"], true);
        assert_eq!(record["min_tests_skipped"], true);
        assert_eq!(record["passed"], true);
    }

    #[test]
    fn a_required_test_passes_in_one_of_its_instruments_actions() {
        let plan = plan();
        let request = |verdict: &Verdict, id: &str| {
            verdict
                .requests
                .iter()
                .find(|request| request.id == id)
                .unwrap()
                .clone()
        };
        let enough = [
            ran("a", &["default"], Some(counts(2, 0, 0, 0)), &[]),
            ran("b", &["default", "j"], Some(counts(2, 0, 0, 0)), &[]),
            ran("a", &["v"], Some(counts(1, 0, 0, 0)), &[]),
        ];
        // One name in each of the instrument's two actions.
        let mut all = enough.to_vec();
        all.push(ran("a", &["i"], Some(counts(1, 0, 0, 0)), &["m::one"]));
        all.push(ran("a", &["i"], Some(counts(1, 0, 0, 0)), &["m::two"]));
        let verdict = Verdict::of(&plan, &all);
        assert_eq!(verdict.unmet, Vec::<String>::new());
        assert_eq!(
            request(&verdict, "i"),
            RequestResult {
                id: "i".to_owned(),
                actions: 2,
                failed: 0,
                excused: 0,
                tests: 2,
                passed: true,
            }
        );
        assert!(verdict.passed());

        // Another request's action showing the name does not count.
        let mut all = enough.to_vec();
        all.push(ran("a", &["i"], Some(counts(1, 0, 0, 0)), &["m::one"]));
        all.push(ran("a", &["v"], Some(counts(1, 0, 0, 0)), &["m::two"]));
        let verdict = Verdict::of(&plan, &all);
        assert_eq!(verdict.unmet.len(), 1, "{:?}", verdict.unmet);
        assert!(
            verdict.unmet[0].starts_with(
                "instrument `i` requires `m::two` to pass, and none of its test executables \
                 printed `test m::two ... ok`"
            ),
            "{}",
            verdict.unmet[0]
        );
        assert!(!request(&verdict, "i").passed);
        assert!(request(&verdict, "v").passed);
        assert!(!verdict.passed());

        // A failed action fails its requests and names no requirement.
        let mut all = enough.to_vec();
        all.push(ran(
            "a",
            &["i"],
            Some(counts(2, 0, 0, 0)),
            &["m::one", "m::two"],
        ));
        all[0].failed = true;
        let verdict = Verdict::of(&plan, &all);
        assert_eq!(verdict.unmet, Vec::<String>::new());
        assert_eq!(verdict.refusal(&plan), None);
        assert_eq!(request(&verdict, "default").failed, 1);
        assert!(!request(&verdict, "default").passed);
        assert!(!verdict.passed());
    }

    /// A variant whose executables all ran no test passed nothing, whoever
    /// else credits its member.
    #[test]
    fn a_variant_that_reports_no_test_is_unmet() {
        let plan = plan();
        let rest = [
            ran("a", &["default"], Some(counts(2, 0, 0, 0)), &[]),
            ran("b", &["default", "j"], Some(counts(2, 0, 0, 0)), &[]),
            ran("a", &["i"], Some(counts(2, 0, 0, 0)), &["m::one", "m::two"]),
        ];
        let with = |variant: &[Ran]| {
            let mut all = rest.to_vec();
            all.extend_from_slice(variant);
            Verdict::of(&plan, &all)
        };
        // Its member met `min-tests` in the default run.
        let verdict = with(&[
            ran("a", &["v"], Some(counts(0, 0, 3, 4)), &[]),
            ran("a", &["v"], Some(counts(0, 0, 0, 0)), &[]),
        ]);
        assert!(verdict.members.iter().all(|member| member.passed));
        assert_eq!(verdict.unmet.len(), 1, "{:?}", verdict.unmet);
        assert!(
            verdict.unmet[0].starts_with("variant `v` reported no test (passed + failed):"),
            "{}",
            verdict.unmet[0]
        );
        let v = verdict.requests.iter().find(|row| row.id == "v").unwrap();
        assert_eq!((v.tests, v.failed, v.passed), (0, 0, false));
        assert!(!verdict.passed());
        // One test in any of its actions is a test.
        let verdict = with(&[
            ran("a", &["v"], Some(counts(0, 0, 3, 4)), &[]),
            ran("a", &["v"], Some(counts(1, 0, 0, 0)), &[]),
        ]);
        assert_eq!(verdict.unmet, Vec::<String>::new());
        assert!(verdict.passed());
        // A failed action already fails the variant; nothing is added.
        let mut failed = ran("a", &["v"], None, &[]);
        failed.failed = true;
        let verdict = with(&[failed]);
        assert_eq!(verdict.unmet, Vec::<String>::new());
        assert!(!verdict.passed());
    }

    /// Why a required name was not shown is said where the harness's own
    /// lines say it.
    #[test]
    fn an_unmet_required_test_names_what_the_harness_printed() {
        let plan = plan();
        let rest = [
            ran("a", &["default"], Some(counts(2, 0, 0, 0)), &[]),
            ran("b", &["default", "j"], Some(counts(2, 0, 0, 0)), &[]),
            ran("a", &["v"], Some(counts(1, 0, 0, 0)), &[]),
        ];
        let mut contradicted = ran("a", &["i"], Some(counts(1, 0, 1, 0)), &["m::one"]);
        contradicted.observed.as_mut().unwrap().contradicted =
            BTreeSet::from(["m::two".to_owned()]);
        let mut all = rest.to_vec();
        all.push(contradicted);
        let verdict = Verdict::of(&plan, &all);
        assert_eq!(verdict.unmet.len(), 1, "{:?}", verdict.unmet);
        assert!(
            verdict.unmet[0].ends_with(
                "printed `test m::two ... ok`: a harness that printed it also printed another \
                 result for that test"
            ),
            "{}",
            verdict.unmet[0]
        );
        let mut void = ran("a", &["i"], Some(counts(1, 0, 1, 0)), &[]);
        void.observed.as_mut().unwrap().void = Some("the harness printed 2".to_owned());
        let mut all = rest.to_vec();
        all.push(void);
        let verdict = Verdict::of(&plan, &all);
        assert_eq!(verdict.unmet.len(), 2, "{:?}", verdict.unmet);
        assert!(
            verdict
                .unmet
                .iter()
                .all(|unmet| unmet.ends_with("... ok`: the harness printed 2")),
            "{:?}",
            verdict.unmet
        );
    }

    /// A harness that failed as libtest reports a failure: exit 101.
    fn libtest_failure() -> CargoResult<()> {
        let mut error = ProcessError::could_not_execute("harness");
        error.code = Some(101);
        Err(error.into())
    }

    /// What a watch of `m::one` and `m::slow` leaves for `reading` after
    /// `exit`.
    fn observed(exit: &CargoResult<()>, reading: &Reading) -> Observed {
        let watch = Watch::new(true, vec!["m::one".to_owned(), "m::slow".to_owned()]);
        watch.conclude(exit, reading);
        watch.take().unwrap()
    }

    /// The failed tests an action names are libtest's own report of them:
    /// only those can be looked up in a known-red file.
    #[test]
    fn a_failed_harness_names_its_failed_tests_only_by_libtests_own_report() {
        let names = |names: &[&str]| {
            Some(
                names
                    .iter()
                    .map(|name| (*name).to_owned())
                    .collect::<BTreeSet<_>>(),
            )
        };
        let lines = [
            "test m::one ... ok",
            "test m::red ... FAILED",
            "test m::panics - should panic ... FAILED",
            "test m::skipped ... ignored",
        ];
        let failed = closing(false, Some(counts(1, 2, 1, 0)));
        let report = run(Some(4), &lines, failed);
        let seen = observed(&libtest_failure(), &report);
        assert_eq!(seen.failed, names(&["m::panics", "m::red"]));
        assert_eq!(seen.unreported, None);
        assert_eq!(seen.tests, Some(counts(1, 2, 1, 0)));
        // A listed test that passed beside the failure is still seen.
        assert_eq!(seen.passed, BTreeSet::from(["m::one".to_owned()]));

        // Not an exit of libtest's: a signal, no exit at all, exit 0.
        let mut signalled = ProcessError::could_not_execute("harness");
        signalled.signal = Some(6);
        let mut both = ProcessError::could_not_execute("harness");
        (both.code, both.signal) = (Some(101), Some(6));
        let unstarted = ProcessError::could_not_execute("harness");
        for exit in [
            Err(signalled.into()),
            Err(both.into()),
            Err(unstarted.into()),
            Err(anyhow::anyhow!("output rejected")),
            Ok(()),
        ] {
            let seen = observed(&exit, &report);
            assert_eq!(seen.failed, None, "{exit:?}");
            // A failed exit that names no failed test says why.
            assert_eq!(
                seen.unreported.is_some_and(
                    |why| why.starts_with("the harness did not exit with a code of its own")
                ),
                exit.is_err(),
                "{exit:?}"
            );
        }
        // An unharnessed target prints no result line of libtest's.
        let unharnessed = Watch::new(false, Vec::new());
        unharnessed.conclude(&libtest_failure(), &report);
        let seen = unharnessed.take().unwrap();
        assert_eq!(seen.failed, None);
        assert_eq!(
            seen.unreported.as_deref(),
            Some("the target has `harness = false`, so it names no failed test")
        );
        // With nothing watched it has nothing unread; a watched name of it
        // can never be seen to pass.
        assert_eq!(seen.void, None);
        let exit: CargoResult<()> = Ok(());
        let unharnessed = Watch::new(false, vec!["m::one".to_owned()]);
        unharnessed.conclude(&exit, &Reading::default());
        assert_eq!(
            unharnessed.take().unwrap().void.as_deref(),
            Some("the target has `harness = false`, so it prints no result lines")
        );

        // Not the close of the announced run as failed.
        for (announced, lines, closing) in [
            // It left mid-run.
            (4, &lines[..], None),
            // An `ok` closing line.
            (4, &lines[..], closing(true, Some(counts(4, 0, 0, 0)))),
            // A FAILED line that counts no failure.
            (4, &lines[..], closing(false, Some(counts(3, 0, 1, 0)))),
            // Another run's closing line.
            (9, &lines[..], failed),
            // A `FAILED` line the closing line does not count.
            (
                5,
                &[
                    "test m::one ... ok",
                    "test m::red ... FAILED",
                    "test m::panics ... FAILED",
                    "test m::forged ... FAILED",
                    "test m::skipped ... ignored",
                ],
                closing(false, Some(counts(1, 2, 2, 0))),
            ),
            // A failure with no line of its own.
            (
                4,
                &["test m::one ... ok", "test m::red ... FAILED"],
                closing(false, Some(counts(1, 2, 1, 0))),
            ),
            // One test's line twice in place of another's.
            (
                4,
                &[
                    "test m::one ... ok",
                    "test m::red ... FAILED",
                    "test m::red ... FAILED",
                ],
                closing(false, Some(counts(1, 2, 1, 0))),
            ),
            // Each failure has a line, and one of them is printed again.
            (
                4,
                &[
                    "test m::one ... ok",
                    "test m::red ... FAILED",
                    "test m::panics ... FAILED",
                    "test m::red ... FAILED",
                ],
                closing(false, Some(counts(1, 2, 1, 0))),
            ),
            // An `ok` line the closing line does not count.
            (
                4,
                &[
                    "test m::one ... ok",
                    "test m::two ... ok",
                    "test m::red ... FAILED",
                    "test m::panics ... FAILED",
                ],
                closing(false, Some(counts(1, 2, 1, 0))),
            ),
        ] {
            let reading = run(Some(announced), lines, closing);
            let seen = observed(&libtest_failure(), &reading);
            assert_eq!(seen.failed, None, "{announced} {lines:?} {closing:?}");
            assert!(
                seen.unreported.is_some(),
                "{announced} {lines:?} {closing:?}"
            );
        }
        // Why, for each way: no closing line, another run's, uncounted lines.
        let why = |announced, lines: &[&str], closing| {
            observed(&libtest_failure(), &run(Some(announced), lines, closing))
                .unreported
                .unwrap()
        };
        assert_eq!(
            why(4, &lines, None),
            "the harness printed no complete closing `test result:` line, so libtest did not \
             report its failed tests"
        );
        assert_eq!(
            why(9, &lines, failed),
            "the harness's closing `test result:` line does not close its own run: it accounts \
             for 4 tests and the harness announced `running 9 tests`"
        );
        assert_eq!(
            why(4, &lines, closing(false, Some(counts(3, 0, 1, 0)))),
            "the harness's closing `test result:` line counts no failed test"
        );
        assert_eq!(
            why(
                4,
                &[
                    "test m::one ... ok",
                    "test child ... ok",
                    "test m::red ... FAILED",
                    "test m::panics ... FAILED",
                ],
                closing(false, Some(counts(1, 2, 1, 0)))
            ),
            "the harness printed 2 `test <name> ... FAILED` lines naming 2 tests and 2 `test \
             <name> ... ok` lines, and closed its run with 2 failed and 1 passed, so its result \
             lines are not read"
        );
        // Output after the closing line.
        let mut trailing = run(Some(4), &lines, failed);
        trailing.line("test m::late ... FAILED");
        assert_eq!(observed(&libtest_failure(), &trailing).failed, None);
    }

    fn known_red(rows: &str) -> ResolvedPlan {
        let mut plan = plan();
        let mut known = crate::ops::cargo_test::plan_expect::KnownRed::parse(rows).unwrap();
        known.file = "red.txt".to_owned();
        plan.known_red = Some(known);
        plan
    }

    fn failed(package: &str, requests: &[&str], tests: TestCounts, names: &[&str]) -> Ran {
        let mut ran = ran(package, requests, Some(tests), &[]);
        ran.failed = true;
        ran.observed.as_mut().unwrap().failed =
            Some(names.iter().map(|name| (*name).to_owned()).collect());
        ran
    }

    #[test]
    fn a_known_red_failure_does_not_fail_its_request_and_a_watch_names_the_listed_tests() {
        let plan = known_red("a::m::red\na::m::shaky # [flaky]\nb::m::gone\n");
        let request = |verdict: &Verdict, id: &str| {
            verdict
                .requests
                .iter()
                .find(|request| request.id == id)
                .unwrap()
                .clone()
        };
        let ids = |ids: &[&str]| ids.iter().map(|id| (*id).to_owned()).collect::<Vec<_>>();
        // The listed tests of the action's binary, beside what an instrument
        // requires.
        assert_eq!(
            plan.watch(true, "a", &ids(&["default", "i"])).names(),
            ["m::one", "m::red", "m::shaky", "m::two"]
        );
        assert_eq!(
            plan.watch(true, "b", &ids(&["default"])).names(),
            ["m::gone"]
        );
        assert!(plan.watch(true, "c", &ids(&["default"])).names().is_empty());

        let rest = [
            ran("b", &["default", "j"], Some(counts(2, 0, 0, 0)), &[]),
            ran("a", &["v"], Some(counts(1, 0, 0, 0)), &[]),
            ran("a", &["i"], Some(counts(2, 0, 0, 0)), &["m::one", "m::two"]),
        ];
        let red = failed("a", &["default"], counts(1, 1, 0, 0), &["m::red"]);
        assert!(plan.excuses(&red));
        let mut all = rest.to_vec();
        all.push(red.clone());
        let verdict = Verdict::of(&plan, &all);
        assert_eq!(
            request(&verdict, "default"),
            RequestResult {
                id: "default".to_owned(),
                actions: 2,
                failed: 1,
                excused: 1,
                tests: 4,
                passed: true,
            }
        );
        assert!(verdict.passed(), "{:?}", verdict.unmet);
        let known = verdict.known_red.unwrap();
        assert_eq!(known.excused, ["a::m::red"]);
        assert!(known.new_failures.is_empty() && known.stale.is_empty());

        // Without the file the same failure fails the request.
        let mut unlisted = plan.clone();
        unlisted.known_red = None;
        assert!(!unlisted.excuses(&red));
        let verdict = Verdict::of(&unlisted, &all);
        assert!(!request(&verdict, "default").passed);
        assert_eq!(request(&verdict, "default").excused, 0);
        assert_eq!(verdict.known_red, None);
        assert!(!verdict.passed());

        // A failure the file does not list beside one it does.
        let mut all = rest.to_vec();
        all.push(failed(
            "a",
            &["default"],
            counts(0, 2, 0, 0),
            &["m::red", "m::new"],
        ));
        let verdict = Verdict::of(&plan, &all);
        assert!(!request(&verdict, "default").passed);
        assert!(!verdict.passed());
        // The listed test is named, and not as excused: nothing was.
        let known = verdict.known_red.unwrap();
        assert!(known.excused.is_empty(), "{known:?}");
        assert_eq!(known.not_excused, ["a::m::red"]);
        assert_eq!(known.new_failures, ["a::m::new"]);

        // A listed test that passed: every action passed, and the run does
        // not, unless the row is flaky.
        let mut all = rest.to_vec();
        all.push(ran(
            "a",
            &["default"],
            Some(counts(2, 0, 0, 0)),
            &["m::red", "m::shaky"],
        ));
        let verdict = Verdict::of(&plan, &all);
        assert!(verdict.requests.iter().all(|request| request.passed));
        assert!(!verdict.passed());
        assert_eq!(
            verdict.unmet,
            [
                "known-red row `a::m::red` is stale: the test passed. Delete the row from \
              `red.txt`, or mark it `[flaky]` if the test may pass or fail"
            ]
        );
        assert_eq!(verdict.known_red.unwrap().stale, ["a::m::red"]);
    }

    /// A row is judged by result lines. Where a binary with rows passed and
    /// its lines were not read, a listed test may have passed unseen: the
    /// run does not pass on that.
    #[test]
    fn rows_of_a_harness_whose_result_lines_are_not_read_are_unjudged() {
        use crate::ops::cargo_test::plan_expect::Unjudged;
        let plan = known_red("a::m::red\n");
        let rest = [
            ran("b", &["default", "j"], Some(counts(2, 0, 0, 0)), &[]),
            ran("a", &["v"], Some(counts(1, 0, 0, 0)), &[]),
            ran("a", &["i"], Some(counts(2, 0, 0, 0)), &["m::one", "m::two"]),
        ];
        let lines = "the harness printed 4 `test <name> ... ok` lines".to_owned();
        let unjudged = |failed, why: &str| Unjudged {
            package: "a".to_owned(),
            binary: "a".to_owned(),
            failed,
            why: why.to_owned(),
        };

        // It passed, and its result lines are void.
        let mut void = ran("a", &["default"], Some(counts(2, 0, 0, 0)), &[]);
        void.observed.as_mut().unwrap().void = Some(lines.clone());
        let mut all = rest.to_vec();
        all.push(void.clone());
        let verdict = Verdict::of(&plan, &all);
        assert!(verdict.requests.iter().all(|request| request.passed));
        assert!(!verdict.passed());
        assert_eq!(
            verdict.unmet,
            [
                "known-red rows of test binary `a` (package `a`) in `red.txt` could not be \
                 judged, so a listed test that passed would go unseen: the harness printed 4 \
                 `test <name> ... ok` lines"
            ]
        );
        assert_eq!(
            verdict.known_red.unwrap().unjudged,
            [unjudged(false, &lines)]
        );

        // It passed, and nothing watched it.
        let mut unwatched = void.clone();
        unwatched.observed = None;
        let mut all = rest.to_vec();
        all.push(unwatched);
        let verdict = Verdict::of(&plan, &all);
        assert!(!verdict.passed());
        assert_eq!(
            verdict.known_red.unwrap().unjudged,
            [unjudged(false, "its harness was not watched")]
        );

        // The same void in a binary the file has no row for is nothing.
        let mut other = ran("b", &["default", "j"], Some(counts(2, 0, 0, 0)), &[]);
        other.observed.as_mut().unwrap().void = Some(lines.clone());
        let mut all = rest[1..].to_vec();
        all.push(other);
        all.push(ran("a", &["default"], Some(counts(2, 0, 0, 0)), &[]));
        let verdict = Verdict::of(&plan, &all);
        assert!(verdict.passed(), "{:?}", verdict.unmet);
        assert!(verdict.known_red.unwrap().unjudged.is_empty());

        // It failed and named no failed test: the row excused nothing, the
        // result says why, and the failure is what fails the run.
        let mut crashed = failed("a", &["default"], counts(0, 0, 0, 0), &[]);
        let observed = crashed.observed.as_mut().unwrap();
        (observed.failed, observed.tests) = (None, None);
        observed.unreported = Some("no closing line".to_owned());
        assert!(!plan.excuses(&crashed));
        let mut all = rest.to_vec();
        all.push(crashed);
        let verdict = Verdict::of(&plan, &all);
        assert!(!verdict.passed());
        // Not a requirement of its own: the failure already fails the run.
        assert!(
            !verdict
                .unmet
                .iter()
                .any(|unmet| unmet.contains("known-red")),
            "{:?}",
            verdict.unmet
        );
        assert_eq!(
            verdict.known_red.unwrap().unjudged,
            [unjudged(true, "no closing line")]
        );
        // A failure libtest reported is judged.
        let mut all = rest.to_vec();
        all.push(failed("a", &["default"], counts(1, 1, 0, 0), &["m::red"]));
        assert!(
            Verdict::of(&plan, &all)
                .known_red
                .unwrap()
                .unjudged
                .is_empty()
        );
    }

    /// Exit 0 says every action ran. A failure the known-red file excuses
    /// does not fail the run, so it cannot be why an action never ran.
    #[test]
    fn an_excused_failure_does_not_explain_an_unrun_action() {
        let plan = known_red("a::m::red\n");
        let passed = ran("b", &["default", "j"], Some(counts(2, 0, 0, 0)), &[]);
        let excused = failed("a", &["default"], counts(1, 1, 0, 0), &["m::red"]);
        let new = failed("a", &["default"], counts(1, 1, 0, 0), &["m::new"]);
        assert!(plan.excuses(&excused) && !plan.excuses(&new));
        let blocked = vec!["v".to_owned()];
        let only_excused = [passed.clone(), excused.clone()];
        assert!(!plan.explains_unrun(false, &only_excused));
        let error = plan
            .require_all_ran(&[&blocked], plan.explains_unrun(false, &only_excused))
            .unwrap_err();
        assert!(
            error
                .to_string()
                .contains("1 test action never ran though nothing failed"),
            "{error}"
        );
        // A failure that fails the run explains it, and so does an
        // interruption.
        assert!(plan.explains_unrun(false, &[passed.clone(), excused.clone(), new]));
        assert!(plan.explains_unrun(true, &only_excused));
        assert!(!plan.explains_unrun(false, &[passed]));
        // Without the file every failure fails the run.
        let mut unlisted = plan.clone();
        unlisted.known_red = None;
        assert!(unlisted.explains_unrun(false, &only_excused));
    }
}
