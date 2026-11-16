//! Trust: execution actions in the existing compilation dependency queue.
//! These unverified native harnesses share its actual permits and prerequisites.

use super::*;
use crate::util::machine_message::{
    Message, PlannedTestExecution, TEST_EXECUTION_SCHEMA_V2, TEST_EXECUTION_SCHEMA_V3,
    TEST_OUTPUT_SCHEMA_V1, TestCounts, TestExecution, TestExecutionState, TestOutput,
    TestOutputStream,
};
use std::time::Duration;

use super::harness_policy::{self, HarnessPolicy};
use super::plan_judge;

#[derive(Clone, Debug)]
pub(crate) struct TestGraphOptions {
    /// The invocation's harness arguments. Each action carries its own copy
    /// (`TestAction::args`); under a test plan these are empty and every
    /// action has its requests' arguments instead.
    pub args: Vec<String>,
    pub no_fail_fast: bool,
    pub required_bins: Vec<String>,
    /// The most credits running test actions hold together.
    pub limit: usize,
    /// The mebibytes running test actions may be counted for together, where
    /// the harness policy counts any: `build.test-memory-mib`, or what this
    /// host had available when the run began, less its reserve.
    pub memory_limit: Option<usize>,
    pub retained: bool,
    pub policy: HarnessPolicy,
    /// Why this invocation cannot grant a harness more than one credit, if
    /// it cannot: its pool's capacity is not Targo's to know.
    pub weight_refusal: Option<&'static str>,
    pub workload: Option<super::workload::Options>,
}

impl TestGraphOptions {
    pub(crate) fn orders_actions(&self) -> bool {
        // With one test credit, preserve the sequential runner's target
        // order in fail-fast mode, even if a later artifact is ready first.
        // Workloads also have an ordered continuation independent of policy.
        self.workload.is_some() || (self.limit == 1 && !self.no_fail_fast)
    }
}

#[derive(Clone, Debug)]
pub(crate) struct TestAction {
    pub index: usize,
    pub total: usize,
    pub unit: Unit,
    pub path: PathBuf,
    /// The harness arguments this action runs with.
    pub args: Vec<String>,
    /// Under a test plan, the ids of the requests this action runs for, in
    /// plan order and never empty. Empty without a plan.
    pub requests: Vec<String>,
    /// Credits held while running, and the libtest threads it gets.
    pub weight: usize,
    /// Runs with nothing beside it.
    pub exclusive: bool,
    /// Mebibytes counted against the memory budget while it runs.
    pub memory: usize,
    /// Expected run time in seconds, or 0: the longest ready action starts
    /// first.
    pub seconds: u64,
    /// None retains ordinary test execution. Workload variants are additional
    /// nodes in this same graph, never another compilation or execution grant.
    pub workload_action: Option<trust_test_execution::workload::Action>,
}

pub(crate) struct TestCompletion {
    pub action: TestAction,
    pub result: CargoResult<()>,
    pub elapsed: Duration,
    pub workload: Option<super::workload::CapturedAction>,
}

#[derive(Default)]
pub(crate) struct TestGraphRun {
    pub completed: Vec<TestCompletion>,
    pub blocked: Vec<TestAction>,
    pub interruption: Option<String>,
    pub reporting_error: Option<anyhow::Error>,
    /// Under a test plan, what each finished action's harness reported, by
    /// action index.
    pub observed: BTreeMap<usize, plan_judge::Observed>,
    /// Keeps the same actual compile-directory writer guards until the
    /// completed workload capsule drops, after the thread scope joined.
    pub workload_outputs: Option<super::workload::OwnedOutputs>,
}

/// How `run_tests` runs this invocation's tests.
pub(super) enum TestRoute {
    /// Compile and test in one native queue.
    Graph(TestGraphOptions),
    /// Cargo's sequential runner. It applies none of the harness policy but
    /// still refuses a typo in it: `check_selected` once the tested packages
    /// are known.
    Sequential(HarnessPolicy),
}

pub(super) fn request(
    ws: &Workspace<'_>,
    options: &TestOptions,
    args: &[&str],
) -> CargoResult<TestRoute> {
    // Check the policy on every route, so a typo is refused even where the
    // sequential runner would not consult it. A plan's own `[harness]`
    // table is the policy of its run.
    let plan = options.compile_opts.build_config.test_plan.as_deref();
    let policy = HarnessPolicy::load(ws, plan)?;
    // A plan states its lane's pool (`[run] test-jobs`); the configuration's
    // stands over it.
    let configured = ws.gctx().build_config()?.test_jobs;
    let retained = ws.gctx().has_retained_test();
    if (!retained && options.no_run)
        || options.compile_opts.build_config.dry_run
        || options.compile_opts.build_config.unit_graph
    {
        return Ok(TestRoute::Sequential(policy));
    }
    // The actual fixed owner already selected BuildRunner's restricted GNU
    // bridge. Keep tests in that SAME queue through its actual retirement;
    // a post-compile sequential command would inherit the wider startup pool.
    // This is distinct from selecting or constructing a v2/v3 runtime.
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    let fixed = ws.gctx().fixed_admission()?.is_some();
    #[cfg(not(any(target_os = "linux", target_os = "macos")))]
    let fixed = false;
    let native = crate::compiler::native_resources_requested(ws.gctx());
    // This is a growth ceiling, not a grant. The existing native dispatch
    // still acquires one actual CPU lease per action, subject to its memory
    // policy. Fixed and retained owners keep their existing default.
    let automatic = (native
        && !fixed
        && !retained
        && crate::is_targo_invocation()
        && !crate::trust_verified_targo())
    .then_some(options.compile_opts.build_config.jobs as usize);
    let requested = requested_test_jobs(
        configured,
        plan.and_then(|plan| plan.plan.run.test_jobs),
        automatic,
    );
    // A plan's requests have their own harness arguments, and two of them
    // may select one executable. Only the graph runs an action per request
    // and keeps such actions apart; the sequential runner has one argument
    // list for every target.
    if plan.is_none() && !retained && requested <= 1 && !native && !fixed {
        return Ok(TestRoute::Sequential(policy));
    }
    anyhow::ensure!(
        plan.is_none() || !retained,
        "a test plan cannot run under retained verified execution"
    );
    anyhow::ensure!(
        crate::is_targo_invocation()
            && ((!crate::trust_verified_targo() && !retained)
                || (crate::trust_verified_targo() && retained && options.no_run)),
        "build.test-jobs currently requires native unverified Targo"
    );
    anyhow::ensure!(
        cfg!(any(target_os = "linux", target_os = "macos")),
        "parallel test supervision requires Linux or macOS"
    );
    let limit = worker_budget::WorkerBudget::managed(ws.gctx())?
        .map_or(requested, |budget| budget.process_limit(requested))
        .min(options.compile_opts.build_config.jobs as usize);
    // A weight-w harness takes w credits at once. Only a pool Targo created
    // has a known size; an inherited jobserver's may be smaller than w, and
    // the native runtime acquires one CPU lease per dispatch, so a weighted
    // harness there could wait forever.
    let weight_refusal = if retained {
        Some("verified retained execution signs one cooperative harness credit")
    } else if native {
        Some("native worker admission takes one CPU lease per test action")
    } else if ws.gctx().jobserver_from_env()?.is_some() {
        Some("the inherited jobserver's capacity is unknown")
    } else {
        None
    };
    // A plan states its pool in credits and credits a harness (`[run]
    // test-jobs`, `test-weight`), which together say how many harnesses the
    // lane runs at once. On a pool that grants one credit at a time the
    // weight lowers to 1 (`admit_actions`), and the credits must lower with
    // it: sixteen credits at four a harness are four harnesses, not sixteen
    // of one thread each. The lane's count of executables at once is what
    // its timing assertions were measured under.
    let limit = match (weight_refusal, plan.map(|plan| &plan.plan.run)) {
        (Some(_), Some(run)) if policy.plans_weight() => {
            let weight = run.test_weight.unwrap_or(1).max(1);
            limit.min((requested / weight).max(1))
        }
        _ => limit,
    };
    let memory_limit = memory_limit(ws.gctx(), &policy)?;
    Ok(TestRoute::Graph(TestGraphOptions {
        args: args.iter().map(|arg| (*arg).to_owned()).collect(),
        no_fail_fast: options.no_fail_fast,
        required_bins: options.required_test_bins.clone(),
        limit,
        memory_limit,
        retained,
        policy,
        weight_refusal,
        workload: None,
    }))
}

fn requested_test_jobs(
    configured: Option<usize>,
    planned: Option<usize>,
    native_ceiling: Option<usize>,
) -> usize {
    configured.or(planned).or(native_ceiling).unwrap_or(1)
}

#[cfg(test)]
mod request_tests {
    use super::requested_test_jobs;

    #[test]
    fn explicit_and_planned_limits_precede_native_growth() {
        assert_eq!(requested_test_jobs(Some(1), Some(12), Some(28)), 1);
        assert_eq!(requested_test_jobs(Some(7), Some(12), Some(28)), 7);
        assert_eq!(requested_test_jobs(None, Some(3), Some(28)), 3);
        assert_eq!(requested_test_jobs(None, None, Some(28)), 28);
        assert_eq!(requested_test_jobs(None, None, Some(1)), 1);
    }

    #[test]
    fn without_native_growth_existing_defaults_and_limits_survive() {
        assert_eq!(requested_test_jobs(None, None, None), 1);
        assert_eq!(requested_test_jobs(None, Some(4), None), 4);
        assert_eq!(requested_test_jobs(Some(2), Some(4), None), 2);
    }
}

/// The memory budget of this run's test actions, where `policy` counts any
/// against one: `build.test-memory-mib`, or else what this host has
/// available now less its reserve (`util::host_memory`), measured once so
/// that the run's admission does not move with its own use. A host that
/// cannot be measured has no budget, and its counted harnesses then run one
/// at a time.
fn memory_limit(gctx: &GlobalContext, policy: &HarnessPolicy) -> CargoResult<Option<usize>> {
    if !policy.counts_memory() {
        return Ok(None);
    }
    if let Some(configured) = gctx.build_config()?.test_memory_mib {
        gctx.shell().status(
            "Admitting",
            format!("tests within {configured} MiB of memory (build.test-memory-mib)"),
        )?;
        return Ok(Some(configured));
    }
    let Some(host) = crate::util::host_memory::measure() else {
        gctx.shell().warn(
            "this host's memory could not be measured; test executables counted against \
             memory run one at a time (set build.test-memory-mib to give a budget)",
        )?;
        return Ok(Some(0));
    };
    let budget = host.test_budget_mib();
    gctx.shell().status(
        "Admitting",
        format!(
            "tests within {budget} MiB of memory: {} MiB available now less a reserve of {} MiB",
            host.available / (1024 * 1024),
            host.reserve_mib()
        ),
    )?;
    Ok(Some(budget))
}

/// Check the population and assign each action its admission. A weight is
/// bounded by the invocation's limit, so threads always equal the credits
/// held and the sum of running weights never exceeds that limit.
pub(crate) fn admit_actions(
    gctx: &GlobalContext,
    actions: &mut [TestAction],
    request: &TestGraphOptions,
    compilation: &Compilation<'_>,
    doctested: &[&crate::workspace::Package],
) -> CargoResult<()> {
    anyhow::ensure!(
        request.limit > 0,
        "native test action limit must be positive"
    );
    anyhow::ensure!(
        !request.retained || request.workload.is_none(),
        "retained verified tests cannot run unverified workload actions"
    );
    if request.workload.is_some() {
        anyhow::ensure!(
            request.limit == 1
                && request.no_fail_fast
                && request.args.is_empty()
                && request.required_bins.is_empty(),
            "native workload owns its exact sequential harness policy"
        );
    }
    let mut lowered = false;
    for action in actions.iter_mut() {
        if request.workload.is_some() {
            anyhow::ensure!(
                action.unit.target.harness(),
                "native workload requires real Rust harnesses"
            );
        }
        anyhow::ensure!(
            compilation.target_runner(action.unit.kind).is_none(),
            "build.test-jobs does not support custom target runners"
        );
        if action.unit.target.harness() {
            let args = action.args.iter().map(String::as_str).collect::<Vec<_>>();
            super::validate_native_test_arguments(&args)?;
        }
        let admission = request
            .policy
            .admission(action.unit.pkg.name().as_str(), &action.unit.target)?;
        let mut weight = admission.weight.min(request.limit);
        // The plan's weight for every harness is the lane's wish, and a pool
        // that grants one credit at a time gives each harness one (the
        // limit was lowered with it, in `request`).
        if admission.weight > 1 && admission.planned_weight && request.weight_refusal.is_some() {
            weight = 1;
            lowered = true;
        }
        anyhow::ensure!(
            !request.retained || weight == 1,
            "verified retained execution requires exactly one signed harness credit"
        );
        if weight > 1
            && let Some(reason) = request.weight_refusal
        {
            anyhow::bail!(
                "test target `{}` of `{}` asks for weight {weight}, but {reason}; set its weight to 1",
                action.unit.target.name(),
                action.unit.pkg.name()
            );
        }
        action.weight = weight;
        action.exclusive = admission.exclusive;
        action.memory = admission.memory;
        action.seconds = admission.seconds;
    }
    if lowered && let Some(reason) = request.weight_refusal {
        gctx.shell().note(format!(
            "the test plan's `[run] test-weight` is lowered to 1 for this run, and its pool \
             to {} test executable{} at once: {reason}",
            request.limit,
            if request.limit == 1 { "" } else { "s" }
        ))?;
    }
    let actions = &*actions;
    request.policy.check_selected(
        gctx,
        actions
            .iter()
            .map(|action| &action.unit.pkg)
            .chain(doctested.iter().copied()),
        harness_policy::Unselected::Warn,
    )?;
    let mut required = BTreeSet::new();
    for name in &request.required_bins {
        anyhow::ensure!(
            required.insert(name),
            "required test binary `{name}` was requested more than once"
        );
        let selected: Vec<_> = actions
            .iter()
            .filter(|action| {
                matches!(action.unit.target.kind(), TargetKind::Bin)
                    && action.unit.target.name() == name
            })
            .collect();
        let count = selected.len();
        anyhow::ensure!(
            count == 1,
            "required test binary `{name}` must select exactly one native harness (selected {count})"
        );
        // Only libtest prints the summary a required binary is judged by.
        anyhow::ensure!(
            selected[0].unit.target.harness(),
            "required test binary `{name}` must use the Rust test harness"
        );
    }
    Ok(())
}

/// How a finished test process ended, when it ended on its own.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) struct Termination {
    pub exit_code: Option<i32>,
    pub signal: Option<i32>,
}

impl Termination {
    /// Read the exit of the test process itself. A failure Targo imposed
    /// (output rejected, a launch failure, its cancellation) names no exit:
    /// the process status there is Targo's own stop, not the test's outcome.
    /// A process that exited by itself and that Targo then judged failed
    /// keeps its exit.
    pub(crate) fn of(result: &CargoResult<()>) -> Self {
        match result {
            Ok(()) => Self {
                exit_code: Some(0),
                signal: None,
            },
            Err(error) => {
                let top = error.chain().next();
                if let Some(judged) = top.and_then(|top| top.downcast_ref::<JudgedAfterExit>()) {
                    return Self {
                        exit_code: Some(judged.exit_code),
                        signal: None,
                    };
                }
                top.and_then(|top| top.downcast_ref::<ProcessError>())
                    .map_or_else(Self::default, |error| Self {
                        exit_code: error.code,
                        signal: error.signal,
                    })
            }
        }
    }
}

/// A test process that exited by itself with `exit_code`, which Targo then
/// judged failed: a required test binary that reported no passing test.
#[derive(Debug)]
pub(crate) struct JudgedAfterExit {
    pub exit_code: i32,
    pub reason: String,
}

impl std::fmt::Display for JudgedAfterExit {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.reason)
    }
}

impl std::error::Error for JudgedAfterExit {}

pub(crate) fn emit(
    gctx: &GlobalContext,
    action: &TestAction,
    state: TestExecutionState,
    elapsed: Option<Duration>,
    termination: Termination,
    tests: Option<TestCounts>,
) -> CargoResult<()> {
    let package_id = action.unit.pkg.package_id().to_spec();
    // Only a plan's actions are v3; every other run keeps v2 byte for byte.
    let planned = !action.requests.is_empty();
    let message = TestExecution {
        schema: if planned {
            TEST_EXECUTION_SCHEMA_V3
        } else {
            TEST_EXECUTION_SCHEMA_V2
        },
        index: action.index,
        total: action.total,
        prerequisite_artifact: &action.path,
        package_id: &package_id,
        package: action.unit.pkg.name().as_str(),
        target: action.unit.target.name(),
        kind: harness_policy::kind_key(&action.unit.target),
        harness: action.unit.target.harness(),
        weight: action.weight,
        exclusive: action.exclusive,
        state,
        elapsed_ms: elapsed.map(|elapsed| elapsed.as_millis().try_into().unwrap_or(u64::MAX)),
        exit_code: termination.exit_code,
        signal: termination.signal,
    };
    let line = if planned {
        let features = action
            .unit
            .features
            .iter()
            .map(|feature| feature.as_str())
            .collect::<Vec<_>>();
        PlannedTestExecution {
            execution: message,
            requests: &action.requests,
            features: &features,
            args: &action.args,
            memory_mib: action.memory,
            expected_seconds: action.seconds,
            tests,
        }
        .to_json_string()
    } else {
        message.to_json_string()
    };
    writeln!(gctx.shell().out(), "{line}")?;
    Ok(())
}

/// Construct the command only after its runtime prerequisite artifacts and
/// build-script outputs have completed. Reuse Cargo's normal environment path.
pub(crate) fn command(
    gctx: &GlobalContext,
    output: &UnitOutput,
    args: &[String],
    compilation: &Compilation<'_>,
    weight: usize,
) -> CargoResult<(String, ProcessBuilder)> {
    let args = args.iter().map(String::as_str).collect::<Vec<_>>();
    let (display, mut command) = cmd_builds(
        gctx,
        gctx.cwd(),
        &output.unit,
        &output.path,
        output.script_metas.as_ref(),
        &output.env,
        &args,
        compilation,
        "unittests",
    )?;
    // Libtest threads equal the credits the action holds. An unharnessed
    // target holds one and is told so, though it may ignore the hint.
    command.env("RUST_TEST_THREADS", weight.to_string());
    Ok((display, command))
}

/// Where a running action's output lines go: to the terminal as they are,
/// or, with JSON messages, as `test-output` records naming the action and
/// the stream, so concurrent harnesses' lines stay attributable.
#[derive(Clone, Copy, Debug)]
pub(crate) enum OutputSink {
    Raw,
    Json { index: usize },
}

impl OutputSink {
    pub(crate) fn write(self, stream: TestOutputStream, line: &str) -> CargoResult<()> {
        use std::io::Write as _;
        // The worker writes directly, one line per lock. Routing lines
        // through the coordinator's bounded queue could park a worker that
        // cancellation must reach before the scope joins it.
        match (self, stream) {
            (Self::Raw, TestOutputStream::Stdout) => writeln!(std::io::stdout().lock(), "{line}")?,
            (Self::Raw, TestOutputStream::Stderr) => writeln!(std::io::stderr().lock(), "{line}")?,
            (Self::Json { index }, stream) => {
                let message = TestOutput {
                    schema: TEST_OUTPUT_SCHEMA_V1,
                    index,
                    stream,
                    line,
                };
                writeln!(std::io::stdout().lock(), "{}", message.to_json_string())?
            }
        }
        Ok(())
    }
}

/// What a test harness may write, per stream: 512 MiB in all, scaled to this
/// machine's memory, in lines of at most 1 MiB. A longer line is cut to that
/// behind `cargo_util::long_line_mark`, not refused: a failing test may print
/// a message of any length (trust-json's `adversarial` prints 5 MB on one
/// line), and a harness stopped there would report none of its tests, where
/// a runner without the limit reports them all. Libtest's own lines are
/// short, and a cut line starts with the mark, so it reads as none of them.
pub(crate) fn harness_output_limits() -> cargo_util::StreamingOutputLimits {
    cargo_util::StreamingOutputLimits::new(1024 * 1024, 512 * 1024 * 1024)
        .with_child_exit_cleanup()
        .with_long_lines_cut()
}

/// `required` names who requires this harness to report a passing test, if
/// anyone does: a `--require-test-bin`, or a test plan's instrument. `watch`
/// is a plan action's: where what the harness reported is left.
pub(crate) fn execute(
    command: &ProcessBuilder,
    required: Option<&str>,
    watch: Option<&plan_judge::Watch>,
    scope: &cargo_util::StreamingProcessScope,
    sink: OutputSink,
) -> CargoResult<()> {
    let mut command = command.clone();
    command.supervised_by(scope);
    let result = if required.is_some() || watch.is_some() {
        execute_judged(&command, required, watch, sink)
    } else {
        command
            .exec_with_streaming_limits(
                &mut |line| sink.write(TestOutputStream::Stdout, line),
                &mut |line| sink.write(TestOutputStream::Stderr, line),
                false,
                harness_output_limits(),
            )
            .map(drop)
    };
    // Trust: a child Targo stopped (a root stop, an observer failure, an
    // interruption) ends with the signal Targo sent its group. That status is
    // Targo's, not the test's outcome, so `Termination::of` must not read it.
    result.map_err(|error| {
        if scope.interrupted() {
            error.context("the test process was stopped by Targo's cancellation")
        } else {
            error
        }
    })
}

pub(super) fn consume(
    ws: &Workspace<'_>,
    options: &TestOptions,
    run: TestGraphRun,
) -> Result<Vec<UnitTestError>, CliError> {
    if let Some(error) = run.reporting_error {
        return Err(error
            .context(format!(
                "test action reporting failed after {} observed completions",
                run.completed.len()
            ))
            .into());
    }
    let plan = options.compile_opts.build_config.test_plan.as_deref();
    // What the plan's verdict reads of each action, before the actions are
    // handed to the failure reports.
    let ran = run
        .completed
        .iter()
        .map(|completion| plan_judge::Ran {
            package: completion.action.unit.pkg.name().to_string(),
            binary: completion.action.unit.target.crate_name(),
            requests: completion.action.requests.clone(),
            failed: completion.result.is_err(),
            observed: run.observed.get(&completion.action.index).cloned(),
        })
        .collect::<Vec<_>>();
    // Under a plan, exit 0 says every action ran. Every known way to leave
    // one unrun also fails or interrupts the run; this holds the verdict to
    // that rather than to each of those ways staying as it is.
    if let Some(plan) = plan {
        let blocked = run
            .blocked
            .iter()
            .map(|action| action.requests.as_slice())
            .collect::<Vec<_>>();
        // An excused failure does not fail the run, so it does not explain
        // an unrun action either.
        let explained = plan.explains_unrun(run.interruption.is_some(), &ran);
        plan.require_all_ran(&blocked, explained)
            .map_err(super::plan_outcome::cannot_judge)?;
    }
    let mut errors = Vec::new();
    let mut exit_code = None;
    for (completion, ran) in run.completed.into_iter().zip(&ran) {
        if let Err(error) = completion.result {
            // A harness that failed only in tests the plan's known-red file
            // lists does not fail the run. Its record stays `failed`; the
            // result record names the tests.
            if let Some(plan) = plan.filter(|plan| plan.excuses(ran)) {
                let known = plan.known_red.as_ref().expect("an excuse has a file");
                let listed = known.judge(ran).known;
                ws.gctx()
                    .shell()
                    .note(format!(
                        "{} `{}` of `{}` failed only in known-red tests (listed in `{}`): {}",
                        harness_policy::kind_key(&completion.action.unit.target),
                        completion.action.unit.target.name(),
                        completion.action.unit.pkg.name(),
                        known.file,
                        listed.join(", ")
                    ))
                    .map_err(anyhow::Error::from)?;
                continue;
            }
            exit_code.get_or_insert_with(|| fail_fast_code(&error));
            // A plan action is rerun by its request: `-p` and a target flag
            // would not carry the request's features or arguments.
            let rerun = plan.and_then(|plan| plan.rerun(&completion.action.requests));
            let args = completion
                .action
                .args
                .iter()
                .map(String::as_str)
                .collect::<Vec<_>>();
            let unit_error = UnitTestError {
                unit: completion.action.unit,
                kind: TestKind::Test,
                rerun,
            };
            report_test_error(ws, &args, &options.compile_opts, &unit_error, error);
            errors.push(unit_error);
        }
    }
    if let Some(interruption) = run.interruption {
        return Err(anyhow::anyhow!(interruption).into());
    }
    if !options.no_fail_fast
        && let Some(code) = exit_code
    {
        return Err(CliError::code(code));
    }
    // The run ran to its end, so the plan has a verdict: what it requires
    // beyond every action passing.
    if let Some(plan) = plan {
        // Unless Targo stopped the run after its last queue drained: then the
        // stop is how it ended (`plan_outcome::conclude`). A phase's verdict
        // is its plan's, not the invocation's.
        if plan.phase.is_none()
            && let Err((_, why)) = super::plan_outcome::conclude()
        {
            return Err(anyhow::anyhow!(why).into());
        }
        let verdict = plan_judge::Verdict::of(plan, &ran);
        // A `[[workspace]]` phase's run ran to its end: what it concluded
        // is the phase's, for the plan that started it (`plan_phases`).
        if let Some(phase) = &plan.phase {
            phase.conclude(super::plan_phases::Outcome {
                passed: errors.is_empty() && verdict.passed(),
                tests: verdict.requests.iter().map(|request| request.tests).sum(),
            });
        }
        if options.compile_opts.build_config.emit_json() {
            writeln!(ws.gctx().shell().out(), "{}", verdict.record(plan))
                .map_err(anyhow::Error::from)?;
        }
        // A failure the known-red file does not list fails by its action;
        // the tests are named here, where the file was read.
        if let Some(result) = &verdict.known_red {
            for key in &result.new_failures {
                ws.gctx()
                    .shell()
                    .error(format!(
                        "new failure, not listed in `{}`: {key}",
                        result.file
                    ))
                    .map_err(anyhow::Error::from)?;
            }
            // A failed harness with rows that excused nothing because its
            // result lines were not read: say so, or the rows look ignored.
            for unjudged in result.unjudged.iter().filter(|unjudged| unjudged.failed) {
                ws.gctx()
                    .shell()
                    .note(format!(
                        "`{}` lists tests of the test binary `{}` (package `{}`), and its \
                         failure names no failed test, so nothing is excused: {}",
                        result.file, unjudged.binary, unjudged.package, unjudged.why
                    ))
                    .map_err(anyhow::Error::from)?;
            }
        }
        if let Some(unmet) = verdict.refusal(plan) {
            // The failed targets are still named: this error replaces the
            // one that would have listed them.
            let failed = no_fail_fast_err(ws, &options.compile_opts, &errors)
                .err()
                .and_then(|failed| failed.error)
                .map_or_else(String::new, |failed| format!("\n{failed}"));
            // Red where something judged is wrong; otherwise the plan's
            // requirements could not be judged. A phase's own run answers
            // to the plan that started it, which reads its row.
            let error = anyhow::anyhow!("{unmet}{failed}");
            let judged = plan.phase.is_some()
                || verdict.outcome(plan) == super::plan_outcome::Outcome::Failed;
            return Err(if judged {
                error.into()
            } else {
                CliError::new(
                    super::plan_outcome::cannot_judge(error),
                    super::plan_outcome::CANNOT_JUDGE,
                )
            });
        }
    }
    Ok(errors)
}
