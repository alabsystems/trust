//! Trust: test actions are dependents in the compiler's one admitted queue.
//!
//! Compilation identities, fingerprints, timings and execution outcomes retain
//! their compile-only meaning. Test failures have their own policy and result
//! channel, while every running action consumes the same jobserver admission.

use std::collections::BTreeMap;
use std::sync::Arc;
use std::thread::Scope;
use std::time::{Duration, Instant};

use anyhow::bail;
use cargo_util::StreamingProcessScope;

use super::{Artifact, DrainState, Job, JobQueue, Message};
use crate::compiler::{BuildRunner, Unit};
use crate::ops::cargo_test::graph::{
    self, OutputSink, Termination, TestAction, TestCompletion, TestGraphOptions, TestGraphRun,
};
use crate::util::CargoResult;
use crate::util::data_structures::HashSet;
use crate::util::log_message::LogMessage;
use crate::util::machine_message::TestExecutionState;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(super) enum QueueNode {
    Compile(Unit),
    Test(usize),
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    Verification(crate::compiler::qualification::VerificationIndex),
}

impl QueueNode {
    pub(super) fn as_compile(&self) -> Option<&Unit> {
        match self {
            Self::Compile(unit) => Some(unit),
            Self::Test(_) => None,
            #[cfg(any(target_os = "linux", target_os = "macos"))]
            Self::Verification(_) => None,
        }
    }
}

#[derive(Debug)]
pub(super) enum QueueWork {
    Compile(Job),
    Test(TestAction),
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    Verification(crate::compiler::qualification::Action),
}

pub(super) struct TestState {
    pub(super) options: TestGraphOptions,
    pub(super) active: HashSet<usize>,
    pub(super) stopped: bool,
    pub(super) signals: Arc<StreamingProcessScope>,
    pub(super) run: TestGraphRun,
    pub(super) reporter: TestReporter,
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    retained: Option<crate::ops::cargo_test::retained::Gate>,
    failed_prerequisites: HashSet<Unit>,
    // Retain every planned action until its actual completion. A missing or
    // blocked prerequisite must not silently shrink the execution population.
    remaining: BTreeMap<usize, TestAction>,
    // Under a test plan, where each running action's worker leaves what its
    // harness reported.
    watches: BTreeMap<usize, crate::ops::cargo_test::plan_judge::Watch>,
    prerequisites: BTreeMap<usize, HashSet<Unit>>,
    inventories: BTreeMap<String, trust_test_execution::workload::Inventory>,
    pub(super) outputs: Option<crate::ops::cargo_test::workload::OwnedOutputs>,
}

impl TestState {
    /// Credits the running actions hold: the sum of their weights.
    pub(super) fn credits(&self) -> usize {
        self.active
            .iter()
            .map(|index| self.remaining[index].weight)
            .sum()
    }

    /// Mebibytes the running actions are counted for.
    pub(super) fn memory(&self) -> usize {
        self.active
            .iter()
            .map(|index| self.remaining[index].memory)
            .sum()
    }

    /// A running action is exclusive.
    pub(super) fn exclusive_running(&self) -> bool {
        self.active
            .iter()
            .any(|index| self.remaining[index].exclusive)
    }

    /// Trust: the running test executables, as a test plan's clock reads
    /// them: in dispatch-index order, each with when it last printed.
    pub(super) fn running(&self) -> Vec<crate::ops::cargo_test::plan_clock::Running<'_>> {
        let mut active = self.active.iter().copied().collect::<Vec<_>>();
        active.sort_unstable();
        active
            .into_iter()
            .map(|index| {
                let action = &self.remaining[&index];
                crate::ops::cargo_test::plan_clock::Running {
                    name: format!(
                        "{} `{}` of `{}`",
                        crate::ops::cargo_test::harness_policy::kind_key(&action.unit.target),
                        action.unit.target.name(),
                        action.unit.pkg.name()
                    ),
                    progress: self.watches.get(&index).map(|watch| watch.progress()),
                }
            })
            .collect()
    }

    pub(super) fn new(
        options: TestGraphOptions,
        actions: Vec<TestAction>,
        prerequisites: BTreeMap<usize, HashSet<Unit>>,
        signals: Arc<StreamingProcessScope>,
        gctx: &crate::util::GlobalContext,
    ) -> CargoResult<Self> {
        #[cfg(any(target_os = "linux", target_os = "macos"))]
        let retained = if options.retained {
            Some(crate::ops::cargo_test::retained::Gate::take(gctx)?)
        } else {
            None
        };
        Ok(Self {
            options,
            active: HashSet::default(),
            stopped: false,
            signals,
            failed_prerequisites: HashSet::default(),
            reporter: TestReporter::default(),
            #[cfg(any(target_os = "linux", target_os = "macos"))]
            retained,
            prerequisites,
            inventories: BTreeMap::new(),
            outputs: None,
            watches: BTreeMap::new(),
            remaining: actions
                .into_iter()
                .map(|action| (action.index, action))
                .collect(),
            run: TestGraphRun {
                completed: Vec::new(),
                blocked: Vec::new(),
                interruption: None,
                reporting_error: None,
                observed: BTreeMap::new(),
                workload_outputs: None,
            },
        })
    }

    pub(super) fn can_dispatch(&self) -> bool {
        // Trust: a test plan run held at a barrier starts no test executable
        // until its caller releases it (`ops::cargo_test::plan_clock`).
        if !crate::ops::cargo_test::plan_clock::armed().is_none_or(|clock| clock.tests_may_start())
        {
            return false;
        }
        if !self.options.retained {
            return true;
        }
        #[cfg(any(target_os = "linux", target_os = "macos"))]
        {
            self.retained
                .as_ref()
                .is_some_and(|gate| gate.authorized().is_some())
        }
        #[cfg(not(any(target_os = "linux", target_os = "macos")))]
        {
            false
        }
    }
}

// Trust: all test observers share this one rejection gate. Preserve its first
// failure and cancel owned peers before any surrounding scope can join them.
#[derive(Default)]
pub(super) struct TestReporter {
    pub(super) error: Option<anyhow::Error>,
}

impl TestReporter {
    fn observe(
        &mut self,
        signals: &StreamingProcessScope,
        report: impl FnOnce() -> CargoResult<()>,
    ) -> bool {
        if self.error.is_some() {
            return false;
        }
        if let Err(error) = observe_report(report) {
            self.error = Some(error);
            signals.cancel();
            return false;
        }
        true
    }
}

/// This guard must be created inside `thread::scope`: its cancellation runs
/// before that scope joins workers after a coordinator panic or early return.
pub(super) struct CancelTestWorkers<'a> {
    signals: Option<&'a StreamingProcessScope>,
    armed: bool,
}

impl<'a> CancelTestWorkers<'a> {
    pub(super) fn new(signals: Option<&'a StreamingProcessScope>) -> Self {
        Self {
            signals,
            armed: true,
        }
    }

    pub(super) fn disarm(&mut self) {
        self.armed = false;
    }
}

impl Drop for CancelTestWorkers<'_> {
    fn drop(&mut self) {
        if self.armed
            && let Some(signals) = self.signals
        {
            signals.cancel();
        }
    }
}

impl JobQueue<'_> {
    pub(super) fn enqueue_tests(
        &mut self,
        build_runner: &BuildRunner<'_, '_>,
        options: &TestGraphOptions,
        actions: &[TestAction],
    ) -> CargoResult<BTreeMap<usize, HashSet<Unit>>> {
        if options.limit == 0 {
            bail!("test action concurrency must be positive");
        }
        let mut indices = HashSet::default();
        let mut prerequisite_inventory = BTreeMap::new();
        // The last action queued for each test target.
        let mut last_on_target = BTreeMap::new();
        let build_scripts: Vec<_> = self
            .queued_units
            .iter()
            .filter(|unit| unit.mode.is_run_custom_build())
            .cloned()
            .collect();
        for action in actions {
            if action.total != actions.len()
                || action.index >= actions.len()
                || !indices.insert(action.index)
                || !self.queued_units.contains(&action.unit)
            {
                bail!("test action population does not match the compiled graph");
            }
            // Compile scheduling intentionally omits executable dependencies.
            // Execution restores the admitted graph's runtime binary/artifact
            // edges, including integration tests' CARGO_BIN_EXE prerequisites.
            let mut worklist = vec![action.unit.clone()];
            worklist.extend(build_scripts.iter().cloned());
            let mut prerequisites = HashSet::default();
            if options.workload.is_some() {
                // This side's complete compiler population retires before its
                // first discovery. All prerequisites remain the original DAG.
                worklist.extend(self.queued_units.iter().cloned());
            }
            while let Some(unit) = worklist.pop() {
                if !prerequisites.insert(unit.clone()) {
                    continue;
                }
                if !self.queued_units.contains(&unit) {
                    bail!("test runtime prerequisite is absent from the compiled queue");
                }
                worklist.extend(
                    build_runner
                        .unit_deps(&unit)
                        .iter()
                        .map(|dep| dep.unit.clone()),
                );
            }
            // Cargo's target-process environment includes native directories
            // from every completed build script, even unrelated packages.
            // Preserve that environment while permitting unrelated ordinary
            // compilation to overlap a ready test action.
            if let Some(logger) = build_runner.bcx.logger {
                let mut indices: Vec<_> = prerequisites
                    .iter()
                    .map(|unit| build_runner.bcx.unit_to_index[unit])
                    .collect();
                indices.sort_unstable();
                logger.log(LogMessage::TestActionRegistered {
                    index: action.index as u64,
                    harness: build_runner.bcx.unit_to_index[&action.unit],
                    prerequisites: indices,
                });
            }
            let cost = super::test_admission::cost(action.weight, action.exclusive, action.seconds);
            let mut edges = prerequisites
                .iter()
                .cloned()
                .map(|unit| (QueueNode::Compile(unit), Artifact::All))
                .collect::<Vec<_>>();
            // A ready artifact cannot overtake its earlier test target.
            let ordered_after =
                (options.orders_actions() && action.index > 0).then(|| action.index - 1);
            // One test target never runs beside itself: two processes of the
            // same tests would share whatever files those tests write. A test
            // plan runs one executable once per distinct argument list of
            // its requests, and builds one target once per feature set of
            // its variants; those are the same tests in the same package
            // directory, whichever file they were linked into. Without a
            // plan a target is one action per compile kind.
            let same_target = last_on_target.insert(
                (
                    action.unit.pkg.package_id(),
                    &action.unit.target,
                    action.unit.kind,
                ),
                action.index,
            );
            edges.extend(
                ordered_after
                    .into_iter()
                    .chain(same_target)
                    .map(|earlier| (QueueNode::Test(earlier), Artifact::All)),
            );
            self.queue.queue(
                QueueNode::Test(action.index),
                QueueWork::Test(action.clone()),
                edges,
                cost,
            );
            prerequisite_inventory.insert(action.index, prerequisites);
        }
        Ok(prerequisite_inventory)
    }
}

impl DrainState<'_> {
    pub(super) fn active_count(&self) -> usize {
        self.compiler_actions_active() + self.tests.as_ref().map_or(0, |tests| tests.active.len())
    }

    /// Only this compiler-finalized coordinator can consume the one-use grant.
    /// No test node is admitted while this call is pending.
    pub(super) fn qualify_retained_tests(
        &mut self,
        build_runner: &BuildRunner<'_, '_>,
        compile_succeeded: bool,
    ) -> CargoResult<bool> {
        let Some(tests) = self.tests.as_mut() else {
            return Ok(false);
        };
        if !tests.options.retained {
            return Ok(false);
        }
        #[cfg(any(target_os = "linux", target_os = "macos"))]
        {
            let gate = tests.retained.as_mut().expect("retained endpoint");
            if !compile_succeeded {
                tests.stopped = true;
                gate.publish_failed(
                    "compilation did not complete successfully",
                    build_runner.bcx.gctx,
                )?;
                return Ok(false);
            }
            let actions = tests.remaining.values().collect::<Vec<_>>();
            if let Err(error) = gate.qualify(
                build_runner.bcx.ws,
                &tests.options,
                &build_runner.compilation,
                &actions,
                &tests.signals,
            ) {
                tests.stopped = true;
                tests.signals.cancel();
                // Export refusal before Ready is a typed failed checkpoint;
                // failures after Ready remain failed actual child outcomes.
                let _ = gate.publish_failed(&format!("{error:#}"), build_runner.bcx.gctx);
                return Err(error);
            }
            return Ok(true);
        }
        #[cfg(not(any(target_os = "linux", target_os = "macos")))]
        anyhow::bail!("retained verified execution is unavailable on this platform")
    }

    pub(super) fn poll_retained_cancellation(&mut self) {
        #[cfg(any(target_os = "linux", target_os = "macos"))]
        if let Some(tests) = self.tests.as_mut()
            && let Some(gate) = tests.retained.as_mut()
        {
            match gate.poll_cancelled() {
                Ok(false) => {}
                result => {
                    tests.stopped = true;
                    tests.signals.cancel();
                    tests.run.interruption.get_or_insert_with(|| match result {
                        Ok(true) => "retained frontend closed the execution session".into(),
                        Err(error) => format!("retained execution control failed: {error:#}"),
                        Ok(false) => unreachable!(),
                    });
                }
            }
        }
    }

    pub(super) fn test_action_ready(
        &mut self,
        build_runner: &BuildRunner<'_, '_>,
        action: &TestAction,
    ) -> bool {
        if self.tests.as_ref().expect("test state").stopped {
            return false;
        }
        // --keep-going may publish a usable artifact despite denied warnings.
        // Compilation can continue to consume it under Cargo's existing
        // policy, but a known failed prerequisite cannot authorize a test.
        let tests = self.tests.as_ref().expect("test state");
        if tests.prerequisites[&action.index]
            .iter()
            .any(|unit| tests.failed_prerequisites.contains(unit))
        {
            return false;
        }
        // Keep ready test nodes pending while opaque qualification runs. They
        // cannot request either a local token or a native root lease yet.
        if !tests.can_dispatch() {
            return true;
        }
        self.emit_test_action(
            build_runner,
            action,
            TestExecutionState::Ready,
            None,
            Termination::default(),
        );
        !self.tests.as_ref().expect("test state").stopped
    }

    pub(super) fn test_prerequisite_failed(&mut self, unit: &Unit) {
        if let Some(tests) = self.tests.as_mut() {
            tests.failed_prerequisites.insert(unit.clone());
        }
    }

    fn emit_test_action(
        &mut self,
        build_runner: &BuildRunner<'_, '_>,
        action: &TestAction,
        state: TestExecutionState,
        elapsed: Option<Duration>,
        termination: Termination,
    ) {
        if !build_runner.bcx.build_config.emit_json() {
            return;
        }
        let tests = self.tests.as_mut().expect("test state");
        // Known once the action has finished; `null` before, and for an
        // action that never ran.
        let counted = tests
            .run
            .observed
            .get(&action.index)
            .and_then(|observed| observed.tests);
        tests.stopped |= !tests.reporter.observe(&tests.signals, || {
            graph::emit(
                build_runner.bcx.gctx,
                action,
                state,
                elapsed,
                termination,
                counted,
            )
        });
    }

    pub(super) fn run_test_action<'s>(
        &mut self,
        action: TestAction,
        build_runner: &mut BuildRunner<'_, '_>,
        scope: &'s Scope<'s, '_>,
        local_token: Option<jobserver::Acquired>,
        #[cfg(any(target_os = "linux", target_os = "macos"))] resources: Option<
            Arc<crate::compiler::resource_runtime::RootContext>,
        >,
    ) {
        let start = Instant::now();
        if self.tests.as_ref().expect("test state").options.retained {
            self.emit_test_action(
                build_runner,
                &action,
                TestExecutionState::Ready,
                None,
                Termination::default(),
            );
            if self.tests.as_ref().expect("test state").stopped {
                return;
            }
        }
        let tests = self.tests.as_mut().expect("test state");
        assert!(tests.can_dispatch(), "test dispatched before qualification");
        assert!(tests.active.insert(action.index));
        if tests.options.workload.is_some() {
            let validation = tests
                .outputs
                .as_ref()
                .ok_or_else(|| {
                    anyhow::anyhow!("native workload has no original compiled output owner")
                })
                .and_then(|outputs| outputs.for_action(&action).map(|_| ()));
            if let Err(error) = validation {
                self.finish_test_action(
                    build_runner,
                    TestCompletion {
                        action,
                        result: Err(error),
                        elapsed: start.elapsed(),
                        workload: None,
                    },
                );
                return;
            }
        }
        #[cfg(any(target_os = "linux", target_os = "macos"))]
        let authorized = tests.retained.as_ref().and_then(|gate| gate.authorized());
        let command = {
            #[cfg(any(target_os = "linux", target_os = "macos"))]
            if let Some(authorized) = &authorized {
                authorized.command(action.index)
            } else {
                build_runner.test_action_command(&action, &tests.options)
            }
            #[cfg(not(any(target_os = "linux", target_os = "macos")))]
            build_runner.test_action_command(&action, &tests.options)
        };
        let (display, mut command) = match command {
            Ok(command) => command,
            Err(error) => {
                self.finish_test_action(
                    build_runner,
                    TestCompletion {
                        action,
                        result: Err(error),
                        elapsed: start.elapsed(),
                        workload: None,
                    },
                );
                return;
            }
        };
        #[cfg(any(target_os = "linux", target_os = "macos"))]
        let scheduling = if authorized.is_some() {
            #[cfg(any(target_os = "linux", target_os = "macos"))]
            let handoff = match &resources {
                Some(resources) => resources.authenticated_test_handoff(),
                None => {
                    crate::ops::cargo_test::auth_scheduling::OwnedSchedulingHandoff::jobserver_only(
                        &build_runner.jobserver,
                    )
                }
            };
            #[cfg(not(any(target_os = "linux", target_os = "macos")))]
            let handoff =
                crate::ops::cargo_test::auth_scheduling::OwnedSchedulingHandoff::jobserver_only(
                    &build_runner.jobserver,
                );
            match handoff {
                Ok(handoff) => Some(handoff),
                Err(error) => {
                    self.finish_test_action(
                        build_runner,
                        TestCompletion {
                            action,
                            result: Err(error),
                            elapsed: start.elapsed(),
                            workload: None,
                        },
                    );
                    return;
                }
            }
        } else {
            None
        };
        command.inherit_jobserver(&build_runner.jobserver);
        #[cfg(any(target_os = "linux", target_os = "macos"))]
        if let Some(resources) = &resources
            && let Err(error) = resources.configure(&mut command, false)
        {
            self.finish_test_action(
                build_runner,
                TestCompletion {
                    action,
                    result: Err(error),
                    elapsed: start.elapsed(),
                    workload: None,
                },
            );
            return;
        }
        // A harness holds `weight` permits of the very same admitted pool as
        // rustc, and libtest runs as many threads. Arguments were validated
        // before graph execution begins.
        command.env("RUST_TEST_THREADS", action.weight.to_string());
        if build_runner.bcx.gctx.extra_verbose() {
            command.display_env_vars();
        }
        let tests = self.tests.as_mut().expect("test state");
        // Two runs of one executable print the same path; the requests tell
        // them apart.
        let display = match build_runner.bcx.build_config.test_plan.as_deref() {
            Some(plan) if !action.requests.is_empty() => {
                format!("{display} [{}]", plan.label(&action.requests))
            }
            _ => display,
        };
        let reported = tests.reporter.observe(&tests.signals, || {
            let gctx = build_runner.bcx.gctx;
            gctx.shell()
                .concise(|shell| shell.status("Running", &display))?;
            gctx.shell()
                .verbose(|shell| shell.status("Running", &command))?;
            Ok(())
        });
        if !reported {
            tests.active.remove(&action.index);
            tests.stopped = true;
            return;
        }
        self.emit_test_action(
            build_runner,
            &action,
            TestExecutionState::Running,
            None,
            Termination::default(),
        );
        if self.tests.as_ref().expect("test state").stopped {
            self.tests
                .as_mut()
                .expect("test state")
                .active
                .remove(&action.index);
            return;
        }
        let tests = self.tests.as_ref().expect("test state");
        let required = matches!(action.unit.target.kind(), crate::workspace::TargetKind::Bin)
            && tests
                .options
                .required_bins
                .iter()
                .any(|name| name == action.unit.target.name());
        let required =
            required.then(|| format!("required test binary `{}`", action.unit.target.name()));
        // A plan's instrument must itself judge a test: a filter that matches
        // nothing exits 0 like one that passed. An unharnessed target prints
        // no summary and is judged by its exit alone.
        let required = required.or_else(|| {
            let plan = build_runner.bcx.build_config.test_plan.as_deref()?;
            let who = plan.must_judge(&action.requests)?;
            action.unit.target.harness().then_some(who)
        });
        // Every plan action's harness is read for what it reported.
        let watch = build_runner
            .bcx
            .build_config
            .test_plan
            .as_deref()
            .filter(|_| !action.requests.is_empty())
            .map(|plan| {
                plan.watch(
                    action.unit.target.harness(),
                    &action.unit.target.crate_name(),
                    &action.requests,
                )
            });
        if let Some(watch) = &watch {
            self.tests
                .as_mut()
                .expect("test state")
                .watches
                .insert(action.index, watch.clone());
        }
        let tests = self.tests.as_ref().expect("test state");
        let signals = tests.signals.clone();
        let supervision = tests.options.policy.supervision();
        let workload = tests.options.workload.clone();
        let messages = self.messages.clone();
        let sink = if build_runner.bcx.build_config.emit_json() {
            OutputSink::Json {
                index: action.index,
            }
        } else {
            OutputSink::Raw
        };
        // Unit contains coordinator-owned graph state and is not Send. The
        // worker returns only this stable index; the retained population owns
        // the TestAction until its actual completion is observed here.
        let index = action.index;
        let spawned = std::thread::Builder::new()
            .name(format!("targo-test-{}", action.index))
            .spawn_scoped(scope, move || {
                // Both credits span the actual child/group wait and terminal
                // publication. The global runtime is retained for inherited
                // CPU handoff and serial cooperative descendant transport.
                let _local_token = local_token;
                #[cfg(any(target_os = "linux", target_os = "macos"))]
                let _resources = resources;
                let (result, captured) =
                    std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                        if let Some(options) = workload {
                            (
                                Ok(()),
                                Some(crate::ops::cargo_test::workload::execute(
                                    &command,
                                    &signals,
                                    &options.plan,
                                )),
                            )
                        } else {
                            #[cfg(any(target_os = "linux", target_os = "macos"))]
                            let result = if let Some(authorized) = &authorized {
                                authorized.execute(
                                    index,
                                    &command,
                                    &signals,
                                    scheduling.as_ref().expect("owned scheduling handoff"),
                                )
                            } else {
                                graph::execute(
                                    &command,
                                    required.as_deref(),
                                    watch.as_ref(),
                                    &signals,
                                    sink,
                                    supervision,
                                )
                            };
                            #[cfg(not(any(target_os = "linux", target_os = "macos")))]
                            let result = graph::execute(
                                &command,
                                required.as_deref(),
                                watch.as_ref(),
                                &signals,
                                sink,
                                supervision,
                            );
                            (result, None)
                        }
                    }))
                    .unwrap_or_else(|_| {
                        (
                            Err(anyhow::anyhow!("native test execution worker panicked")),
                            None,
                        )
                    });

                // Retire the configured command's duplicate lease/fence
                // descriptors before the runtime's descriptor permit retires.
                // The CPU and local credits still cover terminal publication.
                drop(command);
                #[cfg(any(target_os = "linux", target_os = "macos"))]
                drop(scheduling);
                // The executor has reaped its child and discharged its process
                // group before publishing this terminal result.
                messages.push(Message::TestFinished {
                    index,
                    result,
                    elapsed: start.elapsed(),
                    workload: captured,
                });
            });
        if let Err(error) = spawned {
            self.finish_test_action(
                build_runner,
                TestCompletion {
                    action,
                    result: Err(error.into()),
                    elapsed: start.elapsed(),
                    workload: None,
                },
            );
        }
    }

    pub(super) fn finish_test_action_by_index(
        &mut self,
        build_runner: &BuildRunner<'_, '_>,
        index: usize,
        result: CargoResult<()>,
        elapsed: Duration,
        workload: Option<crate::ops::cargo_test::workload::CapturedAction>,
    ) {
        let action = self.tests.as_ref().expect("test state").remaining[&index].clone();
        self.finish_test_action(
            build_runner,
            TestCompletion {
                action,
                result,
                elapsed,
                workload,
            },
        );
    }

    pub(super) fn finish_test_action(
        &mut self,
        build_runner: &BuildRunner<'_, '_>,
        mut completion: TestCompletion,
    ) {
        let tests = self.tests.as_mut().expect("test state");
        assert!(tests.active.remove(&completion.action.index));
        assert!(tests.remaining.remove(&completion.action.index).is_some());
        // The worker has finished, so what it saw is complete.
        if let Some(observed) = tests
            .watches
            .remove(&completion.action.index)
            .and_then(|watch| watch.take())
        {
            tests.run.observed.insert(completion.action.index, observed);
        }
        if completion.action.workload_action.is_some() {
            if let Some(outputs) = &tests.outputs {
                if let Err(error) = outputs.validate() {
                    completion.result = Err(error);
                    tests.stopped = true;
                }
            } else {
                tests.stopped = true;
            }
            let terminal = completion
                .workload
                .as_ref()
                .is_some_and(|capture| capture.native_terminal());
            if completion.result.is_ok() {
                completion.result = completion
                    .workload
                    .as_ref()
                    .ok_or_else(|| anyhow::anyhow!("native workload capture missing"))
                    .and_then(|capture| {
                        crate::ops::cargo_test::workload::validate_native(
                            completion.action.unit.target.name(),
                            completion.action.workload_action.expect("workload action"),
                            capture,
                            &mut tests.inventories,
                        )
                    });
            }
            // Failed discovery and unknown/interrupted delivery stop all later
            // nodes. A known failed sample remains in the complete population.
            tests.stopped |= !terminal
                || (matches!(
                    completion.action.workload_action,
                    Some(trust_test_execution::workload::Action::Inventory)
                ) && completion.result.is_err());
        }
        let failed = completion.result.is_err();
        tests.stopped |= failed && !tests.options.no_fail_fast;
        let action = completion.action.clone();
        let elapsed = completion.elapsed;
        let termination = Termination::of(&completion.result);
        // Preserve the actual result before any fallible observer sees it.
        tests.run.completed.push(completion);
        if let Some(workload) = &tests.options.workload {
            tests.stopped |= !tests.reporter.observe(&tests.signals, || {
                workload
                    .observer
                    .action_finished(tests.run.completed.last().expect("retained completion"))
            });
        }
        // Release the actions queued behind this one: the next in an ordered
        // run, and the next run of the same executable. A failure releases
        // them too unless it stopped the run; a node nothing waits on has no
        // edge to retire.
        if !tests.stopped {
            self.queue
                .finish(&QueueNode::Test(action.index), &Artifact::All);
        }
        self.emit_test_action(
            build_runner,
            &action,
            if failed {
                TestExecutionState::Failed
            } else {
                TestExecutionState::Passed
            },
            Some(elapsed),
            termination,
        );
    }

    pub(super) fn finish_test_graph(
        &mut self,
        build_runner: &BuildRunner<'_, '_>,
    ) -> Option<TestGraphRun> {
        let tests = self.tests.as_ref()?;
        assert!(
            tests.active.is_empty(),
            "test graph finalized before workers drained"
        );
        let blocked: Vec<_> = tests.remaining.values().cloned().collect();
        for action in &blocked {
            self.emit_test_action(
                build_runner,
                action,
                TestExecutionState::Blocked,
                None,
                Termination::default(),
            );
        }
        let mut tests = self.tests.take().expect("test state");
        tests.run.workload_outputs = tests.outputs.take();
        tests.run.blocked = blocked;
        #[cfg(any(target_os = "linux", target_os = "macos"))]
        if let Some(gate) = tests.retained.take()
            && let Err(error) = gate.retain_through_command_result(build_runner.bcx.gctx)
        {
            tests.reporter.error.get_or_insert(error);
        }
        tests.run.reporting_error = tests.reporter.error;
        if self.root_cancelled || tests.signals.interrupted() {
            // Trust: a stop of the plan's own says why itself.
            let stopped = crate::ops::cargo_test::plan_outcome::stopped();
            tests.run.interruption = Some(if let Some((_, why)) = stopped {
                why
            } else if self.root_cancelled {
                build_runner.bcx.gctx.root_cancellation_reason().to_owned()
            } else {
                "native test execution interrupted".to_owned()
            });
        }
        Some(tests.run)
    }
}

pub(super) fn observe_report(report: impl FnOnce() -> CargoResult<()>) -> CargoResult<()> {
    std::panic::catch_unwind(std::panic::AssertUnwindSafe(report))
        .unwrap_or_else(|_| Err(anyhow::anyhow!("native test execution observer panicked")))
}

#[cfg(all(test, any(target_os = "linux", target_os = "macos")))]
mod tests {
    use super::{CancelTestWorkers, observe_report};
    use cargo_util::{ProcessBuilder, StreamingOutputLimits, StreamingProcessScope};
    use std::sync::{Arc, mpsc};
    use std::time::{Duration, Instant};

    #[test]
    fn coordinator_unwind_cancels_a_live_test_before_scoped_join() {
        let signals = Arc::new(StreamingProcessScope::new().unwrap());
        let (ready, observed_ready) = mpsc::channel();
        let (finished, observed_finished) = mpsc::channel();
        let start = Instant::now();
        let unwound = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            std::thread::scope(|workers| {
                let _cancel = CancelTestWorkers::new(Some(&signals));
                let signals = signals.clone();
                workers.spawn(move || {
                    let mut command = ProcessBuilder::new("/bin/sh");
                    command.args(&["-c", "printf 'ready\\n'; exec sleep 10"]);
                    command.supervised_by(&signals);
                    let result = command.exec_with_streaming_limits(
                        &mut |line| {
                            if line == "ready" {
                                ready.send(()).unwrap();
                            }
                            Ok(())
                        },
                        &mut |_| Ok(()),
                        false,
                        StreamingOutputLimits::new(1024, 4096).with_child_exit_cleanup(),
                    );
                    finished.send(result.is_err()).unwrap();
                });
                observed_ready.recv_timeout(Duration::from_secs(5)).unwrap();
                panic!("coordinator failed while a real owned test is running");
            });
        }));
        assert!(unwound.is_err());
        assert!(observed_finished.try_recv().unwrap());
        assert!(start.elapsed() < Duration::from_secs(5));
        Arc::try_unwrap(signals).ok().unwrap().finish().unwrap();
    }

    #[test]
    fn observer_panics_remain_reporting_failures() {
        let error = observe_report(|| panic!("observer failed")).unwrap_err();
        assert!(error.to_string().contains("observer panicked"));
    }
}

// Trust: real owned peers and descendants exercise the production observer
// rejection gate without retaining the retired standalone test coordinator.
#[cfg(all(test, any(target_os = "linux", target_os = "macos")))]
mod observer_tests;
