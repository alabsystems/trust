//! Inventory and repeated samples in the original compilation queue.
//!
//! This graph plan is not native admission. The separately negotiated workload
//! root/output/foreign-phase owner is still required by the native executor;
//! ordinary SDK-bin and resolver profiles cannot dispatch produced artifacts.

use super::graph::{TestAction, TestCompletion, TestGraphOptions};
use crate::compiler::Compilation;
use crate::util::CargoResult;
use crate::workspace::TargetKind;
use cargo_util::{
    CaptureCompletionCause, CapturedProcess, ExecStats, ProcessBuilder, StreamingOutputLimits,
    StreamingProcessScope,
};
use std::sync::Arc;
use std::time::Duration;
use trust_test_execution::workload::{
    Action, Inventory, MAX_CAPTURE_BYTES, MAX_REPETITIONS, TARGETS,
};

#[cfg(unix)]
pub(crate) mod evidence;
mod inputs;
#[cfg(unix)]
pub(crate) use inputs::NativeOutput;
#[cfg(all(test, target_os = "macos", target_arch = "aarch64"))]
pub(crate) use inputs::actual_input_fixture;
pub(crate) use inputs::{Inputs, OwnedOutputs};
mod materialization;
pub(crate) use materialization::Materialization;

/// A continuation observer carries no execution authority. Its fallible ACK
/// only resumes the same live graph after the caller's full original-input
/// check; errors stop that graph and cancel its actually owned peers.
pub(crate) trait Observer: std::fmt::Debug + Send + Sync {
    fn compiler_message(
        &self,
        _run_id: &str,
        _message: &crate::util::log_message::LogMessage,
    ) -> std::io::Result<()> {
        Ok(())
    }
    fn synchronize_compiler_report(&self) -> std::io::Result<()> {
        Ok(())
    }
    fn compiler_retired(
        &self,
        compilation: &Compilation<'_>,
        succeeded: bool,
        outputs: Option<&OwnedOutputs>,
    ) -> CargoResult<()>;
    fn action_finished(&self, completion: &TestCompletion) -> CargoResult<()>;
}
struct CompilerReport(Arc<dyn Observer>);
impl crate::util::logger::native::Observer for CompilerReport {
    fn message(
        &self,
        run_id: &str,
        message: &crate::util::log_message::LogMessage,
    ) -> std::io::Result<()> {
        self.0.compiler_message(run_id, message)
    }
    fn synchronize(&self) -> std::io::Result<()> {
        self.0.synchronize_compiler_report()
    }
}
pub(crate) fn compiler_report(
    observer: Arc<dyn Observer>,
) -> Arc<dyn crate::util::logger::native::Observer> {
    Arc::new(CompilerReport(observer))
}

#[derive(Clone, Copy, Debug)]
pub(crate) struct Plan {
    repetitions: u32,
    timeout: Duration,
}
impl Plan {
    pub fn new(repetitions: u32, timeout: Duration) -> CargoResult<Self> {
        anyhow::ensure!(
            repetitions > 0
                && repetitions <= MAX_REPETITIONS
                && !timeout.is_zero()
                && u64::try_from(timeout.as_nanos()).is_ok(),
            "invalid finite native workload population/budget"
        );
        Ok(Self {
            repetitions,
            timeout,
        })
    }
}

/// Activation retains the original live input owners before compilation. This
/// still grants no native phase admission: the separately ready original root
/// and its actual host phase owner remain mandatory at every delivery.
#[derive(Clone, Debug)]
pub(crate) struct Options {
    pub plan: Plan,
    pub observer: Arc<dyn Observer>,
    pub inputs: Arc<Inputs>,
}
impl Options {
    pub fn graph(
        self,
        workspace: &crate::workspace::Workspace<'_>,
    ) -> CargoResult<TestGraphOptions> {
        Ok(TestGraphOptions {
            memory_limit: None,
            args: Vec::new(),
            no_fail_fast: true,
            required_bins: Vec::new(),
            limit: 1,
            retained: false,
            policy: super::harness_policy::HarnessPolicy::load(workspace, None, None)?,
            weight_refusal: Some("native workload requires its original one-credit phase"),
            workload: Some(self),
        })
    }
}

/// The one actual capture and owning-wait observation, retained on every
/// outcome. Wall is an orchestration interval, never substituted for target GO.
#[derive(Debug)]
pub(crate) struct CapturedAction {
    pub capture: CapturedProcess,
    pub stats: ExecStats,
}
impl CapturedAction {
    pub fn known_terminal(&self) -> bool {
        let c = &self.capture;
        let known_exit_error = c.failure.as_ref().is_none_or(|error| {
            c.status.is_some_and(|status| !status.success())
                && error.downcast_ref::<cargo_util::ProcessError>().is_some()
        });
        c.started
            && c.status.is_some()
            && c.complete()
            && c.read_error.is_none()
            && c.cleanup_error.is_none()
            && known_exit_error
            && c.owner_observation.is_none_or(|owner| {
                owner.retirement_confirmed && owner.cause == Some(CaptureCompletionCause::Exited)
            })
    }
    pub fn passed(&self) -> bool {
        self.known_terminal() && self.capture.status.is_some_and(|s| s.success())
    }
    pub fn native_terminal(&self) -> bool {
        self.known_terminal()
            && self.capture.owner_observation.is_some_and(|owner| {
                owner.retirement_confirmed
                    && owner.cause == Some(CaptureCompletionCause::Exited)
                    && owner.native_member_attempt.is_some()
            })
    }
}

/// Expand the exact real UnitOutput population. No JSON path selection,
/// recompilation, inferred target, or authenticated PreparedTests constructor.
pub(crate) fn expand(actions: Vec<TestAction>, options: &Plan) -> CargoResult<Vec<TestAction>> {
    anyhow::ensure!(
        actions.len() == TARGETS.len(),
        "native workload must compile exactly both consumer targets"
    );
    let mut selected = Vec::new();
    for target in TARGETS {
        let matches = actions
            .iter()
            .filter(|action| {
                action.unit.target.name() == target
                    && matches!(action.unit.target.kind(), TargetKind::Test)
            })
            .collect::<Vec<_>>();
        anyhow::ensure!(
            matches.len() == 1,
            "native workload target `{target}` is missing or ambiguous"
        );
        selected.push(matches[0]);
    }
    let mut expanded = Vec::new();
    for original in &selected {
        let mut action = (**original).clone();
        action.workload_action = Some(Action::Inventory);
        expanded.push(action);
    }
    for original in &selected {
        for repetition in 1..=options.repetitions {
            let mut action = (**original).clone();
            action.workload_action = Some(Action::Sample { repetition });
            expanded.push(action);
        }
    }
    let total = expanded.len();
    for (index, action) in expanded.iter_mut().enumerate() {
        action.index = index;
        action.total = total;
    }
    Ok(expanded)
}

pub(crate) fn configure(command: &mut ProcessBuilder, action: Action) {
    match action {
        Action::Inventory => {
            command.arg("--list");
        }
        Action::Sample { .. } => {
            command.arg("--test-threads=1");
        }
    }
}

pub(crate) fn execute(
    command: &ProcessBuilder,
    scope: &StreamingProcessScope,
    options: &Plan,
) -> CapturedAction {
    let mut command = command.clone();
    command.supervised_by(scope);
    let (stats, capture) = command.exec_with_capture_and_stats(
        StreamingOutputLimits::new(1024 * 1024, MAX_CAPTURE_BYTES)
            .with_timeout(options.timeout)
            .with_child_exit_cleanup(),
        true,
    );
    CapturedAction { capture, stats }
}

/// Interpret successful harness bytes only after actual capture. Unknown,
/// incomplete or interrupted execution stops further delivery. A known failed
/// sample remains a failed sample while later planned samples may proceed.
pub(crate) fn validate(
    target: &str,
    action: Action,
    captured: &CapturedAction,
    inventories: &mut std::collections::BTreeMap<String, Inventory>,
) -> CargoResult<()> {
    anyhow::ensure!(
        captured.known_terminal(),
        "native workload action lacks its complete original terminal/capture"
    );
    match action {
        Action::Inventory => {
            anyhow::ensure!(captured.passed(), "native workload inventory failed");
            let inventory =
                Inventory::parse(&captured.capture.stdout).map_err(anyhow::Error::msg)?;
            anyhow::ensure!(
                inventories.insert(target.into(), inventory).is_none(),
                "native workload inventory repeated"
            );
        }
        Action::Sample { .. } => {
            anyhow::ensure!(
                inventories.len() == TARGETS.len(),
                "native sample preceded complete inventory barrier"
            );
            anyhow::ensure!(
                captured.passed(),
                "native workload sample failed with {:?}",
                captured.capture.status
            );
            inventories
                .get(target)
                .ok_or_else(|| anyhow::anyhow!("sample target has no original inventory"))?
                .validate_sample(&captured.capture.stdout, &captured.capture.stderr)
                .map_err(anyhow::Error::msg)?;
        }
    }
    Ok(())
}

/// Production workload actions additionally require the original live native
/// owner's positive retirement. General byte/exit parsing alone cannot supply
/// that observation; local diagnostic actors keep their narrower meaning.
pub(crate) fn validate_native(
    target: &str,
    action: Action,
    captured: &CapturedAction,
    inventories: &mut std::collections::BTreeMap<String, Inventory>,
) -> CargoResult<()> {
    anyhow::ensure!(
        captured.native_terminal(),
        "workload action has no positively retired original native owner"
    );
    validate(target, action, captured, inventories)
}

#[cfg(all(test, any(target_os = "linux", target_os = "macos")))]
mod tests {
    use super::*;
    use std::collections::BTreeMap;
    use std::os::unix::process::ExitStatusExt as _;
    use std::process::ExitStatus;
    fn options() -> Plan {
        Plan::new(2, Duration::from_secs(60)).unwrap()
    }

    fn with_resolved_actions(check: impl FnOnce(Vec<TestAction>)) {
        use crate::compiler::unit_dependencies::IsArtifact;
        use crate::compiler::{CompileKind, CompileMode, UnitInterner};
        use crate::util::GlobalContext;
        use crate::workspace::{Workspace, profiles::Profile};
        use cargo_util_terminal::Shell;
        use std::rc::Rc;
        let temporary = tempfile::tempdir().unwrap();
        std::fs::create_dir(temporary.path().join("tests")).unwrap();
        for target in TARGETS {
            std::fs::write(
                temporary.path().join("tests").join(format!("{target}.rs")),
                "#[test] fn case() {}\n",
            )
            .unwrap();
        }
        let manifest = temporary.path().join("Cargo.toml");
        std::fs::write(
            &manifest,
            "[package]\nname='resolved-workload-fixture'\nversion='0.1.0'\nedition='2024'\n",
        )
        .unwrap();
        let mut gctx = GlobalContext::new(
            Shell::new(),
            temporary.path().into(),
            temporary.path().join("home"),
        );
        gctx.set_search_stop_path(temporary.path());
        gctx.set_env(Default::default());
        gctx.configure(0, false, None, false, false, true, &None, &[], &[])
            .unwrap();
        let workspace = Workspace::new(&manifest, &gctx).unwrap();
        let package = workspace.current().unwrap();
        let interner = UnitInterner::new();
        let mut actions = Vec::new();
        for target in package
            .targets()
            .iter()
            .filter(|target| matches!(target.kind(), TargetKind::Test))
        {
            let unit = interner.intern(
                package,
                target,
                Profile::default(),
                CompileKind::Host,
                CompileMode::Test,
                vec![],
                Rc::from(Vec::<String>::new()),
                Rc::from(Vec::<String>::new()),
                Rc::new(BTreeMap::new()),
                false,
                0,
                IsArtifact::No,
                None,
                false,
            );
            actions.push(TestAction {
                index: actions.len(),
                total: TARGETS.len(),
                unit,
                path: temporary.path().join("target").join(target.name()),
                args: Vec::new(),
                requests: Vec::new(),
                workload_action: None,
                weight: 1,
                exclusive: false,
                memory: 0,
                seconds: 0,
            });
        }
        check(actions);
    }

    #[test]
    fn resolved_unit_outputs_expand_once_with_all_discoveries_before_repeated_samples() {
        with_resolved_actions(|mut actions| {
            actions.reverse();
            let expanded = expand(actions.clone(), &options()).unwrap();
            assert_eq!(expanded.len(), 6);
            for (index, action) in expanded.iter().enumerate() {
                assert_eq!((action.index, action.total), (index, 6));
                let original = actions
                    .iter()
                    .find(|old| old.unit.target.name() == action.unit.target.name())
                    .unwrap();
                assert_eq!(action.unit, original.unit);
                assert_eq!(action.path, original.path);
            }
            assert_eq!(
                expanded[..2]
                    .iter()
                    .map(|a| a.workload_action)
                    .collect::<Vec<_>>(),
                vec![Some(Action::Inventory); 2]
            );
            assert_eq!(
                expanded[2..]
                    .iter()
                    .map(|a| (a.unit.target.name(), a.workload_action))
                    .collect::<Vec<_>>(),
                vec![
                    (TARGETS[0], Some(Action::Sample { repetition: 1 })),
                    (TARGETS[0], Some(Action::Sample { repetition: 2 })),
                    (TARGETS[1], Some(Action::Sample { repetition: 1 })),
                    (TARGETS[1], Some(Action::Sample { repetition: 2 }))
                ]
            );
            assert!(expand(vec![actions[0].clone()], &options()).is_err());
            assert!(expand(vec![actions[0].clone(), actions[0].clone()], &options()).is_err());
        });
    }
    #[test]
    fn actual_native_plan_maps_complete_paired_service_population() {
        use trust_resource_controller::paired_qualification::service::{Binding, Node, Registered};
        with_resolved_actions(|actions| {
            for repetitions in [1, 3, 32] {
                let expanded = expand(
                    actions.clone(),
                    &Plan::new(repetitions, Duration::from_secs(60)).unwrap(),
                )
                .unwrap();
                let mut observed = std::collections::BTreeSet::new();
                for action in expanded {
                    let node = crate::paired_service::harness_node(
                        action.unit.target.name(),
                        action
                            .workload_action
                            .expect("actual native expansion assigns every action"),
                    )
                    .unwrap();
                    let row = Registered {
                        binding: Binding {
                            root_attempt: [1; 16],
                            invocation_sha256: [2; 32],
                        },
                        node,
                        original_compile_unit: None,
                    };
                    row.encode(repetitions)
                        .expect("every actual native action must encode in the service population");
                    assert!(
                        observed.insert(node),
                        "actual expansion must not collapse a repetition"
                    );
                }
                let expected = Node::population(repetitions)
                    .unwrap()
                    .into_iter()
                    .filter(|node| matches!(node, Node::Inventory { .. } | Node::Sample { .. }))
                    .collect::<std::collections::BTreeSet<_>>();
                assert_eq!(observed, expected);
            }
            for repetition in [0, MAX_REPETITIONS + 1, u32::MAX] {
                assert!(
                    crate::paired_service::harness_node(TARGETS[0], Action::Sample { repetition })
                        .is_err()
                );
            }
            assert!(
                crate::paired_service::harness_node("unselected-target", Action::Inventory)
                    .is_err()
            );
        });
    }
    fn observed(stdout: &[u8]) -> CapturedAction {
        CapturedAction {
            capture: CapturedProcess {
                stdout: stdout.to_vec(),
                started: true,
                status: Some(ExitStatus::from_raw(0)),
                stdout_end: cargo_util::CaptureStreamEnd::Eof,
                stderr_end: cargo_util::CaptureStreamEnd::Eof,
                ..CapturedProcess::default()
            },
            stats: ExecStats::default(),
        }
    }
    const LIST: &[u8] = b"case_a: test\ncase_b: test\n\n2 tests, 0 benchmarks\n";
    const SAMPLE:&[u8]=b"test result: ok. 2 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 0.01s\n";

    #[test]
    fn full_inventory_barrier_and_original_denominator_apply_to_every_sample() {
        // Saved diagnostic bytes exercise parsing only, never admission.
        let mut inventories = BTreeMap::new();
        assert!(
            validate(
                TARGETS[0],
                Action::Sample { repetition: 1 },
                &observed(SAMPLE),
                &mut inventories
            )
            .is_err()
        );
        validate(
            TARGETS[0],
            Action::Inventory,
            &observed(LIST),
            &mut inventories,
        )
        .unwrap();
        assert!(
            validate(
                TARGETS[0],
                Action::Sample { repetition: 1 },
                &observed(SAMPLE),
                &mut inventories
            )
            .is_err()
        );
        validate(
            TARGETS[1],
            Action::Inventory,
            &observed(LIST),
            &mut inventories,
        )
        .unwrap();
        validate(
            TARGETS[0],
            Action::Sample { repetition: 1 },
            &observed(SAMPLE),
            &mut inventories,
        )
        .unwrap();
        assert!(validate(TARGETS[0],Action::Sample{repetition:2},&observed(
            b"test result: ok. 1 passed; 0 failed; 0 ignored; 0 measured; 1 filtered out; finished in 0.01s\n"),&mut inventories).is_err());
        assert!(
            validate(
                TARGETS[0],
                Action::Inventory,
                &observed(LIST),
                &mut inventories
            )
            .is_err()
        );
    }
    #[test]
    fn complete_saved_or_local_bytes_do_not_supply_native_owner_retirement() {
        let capture = observed(LIST);
        let mut inventories = BTreeMap::new();
        assert!(capture.known_terminal());
        assert!(!capture.native_terminal());
        assert!(
            validate_native(TARGETS[0], Action::Inventory, &capture, &mut inventories).is_err()
        );
        assert!(inventories.is_empty());
        // Even an actual locally waited child does not supply the distinct
        // native owner/GO observation needed by a production workload action.
        let scope = StreamingProcessScope::new().unwrap();
        let actual = execute(&ProcessBuilder::new("/usr/bin/true"), &scope, &options());
        assert!(actual.known_terminal());
        assert!(!actual.native_terminal());
        scope.finish().unwrap();
    }
    #[test]
    fn unknown_owner_or_streams_never_become_a_known_terminal_from_success_bytes() {
        for mode in 0..4 {
            let mut sample = observed(SAMPLE);
            match mode {
                0 => sample.capture.stdout_end = cargo_util::CaptureStreamEnd::LeaderExitDrained,
                1 => {
                    sample.capture.owner_observation = Some(cargo_util::CaptureOwnerObservation {
                        native_member_attempt: Some([11; 16]),
                        target_runtime: Some(Duration::ZERO),
                        cause: Some(CaptureCompletionCause::Exited),
                        retirement_confirmed: false,
                    })
                }
                2 => sample.capture.cleanup_error = Some("original cleanup unavailable".into()),
                3 => {
                    sample.capture.failure =
                        Some(anyhow::anyhow!("owner failed after receiving bytes"))
                }
                _ => unreachable!(),
            }
            assert!(!sample.known_terminal(), "mode {mode}");
        }
    }
    #[test]
    fn workload_plan_refuses_zero_or_unbounded_repetitions_and_target_budget() {
        for (repetitions, timeout) in [
            (0, Duration::from_secs(1)),
            (MAX_REPETITIONS + 1, Duration::from_secs(1)),
            (1, Duration::ZERO),
            (1, Duration::from_secs(u64::MAX)),
        ] {
            assert!(Plan::new(repetitions, timeout).is_err());
        }
        assert_eq!(options().repetitions, 2);
    }
    #[test]
    fn actual_native_failure_retains_known_status_bytes_and_same_wait_metrics() {
        // Actual OS child under the test's enclosing build-slot; this does not
        // qualify an Aterm produced-artifact purpose or sealed workload SDK.
        let scope = StreamingProcessScope::new().unwrap();
        let captured = execute(&ProcessBuilder::new("/usr/bin/false"), &scope, &options());
        assert!(
            captured.known_terminal() && !captured.passed(),
            "{:?}",
            captured.capture
        );
        assert_eq!(captured.capture.status.unwrap().code(), Some(1));
        assert!(captured.stats.cpu_times.is_some() && captured.stats.peak_rss.is_some());
        assert!(
            captured.capture.owner_observation.is_none(),
            "local wall is not native GO runtime"
        );
        scope.finish().unwrap();
    }
}
