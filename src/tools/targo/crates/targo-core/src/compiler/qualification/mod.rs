//! Compiler-owned advisory/strict actions, distinct from compile UnitIndex and
//! from proof-gated PreparedTests. Saved command data cannot construct this run.
use super::qualification_command::{FailedCommand, OriginalUnitCommand, Policy, UnitIdentity};
pub(crate) use super::resource_runtime::{ContinuedGraph, RetainedGraph};
pub(crate) mod subject;
use super::{BuildRunner, CompileKind, CompileMode, DefaultExecutor, Executor, Unit};
use crate::ops::cargo_test::workload::{CapturedAction, Inputs};
use crate::util::CargoResult;
use anyhow::{Context as _, ensure};
use cargo_util::{ProcessBuilder, StreamingOutputLimits, StreamingProcessScope};
use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex};
use std::time::Duration;
use trust_resource_controller::paired_qualification::PairedInvocation;

/// Every actual known compile outcome remains visible independently of the
/// next consumer's coverage. An unavailable continuation blocks new delivery;
/// it never reconstructs a runtime from the attempted result's data.
pub(crate) struct Attempt<'gctx> {
    pub result: CargoResult<()>,
    pub compilation: super::Compilation<'gctx>,
    pub continuation: Option<RetainedGraph>,
    pub continuation_failure: Option<String>,
}

/// Own verification indices; these never become compile timing/process rows.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, serde::Serialize)]
pub(crate) struct VerificationIndex(pub u64);
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Action {
    pub index: VerificationIndex,
    pub policy: Policy,
}
impl Action {
    pub(crate) const ALL: [Self; 2] = [
        Self {
            index: VerificationIndex(0),
            policy: Policy::Advisory,
        },
        Self {
            index: VerificationIndex(1),
            policy: Policy::Strict,
        },
    ];
}

/// Report methods observe data only; they cannot release a RootCreditBank
/// loan. The coordinator must still join actual workers and original waits.
pub(crate) trait Observer: Send + Sync {
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
    /// Called only after the existing compiler worker joins/bookkeeping. It
    /// never starts a second process under that original compile UnitIndex.
    fn compiler_retired(
        &self,
        _compilation: &super::Compilation<'_>,
        _succeeded: bool,
    ) -> CargoResult<()> {
        Ok(())
    }
    fn registered(&self, action: Action, compile_unit: &UnitIdentity) -> CargoResult<()>;
    fn scheduled(&self, action: Action) -> CargoResult<()>;
    /// Retain semantic/census failures as data so independent strict/consumer
    /// coverage may still run after a known outcome. Err is reporting/input
    /// binding/transport failure and stops subsequent delivery.
    fn completed(&self, completion: &Completion) -> CargoResult<()>;
    fn blocked(&self, action: Action, reason: &str) -> CargoResult<()>;
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
pub(crate) struct Completion {
    pub action: Action,
    pub capture: CapturedAction,
    pub elapsed: Duration,
    pub input_failure: Option<String>,
}
impl Completion {
    pub(crate) fn complete_observation(&self) -> bool {
        // A known signal/cancellation is retained but cannot complete a
        // verifier census, even if it happened after some TRUST_JSON bytes.
        self.input_failure.is_none()
            && self.capture.native_terminal()
            && self
                .capture
                .capture
                .status
                .is_some_and(|status| status.code().is_some())
    }
    #[cfg(test)]
    pub(crate) fn metrics_available(&self) -> bool {
        self.capture.stats.cpu_times.is_some() && self.capture.stats.peak_rss.is_some()
    }
}
#[derive(Default)]
pub(crate) struct Run {
    pub completed: Vec<Completion>,
    pub blocked: Vec<(Action, String)>,
    pub reporting_failure: Option<String>,
    /// Reporting/transport callback failure is distinct from a known failed
    /// verifier result: it may never open the next consumer's delivery.
    pub fatal_failure: Option<String>,
    /// Original current source/extern/SDK/output owners outlive both actions.
    pub original: Option<Arc<OriginalUnitCommand>>,
    pub original_failure: Option<String>,
    /// Failed captures retain their actual original input/command capsule as
    /// well. This owner has no successful materialization/policy replay API.
    pub failed_original: Option<Arc<FailedCommand>>,
    /// Same original precompile guards even when the selected unit failed.
    /// Custody only: these do not make any failed/missing output eligible.
    pub outputs: Option<Arc<super::build_runner::OriginalOutputLeases>>,
}

#[derive(Default)]
struct Slot {
    value: Mutex<Option<Result<Arc<OriginalUnitCommand>, Arc<FailedCommand>>>>,
}
impl super::qualification_command::Observer for Slot {
    fn completed(&self, command: Arc<OriginalUnitCommand>) -> CargoResult<()> {
        let mut original = self
            .value
            .lock()
            .map_err(|_| anyhow::anyhow!("original AY command owner poisoned"))?;
        ensure!(original.is_none(), "selected AY unit completed twice");
        *original = Some(Ok(command));
        Ok(())
    }
    fn failed(&self, command: FailedCommand) -> CargoResult<()> {
        let mut original = self
            .value
            .lock()
            .map_err(|_| anyhow::anyhow!("original AY command owner poisoned"))?;
        ensure!(original.is_none(), "selected AY unit outcome repeated");
        *original = Some(Err(Arc::new(command)));
        Ok(())
    }
}

pub(crate) struct Options {
    pub invocation: Arc<PairedInvocation>,
    pub inputs: Arc<Inputs>,
    pub observer: Arc<dyn Observer>,
    slot: Arc<Slot>,
}
impl Options {
    pub(crate) fn compiler_report(&self) -> Arc<dyn crate::util::logger::native::Observer> {
        Arc::new(CompilerReport(self.observer.clone()))
    }
    pub(crate) fn new(
        invocation: Arc<PairedInvocation>,
        inputs: Arc<Inputs>,
        observer: Arc<dyn Observer>,
    ) -> CargoResult<Arc<Self>> {
        let original = crate::resource_v3::paired::require(&invocation)?;
        let sink = original
            .workload_evidence
            .as_ref()
            .context("paired graph has no original writer")?;
        ensure!(
            Arc::ptr_eq(&inputs.evidence, sink),
            "paired graph cannot substitute its original input/evidence capsule"
        );
        inputs.validate()?;
        Ok(Arc::new(Self {
            invocation,
            inputs,
            observer,
            slot: Arc::new(Slot::default()),
        }))
    }
    pub(crate) fn validate_workspace(&self, build: &BuildRunner<'_, '_>) -> CargoResult<()> {
        use std::os::unix::ffi::OsStrExt as _;
        crate::resource_v3::paired::require(&self.invocation)?;
        self.inputs
            .validate_target(&build.bcx.ws.target_dir().into_path_unlocked())?;
        ensure!(
            build.native_resources() && crate::resource_worker_v3(),
            "paired compilation lost actual native dispatch"
        );
        ensure!(
            build.bcx.ws.root().as_os_str().as_bytes() == self.invocation.ay.root,
            "verification graph selected another AY workspace"
        );
        let selected = build
            .bcx
            .roots
            .iter()
            .filter(|unit| self.selects(unit))
            .count();
        ensure!(
            selected == 1 && build.bcx.roots.len() == 1,
            "native AY graph requires exactly its selected original library unit"
        );
        Ok(())
    }
    pub(super) fn selects(&self, unit: &Unit) -> bool {
        unit.mode == CompileMode::Build
            && unit.kind == CompileKind::Host
            && unit.target.is_lib()
            && !unit.target.proc_macro()
            && unit.pkg.name().as_str() == "ay-proof-common"
            && unit.pkg.manifest_path().as_os_str().as_encoded_bytes()
                == self.invocation.ay.crate_manifest.path
    }
    pub(crate) fn executor(self: &Arc<Self>) -> Arc<dyn Executor> {
        Arc::new(NativeExecutor(self.clone()))
    }
    pub(crate) fn original(&self) -> CargoResult<Arc<OriginalUnitCommand>> {
        let slot = self
            .slot
            .value
            .lock()
            .map_err(|_| anyhow::anyhow!("original AY command owner poisoned"))?;
        let value = slot.clone();
        drop(slot);
        match value {
            Some(Ok(command)) => {
                command.validate()?;
                require_unverified_baseline(command.original())?;
                Ok(command)
            }
            Some(Err(command)) => anyhow::bail!("original AY unit failed: {}", command.reason()),
            None => anyhow::bail!("original AY full unit outcome/command is missing"),
        }
    }
    pub(super) fn failed_original(&self) -> CargoResult<Option<Arc<FailedCommand>>> {
        let original = self
            .slot
            .value
            .lock()
            .map_err(|_| anyhow::anyhow!("original AY command owner poisoned"))?;
        Ok(original
            .as_ref()
            .and_then(|value| value.as_ref().err())
            .cloned())
    }
    /// A private path in the same actual output capsule, separate from Cargo
    /// fingerprints and each policy's metadata. Current-kernel proof artifacts
    /// may be reused by the compiler; no verdict is copied between policies.
    pub(crate) fn command(&self, action: Action) -> CargoResult<ProcessBuilder> {
        use std::ffi::OsString;
        use std::os::unix::ffi::OsStringExt as _;
        crate::resource_v3::paired::require(&self.invocation)?;
        self.inputs.validate()?;
        let root = PathBuf::from(OsString::from_vec(
            self.invocation.consumer.output_root.clone(),
        ));
        let paths = PolicyPaths::new(&root, self.invocation.consumer.invocation, action.policy);
        create_owned(&root, &paths.metadata)?;
        create_owned(&root, &paths.proof_artifacts)?;
        self.original()?.policy_command(
            action.policy,
            &paths.metadata,
            &paths.proof_artifacts,
            &paths.verification_session,
        )
    }
}
/// Locations only, never materialization, proof or execution authority. The
/// caller must retain its original output/input/runtime owners independently.
struct PolicyPaths {
    metadata: PathBuf,
    proof_artifacts: PathBuf,
    verification_session: String,
}
impl PolicyPaths {
    fn new(
        root: &Path,
        invocation: [u8; 16],
        policy: super::qualification_command::Policy,
    ) -> Self {
        let base = root.join(".trust-paired-qualification-v1");
        Self {
            metadata: base.join(hex::encode(invocation)).join(policy.name()),
            proof_artifacts: base.join("proof-artifacts"),
            verification_session: format!(
                "native-ay-{}-{}",
                hex::encode(invocation),
                policy.name()
            ),
        }
    }
}
fn create_owned(root: &Path, path: &Path) -> CargoResult<()> {
    ensure!(
        path.starts_with(root)
            && root.canonicalize()?.as_path() == root
            && path.components().all(|part| !matches!(
                part,
                std::path::Component::ParentDir | std::path::Component::CurDir
            )),
        "verification output escapes actual root"
    );
    if path != root
        && let Some(parent) = path.parent()
    {
        // Check existing ancestors too. A symlinked parent must be refused
        // before creating its child outside the original output capsule.
        create_owned(root, parent)?;
    }
    use std::os::unix::fs::DirBuilderExt as _;
    match std::fs::DirBuilder::new().mode(0o700).create(path) {
        Ok(()) => {}
        Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => {}
        Err(error) => return Err(error.into()),
    }
    ensure!(
        std::fs::symlink_metadata(path)?.is_dir() && path.canonicalize()?.as_path() == path,
        "verification output directory was replaced/aliased"
    );
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use cargo_util::{
        CaptureCompletionCause, CaptureOwnerObservation, CaptureStreamEnd, CapturedProcess,
        ExecStats,
    };
    use std::os::unix::process::ExitStatusExt as _;

    /// Classification data only: no startup, controller, candidate, execution
    /// grant or proof owner is constructed by these projection controls.
    fn observation() -> Completion {
        Completion {
            action: Action::ALL[1],
            capture: CapturedAction {
                capture: CapturedProcess {
                    started: true,
                    status: Some(std::process::ExitStatus::from_raw(0)),
                    stdout_end: CaptureStreamEnd::Eof,
                    stderr_end: CaptureStreamEnd::Eof,
                    owner_observation: Some(CaptureOwnerObservation {
                        native_member_attempt: Some([7; 16]),
                        target_runtime: Some(Duration::from_nanos(3)),
                        cause: Some(CaptureCompletionCause::Exited),
                        retirement_confirmed: true,
                    }),
                    ..CapturedProcess::default()
                },
                stats: ExecStats::default(),
            },
            elapsed: Duration::from_nanos(9),
            input_failure: None,
        }
    }
    #[test]
    fn known_bytes_and_measurement_completeness_are_independent() {
        let mut complete = observation();
        assert!(complete.complete_observation());
        assert!(!complete.metrics_available());
        complete.capture.stats.cpu_times = Some(cargo_util::CpuTimes {
            user: Duration::ZERO,
            system: Duration::ZERO,
        });
        complete.capture.stats.peak_rss = Some(0);
        assert!(complete.metrics_available());
        complete.input_failure = Some("original source drift".into());
        assert!(!complete.complete_observation());
        complete.input_failure = None;
        complete.capture.capture.status = Some(std::process::ExitStatus::from_raw(libc::SIGKILL));
        assert!(
            !complete.complete_observation(),
            "a signal cannot complete an AY verification census"
        );
        complete.capture.capture.status = Some(std::process::ExitStatus::from_raw(0));
        complete.capture.capture.owner_observation = None;
        assert!(
            !complete.complete_observation(),
            "local bytes cannot impersonate a native member"
        );
    }
    #[test]
    fn output_alias_or_parent_escape_refuses_before_creating_an_outside_directory() {
        let temporary = tempfile::tempdir().unwrap();
        let root = temporary.path().canonicalize().unwrap();
        let target = root.join("target");
        std::fs::create_dir(&target).unwrap();
        assert!(create_owned(&target, &target.join("../escaped")).is_err());
        assert!(!root.join("escaped").exists());
        std::os::unix::fs::symlink(&root, target.join("alias")).unwrap();
        assert!(create_owned(&target, &target.join("alias/child")).is_err());
        assert!(!root.join("child").exists());
        create_owned(&target, &target.join("actual/policy")).unwrap();
    }
    #[test]
    fn policy_paths_reuse_only_untrusted_artifacts_across_fresh_invocations() {
        use super::super::qualification_command::Policy;
        let temporary = tempfile::tempdir().unwrap();
        let root = temporary.path().canonicalize().unwrap();
        let first = PolicyPaths::new(&root, [1; 16], Policy::Advisory);
        create_owned(&root, &first.metadata).unwrap();
        create_owned(&root, &first.proof_artifacts).unwrap();
        let original = first.proof_artifacts.join("retained-untrusted-input.dat");
        std::fs::write(
            &original,
            b"untrusted artifact bytes; not a proof or a cached verdict",
        )
        .unwrap();
        let mut metadata = std::collections::BTreeSet::new();
        let mut sessions = std::collections::BTreeSet::new();
        for invocation in [[1; 16], [2; 16]] {
            for policy in Policy::ALL {
                let next = PolicyPaths::new(&root, invocation, policy);
                assert_eq!(
                    next.proof_artifacts, first.proof_artifacts,
                    "new native invocations must find the same original untrusted artifact cache"
                );
                assert!(metadata.insert(next.metadata.clone()));
                assert!(sessions.insert(next.verification_session.clone()));
                create_owned(&root, &next.metadata).unwrap();
                create_owned(&root, &next.proof_artifacts).unwrap();
                assert_eq!(
                    std::fs::read(&original).unwrap(),
                    b"untrusted artifact bytes; not a proof or a cached verdict"
                );
            }
        }
    }
    #[test]
    fn stable_artifact_locator_never_authorizes_an_aliased_cache_directory() {
        use super::super::qualification_command::Policy;
        let temporary = tempfile::tempdir().unwrap();
        let parent = temporary.path().canonicalize().unwrap();
        let root = parent.join("owned-output");
        let outside = parent.join("outside");
        std::fs::create_dir(&root).unwrap();
        std::fs::create_dir(&outside).unwrap();
        let paths = PolicyPaths::new(&root, [3; 16], Policy::Advisory);
        create_owned(&root, paths.proof_artifacts.parent().unwrap()).unwrap();
        std::os::unix::fs::symlink(&outside, &paths.proof_artifacts).unwrap();
        assert!(create_owned(&root, &paths.proof_artifacts).is_err());
        assert!(std::fs::read_dir(&outside).unwrap().next().is_none());
    }
    #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
    #[test]
    fn failed_original_capture_retains_actual_command_owner_without_successful_materialization() {
        let root = tempfile::tempdir().unwrap();
        let slot = Arc::new(Slot::default());
        let (capture, command, file) =
            super::super::qualification_command::command_fixture(root.path(), slot.clone());
        let pending = capture.pending(&command).unwrap();
        let observed =
            pending.failed("original admitted unit failed; no policy replay eligibility".into());
        super::super::qualification_command::Observer::failed(slot.as_ref(), observed).unwrap();
        drop(capture);
        drop(command);
        let original = slot.value.lock().unwrap();
        let failed = original.as_ref().unwrap().as_ref().unwrap_err();
        assert_eq!(
            failed.reason(),
            "original admitted unit failed; no policy replay eligibility"
        );
        assert_eq!(failed.unit().source, file);
        assert!(
            failed
                .original()
                .get_args()
                .any(|arg| arg == "--emit=dep-info,metadata,link")
        );
        assert!(failed.original().get_cwd().unwrap().join("lib.rs").exists());
    }
    #[test]
    fn baseline_checks_actual_argv_without_reading_cfg_payloads_as_options_or_spending_proofs() {
        let mut command = ProcessBuilder::new("/selected/bin/trustc");
        command.args(&[
            "src/lib.rs",
            "--cfg=literal -Ztrust-policy=certify in data",
            "-Z",
            "trust-verify=off",
        ]);
        require_unverified_baseline(&command).unwrap();
        for extra in [
            "-Ztrust-verify=on",
            "-Ztrust_verify=off",
            "-Ztrust-verify-level=2",
            "-Ztrust-ir-lower=strict",
            "-Ztrust-verify-include-dependencies=yes",
            "-Ztrust-policy=certify",
        ] {
            let mut changed = command.clone();
            changed.arg(extra);
            assert!(require_unverified_baseline(&changed).is_err(), "{extra}");
        }
        assert!(require_unverified_baseline(&ProcessBuilder::new("/selected/bin/trustc")).is_err());
    }
}
struct NativeExecutor(Arc<Options>);
impl Executor for NativeExecutor {
    fn unit_command_observer(
        &self,
        _build: &BuildRunner<'_, '_>,
        unit: &Unit,
    ) -> CargoResult<Option<Arc<dyn super::qualification_command::Observer>>> {
        Ok(self
            .0
            .selects(unit)
            .then(|| self.0.slot.clone() as Arc<dyn super::qualification_command::Observer>))
    }
    fn exec(
        &self,
        command: &ProcessBuilder,
        id: crate::workspace::PackageId,
        target: &crate::workspace::Target,
        mode: CompileMode,
        on_stdout: &mut dyn FnMut(&str) -> CargoResult<()>,
        on_stderr: &mut dyn FnMut(&str) -> CargoResult<()>,
        capture_rusage: bool,
    ) -> (cargo_util::ExecStats, CargoResult<()>) {
        if let Err(error) = require_unverified_baseline(command) {
            return (cargo_util::ExecStats::default(), Err(error));
        }
        DefaultExecutor.exec(
            command,
            id,
            target,
            mode,
            on_stdout,
            on_stderr,
            capture_rusage,
        )
    }
}

/// The base measurement must never spend another verification pass or inherit
/// the project's asserted certify/strict-IR flags. The fresh AY context selects
/// literal RUSTFLAGS=off; validate the actual finalized argv before delivery,
/// and validate warm commands before deriving either policy replay.
fn require_unverified_baseline(command: &ProcessBuilder) -> CargoResult<()> {
    let args = command.get_args().collect::<Vec<_>>();
    let mut index = 0;
    let mut off = false;
    while let Some(arg) = args.get(index) {
        let bytes = arg.as_encoded_bytes();
        let option = if bytes == b"-Z" {
            index += 1;
            Some(
                args.get(index)
                    .context("base compiler has incomplete -Z option")?
                    .as_encoded_bytes(),
            )
        } else {
            bytes
                .strip_prefix(b"-Z")
                .filter(|option| !option.is_empty())
        };
        if let Some(option) = option {
            let option =
                std::str::from_utf8(option).context("base compiler has a non-UTF8 control")?;
            let canonical = option.replace('_', "-");
            let name = canonical.split('=').next().unwrap_or("");
            if name == "trust-verify" && option == "trust-verify=off" {
                off = true;
            } else {
                ensure!(
                    !name.starts_with("trust-verify")
                        && !matches!(
                            name,
                            "trust-policy"
                                | "trust-ir-lower"
                                | "trust-proof-artifact-root"
                                | "no-trust-verify"
                        ),
                    "base AY compilation inherited a verification-policy control: {option}"
                );
            }
        }
        index += 1;
    }
    ensure!(
        off,
        "base AY compiler command lost its explicit verification-off measurement selection"
    );
    Ok(())
}

/// Called only by an admitted queue worker AFTER configuring this command
/// with its distinct actual original compiler RootContext. This function never
/// spawns a local fallback or borrows the original compilation's used loan.
pub(crate) fn execute(
    command: &ProcessBuilder,
    scope: &StreamingProcessScope,
    timeout: Duration,
) -> CapturedAction {
    let mut command = command.clone();
    command.supervised_by(scope);
    let (stats, capture) = command.exec_with_capture_and_stats(
        StreamingOutputLimits::new(1024 * 1024, 64 * 1024 * 1024)
            .with_timeout(timeout)
            .with_child_exit_cleanup(),
        true,
    );
    CapturedAction { capture, stats }
}
