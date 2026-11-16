//! The original Cargo command and input/output owners for native verification
//! nodes. A retained command is not a process or an execution grant.
use std::ffi::{OsStr, OsString};
use std::path::{Path, PathBuf};
use std::sync::Arc;
use std::time::{Duration, Instant};

use anyhow::{Context as _, bail, ensure};
use cargo_util::{PlatformInputs, ProcessBuilder};

use super::action_command::CommandInputs;
use super::action_inputs::SourceInputs;
use super::build_runner::OriginalOutputLeases;
use crate::ops::cargo_test::workload::Materialization;
use crate::util::CargoResult;
use trust_resource_controller::descriptors::AdmittedTargetSysroot;
#[cfg(all(test, target_os = "macos", target_arch = "aarch64"))]
use trust_resource_controller::descriptors::DescriptorBudget;
use trust_resource_provenance::program::HeldProgram;
#[cfg(all(test, target_os = "macos", target_arch = "aarch64"))]
use trust_resource_provenance::program::HeldRustTargetSysroot;

mod dependencies;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Policy {
    Advisory,
    Strict,
}
impl Policy {
    pub const ALL: [Self; 2] = [Self::Advisory, Self::Strict];
    pub fn name(self) -> &'static str {
        match self {
            Self::Advisory => "advisory",
            Self::Strict => "strict",
        }
    }
}

/// Closed native policy selection, not an admission or proof capability.
/// Legacy paired Strict retains its existing runtime-fallback behavior; a
/// native Certify node must request the compiler's actual full-discharge gate.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum NativePolicy {
    Advisory,
    Certify,
}
#[derive(Clone, Copy)]
enum CommandPolicy<'a> {
    Legacy(Policy),
    Native {
        policy: NativePolicy,
        package: &'a str,
        primary: bool,
    },
}
impl<'a> CommandPolicy<'a> {
    fn name(self) -> &'static str {
        match self {
            Self::Legacy(policy) => policy.name(),
            Self::Native {
                policy: NativePolicy::Advisory,
                ..
            } => "advisory",
            Self::Native {
                policy: NativePolicy::Certify,
                ..
            } => "certify",
        }
    }
    fn scope(self) -> Option<(&'a str, bool)> {
        match self {
            Self::Legacy(_) => None,
            Self::Native {
                package, primary, ..
            } => Some((package, primary)),
        }
    }
}

/// Optional native compilation observer. Requesting this observation does not
/// force a rebuild or permit execution. The original queue requires its live
/// precompile output custody and sends success only after the whole unit ends.
pub trait Observer: Send + Sync {
    fn completed(&self, command: Arc<OriginalUnitCommand>) -> CargoResult<()>;
    fn failed(&self, command: FailedCommand) -> CargoResult<()>;
}

/// Actual compile graph equality data, separate from any verification node's
/// index. Neither this value nor an index reconstructed from JSON is an owner.
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize)]
pub struct UnitIdentity {
    pub root_attempt: [u8; 16],
    pub invocation_sha256: [u8; 32],
    pub index: super::UnitIndex,
    pub unit_hash: String,
    pub package: String,
    pub target: String,
    pub source: PathBuf,
}
/// Scope equality DATA captured from the actual resolved Unit, never parsed
/// back from an argument string or a verifier's self-reported package label.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct UnitScope {
    pub package_name: String,
    pub crate_name: String,
    pub primary_package: bool,
}

#[cfg(any(target_os = "linux", target_os = "macos"))]
pub(super) fn unit_identity(
    build: &super::BuildRunner<'_, '_>,
    unit: &super::Unit,
) -> CargoResult<UnitIdentity> {
    let original =
        crate::resource_v3::current().context("unit identity has no original native root")?;
    let evidence = original
        .workload_evidence
        .as_ref()
        .context("unit identity lost original writer")?;
    Ok(UnitIdentity {
        root_attempt: original.query.binding.root_attempt,
        invocation_sha256: evidence.invocation_sha256(),
        index: build.bcx.unit_to_index[unit],
        unit_hash: build.files().unit_hash(unit),
        package: unit.pkg.package_id().to_string(),
        target: unit.target.name().to_owned(),
        source: unit
            .target
            .src_path()
            .path()
            .context("unit has no source path")?
            .to_owned(),
    })
}

/// Original attempted command retained on a failed unit. There is deliberately
/// no conversion into a successful materialization or verification admission.
pub struct FailedCommand {
    pending: PendingCommand,
    reason: String,
}
impl FailedCommand {
    pub fn unit(&self) -> &UnitIdentity {
        &self.pending.unit
    }
    pub fn original(&self) -> &ProcessBuilder {
        &self.pending.command
    }
    pub fn reason(&self) -> &str {
        &self.reason
    }
}

pub(super) struct Capture {
    pub(super) observer: Arc<dyn Observer>,
    source: Arc<SourceInputs>,
    platform: Arc<PlatformInputs>,
    outputs: Arc<OriginalOutputLeases>,
    output_root: PathBuf,
    compiler: Arc<HeldProgram>,
    sysroot: Arc<AdmittedTargetSysroot>,
    deadline: Instant,
    unit: UnitIdentity,
    scope: UnitScope,
    cargo_home: PathBuf,
    evidence: Option<Arc<crate::ops::cargo_test::workload::evidence::Evidence>>,
}

pub(super) struct Observation {
    capture: Arc<Capture>,
    command: Result<Arc<OriginalUnitCommand>, FailedCommand>,
}
impl Observation {
    pub(super) fn incomplete(capture: Arc<Capture>, pending: PendingCommand) -> Self {
        // A worker unwind cannot run potentially failing input IO or create a
        // successful materialization. Retain the attempted data as Unknown.
        Self {capture,command:Err(pending.failed("original worker ended before native materialization; outcome/input revalidation unknown".into()))}
    }
    pub(super) fn failure_reason(&self) -> Option<&str> {
        self.command.as_ref().err().map(FailedCommand::reason)
    }
    pub(super) fn finish(
        capture: Arc<Capture>,
        pending: PendingCommand,
        outcome: Result<Materialization, String>,
    ) -> Self {
        let outcome = match (outcome, pending.validate()) {
            (Ok(materialization), Ok(())) => Ok(materialization),
            (Err(error), Ok(())) => Err(error),
            (Ok(_), Err(drift)) => Err(format!("original command inputs changed: {drift:#}")),
            (Err(error), Err(drift)) => Err(format!(
                "{error}; original command inputs also changed: {drift:#}"
            )),
        };
        let command = match outcome {
            Ok(materialization) => Ok(Arc::new(OriginalUnitCommand {
                pending,
                materialization,
                scope: capture.scope.clone(),
                cargo_home: capture.cargo_home.clone(),
            })),
            Err(reason) => Err(pending.failed(reason)),
        };
        Self { capture, command }
    }
    pub(super) fn notify(self) -> CargoResult<()> {
        match self.command {
            Ok(command) => self.capture.observer.completed(command),
            Err(command) => self.capture.observer.failed(command),
        }
    }
}
impl Capture {
    #[cfg(not(all(target_os = "macos", target_arch = "aarch64")))]
    pub(super) fn for_unit(
        _build: &super::BuildRunner<'_, '_>,
        _unit: &super::Unit,
        _observer: Arc<dyn Observer>,
        _source: Option<Arc<SourceInputs>>,
        _platform: Option<Arc<PlatformInputs>>,
    ) -> CargoResult<Self> {
        bail!("native original compiler command capture is unsupported on this platform")
    }
    #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
    pub(super) fn for_unit(
        build: &super::BuildRunner<'_, '_>,
        unit: &super::Unit,
        observer: Arc<dyn Observer>,
        source: Option<Arc<SourceInputs>>,
        platform: Option<Arc<PlatformInputs>>,
    ) -> CargoResult<Self> {
        ensure!(
            unit.mode == super::CompileMode::Build
                && unit.kind == super::CompileKind::Host
                && unit.target.is_lib()
                && !unit.target.proc_macro()
                && !unit.target.is_custom_build(),
            "original verification command capture requires a normal native Rust library unit"
        );
        ensure!(
            build.bcx.rustc().wrapper.is_none() && build.bcx.rustc().workspace_wrapper.is_none(),
            "original verification command capture refuses custom compiler wrappers"
        );
        let startup = crate::resource_v3::current()
            .filter(|startup| startup.original_root && startup.workload_bank.is_some())
            .context("original command capture requires its actual native workload root")?;
        let process = startup
            .workload_process
            .as_ref()
            .context("original command capture lost actual compiler custody")?;
        let outputs = build.workload_output_leases()?;
        let evidence = startup
            .workload_evidence
            .as_ref()
            .context("original command capture lost its root/invocation binding")?;
        ensure!(
            crate::ops::cargo_test::workload::evidence::is_installed(evidence)
                && evidence.root_attempt() == startup.query.binding.root_attempt
                && startup.workload_bank.as_ref().is_some_and(
                    |bank| bank.binds(evidence.root_attempt(), evidence.invocation_sha256())
                ),
            "original command capture does not retain the installed root/bank/evidence owner"
        );
        Ok(Self {
            observer,
            source: match source {
                Some(source) => source,
                None => Arc::new(SourceInputs::capture(unit.pkg.root())?),
            },
            platform: match platform {
                Some(platform) => platform,
                None => Arc::new(PlatformInputs::capture()?),
            },
            outputs,
            output_root: build.bcx.ws.target_dir().into_path_unlocked(),
            compiler: process.compiler.clone(),
            sysroot: process.sysroot.clone(),
            deadline: process.deadline,
            unit: unit_identity(build, unit)?,
            scope: UnitScope {
                package_name: unit.pkg.name().to_string(),
                crate_name: unit.target.crate_name().to_string(),
                primary_package: build.bcx.roots.contains(unit),
            },
            cargo_home: build.bcx.gctx.home().as_path_unlocked().to_owned(),
            evidence: Some(evidence.clone()),
        })
    }
    pub(super) fn pending(&self, command: &ProcessBuilder) -> CargoResult<PendingCommand> {
        let pending = PendingCommand::capture(
            command,
            self.source.clone(),
            self.platform.clone(),
            self.outputs.clone(),
            self.output_root.clone(),
            self.compiler.clone(),
            self.sysroot.clone(),
            self.deadline,
            self.unit.clone(),
        )?;
        if let Some(evidence) = &self.evidence {
            evidence.publish_original_command(
                self.unit.root_attempt,
                self.unit.invocation_sha256,
                self.unit.index.0,
                pending.inputs.digest(),
                &pending.data_record()?,
            )?;
        }
        Ok(pending)
    }
}

/// Captured directly after native Cargo command finalization, before any
/// per-attempt resource injection. It cannot become eligible after a failed
/// unit or from a saved command/freshness record.
pub(crate) struct PendingCommand {
    command: ProcessBuilder,
    source: Arc<SourceInputs>,
    inputs: CommandInputs,
    platform: Arc<PlatformInputs>,
    outputs: Arc<OriginalOutputLeases>,
    output_root: PathBuf,
    compiler: Arc<HeldProgram>,
    sysroot: Arc<AdmittedTargetSysroot>,
    dependencies: dependencies::Inputs,
    deadline: Instant,
    unit: UnitIdentity,
}
impl std::fmt::Debug for PendingCommand {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("PendingCommand")
            .field("program", &self.command.get_program())
            .field("output_root", &self.output_root)
            .finish_non_exhaustive()
    }
}
impl PendingCommand {
    fn data_record(&self) -> CargoResult<Vec<u8>> {
        let environment=self.inputs.environment().iter().map(|(name,value)| {
            let protected=matches!(name.as_encoded_bytes(),b"ATERM_RESOURCE_JOB_V3"|b"TRUST_CPU_HANDOFF"|b"TRUST_JOBSERVER_HANDOFF"|b"CARGO_JOBSERVER_HANDOFF");
            serde_json::json!({"name_hex":hex::encode(name.as_encoded_bytes()),"value_hex":if protected{None}else{Some(hex::encode(value.as_encoded_bytes()))},"private_transport_omitted":protected})
        }).collect::<Vec<_>>();
        let bytes = serde_json::to_vec(&serde_json::json!({
            "schema":"trust.original-unit-command-observation.v1",
            "scope":"observed pre-resource-injection ProcessBuilder inputs only; no kernel environment attestation, materialization, member, proof or execution authority",
            "unit":self.unit,"command_digest":self.inputs.digest(),"source_digest":self.source.digest(),
            "platform_image":self.platform.digest(),"platform_binding":self.platform.binding(),
            "compiler_input_sha256":self.compiler.observation().executable.sha256,
            "program_hex":hex::encode(self.command.get_program().as_encoded_bytes()),
            "cwd_hex":self.command.get_cwd().map(|path|hex::encode(path.as_os_str().as_encoded_bytes())),
            "args_hex":self.command.get_args().map(|arg|hex::encode(arg.as_encoded_bytes())).collect::<Vec<_>>(),
            "environment":environment,"extern_inputs":self.dependencies.data(),
            "native_member_attempt":null,"materialization":"not-observed"
        }))?;
        ensure!(
            bytes.len() <= 4 * 1024 * 1024,
            "original command observation exceeds its durable bound"
        );
        Ok(bytes)
    }
    pub(crate) fn capture(
        command: &ProcessBuilder,
        source: Arc<SourceInputs>,
        platform: Arc<PlatformInputs>,
        outputs: Arc<OriginalOutputLeases>,
        output_root: PathBuf,
        compiler: Arc<HeldProgram>,
        sysroot: Arc<AdmittedTargetSysroot>,
        deadline: Instant,
        unit: UnitIdentity,
    ) -> CargoResult<Self> {
        source.ensure_current()?;
        platform.ensure_current()?;
        outputs.validate(&output_root)?;
        compiler.validate(deadline.min(Instant::now() + Duration::from_secs(20)))?;
        ensure!(
            command.get_program() == compiler.program().as_os_str() && command.get_arg0().is_none(),
            "native original command does not select its actual held SDK compiler"
        );
        ensure!(
            !command.has_action_sandbox(),
            "native verification command cannot replace a confined compiler action"
        );
        validate_target_command(&sysroot, &compiler, command, deadline)?;
        let inputs = CommandInputs::capture_native(command)?;
        let dependencies = dependencies::Inputs::capture(command, deadline)?;
        Ok(Self {
            command: command.clone(),
            source,
            inputs,
            platform,
            outputs,
            output_root,
            compiler,
            sysroot,
            dependencies,
            deadline,
            unit,
        })
    }
    fn validate(&self) -> CargoResult<()> {
        self.source.ensure_current()?;
        self.platform.ensure_current()?;
        self.outputs.validate(&self.output_root)?;
        self.compiler
            .validate(self.deadline.min(Instant::now() + Duration::from_secs(20)))?;
        validate_target_command(&self.sysroot, &self.compiler, &self.command, self.deadline)?;
        self.dependencies.validate(self.deadline)?;
        self.inputs.ensure_matches(&self.command)?;
        ensure!(
            Instant::now() < self.deadline,
            "original command input validation exceeded original deadline"
        );
        Ok(())
    }
    pub(super) fn failed(self, reason: String) -> FailedCommand {
        FailedCommand {
            pending: self,
            reason,
        }
    }
}

fn validate_target_command(
    sysroot: &Arc<AdmittedTargetSysroot>,
    compiler: &Arc<HeldProgram>,
    command: &ProcessBuilder,
    deadline: Instant,
) -> CargoResult<()> {
    let actual = command.build_command();
    let args = actual
        .get_args()
        .map(|arg| arg.as_encoded_bytes().to_vec())
        .collect::<Vec<_>>();
    let environment = command
        .get_effective_envs()?
        .into_iter()
        .map(|(key, value)| {
            (
                key.as_encoded_bytes().to_vec(),
                value.as_encoded_bytes().to_vec(),
            )
        })
        .collect::<Vec<_>>();
    sysroot.validate_invocation(
        compiler,
        actual.get_program().as_encoded_bytes(),
        command.get_arg0().map(OsStr::as_encoded_bytes),
        &args,
        &environment,
        deadline,
    )?;
    Ok(())
}

/// NonClone original input/output custody shared only through a live Arc.
/// These guards do not authorize a replay: each native verification action
/// still needs the original root's current actual admission and owning wait.
#[derive(Debug)]
pub struct OriginalUnitCommand {
    pending: PendingCommand,
    materialization: Materialization,
    scope: UnitScope,
    cargo_home: PathBuf,
}
impl OriginalUnitCommand {
    /// Actual resolved configuration DATA, not directory/write authority.
    pub fn cargo_home(&self) -> &Path {
        &self.cargo_home
    }
    pub fn scope(&self) -> &UnitScope {
        &self.scope
    }
    pub fn unit(&self) -> &UnitIdentity {
        &self.pending.unit
    }
    pub fn command_digest(&self) -> &str {
        self.pending.inputs.digest()
    }
    pub fn validate(&self) -> CargoResult<()> {
        self.pending.validate()
    }
    pub fn original(&self) -> &ProcessBuilder {
        &self.pending.command
    }
    pub fn producer_attempt(&self) -> Option<[u8; 16]> {
        self.materialization.producer_attempt()
    }
    /// Derive the policy command from the SAME successfully materialized
    /// compiler inputs and a live fresh session. These owners supply neither
    /// CPU admission nor kernel acceptance; the native caller retains its
    /// original resource/output owners through capture and retirement.
    pub(crate) fn native_policy_command(
        &self,
        policy: NativePolicy,
        metadata: &trust_proof_session::MetadataDirectory,
        session: &trust_proof_session::VerificationSession,
    ) -> CargoResult<ProcessBuilder> {
        self.validate()?;
        session.check_current()?;
        metadata.check_current()?;
        ensure!(
            self.producer_attempt().is_some()
                && metadata.path().parent() == Some(session.artifact_root()),
            "native policy session differs from the actual compiler prerequisite"
        );
        let scope = self.scope();
        let command = self.policy_command_scoped(
            CommandPolicy::Native {
                policy,
                package: &scope.package_name,
                primary: scope.primary_package,
            },
            metadata.path(),
            session.artifact_root(),
            session.id(),
        )?;
        metadata.check_current()?;
        session.check_current()?;
        self.validate()?;
        Ok(command)
    }
    pub fn policy_command(
        &self,
        policy: Policy,
        output: &Path,
        artifacts: &Path,
        session: &str,
    ) -> CargoResult<ProcessBuilder> {
        self.policy_command_scoped(CommandPolicy::Legacy(policy), output, artifacts, session)
    }
    fn policy_command_scoped(
        &self,
        policy: CommandPolicy<'_>,
        output: &Path,
        artifacts: &Path,
        session: &str,
    ) -> CargoResult<ProcessBuilder> {
        self.validate()?;
        ensure!(
            output.is_absolute()
                && output.starts_with(&self.pending.output_root)
                && artifacts.is_absolute()
                && artifacts.starts_with(&self.pending.output_root),
            "verification outputs escape the original retained output capsule"
        );
        for path in [output, artifacts] {
            ensure!(
                path.components().all(|component| !matches!(
                    component,
                    std::path::Component::ParentDir | std::path::Component::CurDir
                )),
                "verification output path is not normalized"
            );
            let mut ancestor = path;
            while !ancestor.exists() {
                ancestor = ancestor
                    .parent()
                    .context("verification output has no existing ancestor")?;
            }
            ensure!(
                ancestor.canonicalize()? == ancestor,
                "verification output traverses a substituted directory"
            );
        }
        ensure!(
            !session.is_empty()
                && session.len() <= 128
                && session
                    .bytes()
                    .all(|b| b.is_ascii_alphanumeric() || b == b'-'),
            "invalid native verification session binding"
        );
        let args = policy_arguments_scoped(
            self.pending.command.get_args().map(OsString::as_os_str),
            policy,
            output,
            artifacts,
            session,
        )?;
        let mut command = self.pending.command.clone();
        command.args_replace(&args);
        Ok(command)
    }
}

/// Preserve the captured Cargo compiler/extern/cfg/lint inputs. Only the
/// explicitly owned verification controls, diagnostic transport, incremental
/// directory and metadata destination change. No argv is recovered from text.
#[cfg(test)]
fn policy_arguments<'a>(
    original: impl Iterator<Item = &'a OsStr>,
    policy: Policy,
    output: &Path,
    artifacts: &Path,
    session: &str,
) -> CargoResult<Vec<OsString>> {
    policy_arguments_scoped(
        original,
        CommandPolicy::Legacy(policy),
        output,
        artifacts,
        session,
    )
}
fn policy_arguments_scoped<'a>(
    original: impl Iterator<Item = &'a OsStr>,
    policy: CommandPolicy<'_>,
    output: &Path,
    artifacts: &Path,
    session: &str,
) -> CargoResult<Vec<OsString>> {
    let scope = policy.scope();
    let original = original.map(OsStr::to_os_string).collect::<Vec<_>>();
    ensure!(
        original.len() <= 65_536,
        "excessive original compiler arguments"
    );
    ensure!(
        original
            .iter()
            .all(|arg| !arg.as_encoded_bytes().starts_with(b"@")),
        "verification command refuses response-file substitution"
    );
    let mut args = Vec::new();
    let mut at = 0;
    let mut emitted = false;
    let mut out_dir = false;
    let owned = |option: &str| -> CargoResult<bool> {
        let name = option.split('=').next().unwrap_or(option).replace('_', "-");
        Ok((scope.is_some()
            && matches!(
                name.as_str(),
                "trust-verify-package-name"
                    | "trust-verify-crate-role"
                    | "trust-proc-macro-boundary"
            ))
            || owned_z(option)?)
    };
    while let Some(arg) = original.get(at) {
        ensure!(
            !arg.as_encoded_bytes().starts_with(b"@"),
            "verification command refuses response-file substitution"
        );
        let text = arg.to_str();
        let next = || {
            original
                .get(at + 1)
                .context("incomplete original compiler option")
        };
        match text {
            Some("-v" | "--verbose") => at += 1,
            Some("-Z") => {
                let option = next()?.to_str().context("non-UTF8 verification control")?;
                if !owned(option)? {
                    args.extend([arg.clone(), next()?.clone()]);
                }
                at += 2;
            }
            Some(value) if value.starts_with("-Z") && value.len() > 2 => {
                if !owned(&value[2..])? {
                    args.push(arg.clone());
                }
                at += 1;
            }
            Some("-C") => {
                if !next()?.as_encoded_bytes().starts_with(b"incremental=") {
                    args.extend([arg.clone(), next()?.clone()]);
                }
                at += 2;
            }
            Some(value) if value.starts_with("-Cincremental=") => at += 1,
            Some("--emit") => {
                next()?;
                ensure!(!emitted, "multiple original emit destinations");
                args.push("--emit=metadata".into());
                emitted = true;
                at += 2;
            }
            Some(value) if value.starts_with("--emit=") => {
                ensure!(!emitted, "multiple original emit destinations");
                args.push("--emit=metadata".into());
                emitted = true;
                at += 1;
            }
            Some("--error-format" | "--json") => {
                next()?;
                at += 2;
            }
            Some(value) if value.starts_with("--error-format=") || value.starts_with("--json=") => {
                at += 1
            }
            Some("--out-dir") => {
                next()?;
                ensure!(!out_dir, "multiple original output directories");
                args.extend(["--out-dir".into(), output.as_os_str().into()]);
                out_dir = true;
                at += 2;
            }
            Some(value) if value.starts_with("--out-dir=") => {
                ensure!(!out_dir, "multiple original output directories");
                args.extend(["--out-dir".into(), output.as_os_str().into()]);
                out_dir = true;
                at += 1;
            }
            _ => {
                args.push(arg.clone());
                at += 1;
            }
        }
    }
    ensure!(
        emitted && out_dir,
        "native Cargo command lacks its explicit emit/output identity"
    );
    for control in [
        "trust-verify=on",
        "trust-verify-level=2",
        "trust-verify-profile=unix_hardened",
        "trust-verify-timeout-ms=5000",
        "trust-verify-function-budget-ms=120000",
        "trust-verify-output=both",
    ] {
        args.extend(["-Z".into(), control.into()]);
    }
    for (name, value) in [
        (
            "trust-proof-artifact-root",
            artifacts.as_os_str().to_os_string(),
        ),
        ("trust-policy", policy.name().into()),
        ("trust-verify-session", session.into()),
    ] {
        let mut control = OsString::from(name);
        control.push("=");
        control.push(value);
        args.extend(["-Z".into(), control]);
    }
    if let Some((package, primary)) = scope {
        ensure!(
            !package.is_empty(),
            "native unit has no actual package scope"
        );
        // These fields come from the original actual Unit, never argv or a
        // transport claim. Native capture supports only ordinary lib Build;
        // the real queue separately vetoes the full proc-macro graph closure.
        args.extend(
            super::trust_unit_metadata_args(false, primary, package)
                .into_iter()
                .map(OsString::from),
        );
        args.extend(["-Z".into(), "trust-proc-macro-boundary".into()]);
    }
    Ok(args)
}
fn owned_z(option: &str) -> CargoResult<bool> {
    let name = option.split('=').next().unwrap_or(option).replace('_', "-");
    if name == "trust-verify-ay-path" {
        bail!(
            "legacy external solver configuration requires its own supported native SDK contract"
        );
    }
    Ok(matches!(
        name.as_str(),
        "trust-verify"
            | "trust-policy"
            | "trust-verify-level"
            | "trust-verify-profile"
            | "trust-verify-timeout-ms"
            | "trust-verify-function-budget-ms"
            | "trust-verify-output"
            | "trust-verify-session"
            | "trust-proof-artifact-root"
    ))
}

/// Actual held native input + original Layout actor for data/custody controls.
/// It is not a managed SDK, host, compile or verification admission fixture.
#[cfg(all(test, target_os = "macos", target_arch = "aarch64"))]
pub(in crate::compiler) fn command_fixture(
    parent: &Path,
    observer: Arc<dyn Observer>,
) -> (Arc<Capture>, ProcessBuilder, PathBuf) {
    let root = parent.canonicalize().unwrap();
    let source = root.join("source");
    std::fs::create_dir(&source).unwrap();
    let file = source.join("lib.rs");
    std::fs::write(&file, "pub fn original() {}\n").unwrap();
    let layout = root.join("layout");
    std::fs::create_dir(&layout).unwrap();
    let outputs = Arc::new(OriginalOutputLeases::actual_layout_fixture(&layout));
    let output_root = layout.join("target");
    let image = root.join("native-image");
    std::fs::create_dir_all(image.join("bin")).unwrap();
    std::fs::create_dir_all(image.join("lib/rustlib/aarch64-apple-darwin/lib")).unwrap();
    std::fs::write(
        image.join("lib/rustlib/aarch64-apple-darwin/lib/resource-input"),
        b"original target input",
    )
    .unwrap();
    let program = super::native_input_fixture::materialize(&image);
    let mut hash = cargo_util::Sha256::new();
    hash.update_path(&program).unwrap();
    let deadline = Instant::now() + Duration::from_secs(60);
    let compiler = Arc::new(HeldProgram::open(&image, &program, &hash.finish(), deadline).unwrap());
    let plan = HeldRustTargetSysroot::plan(compiler.clone(), deadline).unwrap();
    let descriptors = DescriptorBudget::for_preparation(1, 0).unwrap();
    let sysroot = descriptors.capture_target(plan, deadline).unwrap();
    let cache = root.join("cache");
    std::fs::create_dir(&cache).unwrap();
    let capture = Arc::new(Capture {
        observer,
        source: Arc::new(
            SourceInputs::capture_admitted(&source, &descriptors, deadline, &layout, &cache)
                .unwrap(),
        ),
        platform: Arc::new(PlatformInputs::capture().unwrap()),
        outputs,
        output_root: output_root.clone(),
        compiler,
        sysroot,
        deadline,
        unit: UnitIdentity {
            root_attempt: [1; 16],
            invocation_sha256: [2; 32],
            index: super::UnitIndex(3),
            unit_hash: "0000000000000004".into(),
            package: "native-input-fixture".into(),
            target: "original-command".into(),
            source: file.clone(),
        },
        scope: UnitScope {
            package_name: "native-input-fixture".into(),
            crate_name: "original_command".into(),
            primary_package: true,
        },
        cargo_home: root.to_owned(),
        evidence: None,
    });
    let mut command = ProcessBuilder::new(program);
    let empty =
        cargo_util::EnvironmentInputs::capture_for(&ProcessBuilder::new("unused"), &[]).unwrap();
    command.cwd(&source).environment_snapshot(empty).args(&[
        OsStr::new("lib.rs"),
        OsStr::new("--sysroot"),
        image.as_os_str(),
        OsStr::new("--emit=dep-info,metadata,link"),
        OsStr::new("--out-dir"),
        output_root.as_os_str(),
    ]);
    (capture, command, file)
}

#[cfg(test)]
mod tests {
    use super::*;
    #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
    #[test]
    fn actual_original_command_data_preserves_native_values_and_omits_private_transport() {
        struct Unused;
        impl Observer for Unused {
            fn completed(&self, _: Arc<OriginalUnitCommand>) -> CargoResult<()> {
                unreachable!()
            }
            fn failed(&self, _: FailedCommand) -> CargoResult<()> {
                unreachable!()
            }
        }
        let root = tempfile::tempdir().unwrap();
        let (capture, mut command, _) = command_fixture(root.path(), Arc::new(Unused));
        command
            .arg("--cfg=literal spaces and @ in data")
            .env("ATERM_RESOURCE_JOB_V3", "private-original-capability");
        let pending = capture.pending(&command).unwrap();
        let bytes = pending.data_record().unwrap();
        let record: serde_json::Value = serde_json::from_slice(&bytes).unwrap();
        assert!(
            record["args_hex"]
                .as_array()
                .unwrap()
                .contains(&serde_json::json!(hex::encode(
                    b"--cfg=literal spaces and @ in data"
                )))
        );
        assert!(record["native_member_attempt"].is_null());
        assert_eq!(record["materialization"], "not-observed");
        assert!(
            !String::from_utf8(bytes.clone())
                .unwrap()
                .contains(&hex::encode(b"private-original-capability"))
        );
        let environment = record["environment"].as_array().unwrap();
        let omitted = environment
            .iter()
            .find(|row| row["name_hex"] == hex::encode(b"ATERM_RESOURCE_JOB_V3"))
            .unwrap();
        assert_eq!(omitted["private_transport_omitted"], true);
        assert!(omitted["value_hex"].is_null());
    }
    #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
    #[test]
    fn failed_original_command_retains_target_bytes_that_loader_custody_does_not_cover() {
        struct Unused;
        impl Observer for Unused {
            fn completed(&self, _: Arc<OriginalUnitCommand>) -> CargoResult<()> {
                unreachable!()
            }
            fn failed(&self, _: FailedCommand) -> CargoResult<()> {
                unreachable!()
            }
        }
        let root = tempfile::tempdir().unwrap();
        let (capture, command, _) = command_fixture(root.path(), Arc::new(Unused));
        let pending = capture.pending(&command).unwrap();
        let weak = Arc::downgrade(&capture.sysroot);
        drop(capture);
        let input = pending
            .compiler
            .root()
            .join("lib/rustlib/aarch64-apple-darwin/lib/resource-input");
        std::fs::write(&input, b"mutated target input!").unwrap();
        pending.compiler.validate(pending.deadline).unwrap();
        assert!(
            pending.validate().is_err(),
            "actual target data mutation lies beyond the executable/loader closure"
        );
        let failed = pending.failed("original target changed".into());
        assert!(
            weak.upgrade().is_some(),
            "failed commands retain the SAME original target owner"
        );
        assert_eq!(failed.original().get_program(), command.get_program());
        drop(failed);
        assert!(weak.upgrade().is_none());
    }

    #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
    #[test]
    fn failed_original_command_keeps_native_package_ownership_after_namespace_drift() {
        struct Unused;
        impl Observer for Unused {
            fn completed(&self, _: Arc<OriginalUnitCommand>) -> CargoResult<()> {
                unreachable!()
            }
            fn failed(&self, _: FailedCommand) -> CargoResult<()> {
                unreachable!()
            }
        }
        let root = tempfile::tempdir().unwrap();
        let (capture, command, file) = command_fixture(root.path(), Arc::new(Unused));
        let pending = capture.pending(&command).unwrap();
        let source = Arc::downgrade(&capture.source);
        drop(capture);
        // The actual finalized command still holds SAME original source, SDK,
        // target and Layout owners; no process was launched by this control.
        pending.validate().unwrap();
        let new = file.parent().unwrap().join("absent.rs");
        std::fs::write(&new, b"new negative lookup").unwrap();
        assert!(pending.validate().is_err());
        std::fs::remove_file(new).unwrap();
        assert!(pending.validate().is_err());
        let failed = pending.failed("original package changed".into());
        assert!(
            source.upgrade().is_some(),
            "actual failed command keeps original source capsule"
        );
        assert_eq!(failed.original().get_program(), command.get_program());
        drop(failed);
        assert!(source.upgrade().is_none());
    }

    #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
    #[test]
    fn equal_image_data_cannot_substitute_an_independently_opened_compiler_owner() {
        struct Unused;
        impl Observer for Unused {
            fn completed(&self, _: Arc<OriginalUnitCommand>) -> CargoResult<()> {
                unreachable!()
            }
            fn failed(&self, _: FailedCommand) -> CargoResult<()> {
                unreachable!()
            }
        }
        let root = tempfile::tempdir().unwrap();
        let (capture, command, _) = command_fixture(root.path(), Arc::new(Unused));
        let mut hash = cargo_util::Sha256::new();
        hash.update_path(capture.compiler.program()).unwrap();
        let substitute = Arc::new(
            HeldProgram::open(
                capture.compiler.root(),
                capture.compiler.program(),
                &hash.finish(),
                capture.deadline,
            )
            .unwrap(),
        );
        assert!(
            validate_target_command(
                &capture.sysroot,
                &capture.compiler,
                &command,
                capture.deadline
            )
            .is_ok()
        );
        assert!(
            validate_target_command(&capture.sysroot, &substitute, &command, capture.deadline)
                .is_err()
        );
        assert!(
            capture.sysroot.validate(capture.deadline).is_err(),
            "a later equal-byte success cannot clear failed original-owner binding"
        );
    }

    #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
    #[test]
    fn native_shared_target_admission_materializes_507_original_files_or_refuses_actual_hard_limit()
    {
        const MODE: &str = "TRUST_NATIVE_TARGET_ADMISSION_ACTOR";
        const TEST: &str = "compiler::qualification_command::tests::native_shared_target_admission_materializes_507_original_files_or_refuses_actual_hard_limit";
        #[expect(
            clippy::disallowed_methods,
            reason = "isolated actual descriptor actor selects only its native limit test mode"
        )]
        let mode = std::env::var(MODE).ok();
        let Some(mode) = mode else {
            use std::io::Read as _;
            struct Actor {
                child: std::process::Child,
                readers: Vec<std::thread::JoinHandle<Vec<u8>>>,
            }
            impl Drop for Actor {
                fn drop(&mut self) {
                    let _ = self.child.kill();
                    let _ = self.child.wait();
                    for reader in self.readers.drain(..) {
                        let _ = reader.join();
                    }
                }
            }
            fn reader(
                stream: impl std::io::Read + Send + 'static,
            ) -> std::thread::JoinHandle<Vec<u8>> {
                std::thread::spawn(move || {
                    let mut output = Vec::new();
                    stream
                        .take(1024 * 1024 + 1)
                        .read_to_end(&mut output)
                        .unwrap();
                    output
                })
            }
            for mode in ["soft", "hard"] {
                let mut child = std::process::Command::new(std::env::current_exe().unwrap())
                    .args(["--exact", TEST, "--nocapture"])
                    .env(MODE, mode)
                    .stdin(std::process::Stdio::null())
                    .stdout(std::process::Stdio::piped())
                    .stderr(std::process::Stdio::piped())
                    .spawn()
                    .unwrap();
                let readers = vec![
                    reader(child.stdout.take().unwrap()),
                    reader(child.stderr.take().unwrap()),
                ];
                let mut actor = Actor { child, readers };
                let deadline = Instant::now() + Duration::from_secs(60);
                let status = loop {
                    if let Some(status) = actor.child.try_wait().unwrap() {
                        break status;
                    }
                    assert!(
                        Instant::now() < deadline,
                        "native target admission actor hang detector expired"
                    );
                    std::thread::sleep(Duration::from_millis(5));
                };
                let stdout = actor.readers.remove(0).join().unwrap();
                let stderr = actor.readers.remove(0).join().unwrap();
                assert!(stdout.len() <= 1024 * 1024 && stderr.len() <= 1024 * 1024);
                let stdout = String::from_utf8(stdout).unwrap();
                let stderr = String::from_utf8(stderr).unwrap();
                assert!(
                    status.success(),
                    "mode={mode} stdout={stdout} stderr={stderr}"
                );
                assert!(
                    stdout.contains("running 1 test") && stdout.contains("1 passed; 0 failed"),
                    "wrong actor test selection: {stdout}"
                );
                assert_eq!(
                    stderr
                        .matches(
                            format!("NATIVE_TARGET_ADMISSION_ASSERTIONS_PASSED={mode}").as_str()
                        )
                        .count(),
                    1,
                    "actor assertions incomplete: {stderr}"
                );
            }
            return;
        };
        assert!(
            matches!(mode.as_str(), "soft" | "hard"),
            "unsupported native descriptor actor mode"
        );
        struct PreserveFailedInput(Option<tempfile::TempDir>);
        impl Drop for PreserveFailedInput {
            fn drop(&mut self) {
                if std::thread::panicking() {
                    if let Some(root) = self.0.take() {
                        eprintln!(
                            "retained native target admission failure input={}",
                            root.keep().display()
                        );
                    }
                }
            }
        }
        let root = PreserveFailedInput(Some(tempfile::tempdir().unwrap()));
        let image = root
            .0
            .as_ref()
            .unwrap()
            .path()
            .canonicalize()
            .unwrap()
            .join("native-image");
        eprintln!("native target admission original input={}", image.display());
        let target = image.join("lib/rustlib/aarch64-apple-darwin/lib");
        std::fs::create_dir_all(&target).unwrap();
        std::fs::create_dir(image.join("bin")).unwrap();
        let program = super::super::native_input_fixture::materialize(&image);
        for index in 0..507 {
            std::fs::write(
                target.join(format!("original-{index}.rmeta")),
                format!("original file {index}"),
            )
            .unwrap();
        }
        let deadline = Instant::now() + Duration::from_secs(60);
        let mut hash = cargo_util::Sha256::new();
        hash.update_path(&program).unwrap();
        let compiler =
            Arc::new(HeldProgram::open(&image, &program, &hash.finish(), deadline).unwrap());
        let mut limit = libc::rlimit {
            rlim_cur: 0,
            rlim_max: 0,
        };
        assert_eq!(
            unsafe { libc::getrlimit(libc::RLIMIT_NOFILE, &mut limit) },
            0
        );
        assert!(
            limit.rlim_cur >= 256 && limit.rlim_max >= 1024,
            "COULD NOT RUN native target admission actor: inherited limits cannot execute exact control; no test raise"
        );
        limit.rlim_cur = 256;
        if mode == "hard" {
            limit.rlim_max = 256;
        }
        assert_eq!(unsafe { libc::setrlimit(libc::RLIMIT_NOFILE, &limit) }, 0);
        let plan = HeldRustTargetSysroot::plan(compiler.clone(), deadline).unwrap();
        assert_eq!(plan.descriptor_demand(deadline).unwrap(), 507);
        let budget = DescriptorBudget::for_preparation(2, 0).unwrap();
        let before = budget.observation().unwrap();
        assert_eq!(before.soft, 256);
        assert_eq!(before.pending, 0);
        assert_eq!(before.held_targets, 0);
        let result = budget.capture_target(plan, deadline);
        if mode == "hard" {
            let failure = result
                .err()
                .expect("actual hard limit must refuse full target ownership");
            assert_eq!(failure.kind(), std::io::ErrorKind::Unsupported);
            let after = budget.observation().unwrap();
            assert_eq!(
                (after.soft, after.hard, after.pending, after.held_targets),
                (256, 256, 0, 0)
            );
        } else {
            let inputs = result.unwrap();
            assert_eq!(inputs.file_observations().count(), 507);
            inputs.validate(deadline).unwrap();
            let observed = inputs.admission_observation();
            assert_eq!(observed.before.soft, 256);
            assert_eq!(observed.shared_descriptors, 507);
            assert!(
                observed.reserved.soft > 256 && observed.reserved.soft <= observed.reserved.hard
            );
            assert_eq!(observed.reserved.pending, 507);
            assert_eq!(
                (
                    observed.materialized.pending,
                    observed.materialized.held_targets
                ),
                (0, 507)
            );
            let acquired_soft = observed.materialized.soft;
            let original_hard = observed.before.hard;
            let next_unit = inputs.clone();
            drop(inputs);
            assert_eq!(
                budget.observation().unwrap().held_targets,
                507,
                "Arc reuse charges shared target exactly once"
            );
            let member = next_unit.try_member().unwrap().unwrap();
            assert_eq!(budget.observation().unwrap().pending, 16);
            drop(member);
            assert_eq!(budget.observation().unwrap().pending, 0);
            std::fs::write(target.join("original-0.rmeta"), b"mutated file 0").unwrap();
            assert!(next_unit.validate(deadline).is_err());
            assert_eq!(
                budget.observation().unwrap().held_targets,
                507,
                "failed original data stays retained and charged"
            );
            let weak = Arc::downgrade(&next_unit);
            drop(next_unit);
            assert!(weak.upgrade().is_none());
            assert_eq!(
                budget.observation().unwrap().held_targets,
                0,
                "charge returns after actual original inputs close"
            );
            let after = budget.observation().unwrap();
            assert_eq!(
                (after.soft, after.hard),
                (acquired_soft, original_hard),
                "process-owned pool remains raised; only scoped charges return"
            );
        }
        eprintln!("NATIVE_TARGET_ADMISSION_ASSERTIONS_PASSED={mode}");
    }

    #[test]
    fn actual_native_argument_values_survive_policy_derivation_without_command_scraping() {
        let args = [
            "--crate-name",
            "ay_proof_common",
            "src/lib.rs",
            "--extern",
            "dep=/SDK with spaces/libdep.rlib",
            "--cfg",
            "feature=\"spaces and @ are data\"",
            "--emit=dep-info,metadata,link",
            "--out-dir",
            "/old output",
            "-C",
            "incremental=/old incremental",
            "-Copt-level=1",
            "--error-format=json",
            "--json=diagnostic-rendered-ansi",
            "-Ztrust-verify=off",
            "-Z",
            "trust-policy=certify",
        ];
        for policy in Policy::ALL {
            let derived = policy_arguments(
                args.iter().map(OsStr::new),
                policy,
                Path::new("/outputs/new policy"),
                Path::new("/outputs/artifacts"),
                "bound-session",
            )
            .unwrap();
            assert!(derived.contains(&OsString::from("dep=/SDK with spaces/libdep.rlib")));
            assert!(derived.contains(&OsString::from("feature=\"spaces and @ are data\"")));
            assert!(derived.contains(&OsString::from("trust-verify=on")));
            assert!(derived.contains(&OsString::from(format!("trust-policy={}", policy.name()))));
            assert!(
                !derived
                    .iter()
                    .any(|arg| arg.as_encoded_bytes().starts_with(b"incremental="))
            );
            assert!(!derived.contains(&OsString::from("trust-policy=certify")));
        }
    }
    #[test]
    fn missing_duplicate_or_substituted_command_inputs_refuse_before_any_execution() {
        for args in [
            vec!["--emit=metadata"],
            vec!["--out-dir", "/out"],
            vec!["--emit=metadata", "--emit=link", "--out-dir", "/out"],
            vec!["--emit=metadata", "--out-dir", "/one", "--out-dir=/two"],
            vec!["@args", "--emit=metadata", "--out-dir=/out"],
            vec![
                "-Ztrust-verify-ay-path=/unowned/ay",
                "--emit=metadata",
                "--out-dir=/out",
            ],
        ] {
            assert!(
                policy_arguments(
                    args.iter().map(OsStr::new),
                    Policy::Advisory,
                    Path::new("/out"),
                    Path::new("/artifacts"),
                    "session"
                )
                .is_err()
            );
        }
    }
    #[test]
    fn native_policy_uses_typed_unit_scope_and_closes_proc_macro_loading() {
        // Argument mechanics only: this fixture supplies no Unit owner, SDK,
        // native launch, report authentication or favorable proof capability.
        let original = [
            "--crate-name",
            "selected_crate",
            "src/lib.rs",
            "--emit=dep-info,metadata,link",
            "--out-dir=/original-output",
            "-Ztrust_verify_package_name=foreign",
            "-Z",
            "trust-verify-crate-role=build-script",
            "-Ztrust_proc_macro_boundary=no",
            "-Ztrust_verify=off",
            "-Ztrust_policy=strict",
        ];
        for policy in [NativePolicy::Advisory, NativePolicy::Certify] {
            for primary in [true, false] {
                let actual = policy_arguments_scoped(
                    original.iter().map(OsStr::new),
                    CommandPolicy::Native {
                        policy,
                        package: "actual-selected-package",
                        primary,
                    },
                    Path::new("/original-output/new-metadata"),
                    Path::new("/original-output/fresh-session"),
                    "fresh-native-session",
                )
                .unwrap();
                let words = actual
                    .iter()
                    .map(|arg| arg.to_str().unwrap())
                    .collect::<Vec<_>>();
                assert!(words.contains(&"selected_crate"));
                assert!(words.contains(&"trust-verify-package-name=actual-selected-package"));
                assert!(words.contains(&if primary {
                    "trust-verify-crate-role=primary"
                } else {
                    "trust-verify-crate-role=dependency"
                }));
                assert!(words.contains(&"trust-proc-macro-boundary"));
                assert!(words.contains(&"trust-verify=on"));
                assert!(words.contains(&"trust-verify-session=fresh-native-session"));
                assert!(words.contains(&match policy {
                    NativePolicy::Advisory => "trust-policy=advisory",
                    NativePolicy::Certify => "trust-policy=certify",
                }));
                assert!(
                    !words.iter().any(|word| word.contains("policy=strict")),
                    "a native Certify contract cannot be implemented with legacy Strict"
                );
                assert!(!words.iter().any(|arg| arg.contains("foreign")
                    || arg.contains("build-script")
                    || arg.contains("boundary=no")
                    || arg.contains("verify=off")));
            }
        }
    }
}
