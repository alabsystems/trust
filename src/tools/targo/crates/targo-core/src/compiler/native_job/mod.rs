//! Actual ordinary compiler nodes in a genuine general job. Retained products
//! are constructed only from this BuildRunner's joined queue, original Layout
//! OFDs and real successful compiler materialization; Fresh/paths cannot seed.
use super::build_runner::OriginalOutputLeases;
pub(crate) use super::resource_runtime::{
    NativeContinuedGraph, NativeOperationGraph, NativeRetainedGraph, NativeVerificationContext,
};
use super::{BuildRunner, CompileKind, FileFlavor};
use crate::ops::cargo_test::workload::{Inputs, Materialization, NativeOutput};
use crate::resource_v3::native_job::outputs::Outputs;
use crate::util::CargoResult;
use anyhow::Context as _;
use std::ffi::OsString;
use std::os::unix::ffi::OsStringExt as _;
use std::path::PathBuf;
use std::sync::{Arc, OnceLock};
use trust_resource_controller::native_job::{CompileMode, Kind, NodeId, TargetKind, UnitSelector};
pub(crate) mod produced;
pub(crate) mod verification;
fn path(bytes: &[u8]) -> PathBuf {
    PathBuf::from(OsString::from_vec(bytes.to_vec()))
}
/// A new genuine unbound SAME-bank unit for trusted local preparation/math.
/// It cannot launch a target or resurrect a retired verification/compiler loan.
pub(crate) struct NativeLocalPreparation {
    startup: Arc<crate::resource_v3::Startup>,
    loan: Arc<crate::resource_v3::workload::bank::PrimaryLoan>,
    lease: Arc<trust_build_cpu::Lease>,
}
impl NativeLocalPreparation {
    pub(crate) fn acquire(startup: &Arc<crate::resource_v3::Startup>) -> CargoResult<Option<Self>> {
        let plan = startup
            .native_job_plan
            .as_ref()
            .context("local preparation lost original native plan")?;
        let actual = crate::resource_v3::native_job::require(plan)?;
        anyhow::ensure!(
            Arc::ptr_eq(&actual, startup),
            "local preparation replaced original native Startup"
        );
        let bank = startup
            .workload_bank
            .as_ref()
            .context("local preparation lost actual original bank")?;
        let Some(loan) = bank.try_primary()? else {
            return Ok(None);
        };
        let lease = loan.lease();
        loan.require_preparation(&lease)?;
        Ok(Some(Self {
            startup: startup.clone(),
            loan,
            lease,
        }))
    }
    pub(crate) fn require(&self, startup: &Arc<crate::resource_v3::Startup>) -> CargoResult<()> {
        let plan = startup
            .native_job_plan
            .as_ref()
            .context("local preparation lost original native plan")?;
        let actual = crate::resource_v3::native_job::require(plan)?;
        anyhow::ensure!(
            Arc::ptr_eq(startup, &self.startup) && Arc::ptr_eq(startup, &actual),
            "local preparation replaced actual Startup"
        );
        self.loan.require_preparation(&self.lease)?;
        Ok(())
    }
}
pub(crate) struct Options {
    pub(crate) registry: Arc<Outputs>,
    pub(crate) artifacts: Arc<crate::resource_v3::native_job::outputs::Artifacts>,
    pub(crate) inputs: Arc<Inputs>,
    pub(crate) node: NodeId,
    recorder: Arc<verification::Recorder>,
}
pub(crate) struct Attempt {
    pub(super) result: CargoResult<()>,
    pub(super) artifact: Option<Artifact>,
    pub(super) continuation: Option<NativeRetainedGraph>,
    pub(super) continuation_failure: Option<String>,
    pub(super) compiler_executions: usize,
    pub(super) warm_units: usize,
    // Retain the exact callback owner even when compilation/capture fails.
    pub(super) _recorder: Arc<verification::Recorder>,
    pub(super) produced: Option<Arc<produced::Original>>,
}
pub(crate) struct Artifact {
    node: NodeId,
    original: Arc<RetiredArtifact>,
}
pub(crate) struct RetiredArtifact {
    key: String,
    selection: UnitSelector,
    inputs: Arc<Inputs>,
    leases: Arc<OriginalOutputLeases>,
    exact: Option<Arc<super::exact_unit::Captured>>,
    produced: Option<Arc<produced::Original>>,
    output: OwnedOutput,
    command: Option<Arc<super::qualification_command::OriginalUnitCommand>>,
}
enum OwnedOutput {
    Program(Arc<NativeOutput>),
    PublishedGraph,
    Data {
        files: Vec<Arc<trust_resource_controller::descriptors::AdmittedRootFile>>,
        materialization: Materialization,
    },
}
impl Attempt {
    pub(crate) fn require_frontend(&self, original: &Arc<NativeOutput>) -> CargoResult<()> {
        self.produced
            .as_ref()
            .context("ordinary SDK attempt has no actual produced coordinator owner")?
            .require_frontend(original)
    }
    pub(crate) fn result(&self) -> CargoResult<()> {
        match &self.result {
            Ok(()) => Ok(()),
            Err(error) => Err(anyhow::anyhow!("{error:#}")),
        }
    }
    pub(crate) fn artifact(&self) -> Option<&Artifact> {
        self.artifact.as_ref()
    }
    pub(crate) fn compiler_executions(&self) -> usize {
        self.compiler_executions
    }
    pub(crate) fn warm_units(&self) -> usize {
        self.warm_units
    }
    pub(crate) fn continuation_failure(&self) -> Option<&str> {
        self.continuation_failure.as_deref()
    }
    pub(crate) fn has_retained_continuation(&self) -> bool {
        self.continuation.is_some() && self.continuation_failure.is_none()
    }
    pub(crate) fn take_continuation(&mut self) -> Option<NativeRetainedGraph> {
        self.continuation.take()
    }
    pub(crate) fn reporting_failed(&mut self, error: anyhow::Error) {
        self.result = Err(match std::mem::replace(&mut self.result, Ok(())) {
            Ok(()) => error,
            Err(original) => {
                error.context(format!("native compiler graph also failed: {original:#}"))
            }
        });
    }
}
impl RetiredArtifact {
    pub(crate) fn key(&self) -> &str {
        &self.key
    }
    fn validate(
        &self,
        inputs: &Arc<Inputs>,
        leases: &Arc<OriginalOutputLeases>,
    ) -> CargoResult<()> {
        let plan = inputs
            .native_plan()
            .context("native reuse lacks actual general inputs")?;
        let actual = crate::resource_v3::native_job::require(plan)?;
        let deadline = actual
            .workload_process
            .as_ref()
            .context("native reuse lost original process")?
            .deadline;
        anyhow::ensure!(
            self.inputs
                .native_master()
                .zip(inputs.native_master())
                .is_some_and(|(old, current)| Arc::ptr_eq(old, current))
                && self
                    .inputs
                    .native_selected_root()
                    .zip(inputs.native_selected_root())
                    .is_some_and(|(old, current)| Arc::ptr_eq(old, current))
                && Arc::ptr_eq(&self.leases, leases),
            "native reuse replaced original master/selected root/Layout"
        );
        self.inputs.validate()?;
        inputs.validate()?;
        self.leases.validate(inputs.held_output_root().path())?;
        match (&self.exact, &self.produced) {
            (Some(exact), None) => exact.require_current()?,
            (None, Some(original)) => original.require()?,
            _ => anyhow::bail!("native artifact lacks one exact actual producer branch"),
        }
        match &self.output {
            OwnedOutput::Program(program) => program.validate(deadline)?,
            OwnedOutput::PublishedGraph => {
                self.produced
                    .as_ref()
                    .context("published graph omitted actual coordinator owner")?
                    .require()?;
            }
            OwnedOutput::Data {
                files,
                materialization,
            } => {
                anyhow::ensure!(
                    materialization.producer_attempt().is_some(),
                    "DATA cannot seed retired metadata ownership"
                );
                for file in files {
                    file.validate(deadline)?;
                }
            }
        }
        Ok(())
    }
}
impl Artifact {
    pub(crate) fn inputs(&self) -> &Arc<Inputs> {
        &self.original.inputs
    }
    pub(crate) fn output_leases(&self) -> &Arc<OriginalOutputLeases> {
        &self.original.leases
    }
    pub(crate) fn original_command(
        &self,
    ) -> CargoResult<Arc<super::qualification_command::OriginalUnitCommand>> {
        self.validate()?;
        let command = self
            .original
            .command
            .as_ref()
            .context("native artifact has no actual normal-library compiler command")?
            .clone();
        command.validate()?;
        command
            .producer_attempt()
            .context("Fresh DATA cannot create a verification prerequisite")?;
        Ok(command)
    }
    pub(super) fn verification_inputs(
        &self,
        registry: &Arc<Outputs>,
    ) -> CargoResult<(Arc<Inputs>, Arc<OriginalOutputLeases>)> {
        anyhow::ensure!(
            self.original
                .inputs
                .native_plan()
                .is_some_and(|plan| Arc::ptr_eq(plan, registry.plan())),
            "verification artifact belongs to another genuine native plan"
        );
        registry.require_registered(
            self.original.inputs.held_output_root().path(),
            &self.original.leases,
        )?;
        self.validate()?;
        Ok((self.original.inputs.clone(), self.original.leases.clone()))
    }
    pub(crate) fn validate(&self) -> CargoResult<()> {
        self.original
            .validate(&self.original.inputs, &self.original.leases)
    }
    pub(crate) fn require(
        &self,
        declared: &trust_resource_controller::native_job::Artifact,
    ) -> CargoResult<()> {
        if let Some(original) = &self.original.produced {
            original.require()?;
        }
        anyhow::ensure!(
            self.node == declared.producer && self.original.selection == declared.unit,
            "native artifact does not match its actual selected producer node"
        );
        Ok(())
    }
    pub(crate) fn program(&self) -> CargoResult<Arc<NativeOutput>> {
        if let Some(original) = &self.original.produced {
            original.require()?;
        }
        match &self.original.output {
            OwnedOutput::Program(program) => Ok(program.clone()),
            OwnedOutput::Data { .. } | OwnedOutput::PublishedGraph => {
                anyhow::bail!("native library/check DATA is not an executable producer")
            }
        }
    }
}
impl Options {
    pub(crate) fn new(
        registry: Arc<Outputs>,
        artifacts: Arc<crate::resource_v3::native_job::outputs::Artifacts>,
        inputs: Arc<Inputs>,
        node: NodeId,
    ) -> Self {
        Self {
            registry,
            artifacts,
            inputs,
            node,
            recorder: verification::Recorder::new(),
        }
    }
    pub(super) fn recorder(&self) -> Arc<verification::Recorder> {
        self.recorder.clone()
    }
    pub(super) fn executor(
        &self,
        runner: &BuildRunner<'_, '_>,
    ) -> CargoResult<Arc<dyn super::Executor>> {
        let selected = runner
            .bcx
            .roots
            .first()
            .filter(|unit| {
                unit.mode == super::CompileMode::Build
                    && unit.target.is_lib()
                    && !unit.target.proc_macro()
            })
            .map(|unit| {
                runner
                    .bcx
                    .unit_to_index
                    .get(unit)
                    .copied()
                    .context("native selected root has no actual graph index")
            })
            .transpose()?;
        Ok(Arc::new(NativeExecutor {
            selected,
            prepared: OnceLock::new(),
            recorder: self.recorder.clone(),
        }))
    }
    pub(super) fn validate(&self, runner: &BuildRunner<'_, '_>) -> CargoResult<()> {
        let startup = crate::resource_v3::native_job::require(self.registry.plan())?;
        self.artifacts.require_outputs(&self.registry)?;
        let node = self
            .registry
            .plan()
            .nodes
            .get(self.node.0 as usize)
            .context("native compiler node omitted")?;
        let Kind::Compile {
            source, unit, mode, ..
        } = &node.kind
        else {
            anyhow::bail!("ordinary native compiler received another node kind")
        };
        self.inputs
            .validate_target(&runner.bcx.ws.target_dir().into_path_unlocked())?;
        anyhow::ensure!(
            self.inputs.native_compile_node() == Some(self.node)
                && self
                    .inputs
                    .native_plan()
                    .is_some_and(|plan| Arc::ptr_eq(plan, self.registry.plan())),
            "native compiler inputs are grafted from another node"
        );
        let bcx = runner.bcx;
        anyhow::ensure!(
            bcx.roots.len() == 1
                && !bcx.build_config.dry_run
                && !bcx.build_config.unit_graph
                && !bcx.build_config.force_rebuild
                && bcx.build_config.requested_kinds == [CompileKind::Host]
                && bcx.jobs() <= startup.local_ceiling,
            "native job requires its actual bounded native graph without forced recompilation"
        );
        let root = &bcx.roots[0];
        super::candidate_semantics::preflight_graph(bcx)?;
        if root.mode == super::CompileMode::Build && root.target.is_lib() {
            anyhow::ensure!(
                !bcx.unit_graph
                    .keys()
                    .chain(
                        bcx.unit_graph
                            .values()
                            .flat_map(|deps| deps.iter().map(|dependency| &dependency.unit))
                    )
                    .any(|unit| unit.target.proc_macro()),
                "native verification command capture refuses a resolved proc-macro closure"
            );
        }
        let target = match unit.kind {
            TargetKind::Library => root.target.is_lib(),
            TargetKind::Binary => root.target.is_bin(),
            TargetKind::Test => root.target.is_test(),
        };
        anyhow::ensure!(
            root.pkg.name().as_str() == unit.package
                && root.target.name() == unit.target
                && target
                && bcx.ws.root_manifest()
                    == path(&self.registry.plan().sources[*source as usize].manifest.path)
                && root.mode.is_check() == matches!(mode, CompileMode::Check),
            "ordinary native graph differs from the declared root/unit/mode"
        );
        Ok(())
    }
    pub(super) fn capture(
        &self,
        runner: &BuildRunner<'_, '_>,
        leases: Option<Arc<OriginalOutputLeases>>,
    ) -> CargoResult<Artifact> {
        let startup = crate::resource_v3::native_job::require(self.registry.plan())?;
        let bank = startup
            .workload_bank
            .as_ref()
            .context("native capture lost original bank")?;
        anyhow::ensure!(
            bank.is_drained()?,
            "native product capture precedes actual compiler/read retirement"
        );
        runner
            .resource_runtime
            .as_ref()
            .context("native product capture lost original resource runtime")?
            .resume_native_preparation()?;
        let loan = bank
            .try_primary()?
            .context("native product capture requires a real original preparation unit")?;
        loan.require_preparation(&loan.lease())?;
        self.validate(runner)?;
        let leases =
            leases.context("native compiler omitted its finalized original Layout OFDs")?;
        self.registry.retain_leases(&self.inputs, leases.clone())?;
        let plan = self.registry.plan();
        let Kind::Compile {
            source, unit, mode, ..
        } = &plan.nodes[self.node.0 as usize].kind
        else {
            unreachable!()
        };
        let source_paths = plan
            .sources
            .iter()
            .map(|source| path(&source.root))
            .collect::<Vec<_>>();
        let selected = super::candidate_semantics::Selected {
            mode: match mode {
                CompileMode::Build => super::candidate_semantics::Mode::Build,
                CompileMode::Check => super::candidate_semantics::Mode::Check,
            },
            sources: &source_paths,
            manifest: &path(&plan.sources[*source as usize].manifest.path),
            package: &unit.package,
            binary: &unit.target,
            output_root: self.inputs.held_output_root().path(),
            cargo_home: &path(&plan.inputs.cargo_home),
            sdk_root: &path(&plan.inputs.sdk_root),
            compiler: &path(&plan.inputs.compiler.path),
            compiler_sha256: plan.inputs.compiler.sha256,
        };
        let digests = super::candidate_semantics::capture_native_job(runner, &selected)?;
        let root = &runner.bcx.roots[0];
        let exact = super::exact_unit::capture(runner, root)?;
        let key = format!(
            "{}:{}:{}",
            hex::encode(digests.configuration_sha256),
            hex::encode(digests.coverage_sha256),
            exact.digest
        );
        let materialization = *runner
            .workload_materializations
            .get(root)
            .context("native output has no actual queue materialization branch")?;
        let original = if materialization.producer_attempt().is_none() {
            let original=self.artifacts.cached(&self.inputs,&key)?.context("Fresh cannot seed an executable/metadata owner; no retained genuine cold producer exists in this cache domain")?;
            original.validate(&self.inputs, &leases)?;
            original
        } else {
            let deadline = startup
                .workload_process
                .as_ref()
                .context("native capture lost original process")?
                .deadline;
            let output = if matches!(mode, CompileMode::Build)
                && matches!(unit.kind, TargetKind::Binary | TargetKind::Test)
            {
                let mut outputs = runner
                    .compilation
                    .binaries
                    .iter()
                    .chain(runner.compilation.tests.iter())
                    .filter(|output| &output.unit == root);
                let output = outputs
                    .next()
                    .context("native graph omitted actual selected UnitOutput")?;
                anyhow::ensure!(
                    outputs.next().is_none(),
                    "native selected executable has ambiguous UnitOutput population"
                );
                OwnedOutput::Program(NativeOutput::capture(
                    self.inputs.clone(),
                    &runner.compilation,
                    output,
                    leases.clone(),
                    materialization,
                )?)
            } else {
                let budget = startup
                    .descriptor_budget
                    .as_ref()
                    .context("native DATA capture lost SAME descriptor budget")?;
                let mut files = Vec::new();
                let outputs = runner.outputs(root)?;
                for output in outputs.iter() {
                    if matches!(
                        output.flavor,
                        FileFlavor::Normal | FileFlavor::Linkable | FileFlavor::Rmeta
                    ) {
                        files.push(budget.capture_output_file(
                            self.inputs.held_output_root(),
                            output.bin_dst(),
                            deadline,
                        )?);
                    }
                }
                anyhow::ensure!(
                    !files.is_empty(),
                    "native library/check omitted actual selected outputs"
                );
                OwnedOutput::Data {
                    files,
                    materialization,
                }
            };
            let original = Arc::new(RetiredArtifact {
                key,
                selection: unit.clone(),
                inputs: self.inputs.clone(),
                leases: leases.clone(),
                exact: Some(exact),
                produced: None,
                output,
                command: if root.mode == super::CompileMode::Build && root.target.is_lib() {
                    let command = self.recorder.original()?;
                    anyhow::ensure!(
                        command.unit()
                            == &super::qualification_command::unit_identity(runner, root)?,
                        "native recorded command differs from the actual selected producer"
                    );
                    Some(command)
                } else {
                    None
                },
            });
            original.validate(&self.inputs, &leases)?;
            self.artifacts.retain(&self.inputs, original.clone())?;
            original
        };
        drop(loan);
        Ok(Artifact {
            node: self.node,
            original,
        })
    }
}

/// Observation is attached to the exact resolved root; ordinary execution is
/// still the maintained DefaultExecutor and its actual native resource owner.
struct NativeExecutor {
    selected: Option<super::UnitIndex>,
    prepared: OnceLock<super::qualification_command::UnitIdentity>,
    recorder: Arc<verification::Recorder>,
}
impl NativeExecutor {
    fn bind_identity(
        &self,
        identity: super::qualification_command::UnitIdentity,
    ) -> CargoResult<()> {
        anyhow::ensure!(
            self.selected == Some(identity.index),
            "native observation selected another graph unit"
        );
        self.prepared
            .set(identity)
            .map_err(|_| anyhow::anyhow!("native observation was already prepared"))
    }
    fn observer_for_identity(
        &self,
        identity: &super::qualification_command::UnitIdentity,
    ) -> CargoResult<Option<Arc<dyn super::qualification_command::Observer>>> {
        if self.selected != Some(identity.index) {
            return Ok(None);
        }
        let prepared = self
            .prepared
            .get()
            .context("native observation was not prepared")?;
        anyhow::ensure!(
            prepared == identity,
            "native observation changed its prepared unit identity"
        );
        Ok(Some(self.recorder.clone()))
    }
}
impl super::Executor for NativeExecutor {
    fn prepare_unit_observation(&self, build: &BuildRunner<'_, '_>) -> CargoResult<()> {
        let Some(index) = self.selected else {
            return Ok(());
        };
        anyhow::ensure!(
            build.bcx.roots.len() == 1,
            "native observation requires the sole actual root"
        );
        let unit = &build.bcx.roots[0];
        anyhow::ensure!(
            build.bcx.unit_to_index.get(unit) == Some(&index)
                && unit.mode == super::CompileMode::Build
                && unit.target.is_lib()
                && !unit.target.proc_macro(),
            "native observation changed its selected root"
        );
        self.bind_identity(super::qualification_command::unit_identity(build, unit)?)
    }
    fn unit_command_observer(
        &self,
        build: &BuildRunner<'_, '_>,
        unit: &super::Unit,
    ) -> CargoResult<Option<Arc<dyn super::qualification_command::Observer>>> {
        if self.selected.is_none() || build.bcx.unit_to_index.get(unit) != self.selected.as_ref() {
            return Ok(None);
        }
        self.observer_for_identity(&super::qualification_command::unit_identity(build, unit)?)
    }
    fn exec(
        &self,
        command: &cargo_util::ProcessBuilder,
        id: crate::workspace::PackageId,
        target: &crate::workspace::Target,
        mode: super::CompileMode,
        on_stdout: &mut dyn FnMut(&str) -> CargoResult<()>,
        on_stderr: &mut dyn FnMut(&str) -> CargoResult<()>,
        capture_rusage: bool,
    ) -> (cargo_util::ExecStats, CargoResult<()>) {
        super::Executor::exec(
            &super::DefaultExecutor,
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

#[cfg(all(test, target_os = "macos", target_arch = "aarch64"))]
mod observation_tests {
    use super::*;
    use crate::compiler::qualification_command::{self, Observation, Observer};

    #[test]
    fn selected_observation_freezes_preparation_and_refuses_cross_graph_identity() {
        // Obtain identity DATA from a real held input whose command failed.
        // Neither that data nor routing can manufacture a successful producer.
        let source = verification::Recorder::new();
        let root = tempfile::tempdir().unwrap();
        let (capture, command, _) =
            qualification_command::command_fixture(root.path(), source.clone());
        let pending = capture.pending(&command).unwrap();
        Observation::finish(
            capture,
            pending,
            Err("actual native prerequisite refused".into()),
        )
        .notify()
        .unwrap();
        let identity = source.failed().unwrap().unit().clone();
        let recorder = verification::Recorder::new();
        let executor = NativeExecutor {
            selected: Some(identity.index),
            prepared: OnceLock::new(),
            recorder: recorder.clone(),
        };
        assert!(executor.observer_for_identity(&identity).is_err());
        executor.bind_identity(identity.clone()).unwrap();
        assert!(executor.bind_identity(identity.clone()).is_err());
        let expected: Arc<dyn Observer> = recorder.clone();
        assert!(Arc::ptr_eq(
            &executor.observer_for_identity(&identity).unwrap().unwrap(),
            &expected
        ));
        let mut mismatches = Vec::new();
        let mut changed = identity.clone();
        changed.root_attempt[0] ^= 1;
        mismatches.push(changed);
        let mut changed = identity.clone();
        changed.invocation_sha256[0] ^= 1;
        mismatches.push(changed);
        let mut changed = identity.clone();
        changed.unit_hash.push_str("-other");
        mismatches.push(changed);
        let mut changed = identity.clone();
        changed.package.push_str("-other");
        mismatches.push(changed);
        let mut changed = identity.clone();
        changed.target.push_str("-other");
        mismatches.push(changed);
        let mut changed = identity.clone();
        changed.source = changed.source.with_file_name("other.rs");
        mismatches.push(changed);
        for changed in mismatches {
            assert!(
                executor.observer_for_identity(&changed).is_err(),
                "{changed:?}"
            );
        }
        let mut unrelated = identity.clone();
        unrelated.index = super::super::UnitIndex(identity.index.0.wrapping_add(1));
        assert!(
            executor
                .observer_for_identity(&unrelated)
                .unwrap()
                .is_none()
        );
        let unselected = NativeExecutor {
            selected: None,
            prepared: OnceLock::new(),
            recorder: recorder.clone(),
        };
        assert!(
            unselected
                .observer_for_identity(&identity)
                .unwrap()
                .is_none()
        );
        assert!(
            recorder.original().is_err(),
            "identity and routing grant no command owner"
        );
        assert!(
            source.original().is_err(),
            "the original prerequisite remains failed"
        );
    }
}
