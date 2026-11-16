//! Select an explicit execution domain without changing the qualified v2 path.
use std::sync::Arc;

use super::{BuildContext, resource_runtime_v2 as v2, resource_runtime_v3 as v3};
use crate::util::{CargoResult, GlobalContext};
use anyhow::Context as _;
use cargo_util::{Jobserver, ProcessBuilder};

pub(super) fn requested(gctx: &GlobalContext) -> bool {
    #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
    if gctx.original_bootstrap_full().is_some() {
        // The actual Full owner has its distinct retained Fixed member path.
        // It must never recreate a cooperative native-v3 Startup or CPU bank.
        return false;
    }
    crate::resource_worker_v3() || v2::requested(gctx)
}

enum Runtime {
    Legacy(Arc<v2::ResourceRuntime>),
    Retained(Arc<v3::ResourceRuntime>),
}
pub(super) struct ResourceRuntime(Runtime);
enum Root {
    Legacy(Arc<v2::RootContext>),
    Retained(Arc<v3::RootContext>),
}
pub(super) struct RootContext(Root);

/// NonClone sequential graph continuation. It retains the original runtime,
/// graph-wide output OFDs and every real unused GNU token while parked.
pub(crate) struct RetainedGraph {
    runtime: Arc<ResourceRuntime>,
    outputs: Option<Arc<super::build_runner::OriginalOutputLeases>>,
    inputs: Arc<crate::ops::cargo_test::workload::Inputs>,
    root: std::path::PathBuf,
    escrow: super::resource_fifo::ForeignGnuEscrow,
}
pub(crate) struct ContinuedGraph {
    runtime: Arc<ResourceRuntime>,
    outputs: Option<Arc<super::build_runner::OriginalOutputLeases>>,
    inputs: Arc<crate::ops::cargo_test::workload::Inputs>,
    root: std::path::PathBuf,
}
/// NonClone whole-job continuation. All actual unused GNU tokens and the
/// SAME runtime/original per-root registry remain owned while parked.
pub(crate) struct NativeRetainedGraph {
    runtime: Arc<ResourceRuntime>,
    registry: Arc<crate::resource_v3::native_job::outputs::Outputs>,
    escrow: super::resource_fifo::ForeignGnuEscrow,
}
pub(crate) struct NativeContinuedGraph {
    runtime: Arc<ResourceRuntime>,
    inputs: Arc<crate::ops::cargo_test::workload::Inputs>,
    outputs: Option<Arc<super::build_runner::OriginalOutputLeases>>,
}
/// Original runtime active for one fixed trusted Root operation, with no
/// compiler/foreign target. A later scoped suspension must retain the SAME
/// actual GNU credits and positively drained bank before another node starts.
pub(crate) struct NativeOperationGraph {
    runtime: Arc<ResourceRuntime>,
    registry: Arc<crate::resource_v3::native_job::outputs::Outputs>,
}
pub(crate) struct NativeVerificationContext {
    context: Arc<RootContext>,
    startup: Arc<crate::resource_v3::Startup>,
}
impl NativeRetainedGraph {
    pub(crate) fn resume_operation(self) -> CargoResult<NativeOperationGraph> {
        crate::resource_v3::native_job::require(self.registry.plan())?;
        match &self.runtime.0 {
            Runtime::Retained(runtime) => runtime.resume_native_job_graph(self.escrow)?,
            Runtime::Legacy(_) => {
                anyhow::bail!("native operation has no retained original runtime")
            }
        }
        Ok(NativeOperationGraph {
            runtime: self.runtime,
            registry: self.registry,
        })
    }
    pub(crate) fn resume(
        self,
        inputs: Arc<crate::ops::cargo_test::workload::Inputs>,
    ) -> CargoResult<NativeContinuedGraph> {
        let outputs = self.registry.leases(&inputs)?;
        match &self.runtime.0 {
            Runtime::Retained(runtime) => runtime.resume_native_job_graph(self.escrow)?,
            Runtime::Legacy(_) => {
                anyhow::bail!("general continuation lacks original native runtime")
            }
        }
        Ok(NativeContinuedGraph {
            runtime: self.runtime,
            inputs,
            outputs,
        })
    }
}
impl NativeOperationGraph {
    pub(in crate::compiler) fn run_coordinator(
        &self,
        frontend: Arc<crate::ops::cargo_test::workload::NativeOutput>,
        inputs: Arc<crate::ops::cargo_test::workload::Inputs>,
        plan: trust_resource_controller::workload::host::coordinator::Plan,
        leases: Arc<super::build_runner::OriginalOutputLeases>,
        dependencies: &mut Option<super::candidate_dependencies::Ledger>,
        deadline: std::time::Instant,
    ) -> CargoResult<super::resource_runtime_v3::native_coordinator::Completed> {
        match &self.runtime.0 {
            Runtime::Retained(runtime) => {
                runtime.run_coordinator(frontend, inputs, plan, leases, dependencies, deadline)
            }
            Runtime::Legacy(_) => anyhow::bail!("produced coordinator lost SAME native runtime"),
        }
    }
    /// Select only the producer's SAME retained original output/OFD capsule.
    /// Identity bookends run under a real local preparation unit; Host selection
    /// then independently requires the positively drained original bank.
    pub(crate) fn select_artifact(
        &self,
        artifact: &super::native_job::Artifact,
    ) -> CargoResult<()> {
        let preparation = self.prepare_local()?.context(
            "verification artifact selection lacks an actual available preparation unit",
        )?;
        let startup = crate::resource_v3::native_job::require(self.registry.plan())?;
        preparation.require(&startup)?;
        let (inputs, leases) = artifact.verification_inputs(&self.registry)?;
        preparation.require(&startup)?;
        drop(preparation);
        match &self.runtime.0 {
            Runtime::Retained(runtime) => {
                runtime.retain_workload_outputs(leases, inputs.held_output_root().path())
            }
            Runtime::Legacy(_) => {
                anyhow::bail!("verification selection lost genuine native runtime")
            }
        }
    }
    pub(crate) fn prepare_local(
        &self,
    ) -> CargoResult<Option<super::native_job::NativeLocalPreparation>> {
        let startup = crate::resource_v3::native_job::require(self.registry.plan())?;
        super::native_job::NativeLocalPreparation::acquire(&startup)
    }
    pub(crate) fn try_verification(&self) -> CargoResult<Option<NativeVerificationContext>> {
        let startup = crate::resource_v3::native_job::require(self.registry.plan())?;
        let context = self.runtime.try_root(false)?;
        context
            .map(|context| {
                let actual = context.verification_preparation()?;
                anyhow::ensure!(
                    Arc::ptr_eq(&startup, &actual),
                    "verification context replaced original native Startup"
                );
                Ok(NativeVerificationContext { context, startup })
            })
            .transpose()
    }
    pub(crate) fn try_suspend(self) -> Result<NativeRetainedGraph, (anyhow::Error, Self)> {
        match self.runtime.suspend_native_job_graph(self.registry.clone()) {
            Ok(continuation) => Ok(continuation),
            Err(error) => Err((error, self)),
        }
    }
}
impl NativeVerificationContext {
    /// A known pre-dispatch refusal may abandon only this SAME still-unbound
    /// actual reservation. No before_request/settlement or status inference.
    pub(crate) fn cancel_preparation(self) -> Result<(), (anyhow::Error, Self)> {
        match self.preparation() {
            Ok(_) => Ok(()),
            Err(error) => Err((error, self)),
        }
    }
    /// Consumes the policy command and applies the SAME existing native
    /// finalization internally. Do not configure it a second time.
    pub(crate) fn capture(
        &self,
        command: ProcessBuilder,
        limits: cargo_util::StreamingOutputLimits,
    ) -> CargoResult<crate::resource_v3::NativeVerificationCapture> {
        match &self.context.0 {
            Root::Retained(root) => root.capture_verification(command, limits),
            Root::Legacy(_) => anyhow::bail!("verification capture lost actual native context"),
        }
    }
    pub(crate) fn try_retire(
        self,
        capture: &crate::resource_v3::NativeVerificationCapture,
    ) -> Result<(), (anyhow::Error, Self)> {
        let result = match &self.context.0 {
            Root::Retained(root) => root.retire_verification(capture),
            Root::Legacy(_) => Err(anyhow::anyhow!(
                "verification retirement lost actual native context"
            )),
        };
        match result {
            Ok(()) => Ok(()),
            Err(error) => Err((error, self)),
        }
    }
    pub(crate) fn preparation(&self) -> CargoResult<Arc<crate::resource_v3::Startup>> {
        let actual = self.context.verification_preparation()?;
        anyhow::ensure!(
            Arc::ptr_eq(&actual, &self.startup),
            "verification context preparation replaced original Startup"
        );
        Ok(actual)
    }
}
impl NativeContinuedGraph {
    pub(super) fn install(
        self,
        bcx: &BuildContext<'_, '_>,
    ) -> CargoResult<(
        Arc<ResourceRuntime>,
        Option<Arc<super::build_runner::OriginalOutputLeases>>,
        Arc<crate::ops::cargo_test::workload::Inputs>,
    )> {
        match &self.runtime.0 {
            Runtime::Retained(runtime) => runtime.validate_native_job_graph(bcx, &self.inputs)?,
            Runtime::Legacy(_) => {
                anyhow::bail!("general continuation lacks original native runtime")
            }
        }
        Ok((self.runtime, self.outputs, self.inputs))
    }
}
impl RetainedGraph {
    /// Resume for the next workspace's ordinary compiler identity/config
    /// queries before create_bcx. Only this live continuation can do so.
    pub(crate) fn resume(self) -> CargoResult<ContinuedGraph> {
        self.inputs.validate_target(&self.root)?;
        if let Some(outputs) = &self.outputs {
            outputs.validate(&self.root)?;
        }
        match &self.runtime.0 {
            Runtime::Retained(runtime) => runtime.resume_paired_graph(self.escrow)?,
            Runtime::Legacy(_) => {
                anyhow::bail!("paired continuation has no original retained runtime")
            }
        }
        Ok(ContinuedGraph {
            runtime: self.runtime,
            outputs: self.outputs,
            inputs: self.inputs,
            root: self.root,
        })
    }
}
impl ContinuedGraph {
    pub(super) fn install(
        self,
        bcx: &BuildContext<'_, '_>,
    ) -> CargoResult<(
        Arc<ResourceRuntime>,
        Option<Arc<super::build_runner::OriginalOutputLeases>>,
        Arc<crate::ops::cargo_test::workload::Inputs>,
    )> {
        anyhow::ensure!(
            bcx.ws.target_dir().into_path_unlocked() == self.root,
            "continued graph replaced original output root"
        );
        self.inputs.validate_target(&self.root)?;
        if let Some(outputs) = &self.outputs {
            outputs.validate(&self.root)?;
        }
        match &self.runtime.0 {
            Runtime::Retained(runtime) => runtime.validate_paired_graph(bcx)?,
            Runtime::Legacy(_) => anyhow::bail!("continued graph has no retained native runtime"),
        }
        Ok((self.runtime, self.outputs, self.inputs))
    }
}

impl ResourceRuntime {
    /// Read-only transport data for compiler tool-input observations. The
    /// selected runtime, rather than an ambient worker flag, identifies the
    /// local v2 path. Retained v3 execution has no qualified local profile.
    /// V2 stays distinct because Rustc may select its paired native linker;
    /// CPU counts, admission state and leases do not become cache identity.
    pub(super) fn tool_input_transport_profile(
        &self,
    ) -> Option<trust_fs_observation::tool_lookup::Profile> {
        match &self.0 {
            Runtime::Legacy(_) => {
                Some(trust_fs_observation::tool_lookup::Profile::LocalUnixNativeResourceV2)
            }
            Runtime::Retained(_) => None,
        }
    }

    /// Queue join has parked the bank. Observe ALL real returned GNU credits
    /// before resuming only trusted local preparation under a fresh SAME-bank
    /// reservation. A parked table alone never supplies CPU admission.
    pub(super) fn resume_native_preparation(&self) -> CargoResult<()> {
        match &self.0 {
            Runtime::Retained(runtime) => {
                let escrow = runtime.suspend_native_job_graph()?;
                runtime.resume_native_job_graph(escrow)
            }
            Runtime::Legacy(_) => {
                anyhow::bail!("native preparation lost original retained runtime")
            }
        }
    }
    pub(super) fn suspend_native_job_graph(
        self: &Arc<Self>,
        registry: Arc<crate::resource_v3::native_job::outputs::Outputs>,
    ) -> CargoResult<NativeRetainedGraph> {
        crate::resource_v3::native_job::require(registry.plan())?;
        let escrow = match &self.0 {
            Runtime::Retained(runtime) => runtime.suspend_native_job_graph()?,
            Runtime::Legacy(_) => {
                anyhow::bail!("general continuation requires actual retained native runtime")
            }
        };
        Ok(NativeRetainedGraph {
            runtime: self.clone(),
            registry,
            escrow,
        })
    }
    pub(super) fn suspend_paired_graph(
        self: &Arc<Self>,
        outputs: Option<Arc<super::build_runner::OriginalOutputLeases>>,
        inputs: Arc<crate::ops::cargo_test::workload::Inputs>,
        root: &std::path::Path,
    ) -> CargoResult<RetainedGraph> {
        inputs.validate_target(root)?;
        let escrow = match &self.0 {
            Runtime::Retained(runtime) => runtime.suspend_paired_graph(outputs.as_ref(), root)?,
            Runtime::Legacy(_) => {
                anyhow::bail!("paired continuation requires actual retained native runtime")
            }
        };
        Ok(RetainedGraph {
            runtime: self.clone(),
            outputs,
            inputs,
            root: root.to_owned(),
            escrow,
        })
    }
    pub(super) fn enter_workload_harnesses(
        &self,
        outputs: &crate::ops::cargo_test::workload::OwnedOutputs,
    ) -> CargoResult<()> {
        match &self.0 {
            Runtime::Retained(runtime) => runtime.enter_workload_harnesses(outputs),
            Runtime::Legacy(_) => {
                anyhow::bail!("workload harness phase requires original retained runtime")
            }
        }
    }
    pub(super) fn enter_workload_build_script(
        &self,
        original: Arc<crate::ops::cargo_test::workload::NativeOutput>,
    ) -> CargoResult<()> {
        match &self.0 {
            Runtime::Retained(runtime) => runtime.enter_workload_build_script(original),
            Runtime::Legacy(_) => {
                anyhow::bail!("workload script requires original retained runtime")
            }
        }
    }
    pub(super) fn finish_workload_build_script(&self) -> CargoResult<()> {
        match &self.0 {
            Runtime::Retained(runtime) => runtime.finish_workload_build_script(),
            Runtime::Legacy(_) => {
                anyhow::bail!("workload script requires original retained runtime")
            }
        }
    }

    pub(super) fn finish_workload_harnesses(&self) -> CargoResult<()> {
        match &self.0 {
            Runtime::Retained(runtime) => runtime.finish_workload_harnesses(),
            Runtime::Legacy(_) => Ok(()),
        }
    }
    pub(super) fn new(bcx: &BuildContext<'_, '_>) -> CargoResult<Option<Arc<Self>>> {
        #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
        if let Some(full) = bcx.gctx.original_bootstrap_full() {
            full.check_current()?;
            return Ok(None);
        }
        if crate::resource_worker_v3() {
            return v3::ResourceRuntime::new(bcx)
                .map(|runtime| Some(Arc::new(Self(Runtime::Retained(runtime)))));
        }
        Ok(v2::ResourceRuntime::new(bcx)?.map(|runtime| Arc::new(Self(Runtime::Legacy(runtime)))))
    }
    pub(super) fn jobserver(&self) -> Jobserver {
        match &self.0 {
            Runtime::Legacy(runtime) => runtime.jobserver(),
            Runtime::Retained(runtime) => runtime.jobserver(),
        }
    }

    pub(super) fn retain_workload_outputs(
        &self,
        capsule: Arc<super::build_runner::OriginalOutputLeases>,
        root: &std::path::Path,
    ) -> CargoResult<()> {
        match &self.0 {
            Runtime::Retained(runtime) => runtime.retain_workload_outputs(capsule, root),
            Runtime::Legacy(_) => {
                anyhow::bail!("workload output custody requires its original retained runtime")
            }
        }
    }

    pub(super) fn park_workload(&self) -> CargoResult<()> {
        match &self.0 {
            Runtime::Retained(runtime) => runtime.park_workload(),
            Runtime::Legacy(_) => {
                anyhow::bail!("workload phase requires its original retained runtime")
            }
        }
    }

    pub(super) fn try_root(
        self: &Arc<Self>,
        external_serial: bool,
    ) -> CargoResult<Option<Arc<RootContext>>> {
        Ok(match &self.0 {
            Runtime::Legacy(runtime) => runtime.try_root(external_serial)?.map(Root::Legacy),
            Runtime::Retained(runtime) => runtime.try_root(external_serial)?.map(Root::Retained),
        }
        .map(|root| Arc::new(RootContext(root))))
    }
}

impl RootContext {
    pub(super) fn verification_preparation(&self) -> CargoResult<Arc<crate::resource_v3::Startup>> {
        match &self.0 {
            Root::Retained(root) => root.verification_preparation(),
            Root::Legacy(_) => {
                anyhow::bail!("verification preparation requires retained original native context")
            }
        }
    }
    // Trust: keep the actual dispatch owner through authenticated legacy test
    // retirement. The separately gated v3 compiler domain supplies no test
    // handoff; a refusal must never select a second execution domain.
    pub(super) fn authenticated_test_handoff(
        self: &Arc<Self>,
    ) -> CargoResult<crate::ops::cargo_test::auth_scheduling::OwnedSchedulingHandoff> {
        match &self.0 {
            Root::Legacy(root) => {
                let mut handoff = root.authenticated_test_handoff()?;
                handoff.retain_origin(Arc::clone(self));
                Ok(handoff)
            }
            Root::Retained(_) => {
                anyhow::bail!("native v3 retained verified tests are not qualified")
            }
        }
    }

    pub(super) fn completed_workload_compiler(&self) -> CargoResult<Option<[u8; 16]>> {
        match &self.0 {
            Root::Retained(root) => root.completed_workload_compiler(),
            Root::Legacy(_) => Ok(None),
        }
    }

    pub(super) fn configure(
        &self,
        command: &mut ProcessBuilder,
        compiler: bool,
    ) -> CargoResult<()> {
        match &self.0 {
            Root::Legacy(root) => root.configure(command, compiler),
            Root::Retained(root) => root.configure(command, compiler),
        }
    }
}
