//! Actual produced-frontend node consumer. Preparation acquires the SAME real
//! Layouts; execution goes through the native coordinator and its opaque graph
//! acknowledgement. A report/path/Fresh state cannot construct an artifact.
use super::*;
use crate::util::GlobalContext;
use cargo_util_terminal::Shell;
use std::time::Instant;
use trust_resource_controller::native_job::Frontend;
use trust_resource_controller::workload::host::coordinator::{self, Plan};

pub(crate) struct Original {
    completed: super::super::resource_runtime_v3::native_coordinator::Completed,
    plan: Plan,
    frontend: Arc<NativeOutput>,
}
impl Original {
    pub(super) fn require(&self) -> CargoResult<()> {
        anyhow::ensure!(
            self.completed.phase_failure.is_none(),
            "produced coordinator phase failed to close"
        );
        self.completed.attempt.require_plan(&self.plan)?;
        self.completed.attempt.require_frontend(&self.frontend)
    }
    pub(super) fn require_frontend(&self, frontend: &Arc<NativeOutput>) -> CargoResult<()> {
        self.require()?;
        anyhow::ensure!(
            Arc::ptr_eq(frontend, &self.frontend),
            "native node executed another retained frontend"
        );
        self.completed.attempt.require_frontend(frontend)
    }
}
/// Retain the whole original operation if suspension cannot positively prove
/// drain. A catch/unwind must not free its runtime, phase or native IO owners.
struct State {
    operation: Option<NativeOperationGraph>,
    completed: Option<super::super::resource_runtime_v3::native_coordinator::Completed>,
}
impl Drop for State {
    fn drop(&mut self) {
        if self.operation.is_some() {
            if let Some(completed) = self.completed.take() {
                std::mem::forget(completed);
            }
            if let Some(operation) = self.operation.take() {
                std::mem::forget(operation);
            }
        }
    }
}

pub(crate) fn run(
    registry: Arc<Outputs>,
    artifacts: Arc<crate::resource_v3::native_job::outputs::Artifacts>,
    inputs: Arc<Inputs>,
    node: NodeId,
    frontend: Arc<NativeOutput>,
    operation: NativeOperationGraph,
    deadline: Instant,
) -> Attempt {
    let mut state = State {
        operation: Some(operation),
        completed: None,
    };
    let mut selected = None;
    let mut compiler_executions = 0;
    let mut warm_units = 0;
    let result = (|| -> CargoResult<Artifact> {
        let operation = state
            .operation
            .as_ref()
            .context("produced operation missing")?;
        let preparation = operation
            .prepare_local()?
            .context("produced preparation has no actual original CPU unit")?;
        let startup = crate::resource_v3::native_job::require(registry.plan())?;
        preparation.require(&startup)?;
        artifacts.require_outputs(&registry)?;
        let declared = registry
            .plan()
            .nodes
            .get(node.0 as usize)
            .context("produced node missing")?;
        let Kind::Compile {
            source,
            unit,
            mode,
            features,
            frontend: Frontend::Produced(_),
            ..
        } = &declared.kind
        else {
            anyhow::bail!("produced compiler received another native node role")
        };
        anyhow::ensure!(
            unit.kind == TargetKind::Binary,
            "native coordinator currently selects a normal binary graph"
        );
        anyhow::ensure!(
            registry.plan().sources.len() <= coordinator::MAX_SOURCES,
            "complete original source population exceeds coordinator bound"
        );
        inputs.validate()?;
        frontend.validate(deadline)?;
        let plan = Plan {
            sources: registry
                .plan()
                .sources
                .iter()
                .map(|source| coordinator::Source {
                    root: source.root.clone(),
                    sha256: source.namespace_sha256,
                })
                .collect(),
            manifest: registry.plan().sources[*source as usize].manifest.clone(),
            package: unit.package.clone(),
            binary: unit.target.clone(),
            features: features.clone(),
            output_root: inputs
                .held_output_root()
                .path()
                .as_os_str()
                .as_encoded_bytes()
                .to_vec(),
            cargo_home: registry.plan().inputs.cargo_home.clone(),
            sdk_root: registry.plan().inputs.sdk_root.clone(),
            compiler: registry.plan().inputs.compiler.clone(),
            mode: match mode {
                CompileMode::Build => coordinator::Mode::Build,
                CompileMode::Check => coordinator::Mode::Check,
            },
            timeout_ns: declared.timeout_ns,
        };
        plan.validate()?;
        let mut gctx = GlobalContext::new(
            Shell::new(),
            path(&registry.plan().sources[*source as usize].root),
            path(&plan.cargo_home),
        );
        super::super::candidate_coordinator::configure_context(&mut gctx, &plan)?;
        let workspace = super::super::candidate_coordinator::selected_workspace(&gctx, &plan)?;
        let options = super::super::candidate_coordinator::compile_options(&gctx, &plan)?;
        let leases = OriginalOutputLeases::prepare_native(
            &workspace,
            &options.build_config,
            inputs.clone(),
            &registry,
            &preparation,
        )?;
        preparation.require(&startup)?;
        // SAME real guards acquired; no resolver/BuildRunner/compile was used
        // just to obtain them. Close the local unit before bank/Host selection.
        drop(options);
        drop(workspace);
        drop(gctx);
        drop(preparation);
        selected = Some((plan.clone(), unit.clone()));
        let mut ledger = artifacts.take_ledger(&inputs)?;
        let native = operation.run_coordinator(
            frontend.clone(),
            inputs.clone(),
            plan.clone(),
            leases.clone(),
            &mut ledger,
            deadline,
        );
        // Retain actual native completion BEFORE any fallible cache/postcheck.
        let error = match native {
            Ok(completed) => {
                state.completed = Some(completed);
                None
            }
            Err(error) => Some(error),
        };
        // Pre-admission refusal must not discard unrelated real warm owners.
        if let Some(ledger) = ledger {
            artifacts.retain_ledger(&inputs, ledger)?;
        }
        if let Some(error) = error {
            return Err(error);
        }
        let completed = state
            .completed
            .as_mut()
            .context("produced coordinator lost actual completion")?;
        // Retain native completion before any fallible graph/postcheck. Move
        // the SAME ledger for later epochs even when this epoch failed.
        if let Some(ledger) = completed.attempt.relay.take_dependencies()? {
            artifacts.retain_ledger(&inputs, ledger)?;
        }
        completed.attempt.require_plan(&plan)?;
        completed.attempt.require_frontend(&frontend)?;
        let counts = completed.attempt.relay.compilation_counts()?;
        compiler_executions = counts.0;
        warm_units = counts.1;
        let output = match mode {
            CompileMode::Build => {
                let programs = completed.attempt.published_programs()?;
                anyhow::ensure!(
                    programs.len() == 1,
                    "selected normal binary must have one actual published executable"
                );
                OwnedOutput::Program(NativeOutput::from_published(programs[0].clone())?)
            }
            CompileMode::Check => {
                anyhow::ensure!(
                    completed.attempt.published_programs()?.is_empty(),
                    "Check graph unexpectedly published an executable"
                );
                OwnedOutput::PublishedGraph
            }
        };
        // Artifact construction below retains this actual lifecycle, not DATA
        // metadata or an invented ordinary-queue Materialization.
        Ok(Artifact {
            node,
            original: Arc::new(RetiredArtifact {
                key: format!("produced:{}", node.0),
                selection: unit.clone(),
                inputs: inputs.clone(),
                leases,
                exact: None,
                produced: None,
                output,
                command: None,
            }),
        })
    })();
    let original = match (state.completed.take(), selected.as_ref()) {
        (Some(completed), Some((plan, _))) => Some(Arc::new(Original {
            completed,
            plan: plan.clone(),
            frontend,
        })),
        (Some(completed), None) => {
            std::mem::forget(completed);
            None
        }
        (None, _) => None,
    };
    let (result, artifact) = match result {
        Ok(mut artifact) => {
            let original = original
                .as_ref()
                .expect("actual artifact has native completion")
                .clone();
            // Sole-owned just-built record; no Clone or DATA constructor.
            Arc::get_mut(&mut artifact.original)
                .expect("new artifact shared prematurely")
                .produced = Some(original);
            (Ok(()), Some(artifact))
        }
        Err(error) => (Err(error), None),
    };
    let operation = state
        .operation
        .take()
        .expect("actual produced operation missing at suspension");
    let (continuation, continuation_failure) = match operation.try_suspend() {
        Ok(continuation) => (Some(continuation), None),
        Err((error, operation)) => {
            // Preserve all unknown owners; no command status can drain them.
            state.operation = Some(operation);
            (None, Some(format!("{error:#}")))
        }
    };
    // Original is retained in both success and refusal; phase failures prevent
    // successful artifact validation and never fabricate a continuation.
    let result = match original
        .as_ref()
        .and_then(|owner| owner.completed.phase_failure.as_ref())
    {
        Some(error) => Err(result
            .err()
            .unwrap_or_else(|| anyhow::anyhow!("produced native phase failed: {error:#}"))),
        None => result,
    };
    Attempt {
        result,
        artifact,
        continuation,
        continuation_failure,
        compiler_executions,
        warm_units,
        _recorder: verification::Recorder::new(),
        produced: original,
    }
}
