//! Native service entry and bounded dependency population. Ordinary compiler
//! nodes enter the maintained resolver/queue once and retain its actual output
//! and sequential original-runtime continuation. Unsupported native consumers
//! are FAILED nodes; no omitted/ignored population can make a job successful.
use super::context::{CompletedNode, NodeContext};
use crate::compiler::{
    UserIntent,
    native_job::{Attempt, NativeRetainedGraph, Options},
};
use crate::context::root_control::RootControl;
use crate::ops;
use crate::util::{CargoResult, Filesystem, GlobalContext};
use crate::workload_service::{
    Bootstrap,
    transport::{Control, Input, Output},
};
use crate::workspace::Workspace;
use anyhow::Context as _;
use cargo_util_terminal::Shell;
use std::ffi::OsString;
use std::os::unix::ffi::OsStringExt as _;
use std::path::PathBuf;
use std::sync::Arc;
use std::sync::atomic::Ordering;
use std::time::{Duration, Instant};
use trust_resource_controller::native_job::{
    CompileMode, Frontend, Kind, NodeId, Plan, TargetKind,
    service::{self, Binding, Outcome},
};
use trust_resource_controller::workload::budget;
enum NodeAttempt {
    Compile(Attempt),
    Compare(super::comparison_attempt::Attempt),
    Land(super::land_attempt::Attempt),
    Verify(super::verification::VerificationAttempt),
}
impl NodeAttempt {
    fn reporting_failed(&mut self, error: anyhow::Error) {
        match self {
            Self::Compile(attempt) => attempt.reporting_failed(error),
            Self::Compare(attempt) => attempt.reporting_failed(error),
            Self::Land(attempt) => attempt.reporting_failed(error),
            Self::Verify(attempt) => attempt.reporting_failed(error),
        }
    }
    fn completed(self, id: NodeId, entered: Instant, returned: Instant) -> CompletedNode {
        match self {
            Self::Compile(attempt) => CompletedNode::compiler(id, entered, returned, attempt),
            Self::Compare(attempt) => CompletedNode::compared(id, entered, returned, attempt),
            Self::Land(attempt) => CompletedNode::land(id, entered, returned, attempt),
            Self::Verify(attempt) => CompletedNode::verified(id, entered, returned, attempt),
        }
    }
}
fn path(bytes: &[u8]) -> PathBuf {
    PathBuf::from(OsString::from_vec(bytes.to_vec()))
}
fn reason(error: impl std::fmt::Display) -> String {
    let mut value = error.to_string().replace('\0', "?");
    if value.len() > 4096 {
        let mut end = 4096;
        while !value.is_char_boundary(end) {
            end -= 1;
        }
        value.truncate(end);
    }
    if value.is_empty() {
        value.push_str("native node failed");
    }
    value
}
pub(super) fn run(
    args: &[OsString],
    bootstrap: Bootstrap,
    configure_lane: impl FnOnce() -> CargoResult<()>,
) -> CargoResult<()> {
    anyhow::ensure!(
        args.len() == 1 && super::requested(args),
        "general native job accepts only its exact private argument"
    );
    let entered = Instant::now();
    let mut input = Input::capture_stdin()?;
    let plan =
        Plan::decode(&input.frame(entered + Duration::from_nanos(budget::STARTUP_NS), None)?)?;
    let prepared = crate::resource_v3::native_job::startup::prepare(plan, bootstrap, entered)?;
    let startup = prepared.startup;
    let inputs = prepared.inputs;
    let plan = inputs
        .native_plan()
        .context("native ready omitted its original full plan")?
        .clone();
    let outputs = startup
        .native_outputs
        .get()
        .context("native ready omitted original selected-output registry")?
        .clone();
    let artifacts = outputs.artifacts();
    let process = startup
        .workload_process
        .as_ref()
        .context("native job lost original process")?;
    let binding = Binding {
        root_attempt: inputs.evidence.root_attempt(),
        invocation_sha256: inputs.evidence.invocation_sha256(),
    };
    let output = Output::capture_stdout(prepared.deadline, process.cancelled.clone())?;
    let (mut input, control) =
        Control::start_native_job(binding, input, prepared.deadline, process.cancelled.clone())?;
    let mut control = Some(control);
    output.frame(
        &service::ready(binding, &prepared.ready)?,
        prepared.deadline,
    )?;
    configure_lane()?;
    let mut completed = Vec::new();
    completed.try_reserve_exact(plan.nodes.len())?;
    let mut observations = Vec::new();
    observations.try_reserve_exact(plan.nodes.len())?;
    let mut continuation: Option<NativeRetainedGraph> = None;
    let mut compiled_once = false;
    while completed.len() < plan.nodes.len() {
        let index = (0..plan.nodes.len())
            .find(|index| {
                !completed
                    .iter()
                    .any(|record: &CompletedNode| record.id().0 as usize == *index)
                    && plan.nodes[*index]
                        .dependencies
                        .iter()
                        .all(|dep| completed.iter().any(|record| record.id() == dep.node))
            })
            .context("validated native graph has no next complete prerequisite population")?;
        let id = NodeId(index as u32);
        let started = Instant::now();
        let deadline = started
            .checked_add(Duration::from_nanos(plan.nodes[index].timeout_ns))
            .context("native node deadline overflow")?
            .min(prepared.deadline);
        let context = NodeContext::new(id, &startup, &plan, &inputs, &outputs, &completed);
        let mut blocked = false;
        let call = match context {
            Err(error) => {
                blocked = true;
                Err(error)
            }
            Ok(context) => {
                if process.cancelled.load(Ordering::Acquire)
                    || process.poisoned.load(Ordering::Acquire)
                    || Instant::now() >= prepared.deadline
                {
                    blocked = true;
                    Err(anyhow::anyhow!(
                        "original native job was cancelled, poisoned or expired"
                    ))
                } else {
                    input.begin_native_node(deadline)?;
                    let result = match &plan.nodes[index].kind {
                        Kind::Compile {
                            frontend: Frontend::OriginalSdk,
                            ..
                        } => {
                            if compiled_once && continuation.is_none() {
                                Err(anyhow::anyhow!(
                                    "next compiler node lacks its actual original runtime/GNU continuation"
                                ))
                            } else {
                                compiled_once = true;
                                original_compile(
                                    &context,
                                    artifacts.clone(),
                                    continuation.take(),
                                    &mut control,
                                )
                                .map(NodeAttempt::Compile)
                            }
                        }
                        Kind::Compile { frontend: Frontend::Produced(frontend), .. } => {
                            context.artifact(frontend).and_then(|artifact| artifact.program()).and_then(|frontend| {
                                let inputs = context.outputs().inputs(context.node())?;
                                let operation = continuation.take().context("produced compiler lacks SAME original runtime/GNU continuation")?.resume_operation()?;
                                Ok(NodeAttempt::Compile(crate::compiler::native_job::produced::run(
                                    context.outputs().clone(), artifacts.clone(), inputs, context.node(), frontend, operation, deadline)))
                            })
                        },
                        Kind::Verify { .. } => continuation
                            .take()
                            .context(
                                "native Verify lacks the actual original runtime/GNU continuation",
                            )
                            .and_then(|original| original.resume_operation())
                            .map(|operation| {
                                NodeAttempt::Verify(super::verification::run(
                                    &context, operation, deadline,
                                ))
                            }),
                        Kind::Tests { .. } | Kind::Run { .. } => Err(anyhow::anyhow!(
                            "general native application requires its actual registered member/input/scope consumer"
                        )),
                        Kind::Compare { .. } => Ok(NodeAttempt::Compare(
                            super::comparison_attempt::Attempt::run(&context, continuation.take()),
                        )),
                        Kind::Land { .. } => Ok(NodeAttempt::Land(
                            super::land_attempt::Attempt::run(&context, continuation.take()),
                        )),
                    };
                    let ended = input.end_native_node();
                    match (result, ended) {
                        (Ok(attempt), Ok(())) => Ok(attempt),
                        (Err(error), _) => Err(error),
                        (Ok(mut attempt), Err(error)) => {
                            attempt.reporting_failed(error.into());
                            Ok(attempt)
                        }
                    }
                }
            }
        };
        let returned = Instant::now();
        let mut record = match call {
            Ok(attempt) => attempt.completed(id, started, returned),
            Err(error) => CompletedNode::refused(id, started, returned, error),
        };
        if let Some(original) = record.take_continuation() {
            continuation = Some(original);
        }
        let outcome = match record.failure() {
            Some(failure) if blocked => Outcome::Blocked {
                reason: reason(failure),
            },
            Some(failure) => Outcome::Failed {
                reason: reason(failure),
            },
            None if record.succeeded() => Outcome::Succeeded,
            None => Outcome::Failed {
                reason: "native node omitted an actual successful completion owner".into(),
            },
        };
        let observation = service::Node {
            binding,
            id,
            outcome,
            parent_elapsed_ns: u64::try_from(record.interval().elapsed().as_nanos())
                .unwrap_or(u64::MAX),
            compiler_executions: record.compiler_executions(),
            reused_units: record.reused_units(),
        };
        output.frame(&observation.encode()?, prepared.deadline)?;
        observations.push(observation);
        completed.push(record);
    }
    input.finish()?;
    inputs.validate()?;
    let until =
        (Instant::now() + Duration::from_nanos(budget::SETTLEMENT_NS)).min(prepared.deadline);
    let bank = startup
        .workload_bank
        .as_ref()
        .context("native final graph lost original bank")?;
    bank.park()?;
    while !bank.is_drained()? {
        anyhow::ensure!(
            Instant::now() < until,
            "native job original bank did not positively drain"
        );
        std::thread::sleep(Duration::from_millis(5));
    }
    let mut broker = startup
        .workload_control
        .as_ref()
        .context("native final graph lost original broker")?
        .lock()
        .map_err(|_| anyhow::anyhow!("native original broker poisoned"))?
        .take()
        .context("native original broker consumed twice")?;
    broker.drained()?;
    let _control = broker.finish()?;
    startup
        .workload_evidence
        .as_ref()
        .context("native final graph lost original evidence owner")?
        .synchronize(until)?;
    observations.sort_by_key(|node| node.id);
    output.frame(
        &service::graph(binding, &plan, &observations)?,
        prepared.deadline,
    )?;
    anyhow::ensure!(
        !process.cancelled.load(Ordering::Acquire)
            && !process.poisoned.load(Ordering::Acquire)
            && observations
                .iter()
                .all(|node| matches!(&node.outcome, Outcome::Succeeded)),
        "native job did not complete its entire original successful node population"
    );
    drop(continuation);
    drop(completed);
    drop(artifacts);
    Ok(())
}
fn original_compile(
    context: &NodeContext<'_>,
    artifacts: Arc<crate::resource_v3::native_job::outputs::Artifacts>,
    continuation: Option<NativeRetainedGraph>,
    control: &mut Option<RootControl>,
) -> CargoResult<Attempt> {
    let Kind::Compile {
        source,
        output,
        unit,
        mode,
        features,
        frontend: Frontend::OriginalSdk,
    } = &context.plan().nodes[context.node().0 as usize].kind
    else {
        anyhow::bail!("ordinary compiler received another native node kind")
    };
    let inputs = context.outputs().inputs(context.node())?;
    let continuation = continuation
        .map(|original| original.resume(inputs.clone()))
        .transpose()?;
    let mut gctx = GlobalContext::new(
        Shell::new(),
        path(&context.plan().sources[*source as usize].root),
        path(&context.plan().inputs.cargo_home),
    );
    gctx.install_root_control(
        control
            .take()
            .context("native compiler lost its original cancellation endpoint")?,
    )?;
    let attempted = (|| {
        let target = path(&context.plan().outputs[*output as usize].root);
        gctx.configure(
            0,
            false,
            Some("never"),
            false,
            true,
            true,
            &Some(target.clone()),
            &[],
            &[],
        )?;
        let mut workspace = Workspace::new(
            &path(&context.plan().sources[*source as usize].manifest.path),
            &gctx,
        )?;
        workspace.set_target_dir(Filesystem::new(target));
        inputs.validate_target(workspace.target_dir().as_path_unlocked())?;
        let intent = match (mode, unit.kind) {
            (CompileMode::Check, kind) => UserIntent::Check {
                test: matches!(kind, TargetKind::Test),
            },
            (_, TargetKind::Test) => UserIntent::Test,
            _ => UserIntent::Build,
        };
        let mut options = ops::CompileOptions::new(&gctx, intent)?;
        options.build_config.jobs = context.startup().local_ceiling;
        options.spec = ops::Packages::Packages(vec![unit.package.clone()]);
        options.cli_features =
            crate::resolver::features::CliFeatures::from_command_line(features, false, true)?;
        options.filter = ops::CompileFilter::from_raw_arguments(
            matches!(unit.kind, TargetKind::Library),
            if matches!(unit.kind, TargetKind::Binary) {
                vec![unit.target.clone()]
            } else {
                Vec::new()
            },
            false,
            if matches!(unit.kind, TargetKind::Test) {
                vec![unit.target.clone()]
            } else {
                Vec::new()
            },
            false,
            Vec::new(),
            false,
            Vec::new(),
            false,
            false,
        );
        ops::cargo_compile::compile_native_job(
            &workspace,
            &options,
            Arc::new(Options::new(
                context.outputs().clone(),
                artifacts,
                inputs,
                context.node(),
            )),
            continuation,
        )
    })();
    *control = gctx.into_root_control();
    anyhow::ensure!(
        control.is_some(),
        "native compiler lost its original cancellation endpoint after scoped return"
    );
    attempted
}
