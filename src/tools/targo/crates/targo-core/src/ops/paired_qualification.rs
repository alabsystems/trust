//! The native paired stages use ordinary Cargo resolution/fingerprints and
//! the existing admitted queues. No command scraping or capture compilation.
//! Actual distinct paired startup is mandatory; decoded plan data grants none.
use crate::compiler::{
    Compilation, UserIntent,
    qualification::{self, RetainedGraph},
};
use crate::context::root_control::RootControl;
use crate::ops::cargo_test::workload::{self, Inputs};
use crate::ops::{self, CompileOptions};
use crate::util::{CargoResult, Filesystem, GlobalContext};
use crate::workspace::Workspace;
use anyhow::Context as _;
use cargo_util_terminal::Shell;
use std::ffi::OsString;
use std::os::unix::ffi::OsStringExt as _;
use std::path::PathBuf;
use std::sync::Arc;
use std::time::Duration;
use trust_resource_controller::paired_qualification::PairedInvocation;
fn path(value: &[u8]) -> PathBuf {
    PathBuf::from(OsString::from_vec(value.to_vec()))
}

pub(crate) struct AyStage {
    /// Original unverified compile/preparation result, separate from the two
    /// independently observed verification results below.
    pub result: CargoResult<()>,
    pub verification: qualification::Run,
    pub continuation: Option<RetainedGraph>,
    pub continuation_failure: Option<String>,
    pub input_failure: Option<String>,
    /// SAME private cancellation endpoint; never a new or competing reader.
    pub control: RootControl,
}

pub(crate) fn run_ay(
    plan: Arc<PairedInvocation>,
    inputs: Arc<Inputs>,
    observer: Arc<dyn qualification::Observer>,
    shell: Shell,
    control: RootControl,
) -> CargoResult<AyStage> {
    let startup = crate::resource_v3::paired::require(&plan)?;
    let mut context =
        GlobalContext::new(shell, path(&plan.ay.root), path(&plan.consumer.cargo_home));
    context.install_root_control(control)?;
    let observed = compile_ay(&mut context, plan, inputs.clone(), observer);
    let (result, verification, mut continuation, mut continuation_failure) = match observed {
        Ok(mut attempt) => {
            let verification = attempt.compilation.qualification.take().unwrap_or_else(|| {
                blocked(
                    &attempt.result,
                    "original AY graph did not register verification dependents",
                )
            });
            drop(attempt.compilation);
            (
                attempt.result,
                verification,
                attempt.continuation,
                attempt.continuation_failure,
            )
        }
        Err(error) => {
            let result = Err(error);
            let mut verification = blocked(
                &result,
                "AY preparation failed before verification graph creation",
            );
            if result.as_ref().err().is_some_and(|error| {
                error
                    .downcast_ref::<crate::util::logger::native::Failure>()
                    .is_some()
            }) {
                verification.fatal_failure = Some("original native compiler report failed".into());
            }
            (result, verification, None, None)
        }
    };
    if let Some(failure) = &verification.fatal_failure {
        if let Some(process) = &startup.workload_process {
            process
                .poisoned
                .store(true, std::sync::atomic::Ordering::Release);
        }
        drop(continuation.take());
        continuation_failure.get_or_insert_with(|| {
            format!("original AY reporting/input channel failed: {failure}")
        });
    }
    let input_failure = inputs.validate().err().map(|error| format!("{error:#}"));
    if let Some(failure) = &input_failure {
        if let Some(process) = &startup.workload_process {
            process
                .poisoned
                .store(true, std::sync::atomic::Ordering::Release);
        }
        drop(continuation.take());
        continuation_failure
            .get_or_insert_with(|| format!("original AY stage inputs changed: {failure}"));
    }
    let control = context
        .into_root_control()
        .context("AY stage lost its original cancellation endpoint")?;
    Ok(AyStage {
        result,
        verification,
        continuation,
        continuation_failure,
        input_failure,
        control,
    })
}
fn blocked(result: &CargoResult<()>, fallback: &str) -> qualification::Run {
    let reason = result.as_ref().err().map_or_else(
        || fallback.to_owned(),
        |error| format!("{fallback}: {error:#}"),
    );
    qualification::Run {
        blocked: qualification::Action::ALL
            .into_iter()
            .map(|action| (action, reason.clone()))
            .collect(),
        original_failure: Some(reason),
        ..qualification::Run::default()
    }
}
fn compile_ay<'gctx>(
    context: &'gctx mut GlobalContext,
    plan: Arc<PairedInvocation>,
    inputs: Arc<Inputs>,
    observer: Arc<dyn qualification::Observer>,
) -> CargoResult<qualification::Attempt<'gctx>> {
    let startup = crate::resource_v3::paired::require(&plan)?;
    context.prepare_paired_ay_measurement(&plan, &inputs)?;
    let target = path(&plan.consumer.output_root);
    context.configure(
        0,
        false,
        Some("never"),
        false,
        true,
        true,
        &Some(target.clone()),
        &["mem-stats".into()],
        &[],
    )?;
    let mut workspace = Workspace::new(&path(&plan.ay.workspace_manifest.path), context)?;
    workspace.set_target_dir(Filesystem::new(target));
    let mut options = CompileOptions::new(context, UserIntent::Build)?;
    // This purpose has a closed policy: min(actual retained native domain,7),
    // selected by actual startup, plus the bank's live memory/CPU veto. It is
    // not a requested count or machine-exclusivity claim. NUM_JOBS comes from
    // this actual BuildConfig and stays unchanged through script phases.
    options.build_config.jobs = startup.local_ceiling;
    options.spec = ops::Packages::Packages(vec!["ay-proof-common".into()]);
    options.filter = ops::CompileFilter::from_raw_arguments(
        true,
        Vec::new(),
        false,
        Vec::new(),
        false,
        Vec::new(),
        false,
        Vec::new(),
        false,
        false,
    );
    let qualification = qualification::Options::new(plan, inputs, observer)?;
    ops::cargo_compile::compile_with_native_qualification(&workspace, &options, qualification)
}

/// Caller installs the SAME original control endpoint returned by run_ay in
/// this fresh consumer context. Known AY semantic failures remain in AyStage;
/// transport/input/unknown failures may never resume or reconstruct authority.
pub(crate) fn run_consumer<'gctx>(
    context: &'gctx mut GlobalContext,
    plan: &PairedInvocation,
    inputs: Arc<Inputs>,
    observer: Arc<dyn workload::Observer>,
    continuation: Option<RetainedGraph>,
) -> CargoResult<Compilation<'gctx>> {
    let startup = crate::resource_v3::paired::require(plan)?;
    let result = compile_consumer(context, plan, inputs.clone(), observer, continuation);
    // Rebind on EVERY known outcome, including preparation/selection errors.
    let rebind = inputs.validate();
    if (rebind.is_err()
        || result.as_ref().err().is_some_and(|error| {
            error
                .downcast_ref::<crate::util::logger::native::Failure>()
                .is_some()
        }))
        && let Some(process) = &startup.workload_process
    {
        process
            .poisoned
            .store(true, std::sync::atomic::Ordering::Release);
    }
    match (result, rebind) {
        (Ok(compilation), Ok(())) => Ok(compilation),
        (Err(error), Ok(())) | (Ok(_), Err(error)) => Err(error),
        (Err(error), Err(drift)) => Err(anyhow::anyhow!(
            "{error:#}; original consumer inputs also changed: {drift:#}"
        )),
    }
}
fn compile_consumer<'gctx>(
    context: &'gctx mut GlobalContext,
    plan: &PairedInvocation,
    inputs: Arc<Inputs>,
    observer: Arc<dyn workload::Observer>,
    continuation: Option<RetainedGraph>,
) -> CargoResult<Compilation<'gctx>> {
    let startup = crate::resource_v3::paired::require(plan)?;
    anyhow::ensure!(
        context.has_root_control() && context.cwd() == path(&plan.consumer.cwd),
        "consumer lost original control/workspace binding"
    );
    inputs.validate()?;
    // Actual next-workspace compiler probes need the SAME bank resumed BEFORE
    // configure/create_bcx. Only this live token can return its original GNU
    // escrow and runtime. If no runtime existed before known AY preparation
    // failure, normal construction creates the first one; any second refuses.
    let continuation = continuation.map(RetainedGraph::resume).transpose()?;
    let target = path(&plan.consumer.output_root);
    context.configure(
        0,
        false,
        Some("never"),
        false,
        true,
        true,
        &Some(target.clone()),
        &["mem-stats".into()],
        &[],
    )?;
    let mut workspace = Workspace::new(&path(&plan.consumer.cwd).join("Cargo.toml"), context)?;
    workspace.set_target_dir(Filesystem::new(target));
    inputs.validate_target(workspace.target_dir().as_path_unlocked())?;
    let mut options = CompileOptions::new(context, UserIntent::Test)?;
    options.build_config.jobs = startup.local_ceiling;
    options.spec = ops::Packages::Packages(vec!["trust-vc-core".into()]);
    options.filter = ops::CompileFilter::from_raw_arguments(
        false,
        Vec::new(),
        false,
        trust_test_execution::workload::TARGETS
            .iter()
            .map(|target| (*target).to_owned())
            .collect(),
        false,
        Vec::new(),
        false,
        Vec::new(),
        false,
        false,
    );
    let compiler_report = workload::compiler_report(observer.clone());
    let graph = workload::Options {
        plan: workload::Plan::new(
            plan.consumer.repetitions,
            Duration::from_nanos(plan.consumer.timeout_ns),
        )?,
        observer,
        inputs,
    }
    .graph(&workspace)?;
    ops::cargo_compile::compile_with_paired_test_execution(
        &workspace,
        &options,
        graph,
        continuation,
        compiler_report,
    )
}
