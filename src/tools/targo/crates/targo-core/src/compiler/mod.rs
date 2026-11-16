//! # Interact with the compiler
//!
//! If you consider [`ops::cargo_compile::compile`] as a `rustc` driver but on
//! Cargo side, this module is kinda the `rustc_interface` for that merits.
//! It contains all the interaction between Cargo and the rustc compiler,
//! from preparing the context for the entire build process, to scheduling
//! and executing each unit of work (e.g. running `rustc`), to managing and
//! caching the output artifact of a build.
//!
//! However, it hasn't yet exposed a clear definition of each phase or session,
//! like what rustc has done. Also, no one knows if Cargo really needs that.
//! To be pragmatic, here we list a handful of items you may want to learn:
//!
//! * [`BuildContext`] is a static context containing all information you need
//!   before a build gets started.
//! * [`BuildRunner`] is the center of the world, coordinating a running build and
//!   collecting information from it.
//! * [`custom_build`] is the home of build script executions and output parsing.
//! * [`fingerprint`] not only defines but also executes a set of rules to
//!   determine if a re-compile is needed.
//! * [`job_queue`] is where the parallelism, job scheduling, and communication
//!   machinery happen between Cargo and the compiler.
//! * [`layout`] defines and manages output artifacts of a build in the filesystem.
//! * [`unit_dependencies`] is for building a dependency graph for compilation
//!   from a result of dependency resolution.
//! * [`Unit`] contains sufficient information to build something, usually
//!   turning into a compiler invocation in a later phase.
//!
//! [`ops::cargo_compile::compile`]: crate::ops::compile

mod action_command;
mod action_inputs;
mod action_sandbox;
pub mod artifact;
#[cfg(any(target_os = "linux", target_os = "macos"))]
pub(crate) mod candidate_commands;
#[cfg(any(target_os = "linux", target_os = "macos"))]
pub mod candidate_coordinator;
#[cfg(any(target_os = "linux", target_os = "macos"))]
pub(crate) mod candidate_dependencies;
#[cfg(any(target_os = "linux", target_os = "macos"))]
pub(crate) mod candidate_runner;
#[cfg(any(target_os = "linux", target_os = "macos"))]
pub(crate) mod qualification;
pub mod qualification_command;
mod shared_dependencies;
// Trust: compiler-declared managed cache ownership, separate from proof transport.
mod build_config;
// Trust: DC-12a, the receipt a successful build keeps of the units it used.
mod build_receipt;
// Trust: DC-12b, the incremental folders a build directory keeps.
mod incremental_trim;
pub(crate) mod build_context;
pub(crate) mod build_runner;
mod compilation;
mod compile_kind;
mod crate_type;
mod custom_build;
mod post_build_compiler;
mod rustc_command_context;
pub(crate) mod trust_witness_cleanup;
// Trust: deterministic evidence identities over the resolved dependency graph.
#[cfg(any(target_os = "linux", target_os = "macos"))]
pub(crate) mod candidate_semantics;
mod exact_unit;
mod executable_output;
pub(crate) mod fingerprint;
pub mod future_incompat;
pub(crate) mod job_queue;
pub(crate) mod layout;
mod links;
mod locking;
mod lto;
#[cfg(any(target_os = "linux", target_os = "macos"))]
pub(crate) mod native_job;
// Trust: current compiler reports gate native pipelined metadata readiness.
mod metadata_readiness;
#[cfg(all(test, target_os = "macos", target_arch = "aarch64"))]
pub(crate) mod native_input_fixture;
mod output_depinfo;
mod output_observation;
mod output_sbom;
mod resource_budget;
#[cfg(any(target_os = "linux", target_os = "macos"))]
mod resource_descriptors;
#[cfg(any(target_os = "linux", target_os = "macos"))]
pub(crate) mod resource_fifo;
#[cfg(any(target_os = "linux", target_os = "macos"))]
mod resource_gnu_fixed;
// Trust: one original-owner path for post-compilation run and benchmark leaves.
#[cfg(any(target_os = "linux", target_os = "macos"))]
mod resource_inherited;
#[cfg(any(target_os = "linux", target_os = "macos"))]
mod resource_runtime;
#[cfg(any(target_os = "linux", target_os = "macos"))]
mod resource_runtime_v2;
#[cfg(any(target_os = "linux", target_os = "macos"))]
mod resource_runtime_v3;
#[cfg(any(target_os = "linux", target_os = "macos"))]
mod resource_serial;
pub mod rustdoc;
pub mod standard_lib;
mod target_execution;
pub mod timings;
// Trust (D2): the certified-monitor seal, obtainable only by capture.
mod trust_certified_monitor_seal;
// Trust (D2d): census of the doctests a verified `targo test` defers.
mod trust_doctest_census;
// Trust: a verification-off unit's `unit_id` leaves out the run's nonce.
pub(crate) mod trim_paths;
mod trust_unit_id;
mod unit;
pub mod unit_dependencies;
pub mod unit_graph;
pub mod unused_deps;

use crate::util::data_structures::{HashMap, HashSet};
use std::borrow::Cow;
use std::cell::OnceCell;
use std::collections::{BTreeMap, BTreeSet};
use std::env;
use std::ffi::{OsStr, OsString};
use std::fmt::Display;
use std::fs::{self, File};
use std::io::{BufRead, Write};
use std::ops::{Deref, Range};
use std::path::{Path, PathBuf};
use std::sync::{Arc, LazyLock};

use anyhow::{Context as _, Error};
use cargo_platform::{Cfg, Platform};
use cargo_util_terminal::report::{AnnotationKind, Group, Level, Renderer, Snippet};
use regex::Regex;
use tracing::{debug, instrument, trace};

pub use self::build_config::UserIntent;
pub use self::build_config::{BuildConfig, CompileMode, MessageFormat};
pub use self::build_context::BuildContext;
pub use self::build_context::DepKindSet;
pub use self::build_context::FileFlavor;
pub use self::build_context::FileType;
pub use self::build_context::RustcTargetData;
pub use self::build_context::TargetInfo;
pub use self::build_runner::{BuildRunner, Metadata, UnitHash};
use self::compilation::RustcProcessRole;
pub use self::compilation::{Compilation, Doctest, UnitOutput};
pub use self::compile_kind::{CompileKind, CompileKindFallback, CompileTarget};
pub use self::crate_type::CrateType;
pub use self::custom_build::LinkArgTarget;
pub use self::custom_build::{BuildOutput, BuildScriptOutputs, BuildScripts, LibraryPath};
pub(crate) use self::fingerprint::DirtyReason;
pub use self::fingerprint::RustdocFingerprint;
pub use self::job_queue::Freshness;
use self::job_queue::{Job, JobQueue, JobState, Work};
pub(crate) use self::layout::Layout;
pub use self::lto::Lto;
use self::output_depinfo::output_depinfo;
use self::output_sbom::build_sbom;
use self::rustc_command_context::RustcCommandContext;
use self::trim_paths::trim_paths_args_rustdoc;
use self::trust_certified_monitor_seal::CertifiedMonitorSeal;
use self::unit_graph::UnitDep;

use crate::compiler::future_incompat::FutureIncompatReport;
use crate::compiler::locking::LockKey;
use crate::compiler::timings::SectionTiming;
pub use crate::compiler::unit::Unit;
pub use crate::compiler::unit::UnitIndex;
pub use crate::compiler::unit::UnitInterner;
use crate::context::FingerprintMethod;
use crate::diagnostics::get_key_value;
use crate::util::OnceExt;
use crate::util::errors::{CargoResult, VerboseError};
use crate::util::interning::InternedString;
use crate::util::machine_message::{self, Message};
use crate::util::process_authority::{
    CARGO_PRIMARY_PACKAGE_ENV, FIX_ENV_INTERNAL, FIX_PROXY_CONTROL_ENVS,
    RUSTC_WORKSPACE_WRAPPER_ENV, is_authenticated_targo_process_authority_env,
    is_benign_build_script_provenance_env, validate_verified_command_runtime_library_authority,
};
use crate::util::rustc_options::{canonical_codegen_backend_value, rustc_option_parts};
use crate::util::tippy_arg_protocol::{CLIPPY_ARGS_ENV, TIPPY_ENCODED_ARGS_ENV};
use crate::util::{add_path_args, internal, path_args};
use crate::workspace::manifest::TargetSourcePath;
use crate::workspace::profiles::Lto as ProfileLto;
use crate::workspace::profiles::{PanicStrategy, Profile, StripInner};
use crate::workspace::{Feature, PackageId, Target};
use crate::workspace::{Package, TargetKind};

use cargo_util::{ExecStats, ProcessBuilder, ProcessError, Sha256, StreamingOutputLimits, paths};
use cargo_util_schemas::manifest::TomlDebugInfo;
use cargo_util_terminal::Verbosity;
use rustfix::diagnostics::Applicability;

const RUSTDOC_CRATE_VERSION_FLAG: &str = "--crate-version";

// Trust: test graph selection uses the exact same explicit/inherited native
// request predicate as runtime construction, while unsupported hosts retain
// their legacy route and the frontend's explicit-mode platform refusal.
pub(crate) fn native_resources_requested(gctx: &crate::GlobalContext) -> bool {
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    {
        resource_runtime::requested(gctx)
    }
    #[cfg(not(any(target_os = "linux", target_os = "macos")))]
    {
        let _ = gctx;
        false
    }
}

// Trust: these match targo-trust's authenticated Cargo transport reader.
// Enforcing them inside Cargo as well closes the interval in which a compiler,
// rustdoc, or build script can grow a newline-free pipe buffer before the proof
// driver gets an opportunity to inspect the resulting Cargo JSON line. Upstream
// streams without a ceiling, so this is a divergence to keep across re-aligns.
const VERIFIED_TARGO_MAX_CHILD_LINE_BYTES: usize = 128 * 1024 * 1024;
const VERIFIED_TARGO_MAX_CHILD_STREAM_BYTES: usize = 512 * 1024 * 1024;

/// Trust: single choke point for every child-process stream Cargo reads, so a
/// re-align only has to redirect upstream's `exec_with_streaming` calls here
/// rather than rediscover which of them carry proof transport.
fn exec_with_targo_streaming_policy(
    cmd: &ProcessBuilder,
    on_stdout_line: &mut dyn FnMut(&str) -> CargoResult<()>,
    on_stderr_line: &mut dyn FnMut(&str) -> CargoResult<()>,
    capture_output: bool,
    capture_rusage: bool,
) -> (ExecStats, CargoResult<std::process::Output>) {
    // Trust: a test plan run holds custody of every child it starts
    // (`ops::cargo_test::plan_clock`): each compiler, build script and
    // linker runs in its own process group under the run's scope, so that a
    // bound that ran out, or a signal to Targo, ends a build that would
    // never end by itself. The stream ceilings are the verified lane's.
    if let Some(custody) =
        crate::ops::cargo_test::plan_clock::armed().and_then(|clock| clock.custody())
    {
        let mut cmd = cmd.clone();
        cmd.supervised_by(custody);
        return cmd.exec_with_streaming_limits_and_stats(
            on_stdout_line,
            on_stderr_line,
            capture_output,
            StreamingOutputLimits::new(
                VERIFIED_TARGO_MAX_CHILD_LINE_BYTES,
                VERIFIED_TARGO_MAX_CHILD_STREAM_BYTES,
            )
            .with_child_exit_cleanup(),
            capture_rusage,
        );
    }
    if crate::is_targo_invocation() && crate::trust_verified_targo() {
        cmd.exec_with_streaming_limits_and_stats(
            on_stdout_line,
            on_stderr_line,
            capture_output,
            StreamingOutputLimits::new(
                VERIFIED_TARGO_MAX_CHILD_LINE_BYTES,
                VERIFIED_TARGO_MAX_CHILD_STREAM_BYTES,
            ),
            capture_rusage,
        )
    } else {
        cmd.exec_with_streaming(
            on_stdout_line,
            on_stderr_line,
            capture_output,
            capture_rusage,
        )
    }
}

/// A glorified callback for executing calls to rustc. Rather than calling rustc
/// directly, we'll use an `Executor`, giving clients an opportunity to intercept
/// the build calls.
pub trait Executor: Send + Sync + 'static {
    /// Whether ordinary native-tool readset data describes this executor's
    /// compiler transport. Unknown executors stay cache-ineligible; this is
    /// neither process authentication nor permission/proof authority.
    fn supports_native_tool_inputs(&self) -> bool {
        false
    }

    /// Called after a rustc process invocation is prepared up-front for a given
    /// unit of work (may still be modified for runtime-known dependencies, when
    /// the work is actually executed).
    fn init(&self, _build_runner: &BuildRunner<'_, '_>, _unit: &Unit) {}

    /// Retain the actual finalized native command without a capture compilation.
    /// Requires original live workload output custody; default is unchanged.
    fn prepare_unit_observation(&self, _build: &BuildRunner<'_, '_>) -> CargoResult<()> {
        Ok(())
    }

    fn unit_command_observer(
        &self,
        _build: &BuildRunner<'_, '_>,
        _unit: &Unit,
    ) -> CargoResult<Option<Arc<dyn qualification_command::Observer>>> {
        Ok(None)
    }

    /// In case of an `Err`, Cargo will not continue with the build process for
    /// this package.
    ///
    /// When `capture_rusage` is set, the returned [`ExecStats`] hold the peak
    /// memory of the invocation (for `--timings`), even when it failed.
    fn exec(
        &self,
        cmd: &ProcessBuilder,
        id: PackageId,
        target: &Target,
        mode: CompileMode,
        on_stdout_line: &mut dyn FnMut(&str) -> CargoResult<()>,
        on_stderr_line: &mut dyn FnMut(&str) -> CargoResult<()>,
        capture_rusage: bool,
    ) -> (ExecStats, CargoResult<()>);

    /// Queried when queuing each unit of work. If it returns true, then the
    /// unit will always be rebuilt, independent of whether it needs to be.
    fn force_rebuild(&self, _unit: &Unit) -> bool {
        false
    }
}

/// A `DefaultExecutor` calls rustc without doing anything else. It is Cargo's
/// default behaviour.
#[derive(Copy, Clone)]
pub struct DefaultExecutor;

impl Executor for DefaultExecutor {
    fn supports_native_tool_inputs(&self) -> bool {
        true
    }

    #[instrument(name = "rustc", skip_all, fields(package = id.name().as_str(), process = cmd.to_string()))]
    fn exec(
        &self,
        cmd: &ProcessBuilder,
        id: PackageId,
        _target: &Target,
        _mode: CompileMode,
        on_stdout_line: &mut dyn FnMut(&str) -> CargoResult<()>,
        on_stderr_line: &mut dyn FnMut(&str) -> CargoResult<()>,
        capture_rusage: bool,
    ) -> (ExecStats, CargoResult<()>) {
        let (stats, result) = exec_with_targo_streaming_policy(
            cmd,
            on_stdout_line,
            on_stderr_line,
            false,
            capture_rusage,
        );
        (stats, result.map(drop))
    }
}

/// Builds up and enqueue a list of pending jobs onto the `job` queue.
///
/// Starting from the `unit`, this function recursively calls itself to build
/// all jobs for dependencies of the `unit`. Each of these jobs represents
/// compiling a particular package.
///
/// Note that **no actual work is executed as part of this**, that's all done
/// next as part of [`JobQueue::execute`] function which will run everything
/// in order with proper parallelism.
#[tracing::instrument(skip(build_runner, jobs, exec))]
fn compile<'gctx>(
    build_runner: &mut BuildRunner<'_, 'gctx>,
    jobs: &mut JobQueue<'gctx>,
    unit: &Unit,
    exec: &Arc<dyn Executor>,
    force_rebuild: bool,
) -> CargoResult<()> {
    // Trust: assertions are graph admission requirements, including for fresh
    // or compile-time-filtered units. Check before either cache branch and
    // before queue execution; JSON proof inventory is not the enforcement gate.
    require_trust_unit_verification_assertion(build_runner, unit)?;
    if !build_runner.compiled.insert(unit.clone()) {
        return Ok(());
    }

    // Trust: the unit graph is the last place a monitored test session can still
    // be refused as a whole. Once a job is enqueued the decision is per-process
    // and a build script has already been granted arbitrary execution, so both
    // admission checks have to happen before `jobs.enqueue` below.
    let monitor_authority_present = verified_targo_protocol_active()
        && build_runner
            .bcx
            .gctx
            .get_env_os(TRUST_TARGO_TEST_MONITOR_AUTHORITY_SESSION)
            .is_some();
    // Trust: same lane rule as `prepare_rustc` — an evidence-grade seal refuses
    // only in a lane that claims proof authority; the advisory lane forfeits it
    // and says so once per requested root.
    let execution_tcb_enforced = monitor_authority_present
        && trust_policy_claims_proof_authority(
            &unit.rustflags,
            build_runner
                .bcx
                .extra_args_for(unit)
                .map(Vec::as_slice)
                .unwrap_or_default(),
        )
        .map_err(anyhow::Error::msg)?;
    if monitor_authority_present
        && !execution_tcb_enforced
        && is_resolved_root_unit(unit, &build_runner.bcx.roots)
    {
        build_runner.bcx.gctx.shell().warn(format!(
            "advisory lane: certified-monitor execution TCB seals are forfeited for root unit {}::{}; test execution evidence in this session is not evidence-grade",
            unit.pkg.package_id(),
            unit.target.name()
        ))?;
    }
    reject_certified_monitor_custom_build_unit(
        execution_tcb_enforced,
        unit.target.is_custom_build() || unit.mode.is_run_custom_build(),
        &format!("{}::{}", unit.pkg.package_id(), unit.target.name()),
    )
    .map_err(anyhow::Error::msg)?;

    reject_compilation_during_prepared_execution(
        build_runner
            .bcx
            .gctx
            .get_env_os(TRUST_TARGO_PREPARED_TEST_SESSION),
    )
    .map_err(anyhow::Error::msg)?;

    let lock = if build_runner.bcx.gctx.cli_unstable().fine_grain_locking {
        Some(build_runner.lock_manager.lock_shared(build_runner, unit)?)
    } else {
        None
    };

    match build_runner
        .bcx
        .gctx
        .build_config()?
        .fingerprint
        .unwrap_or_default()
    {
        FingerprintMethod::Content => {
            if !build_runner.bcx.gctx.cli_unstable().checksum_freshness {
                build_runner.bcx.gctx.shell().warn(
                    r#"ignoring `build.fingerprint = "content"` without `-Zchecksum-freshness`"#,
                )?;
            }
        }
        FingerprintMethod::Mtime => {}
    }

    // If we are in `--compile-time-deps` and the given unit is not a compile time
    // dependency, skip compiling the unit and jumps to dependencies, which still
    // have chances to be compile time dependencies
    if !unit.skip_non_compile_time_dep {
        // Build up the work to be done to compile this unit, enqueuing it once
        // we've got everything constructed.
        fingerprint::prepare_init(build_runner, unit)?;

        let job = if unit.mode.is_run_custom_build() {
            custom_build::prepare(build_runner, unit)?
        } else if unit.mode.is_doc_test() {
            // Trust (D2d): a verified JSON run collects (never runs) this
            // Unit's doctests so the proof frontier can tell an empty doctest
            // Unit from one that defers real doctests.
            match trust_doctest_census::doctest_census_job(
                build_runner,
                unit,
                execution_tcb_enforced,
            )? {
                Some(job) => job,
                // We run these targets later, so this is just a no-op for now.
                None => Job::new_fresh(),
            }
        } else {
            let force = match &build_runner.lease_forces {
                Some(selected) => selected[unit],
                None => exec.force_rebuild(unit) || force_rebuild,
            };
            let mut job = fingerprint::prepare_target(build_runner, unit, force)?;
            let capture = exec
                .unit_command_observer(build_runner, unit)?
                .map(|observer| {
                    qualification_command::Capture::for_unit(
                        build_runner,
                        unit,
                        observer,
                        None,
                        None,
                    )
                    .map(Arc::new)
                })
                .transpose()?;
            job.before(if job.freshness().is_dirty() {
                let mut work = if unit.mode.is_doc() || unit.mode.is_doc_scrape() {
                    rustdoc(build_runner, unit)?
                } else {
                    rustc(build_runner, unit, exec, capture.clone(), false)?
                };
                if build_runner.bcx.gctx.cli_unstable().fine_grain_locking {
                    work = fingerprint::invalidate_before_build(build_runner, unit).then(work);
                }
                work.then(link_targets(build_runner, unit, false)?)
            } else {
                let output_options = OutputOptions::for_fresh(build_runner, unit);
                let manifest = ManifestErrorContext::new(build_runner, unit)?;
                let work = replay_output_cache(
                    unit.pkg.package_id(),
                    manifest,
                    &unit.target,
                    build_runner.files().message_cache_path(unit),
                    output_options,
                );
                // Need to link targets on both the dirty and fresh.
                let work = if capture.is_some() {
                    rustc(build_runner, unit, exec, capture.clone(), true)?.then(work)
                } else {
                    work
                };
                work.then(link_targets(build_runner, unit, true)?)
            });

            // Trust: the complete graph generation already owns every write
            // right before callbacks or Work preparation. The existing runtime
            // recheck stays on its worker; no inline Fresh job waits on queue IPC.
            if build_runner.bcx.gctx.cli_unstable().fine_grain_locking && job.freshness().is_dirty()
            {
                if let Some(lock) = lock {
                    let output_options = OutputOptions::for_fresh(build_runner, unit);
                    let manifest = ManifestErrorContext::new(build_runner, unit)?;
                    let fresh_work = replay_output_cache(
                        unit.pkg.package_id(),
                        manifest,
                        &unit.target,
                        build_runner.files().message_cache_path(unit),
                        output_options,
                    )
                    .then(link_targets(build_runner, unit, true)?);
                    let fresh_work = if capture.is_some() {
                        rustc(build_runner, unit, exec, capture.clone(), true)?.then(fresh_work)
                    } else {
                        fresh_work
                    };
                    job.recheck_after_lock(fresh_work, force);
                    job.before(prebuild_lock_exclusive(lock.clone()));
                    job.after(downgrade_lock_to_shared(lock));
                }
            }

            job
        };
        jobs.enqueue(build_runner, unit, job)?;
    }

    // Be sure to compile all dependencies of this target as well.
    let deps = Vec::from(build_runner.unit_deps(unit)); // Create vec due to mutable borrow.
    for dep in deps {
        compile(build_runner, jobs, &dep.unit, exec, false)?;
    }

    Ok(())
}

/// Generates the warning message used when fallible doc-scrape units fail,
/// either for rustdoc or rustc.
fn make_failed_scrape_diagnostic(
    build_runner: &BuildRunner<'_, '_>,
    unit: &Unit,
    top_line: impl Display,
) -> String {
    let manifest_path = unit.pkg.manifest_path();
    let relative_manifest_path = manifest_path
        .strip_prefix(build_runner.bcx.ws.root())
        .unwrap_or(&manifest_path);

    format!(
        "\
{top_line}
    Try running with `--verbose` to see the error message.
    If an example should not be scanned, then consider adding `doc-scrape-examples = false` to its `[[example]]` definition in {}",
        relative_manifest_path.display()
    )
}

/// Creates a unit of work invoking `rustc` for building the `unit`.
#[tracing::instrument(skip_all)]
fn rustc(
    build_runner: &mut BuildRunner<'_, '_>,
    unit: &Unit,
    exec: &Arc<dyn Executor>,
    qualification: Option<Arc<qualification_command::Capture>>,
    capture_only: bool,
) -> CargoResult<Work> {
    // Trust: upstream `prepare_rustc` returns only the command. Everything the
    // exec-edge re-checks has to be decided here, while the unit graph is still
    // in scope, and then travel into the closure below — the closure runs on a
    // job-queue thread with no `BuildRunner` to consult.
    let (
        mut rustc,
        process_authority,
        verified_policy,
        audited_trust_spec_sources,
        audited_proc_macro_externs,
        cargo_compiler_closure,
        certified_monitor_session,
        execution_tcb_enforced,
        audited_proc_macro_unit,
        certified_monitor_seal,
    ) = prepare_rustc(build_runner, unit)?;
    let source_inputs = action_inputs::for_unit(build_runner, unit)?;
    let command_inputs = action_command::for_unit(build_runner, unit, source_inputs.as_deref())?;
    let platform_inputs = build_runner
        .bcx
        .action_platform
        .clone()
        .filter(|_| build_runner.bcx.confines(unit));
    let authenticated_targo = crate::is_targo_invocation();

    let name = unit.pkg.name();

    let outputs = build_runner.outputs(unit)?;
    let root = build_runner.files().output_dir(unit);

    // Prepare the native lib state (extra `-L` and `-l` flags).
    let build_script_outputs = Arc::clone(&build_runner.build_script_outputs);
    let current_id = unit.pkg.package_id();
    let manifest = ManifestErrorContext::new(build_runner, unit)?;
    let build_scripts = build_runner.build_scripts.get(unit).cloned();

    // If we are a binary and the package also contains a library, then we
    // don't pass the `-l` flags.
    let pass_l_flag = unit.target.is_lib() || !unit.pkg.targets().iter().any(|t| t.is_lib());

    let dep_info_name =
        if let Some(c_extra_filename) = build_runner.files().metadata(unit).c_extra_filename() {
            format!("{}-{}.d", unit.target.crate_name(), c_extra_filename)
        } else {
            format!("{}.d", unit.target.crate_name())
        };
    let rustc_dep_info_loc = root.join(dep_info_name);
    let dep_info_loc = fingerprint::dep_info_loc(build_runner, unit);

    let mut output_options = OutputOptions::for_dirty(build_runner, unit);
    let package_id = unit.pkg.package_id();
    let target = Target::clone(&unit.target);
    let mode = unit.mode;
    let capture_rusage = build_runner.bcx.capture_rusage();

    if !capture_only {
        exec.init(build_runner, unit);
    }
    let exec = exec.clone();

    let root_output = build_runner.files().host_dest().map(|v| v.to_path_buf());
    let build_dir = build_runner.files().build_root(unit);
    let pkg_root = unit.pkg.root().to_path_buf();
    let ws_root = build_runner.bcx.ws.root().to_path_buf();
    let cwd = rustc
        .get_cwd()
        .unwrap_or_else(|| build_runner.bcx.gctx.cwd())
        .to_path_buf();
    let output_publication = fingerprint::output_publication(build_runner, unit)?;
    let required_executable = fingerprint::required_executable(build_runner, unit)?;
    output_options.output_observation = output_publication
        .as_ref()
        .map(|publication| output_observation::Observer::new(publication.expected(), cwd.clone()));
    // Trust: only coordinator-demanded native Build metadata gets this live
    // gate. Standalone custom routing and fresh replay do not acquire demand.
    if !capture_only && authenticated_targo && build_runner.rmeta_required(unit) {
        let mut metadata = outputs
            .iter()
            .filter(|output| output.flavor == FileFlavor::Rmeta);
        let expected = metadata.next().ok_or_else(|| {
            anyhow::anyhow!("native pipelined unit has no planned metadata output")
        })?;
        if metadata.next().is_some() {
            anyhow::bail!("native pipelined unit has multiple planned metadata outputs");
        }
        output_options.metadata_readiness =
            metadata_readiness::MetadataReadiness::required(expected.path.clone(), cwd.clone())?;
    }
    let fingerprint_dir = build_runner.files().fingerprint_dir(unit);
    let script_metadatas = build_runner.find_build_script_metadatas(unit);
    let content_source_paths =
        authenticated_targo && build_runner.bcx.source_fingerprint == FingerprintMethod::Content;
    let track_package_sources = unit.is_local() || content_source_paths;
    let artifact = unit.artifact;
    let sbom_files = build_runner.sbom_output_files(unit)?;
    let sbom = if !sbom_files.is_empty() {
        Some(build_sbom(build_runner, unit)?)
    } else {
        None
    };

    let unremap_files = build_runner.unremap_output_files(unit)?;
    let unremap_content = if unremap_files.is_empty() {
        None
    } else {
        let mut buf = Vec::new();
        trim_paths::write_unremap_file(&mut buf, build_runner, unit)?;
        Some(buf)
    };

    let hide_diagnostics_for_scrape_unit = build_runner.bcx.unit_can_fail_for_docscraping(unit)
        && !matches!(
            build_runner.bcx.gctx.shell().verbosity(),
            Verbosity::Verbose
        );
    let failed_scrape_diagnostic = hide_diagnostics_for_scrape_unit.then(|| {
        // If this unit is needed for doc-scraping, then we generate a diagnostic that
        // describes the set of reverse-dependencies that cause the unit to be needed.
        let target_desc = unit.target.description_named();
        let mut for_scrape_units = build_runner
            .bcx
            .scrape_units_have_dep_on(unit)
            .into_iter()
            .map(|unit| unit.target.description_named())
            .collect::<Vec<_>>();
        for_scrape_units.sort();
        let for_scrape_units = for_scrape_units.join(", ");
        make_failed_scrape_diagnostic(build_runner, unit, format_args!("failed to check {target_desc} in package `{name}` as a prerequisite for scraping examples from: {for_scrape_units}"))
    });
    if hide_diagnostics_for_scrape_unit {
        output_options.show_diagnostics = false;
    }
    let env_config = Arc::clone(build_runner.bcx.gctx.env_config()?);
    // Trust: EW-9 relocation roots for the translated dep-info.
    let relocation_roots = build_runner
        .bcx
        .gctx
        .cli_unstable()
        .trust_relocation_roots
        .clone();
    return Ok(Work::new(move |state| {
        if !capture_only && let Some(publication) = &output_publication {
            publication.invalidate(&rustc_dep_info_loc)?;
        }
        // Artifacts are in a different location than typical units,
        // hence we must assure the crate- and target-dependent
        // directory is present.
        if !capture_only && artifact.is_true() {
            paths::create_dir_all(&root)?;
        }

        // Only at runtime have we discovered what the extra -L and -l
        // arguments are for native libraries, so we process those here. We
        // also need to be sure to add any -L paths for our plugins to the
        // dynamic library load path as a plugin's dynamic library may be
        // located somewhere in there.
        // Finally, if custom environment variables have been produced by
        // previous build scripts, we include them in the rustc invocation.
        if let Some(build_scripts) = build_scripts {
            let script_outputs = build_script_outputs.lock().unwrap();
            append_build_script_overlays(
                &mut rustc,
                &script_outputs,
                BuildScriptOverlay {
                    scripts: &build_scripts,
                    pass_l_flag,
                    target: &target,
                    current_id,
                    mode,
                    root_output: root_output.as_deref(),
                    script_metadatas,
                },
                process_authority.as_ref(),
                authenticated_targo,
            )?;
        }

        // Trust: build-script `cargo::rustc-cfg`/`cargo::rustc-env` data arrives
        // after `prepare_rustc`. Re-run the boundary check at the actual exec
        // edge so a cfg value such as `@hidden.args` cannot become a late
        // response-file injection channel. This block is the exec-edge half of
        // the admission pair; keep it adjacent to the `Executor` call below.
        if let Some(policy) = &verified_policy {
            validate_verified_targo_compiler_argument_boundaries(&rustc, policy)
                .map_err(anyhow::Error::msg)?;
        }
        // Trust: native output coverage cannot account for a late original
        // @ operand, including one from a first build script whose controls
        // were unavailable during planning. Keep compiler success/readiness,
        // but withhold its seal. This precedes Cargo's own argfile transport.
        suppress_native_argfile_output_observation(&rustc, &mut output_options.output_observation);
        // Trust: reinstall the PREPARE-TIME capture, never whatever a late
        // overlay (build-script `rustc-env`, `[env]`) left on this command.
        // The seal is a `CertifiedMonitorSeal`, so this call cannot pass a
        // missing loader value for an enforced seal (the D2 wiring slip).
        seal_certified_monitor_graph_compiler_environment(
            &mut rustc,
            &certified_monitor_seal,
            certified_monitor_session.as_deref(),
        )
        .map_err(anyhow::Error::msg)?;
        reject_certified_monitor_dynamic_rust_linkage_with_audited_proc_macro(
            &rustc,
            execution_tcb_enforced,
            &audited_proc_macro_externs,
            &cargo_compiler_closure,
            audited_proc_macro_unit,
        )
        .map_err(anyhow::Error::msg)?;
        validate_certified_monitor_command_env(&rustc, certified_monitor_session.as_deref())
            .map_err(anyhow::Error::msg)?;
        for source in &audited_trust_spec_sources {
            source.verify_unchanged().map_err(anyhow::Error::msg)?;
        }
        if let Some(inputs) = &source_inputs {
            inputs.ensure_current()?;
        }
        if let Some(inputs) = &platform_inputs {
            inputs.ensure_current()?;
        }
        if let Some(inputs) = &command_inputs {
            inputs.ensure_matches(&rustc)?;
        }

        // The ordinary warm and dirty paths use the SAME runtime dependency/
        // cfg/environment assembly above. A warm command stops before output
        // invalidation/deletion, timestamp/fingerprint writes or any compiler.
        if let Some(capture) = &qualification {
            state.retain_original_command(capture.clone(), &rustc)?;
        }
        if capture_only {
            anyhow::ensure!(
                qualification.is_some(),
                "capture-only unit has no original observer"
            );
            validate_verified_command_runtime_library_authority(&rustc)?;
            return Ok(());
        }

        for output in outputs.iter() {
            // If there is both an rmeta and rlib, rustc will prefer to use the
            // rlib, even if it is older. Therefore, we must delete the rlib to
            // force using the new rmeta.
            if output.path.extension() == Some(OsStr::new("rmeta")) {
                let dst = root.join(&output.path).with_extension("rlib");
                if dst.exists() {
                    paths::remove_file(&dst)?;
                }
            }

            // Some linkers do not remove the executable, but truncate and modify it.
            // That results in the old hard-link being modified even after renamed.
            // We delete the old artifact here to prevent this behavior from confusing users.
            // See rust-lang/cargo#8348.
            if output.hardlink.is_some() && output.path.exists() {
                _ = paths::remove_file(&output.path).map_err(|e| {
                    tracing::debug!(
                        "failed to delete previous output file `{:?}`: {e:?}",
                        output.path
                    );
                });
            }
        }

        // Trust: last statement before the argv is frozen — dynamic-loader
        // environment (`LD_PRELOAD` and friends) is not part of argv, so it
        // escapes every argument-level check above.
        validate_verified_command_runtime_library_authority(&rustc)?;
        state.configure_resources(&mut rustc, true)?;
        state.running(&rustc);
        let timestamp = paths::set_invocation_time(&fingerprint_dir)?;
        if let Some(sbom) = sbom {
            for file in sbom_files {
                tracing::debug!("writing sbom to {}", file.display());
                output_sbom::write_sbom(paths::create(&file)?, &sbom)
                    .with_context(|| format!("could not write SBOM to {}", file.display()))?;
            }
        }

        // Trust: `cargo fix` re-enters this same path through a proxy; the
        // handoff envelope has to be closed here or the proxied child inherits
        // an authority it was never granted.
        crate::ops::seal_targo_fix_proxy_handoff(&mut rustc)?;
        if let Some(content) = &unremap_content {
            for file in &unremap_files {
                tracing::debug!("writing unremap file to {}", file.display());
                paths::write_atomic(file, content)?;
            }
        }

        // Trust: observe configured tool namespace stamps after every overlay,
        // immediately before the owning compiler execution. Only the matching
        // post-wait observation may authorize output receipt publication.
        let linker_execution = output_publication
            .as_ref()
            .map(|publication| publication.begin(&rustc));
        let (stats, result) = exec.exec(
            &rustc,
            package_id,
            &target,
            mode,
            &mut |line| on_stdout_line(state, line, package_id, &target),
            &mut |line| {
                on_stderr_line(
                    state,
                    line,
                    package_id,
                    &manifest,
                    &target,
                    &mut output_options,
                )
            },
            capture_rusage,
        );
        let result = result
            .map_err(|e| {
                if output_options.errors_seen == 0 {
                    // If we didn't expect an error, do not require --verbose to fail.
                    // This is intended to debug
                    // https://github.com/rust-lang/crater/issues/733, where we are seeing
                    // Cargo exit unsuccessfully while seeming to not show any errors.
                    e
                } else {
                    verbose_if_simple_exit_code(e)
                }
            })
            .with_context(|| {
                // adapted from rustc_errors/src/lib.rs
                let warnings = match output_options.warnings_seen {
                    0 => String::new(),
                    1 => "; 1 warning emitted".to_string(),
                    count => format!("; {} warnings emitted", count),
                };
                let errors = match output_options.errors_seen {
                    0 => String::new(),
                    1 => " due to 1 previous error".to_string(),
                    count => format!(" due to {} previous errors", count),
                };
                let name = descriptive_pkg_name(&name, &target, &mode);
                format!("could not compile {name}{errors}{warnings}")
            });

        if let Some(peak_memory) = stats.peak_rss {
            state.peak_memory(peak_memory);
        }
        if let Some(times) = stats.cpu_times {
            state.cpu_times(times);
        }

        if let Err(e) = result {
            // Trust: failed compilation can replace dep-info while retaining a
            // previous managed cache. Its declared partial outputs still belong
            // to this unit. Keep the original compiler error authoritative.
            if rustc_dep_info_loc.exists() {
                if let Err(error) = trust_witness_cleanup::record(&rustc_dep_info_loc, package_id) {
                    state.warning(format!(
                        "could not retain managed witness cleanup ownership: {error:#}"
                    ));
                }
            }
            if let Some(diagnostic) = failed_scrape_diagnostic {
                state.warning(diagnostic);
            }

            return Err(e);
        }

        // Trust: re-hash after the compiler exits. The pre-exec check only
        // proves the provider was audited when the job started; a concurrent
        // job could have rewritten it while this unit compiled.
        for source in &audited_trust_spec_sources {
            source.verify_unchanged().map_err(anyhow::Error::msg)?;
        }

        // Exec should never return with success *and* generate an error.
        if let Some(inputs) = &platform_inputs {
            inputs.ensure_current()?;
        }
        if let Some(inputs) = &source_inputs {
            inputs.ensure_current()?;
        }
        debug_assert_eq!(output_options.errors_seen, 0);

        // Trust: a linker/strip failure can leave an empty executable even when
        // the compiler exits0. Refuse it before artifact/fingerprint publication.
        if let Some(executable) = &required_executable {
            executable_output::require(executable)?;
        }

        // Trust: a successful dirty job must not synthesize metadata readiness
        // in JobState::run_to_finish when the live report/file was missing.
        output_options.metadata_readiness.finish()?;

        if rustc_dep_info_loc.exists() {
            // Trust: the compiler names its opaque cache; bind that declaration
            // to this compilation's package, never to a directory scan.
            trust_witness_cleanup::record(&rustc_dep_info_loc, package_id)?;
            fingerprint::translate_dep_info(
                &rustc_dep_info_loc,
                &dep_info_loc,
                &cwd,
                &pkg_root,
                &build_dir,
                &ws_root,
                &rustc,
                // Native content reuse checks registry/git source bytes too;
                // a path under CARGO_HOME is not evidence of immutability.
                track_package_sources,
                content_source_paths,
                &env_config,
                relocation_roots.as_ref(),
            )
            .with_context(|| {
                internal(format!(
                    "could not parse/generate dep info at: {}",
                    rustc_dep_info_loc.display()
                ))
            })?;
            // This mtime shift allows Cargo to detect if a source file was
            // modified in the middle of the build.
            paths::set_file_time_no_err(dep_info_loc, timestamp);
        }

        // This mtime shift for .rmeta is a workaround as rustc incremental build
        // since rust-lang/rust#114669 (1.90.0) skips unnecessary rmeta generation.
        //
        // The situation is like this:
        //
        // 1. When build script execution's external dependendies
        //    (rerun-if-changed, rerun-if-env-changed) got updated,
        //    the execution unit reran and got a newer mtime.
        // 2. rustc type-checked the associated crate, though with incremental
        //    compilation, no rmeta regeneration. Its `.rmeta` stays old.
        // 3. Run `cargo check` again. Cargo found build script execution had
        //    a new mtime than existing crate rmeta, so re-checking the crate.
        //    However the check is a no-op (input has no change), so stuck.
        if mode.is_check() {
            for output in outputs.iter() {
                paths::set_file_time_no_err(&output.path, timestamp);
            }
        }

        // Only this successful live Work can authorize receipt publication.
        // Missing coverage is a cache miss, never a standalone compile error.
        if let Some(publication) = output_publication {
            publication.complete(
                output_options
                    .output_observation
                    .take()
                    .and_then(output_observation::Observer::finish),
                linker_execution,
            );
        }
        Ok(())
    }));
}

// Add all relevant `-L` and `-l` flags from dependencies (now calculated and
// present in `state`) to the command provided.
fn add_native_deps(
    rustc: &mut ProcessBuilder,
    build_script_outputs: &BuildScriptOutputs,
    build_scripts: &BuildScripts,
    pass_l_flag: bool,
    target: &Target,
    current_id: PackageId,
    mode: CompileMode,
) -> CargoResult<()> {
    let mut library_paths = vec![];

    for key in build_scripts.to_link.iter() {
        let output = build_script_outputs.get(key.1).ok_or_else(|| {
            internal(format!(
                "couldn't find build script output for {}/{}",
                key.0, key.1
            ))
        })?;
        library_paths.extend(output.library_paths.iter());
    }

    // NOTE: This very intentionally does not use the derived ord from LibraryPath because we need to
    // retain relative ordering within the same type (i.e. not lexicographic). The use of a stable sort
    // is also important here because it ensures that paths of the same type retain the same relative
    // ordering (for an unstable sort to work here, the list would need to retain the idx of each element
    // and then sort by that idx when the type is equivalent.
    library_paths.sort_by_key(|p| match p {
        LibraryPath::CargoArtifact(_) => 0,
        LibraryPath::External(_) => 1,
    });

    for path in library_paths.iter() {
        rustc.arg("-L").arg(path.as_ref());
    }

    for key in build_scripts.to_link.iter() {
        let output = build_script_outputs.get(key.1).ok_or_else(|| {
            internal(format!(
                "couldn't find build script output for {}/{}",
                key.0, key.1
            ))
        })?;

        if key.0 == current_id {
            if pass_l_flag {
                for name in output.library_links.iter() {
                    rustc.arg("-l").arg(name);
                }
            }
        }

        for (lt, arg) in &output.linker_args {
            // There was an unintentional change where cdylibs were
            // allowed to be passed via transitive dependencies. This
            // clause should have been kept in the `if` block above. For
            // now, continue allowing it for cdylib only.
            // See https://github.com/rust-lang/cargo/issues/9562
            if lt.applies_to(target, mode) && (key.0 == current_id || *lt == LinkArgTarget::Cdylib)
            {
                rustc.arg("-C").arg(format!("link-arg={}", arg));
            }
        }
    }
    Ok(())
}

// Trust: one late-overlay recipe serves actual Work and early command data.
// This carries no process executor, resource owner or publication authority.
struct BuildScriptOverlay<'a> {
    scripts: &'a BuildScripts,
    pass_l_flag: bool,
    target: &'a Target,
    current_id: PackageId,
    mode: CompileMode,
    root_output: Option<&'a Path>,
    script_metadatas: Option<Vec<UnitHash>>,
}

fn append_build_script_overlays(
    command: &mut ProcessBuilder,
    outputs: &BuildScriptOutputs,
    overlay: BuildScriptOverlay<'_>,
    process_authority: Option<&AuthenticatedTargoProcessAuthority>,
    authenticated_targo: bool,
) -> CargoResult<()> {
    add_native_deps(
        command,
        outputs,
        overlay.scripts,
        overlay.pass_l_flag,
        overlay.target,
        overlay.current_id,
        overlay.mode,
    )?;
    if let Some(root) = overlay.root_output {
        add_plugin_deps(command, outputs, overlay.scripts, root)?;
    }
    add_custom_flags(
        command,
        process_authority,
        authenticated_targo,
        outputs,
        overlay.script_metadatas,
    )
}

fn verbose_if_simple_exit_code(err: Error) -> Error {
    // If a signal on unix (`code == None`) or an abnormal termination
    // on Windows (codes like `0xC0000409`), don't hide the error details.
    match err
        .downcast_ref::<ProcessError>()
        .as_ref()
        .and_then(|perr| perr.code)
    {
        Some(n) if cargo_util::is_simple_exit_code(n) => VerboseError::new(err).into(),
        _ => err,
    }
}

fn prebuild_lock_exclusive(lock: LockKey) -> Work {
    Work::new(move |state| {
        state.lock_exclusive(&lock)?;
        Ok(())
    })
}

fn downgrade_lock_to_shared(lock: LockKey) -> Work {
    Work::new(move |state| {
        state.downgrade_to_shared(&lock)?;
        Ok(())
    })
}

// Trust: both the normal destination and --artifact-dir export use the same
// Unit-selected publication policy. Debug directories and library artifacts
// retain their existing linking behavior.
fn publish_unit_output(
    source: &Path,
    destination: &Path,
    independent_executable: bool,
    flavor: &FileFlavor,
) -> CargoResult<()> {
    if independent_executable && flavor == &FileFlavor::Normal {
        paths::copy_independent_file(source, destination)
    } else {
        paths::link_or_copy(source, destination)
    }
}

#[cfg(all(test, unix))]
mod independent_output_publication_tests {
    use super::{FileFlavor, publish_unit_output};
    use std::os::unix::fs::MetadataExt as _;

    #[test]
    fn independent_publication_of_actual_native_image_and_export_keeps_separate_inodes() {
        let directory = tempfile::tempdir().unwrap();
        let compiled = directory.path().join("compiled");
        let executable = directory.path().join("build-script-build");
        let exported = directory.path().join("exported");
        std::fs::copy(std::env::current_exe().unwrap(), &compiled).unwrap();
        std::fs::hard_link(&compiled, &executable).unwrap();

        for destination in [&executable, &exported] {
            publish_unit_output(&compiled, destination, true, &FileFlavor::Normal).unwrap();
            let metadata = std::fs::metadata(destination).unwrap();
            assert_eq!(metadata.nlink(), 1);
            assert!(!same_file::is_same_file(&compiled, destination).unwrap());
        }
        assert!(!same_file::is_same_file(&executable, &exported).unwrap());
        let first = std::fs::metadata(&executable).unwrap();
        publish_unit_output(&compiled, &executable, true, &FileFlavor::Normal).unwrap();
        assert_eq!(std::fs::metadata(&executable).unwrap().ino(), first.ino());
        // This is the actual native test image, not an SDK-authority fixture.
        let output = std::process::Command::new(&executable)
            .arg("--list")
            .output()
            .unwrap();
        assert!(output.status.success(), "{output:?}");
        assert!(String::from_utf8(output.stdout).unwrap().contains(
            "independent_publication_of_actual_native_image_and_export_keeps_separate_inodes"
        ));
    }
}

/// Link the compiled target (often of form `foo-{metadata_hash}`) to the
/// final target. This must happen during both "Fresh" and "Compile".
fn link_targets(
    build_runner: &mut BuildRunner<'_, '_>,
    unit: &Unit,
    fresh: bool,
) -> CargoResult<Work> {
    let bcx = build_runner.bcx;
    let outputs = build_runner.outputs(unit)?;
    let export_dir = build_runner.files().export_dir();
    let private_publication = build_runner.files().private_unit(unit).is_some();
    let package_id = unit.pkg.package_id();
    let manifest_path = PathBuf::from(unit.pkg.manifest_path());
    let profile = unit.profile.clone();
    let unit_mode = unit.mode;
    // Trust: executable publication belongs to the actual Unit/Layout path,
    // before native output capture. Never relax capture's single-link rule to
    // accept the aliases that Cargo historically creates here.
    let independent_executable = crate::is_targo_invocation()
        && unit_mode == CompileMode::Build
        && (unit.target.is_bin() || unit.target.is_custom_build());
    // Trust: upstream emits features in iteration order. The artifact envelope
    // below is hashed and compared across runs, so the set has to be canonical
    // or two byte-identical compilations disagree on their unit identity.
    let features = canonical_trust_string_set(
        "enabled feature",
        unit.features.iter().map(ToString::to_string),
    )
    .map_err(anyhow::Error::msg)?;
    let json_messages = bcx.build_config.emit_json();
    let executable = build_runner.get_executable(unit)?;
    let required_executable = fingerprint::required_executable(build_runner, unit)?;
    let mut target = Target::clone(&unit.target);
    let compile_kind = unit.kind;
    // Trust: `link_targets` is where an artifact first becomes addressable to
    // anything outside Cargo, so it is also where the unit's identity has to be
    // pinned. Everything below is computed here rather than in the closure
    // because the closure runs after the compiler exited and can no longer see
    // the unit graph.
    let trust_target_identity_enabled = crate::is_targo_invocation();
    let trust_compile_target = trust_target_identity_enabled
        .then(|| scoped_unit_compile_target(bcx, unit))
        .transpose()?;
    // Capture before this post-compile Work is constructed. The closure must
    // compare a fresh endpoint hash before it can emit an artifact envelope;
    // otherwise a same-path mutation between compiler execution and artifact
    // publication could attribute the compilation to only the later bytes.
    let trust_compile_target_spec_sha256 = if trust_target_identity_enabled {
        exact_unit_compile_target_spec_sha256(compile_kind)?
    } else {
        None
    };
    let trust_compile_mode =
        trust_target_identity_enabled.then(|| exact_unit_compile_mode(unit_mode));
    let trust_compile_kind =
        trust_target_identity_enabled.then(|| exact_unit_compile_kind(compile_kind));
    let captured_exact_unit = trust_target_identity_enabled
        .then(|| {
            let captured = exact_unit::capture(build_runner, unit)?;
            captured.require_spec(compile_kind, trust_compile_target_spec_sha256.as_deref())?;
            Ok::<_, anyhow::Error>(captured)
        })
        .transpose()?;
    let trust_unit_identity_sha256 = captured_exact_unit
        .as_ref()
        .map(|captured| captured.digest.clone());
    let trust_proof_unit = trust_proof_unit_identity(build_runner, unit)?;
    if let TargetSourcePath::Metabuild = target.src_path() {
        // Give it something to serialize.
        let path = unit
            .pkg
            .manifest()
            .metabuild_path(build_runner.bcx.ws.build_dir());
        target.set_src_path(TargetSourcePath::Path(path));
    }

    let private_selection = if private_publication {
        use std::os::unix::ffi::OsStrExt as _;
        let mut destinations = outputs
            .iter()
            .flat_map(|output| output.hardlink.iter().chain(output.export_path.iter()))
            .map(|path| path.as_os_str().as_bytes().to_vec())
            .collect::<Vec<_>>();
        destinations.sort();
        let selection =
            trust_resource_controller::workload::host::coordinator::PublicationSelection {
                unit_sha256: trust_unit_identity_sha256
                    .clone()
                    .context("private publication has no actual exact unit identity")?,
                unit_id: build_runner.files().metadata(unit).unit_id().to_string(),
                destinations,
            };
        selection.validate()?;
        Some(selection)
    } else {
        None
    };

    Ok(Work::new(move |state| {
        // Trust: a confined candidate compiler owns only its private unit
        // namespace. Canonical aliases require the original parent's typed
        // publication operation, including Fresh reuse; never widen child
        // write authority to perform Cargo's historical publication here.
        let _publication_ack = private_selection
            .as_ref()
            .map(|selection| {
                let ack = crate::resource_v3::candidate_coordinator::publish(selection.clone())?;
                anyhow::ensure!(
                    ack.selection() == selection,
                    "parent publication reply differs from SAME exact unit/output selection"
                );
                Ok::<_, anyhow::Error>(ack)
            })
            .transpose()?;
        // Trust: a custom target JSON is read by the compiler and again here; a
        // rewrite in between would publish an artifact under a target spec that
        // never compiled it.
        if trust_target_identity_enabled {
            ensure_exact_unit_compile_target_spec_unchanged(
                compile_kind,
                trust_compile_target_spec_sha256.as_deref(),
            )?;
        }
        if let Some(captured) = &captured_exact_unit {
            captured.require_current()?;
        }
        // Check again at the actual dirty OR fresh publication edge. Planning
        // and a successful compiler status do not establish file validity.
        if let Some(required) = &required_executable {
            executable_output::require(required)?;
        }
        // If we're a "root crate", e.g., the target of this compilation, then we
        // hard link our outputs out of the `deps` directory into the directory
        // above. This means that `cargo build` will produce binaries in
        // `target/debug` which one probably expects.
        let mut destinations = vec![];
        for output in outputs.iter() {
            let src = &output.path;
            // This may have been a `cargo rustc` command which changes the
            // output, so the source may not actually exist.
            if !src.exists() {
                continue;
            }
            let Some(dst) = output.hardlink.as_ref() else {
                destinations.push(src.clone());
                continue;
            };
            destinations.push(dst.clone());
            if !private_publication {
                publish_unit_output(src, dst, independent_executable, &output.flavor)?;
            }
            if let Some(ref path) = output.export_path {
                let export_dir = export_dir.as_ref().unwrap();
                if !private_publication {
                    paths::create_dir_all(export_dir)?;
                    publish_unit_output(src, path, independent_executable, &output.flavor)?;
                }
            }
        }

        if let Some(required) = &required_executable {
            for output in outputs.iter().filter(|output| &output.path == required) {
                executable_output::require(output.bin_dst())?;
                if let Some(exported) = &output.export_path {
                    executable_output::require(exported)?;
                }
            }
        }

        if json_messages {
            // Trust: hash the executable that was actually published, not
            // the one the compiler wrote — the loop above is the last mutation
            // point before a consumer can observe the file.
            let trust_executable_sha256 = if trust_target_identity_enabled {
                executable
                    .as_deref()
                    .map(regular_file_sha256)
                    .transpose()
                    .map_err(anyhow::Error::msg)?
            } else {
                None
            };
            let debuginfo = match profile.debuginfo.into_inner() {
                TomlDebugInfo::None => machine_message::ArtifactDebuginfo::Int(0),
                TomlDebugInfo::Limited => machine_message::ArtifactDebuginfo::Int(1),
                TomlDebugInfo::Full => machine_message::ArtifactDebuginfo::Int(2),
                TomlDebugInfo::LineDirectivesOnly => {
                    machine_message::ArtifactDebuginfo::Named("line-directives-only")
                }
                TomlDebugInfo::LineTablesOnly => {
                    machine_message::ArtifactDebuginfo::Named("line-tables-only")
                }
            };
            let art_profile = machine_message::ArtifactProfile {
                opt_level: profile.opt_level.as_str(),
                debuginfo: Some(debuginfo),
                debug_assertions: profile.debug_assertions,
                overflow_checks: profile.overflow_checks,
                test: unit_mode.is_any_test(),
            };

            let msg = machine_message::Artifact {
                package_id: package_id.to_spec(),
                manifest_path,
                target: &target,
                trust_compile_target: trust_compile_target.as_deref(),
                trust_compile_target_spec_sha256: trust_compile_target_spec_sha256.as_deref(),
                trust_compile_mode,
                trust_compile_kind,
                trust_unit_identity_sha256: trust_unit_identity_sha256.as_deref(),
                trust_executable_sha256,
                trust_proof_unit: trust_proof_unit.as_ref(),
                profile: art_profile,
                features,
                filenames: destinations,
                executable,
                fresh,
            }
            .to_json_string();
            state.stdout(msg)?;
        }
        Ok(())
    }))
}

// For all plugin dependencies, add their -L paths (now calculated and present
// in `build_script_outputs`) to the dynamic library load path for the command
// to execute.
fn add_plugin_deps(
    rustc: &mut ProcessBuilder,
    build_script_outputs: &BuildScriptOutputs,
    build_scripts: &BuildScripts,
    root_output: &Path,
) -> CargoResult<()> {
    let var = paths::dylib_path_envvar();
    let search_path = rustc.get_env(var).unwrap_or_default();
    let mut search_path = env::split_paths(&search_path).collect::<Vec<_>>();
    for (pkg_id, metadata) in &build_scripts.plugins {
        let output = build_script_outputs
            .get(*metadata)
            .ok_or_else(|| internal(format!("couldn't find libs for plugin dep {}", pkg_id)))?;
        search_path.append(&mut filter_dynamic_search_path(
            output.library_paths.iter().map(AsRef::as_ref),
            root_output,
        ));
    }
    let search_path = paths::join_paths(&search_path, var)?;
    rustc.env(var, &search_path);
    Ok(())
}

fn get_dynamic_search_path(path: &Path) -> &Path {
    match path.to_str().and_then(|s| s.split_once("=")) {
        Some(("native" | "crate" | "dependency" | "framework" | "all", path)) => Path::new(path),
        _ => path,
    }
}

// Determine paths to add to the dynamic search path from -L entries
//
// Strip off prefixes like "native=" or "framework=" and filter out directories
// **not** inside our output directory since they are likely spurious and can cause
// clashes with system shared libraries (issue #3366).
fn filter_dynamic_search_path<'a, I>(paths: I, root_output: &Path) -> Vec<PathBuf>
where
    I: Iterator<Item = &'a PathBuf>,
{
    let mut search_path = vec![];
    for dir in paths {
        let dir = get_dynamic_search_path(dir);
        if dir.starts_with(&root_output) {
            search_path.push(dir.to_path_buf());
        } else {
            debug!(
                "Not including path {} in runtime library search path because it is \
                 outside target root {}",
                dir.display(),
                root_output.display()
            );
        }
    }
    search_path
}

// Trust: everything from here to the end of `trust_verification_role_tests` is
// Trust-authored and has no upstream counterpart — it is the verified-Targo
// admission layer that decides, per unit, whether a compilation may claim proof
// authority and what the compiler is allowed to be handed.
//
// It lives inside `compiler/mod.rs`, wrapped around `prepare_rustc`, because the
// decision needs the unit graph, the resolved rustflags, and the final argv at
// once; splitting it into a sibling module would either duplicate that state or
// let the argv be mutated between decision and exec. `prepare_rustc` itself is
// upstream's function with a widened return type, and stays in its original
// position below.
//
// On a cargo re-align: upstream owns `prepare_rustc`'s body; this surrounding
// block is Trust's and should be carried across wholesale.
//
/// Trust (PM-1, 2026-10-01): every dependency unit whose crate the verified
/// unit's rustc can load — the closure rustc's crate loader walks.
///
/// rustc registers a crate's dependencies recursively and `dlopen`s every
/// proc-macro crate it meets, even one no macro invocation names, so a facade
/// re-export (`pub use derive_crate::Derive;`) or a dependency that privately
/// derives runs that macro's code inside THIS rustc (MEASURED 2026-09-28,
/// docs/KNOWN_HAZARDS.md "A strict `targo trust check` PASS does not exclude
/// in-process third-party code"). The direct-dependency scan this replaces saw
/// neither. The walk follows library edges transitively, keeps proc-macro units
/// as leaves (rustc resolves no dependency of a proc-macro crate:
/// `CrateLoader::resolve_crate_deps` returns an empty map for one), and skips
/// build-script units, whose macros run in the build script's own rustc. A
/// superset of what rustc loads only refuses more, never less.
fn rustc_loaded_dependency_closure(build_runner: &BuildRunner<'_, '_>, unit: &Unit) -> Vec<Unit> {
    loader_closure(
        build_runner
            .unit_deps(unit)
            .iter()
            .map(|dependency| dependency.unit.clone()),
        |dependency: &Unit| {
            build_runner
                .unit_deps(dependency)
                .iter()
                .map(|nested| nested.unit.clone())
                .collect()
        },
        |dependency: &Unit| dependency.target.is_custom_build(),
        |dependency: &Unit| dependency.target.proc_macro(),
    )
}

/// The graph walk behind [`rustc_loaded_dependency_closure`], generic so it is
/// unit-tested without a Cargo build graph: transitive over library edges,
/// proc macros kept as leaves, build-script nodes neither kept nor followed.
fn loader_closure<U: Clone + Eq + std::hash::Hash>(
    roots: impl IntoIterator<Item = U>,
    deps: impl Fn(&U) -> Vec<U>,
    is_build_script: impl Fn(&U) -> bool,
    is_proc_macro: impl Fn(&U) -> bool,
) -> Vec<U> {
    let mut seen = HashSet::default();
    let mut stack = roots.into_iter().collect::<Vec<_>>();
    let mut closure = Vec::new();
    while let Some(node) = stack.pop() {
        if is_build_script(&node) || !seen.insert(node.clone()) {
            continue;
        }
        if !is_proc_macro(&node) {
            stack.extend(deps(&node));
        }
        closure.push(node);
    }
    closure
}

/// Trust (D21): where the proc macros a unit's rustc loads will run.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ProcMacroExpansion {
    /// In the unit's rustc, which opens each proc-macro dylib itself.
    InProcess,
    /// In the sandboxed worker `-Ztrust-proc-macro-isolation` starts: the
    /// unit's rustc opens no proc-macro dylib, and the worker shares none of
    /// its argv, memory, stdout, stderr or writable filesystem.
    IsolatedWorker,
}

/// Whether this host's trustc has the isolated proc-macro worker. The
/// compiler's own rule is `rustc_session::TRUST_PROC_MACRO_ISOLATION_HOST`
/// (the worker needs the macOS seatbelt sandbox); a Targo and a trustc of one
/// toolchain are built for one host, and a disagreement fails closed either
/// way: trustc refuses the option where it has no sandbox, and where Targo
/// does not pass it the in-process refusal below stands.
const PROC_MACRO_ISOLATION_HOST: bool = cfg!(target_os = "macos");

/// The lane's `--no-proc-macro-isolation`, as it reaches a unit's flags.
const PROC_MACRO_ISOLATION_OPTION: &str = "trust-proc-macro-isolation";

/// Trust (D21): how a verified unit's proc macros expand, and whether the
/// unit's own flags already spell the option (so Targo must not add a second).
///
/// The default is the host's: isolated wherever the worker exists. The lane
/// may switch it off (`targo trust … --no-proc-macro-isolation` carries
/// `-Ztrust-proc-macro-isolation=no`), which only restores the in-process
/// refusal. Asking for it on a host without the worker is refused here, as
/// trustc would refuse it, rather than read as in-process.
fn trust_proc_macro_expansion(
    host_has_worker_sandbox: bool,
    unit_rustflags: &[String],
    extra_compiler_args: &[String],
) -> Result<(ProcMacroExpansion, bool), String> {
    let unit = trust_bool_option(unit_rustflags, PROC_MACRO_ISOLATION_OPTION)?;
    let extra = trust_bool_option(extra_compiler_args, PROC_MACRO_ISOLATION_OPTION)?;
    let requested = match (unit, extra) {
        (Some(_), Some(_)) => {
            return Err(format!(
                "duplicate -Z{PROC_MACRO_ISOLATION_OPTION} options are not allowed"
            ));
        }
        (unit, extra) => unit.or(extra),
    };
    match requested {
        Some(true) if !host_has_worker_sandbox => Err(format!(
            "-Z{PROC_MACRO_ISOLATION_OPTION} is refused on this host: the isolated proc-macro worker needs the macOS seatbelt sandbox, and expansion does not fall back to the compiler's process"
        )),
        Some(true) => Ok((ProcMacroExpansion::IsolatedWorker, true)),
        Some(false) => Ok((ProcMacroExpansion::InProcess, true)),
        None if host_has_worker_sandbox => Ok((ProcMacroExpansion::IsolatedWorker, false)),
        None => Ok((ProcMacroExpansion::InProcess, false)),
    }
}

// A verified unit's trusted computing base is the compiler process and nothing
// else. A proc-macro shares rustc's argv, memory, stderr, and artifact
// filesystem, so it could forge the proof transport rather than merely
// influence the program being proved.
fn reject_in_process_proc_macro_tcb(
    verified_targo: bool,
    unit_identity: &str,
    proc_macro_dependencies: impl IntoIterator<Item = String>,
) -> Result<(), String> {
    if !verified_targo {
        return Ok(());
    }
    let mut proc_macros = proc_macro_dependencies.into_iter().collect::<Vec<_>>();
    proc_macros.sort();
    proc_macros.dedup();
    if proc_macros.is_empty() {
        return Ok(());
    }
    Err(format!(
        "verified Targo refuses unit {unit_identity}: in-process proc-macro dependencies [{}] share rustc's argv, memory, stderr, and artifact filesystem and can forge compiler-message/TRUSTJSON proof transport or mutate authenticated outputs. Evidence-grade verification enforces a no-proc-macro TCB boundary on in-process expansion: verify where the isolated proc-macro worker runs (a macOS host, without --no-proc-macro-isolation), or expand/remove these macros before verification",
        proc_macros.join(", "),
    ))
}

/// Trust: the lane-aware consequence of the no-proc-macro TCB boundary.
///
/// The boundary protects PROOF AUTHORITY: a proc macro shares the verifying
/// compiler's process and could forge that unit's transport. A lane that
/// claims proof authority (the default strict policy, `certify`,
/// `memory-safe`) therefore still refuses to compile the unit, byte-for-byte
/// as `reject_in_process_proc_macro_tcb` always has. A lane that claims none
/// (`-Ztrust-policy=advisory`: `targo trust … --allow-l0-gaps` / `--survey`)
/// has no evidence-grade claim for the macro to forge, so the unit compiles
/// and verifies advisorily, and the FORFEITURE is the returned warning, which
/// names the unit and every unaudited macro in canonical order. `Ok(None)`
/// means the boundary is clean or out of scope.
///
/// This never widens the audited allowlist: an unaudited macro stays
/// unaudited; only what happens to the unit that loads it depends on the lane.
///
/// Trust (D21): all of the above is about macros that run IN the unit's
/// rustc. With [`ProcMacroExpansion::IsolatedWorker`] none does: the compiler
/// opens no proc-macro dylib and every expansion comes back over a checked
/// protocol from a process that cannot write to the compiler's stderr, memory
/// or artifacts. Such a unit has no in-process dependency to refuse or to
/// forfeit for, on any lane. This is containment, not authority: the macro is
/// still unaudited, and its expansion is verified as the source it becomes
/// (docs/TCB.md, PROC-MACRO ISOLATION).
fn admit_in_process_proc_macro_tcb(
    in_scope: bool,
    claims_proof_authority: bool,
    expansion: ProcMacroExpansion,
    unit_identity: &str,
    proc_macro_dependencies: impl IntoIterator<Item = String>,
) -> Result<Option<String>, String> {
    if expansion == ProcMacroExpansion::IsolatedWorker {
        return Ok(None);
    }
    if claims_proof_authority {
        reject_in_process_proc_macro_tcb(in_scope, unit_identity, proc_macro_dependencies)?;
        return Ok(None);
    }
    if !in_scope {
        return Ok(None);
    }
    let mut proc_macros = proc_macro_dependencies.into_iter().collect::<Vec<_>>();
    proc_macros.sort();
    proc_macros.dedup();
    if proc_macros.is_empty() {
        return Ok(None);
    }
    Ok(Some(format!(
        "advisory lane: unit {unit_identity} forfeits proof authority: in-process proc-macro dependencies [{}] share rustc's argv, memory, stderr, and artifact filesystem and could forge this unit's compiler-message/TRUSTJSON proof transport; its verification results are reported but are not evidence-grade",
        proc_macros.join(", "),
    )))
}

struct AuditedTrustSpecSource {
    package: &'static str,
    /// The resolved version this audit applies to, or `None` when the version
    /// is not audit evidence for this provider — see
    /// [`AUDITED_TRUST_SPEC_SOURCES`]. `None` never widens what BYTES are
    /// admitted: both digests still have to match exactly.
    version: Option<&'static str>,
    manifest_sha256: &'static str,
    lib_sha256: &'static str,
}

#[derive(Clone)]
pub(super) struct AuditedTrustSpecCapture {
    package_identity: String,
    manifest_path: PathBuf,
    lib_path: PathBuf,
    expected_manifest_sha256: &'static str,
    expected_lib_sha256: &'static str,
}

impl AuditedTrustSpecCapture {
    fn verify_unchanged(&self) -> Result<(), String> {
        let manifest_sha256 = regular_file_sha256(&self.manifest_path)?;
        let lib_sha256 = regular_file_sha256(&self.lib_path)?;
        if manifest_sha256 != self.expected_manifest_sha256
            || lib_sha256 != self.expected_lib_sha256
        {
            return Err(format!(
                "Trust spec provider `{}` does not match its audited source identity (manifest_sha256={manifest_sha256}, lib_sha256={lib_sha256})",
                self.package_identity
            ));
        }
        Ok(())
    }
}

// A proc macro executes inside the verified compiler process, so a crate/lib
// name is not authority.  These are the exact, dependency-free passthrough
// sources reviewed with this toolchain.  Adding or changing a provider requires
// an explicit source audit and an allowlist update.
//
// WHAT THE TWO DIGESTS ATTEST, AND WHY `version` IS NOT A THIRD DIGEST.
// `manifest_sha256` and `lib_sha256` fully determine the bytes admitted into
// the verified compiler's address space: the manifest fixes the dependency set,
// the absence of a build script, and the `[lib] proc-macro` shape, and the
// library source fixes the code. A resolved VERSION is not covered by either
// digest whenever the manifest inherits it (`version.workspace = true`), because
// it then comes from a workspace root that is not hashed. For such a provider
// the version is metadata its own workspace chooses — it constrains nothing an
// adversary controls, while guaranteeing that an unrelated `pub bump` silently
// expires the carve-out and `targo trust check -p ny-cert` stops starting with
// a no-proc-macro TCB refusal that names a crate which never changed.
//
// So `version` is `None` for inheriting providers and the digests carry the
// identity. This does not widen the admitted bytes: a provider that pins its
// own literal version has DIFFERENT manifest bytes, hence a different digest,
// and can never match a `None` row. Both providers inherit today: `trust-spec`
// carried `version = "0.1.1"` literally (and was keyed on it) until
// `c9a8f1f481` (2026-09-24) moved it to `version.workspace = true`, which left
// its `Some("0.1.1")` row a DEAD PIN — no manifest declared that version any
// more, so the lookup missed and the provider silently fell off this list
// (measured on seal trust-7d5533b2 against that tree: `targo trust check
// --allow-l0-gaps -p trust-spec` ran NO audited-source check at all). The
// drift lane `scripts/check_audited_trust_spec_sources.py` refuses exactly
// that shape.
const AUDITED_TRUST_SPEC_SOURCES: &[AuditedTrustSpecSource] = &[
    AuditedTrustSpecSource {
        package: "trust-spec",
        // NOT digest-covered since `c9a8f1f481`: the manifest inherits
        // `version.workspace = true` from crates/Cargo.toml (0.10.0 at that
        // commit), so the version is a workspace choice and the digests carry
        // the identity, exactly as for `ny-contracts` below.
        version: None,
        // Re-audited 2026-08-20. The previous pin (faa5a553...) was the state at
        // `fix(targo): authenticate renamed NY contract source`; exactly one
        // commit moved it, `wave 3: Trust compiles pure Lean, and the TCB says
        // what it actually is`, and the entire diff is three lines adding
        // `[lints] workspace = true`. That inherits `[workspace.lints.rust]
        // warnings = "warn"` — a lint LEVEL, which cannot introduce code,
        // dependencies, or output. No dependency section, no build script, no
        // change to `[lib] name = "trust"` / `proc-macro = true`, and no version
        // change.
        //
        // MANIFEST RE-AUDITED 2026-09-24, and its pin MOVED 4ae3ab86... ->
        // fada73aa.... Exactly one commit touched crates/trust-spec/Cargo.toml
        // after the 2026-08-20 audit — `c9a8f1f481` ("version: ONE line, ONE
        // authority") — and its entire diff is ONE line, `version = "0.1.1"` ->
        // `version.workspace = true`. A version is package metadata: it adds no
        // `[dependencies]` entry, no build script, no feature, and leaves
        // `[lib] name = "trust"` / `proc-macro = true` and `[lints] workspace =
        // true` exactly as audited. Capabilities gained: NONE. The consequence
        // is the key, not the bytes: the version is no longer digest-covered,
        // so `version` is now `None` (see the block comment above this const).
        //
        // LIBRARY SOURCE RE-AUDITED 2026-09-11, and the pin below MOVED:
        // 892427b1... (the initial commit's bytes) -> 853603e0..., the state
        // since the merge `a738bf8c8e` combined `42afd77700` ("`#[trust::
        // decreases(e)]` IS `fn f(..) decreases e`") and `08877adcb0`
        // ("`invariant` refuses instead of erasing"). The pin had been stale
        // since 2026-08-26/27, so EVERY verified build that compiled
        // `trust-spec` was refused fleet-wide for two weeks — on main, on
        // seal/15 and on seal/16 — with `does not match its audited source
        // identity` (measured 2026-09-11: exit 2 in 7s). The new drift lane
        // `scripts/check_audited_trust_spec_sources.py` is why that cannot
        // recur silently.
        //
        // WHAT THE ADMITTED BYTES GAIN, in TCB terms. Capabilities: NONE.
        // `#![forbid(unsafe_code)]` is still the first item; the only `use` is
        // still `proc_macro::TokenStream`; the manifest still declares no
        // `[dependencies]`, no build script, and `[lib] name = "trust"` /
        // `proc-macro = true`; the crate still performs no I/O, no env access,
        // no process spawn, and reads nothing outside its own token streams.
        //
        // What DID change is what two macros EXPAND TO, and both moves are in
        // the REFUSING direction:
        //   * `invariant` was a passthrough that returned the item unchanged —
        //     an annotation shaped like a specification that nothing checked.
        //     It now prepends a `compile_error!` built from a string literal in
        //     that file, so the same source is REFUSED where it was silently
        //     erased. Strictly stronger.
        //   * `decreases` is NEW. It is not a bare passthrough: it appends
        //     `#[cfg(trust_verify)] ::core::compile_error!(...)`, so on a
        //     toolchain that does NOT substitute the compiler-owned
        //     `ExpandTrustDecreases` builtin the build FAILS instead of erasing
        //     the termination measure. `cfg(trust_verify)` is compiler-injected
        //     exactly when verification is on (rustc_session/src/config/cfg.rs,
        //     asserted by `trust_verify_cfg_matches_activation_flags`), and the
        //     builtin is registered in rustc_builtin_macros/src/lib.rs. So the
        //     new export fails CLOSED; verification-off builds strip the marker
        //     and claim nothing.
        // Every token either macro emits is a fixed literal from this file plus
        // the caller's own item; the attribute tokens are dropped. Neither can
        // emit compiler-message/TRUSTJSON proof transport, so the no-forgery
        // property the digests exist to protect is unchanged. Nothing in the
        // diff WEAKENS a proof: the only direction of travel is from "accepted
        // and unchecked" to "refused".
        manifest_sha256: "fada73aa63928043b5985b75ae6a9f407014db215b59058c6245bd15bdad4430",
        // sha256 over the exact bytes of crates/trust-spec/src/lib.rs
        // (8220 bytes), computed with `shasum -a 256` and independently with
        // Python `hashlib`; the three pins that did NOT move re-compute to the
        // same values with the same command, which is the algorithm check.
        lib_sha256: "853603e08995c6008b852a8eaa8886658bba1f834f71212a8177af27df0dcca6",
    },
    AuditedTrustSpecSource {
        package: "ny-contracts",
        // NOT digest-covered: this manifest declares `version.workspace = true`,
        // so the resolved version comes from NY's workspace root. Audited at
        // 0.1.0; NY's submodule pin resolves 0.2.0 and the sibling checkout
        // 0.3.0, all with these identical digests (verified 2026-08-20 against
        // both checkouts and against the pinned submodule commit).
        version: None,
        manifest_sha256: "83569caf993ba8a93f6cd7af9d3ba23440f69baa23e6fe1cf053679eb82f42aa",
        lib_sha256: "af8f868e0706b3084e4ee0911aa9256b8c46ba8c0d0db50f44703d4013380a29",
    },
    // Trust: MERGE (b62-merge-redo <- origin/main; squash d24c671211, 2026-08-22): our explicit
    // ny-contracts 0.2.0 (6906ae2948) and 0.3.0 (0360a02a10) entries are REMOVED, because upstream
    // solved the same recurring failure mode better and their entry above subsumes
    // both - same package, byte-identical manifest/lib digests, and `version: None`.
    //
    // Those two commits were patching an enumerate-the-resolved-version key one bump
    // at a time; our own note here called it "a RECURRING failure mode (0.1.0 -> 0.2.0
    // -> 0.3.0)". It also warned: "do NOT relax the key to a version range, which would
    // admit an unaudited future rewrite under an already-blessed major." Upstream's
    // `version: None` is NOT a version range - it drops the version as a LOOKUP KEY
    // while still requiring BOTH exact digests, which our own note called "the real
    // authority". An unaudited rewrite changes those digests and is still refused, so
    // the concern that warning names is answered, not relaxed.
    //
    // Keeping our entries was not an option regardless: upstream changed the field to
    // `Option<&'static str>`, so `version: "0.2.0"` no longer type-checks.
];

fn audited_trust_spec_source(
    package: &str,
    version: &str,
) -> Option<&'static AuditedTrustSpecSource> {
    AUDITED_TRUST_SPEC_SOURCES.iter().find(|entry| {
        entry.package == package
            && match entry.version {
                Some(audited) => audited == version,
                // Not "any provider is fine": the caller still has to match
                // BOTH digests, and those digests cover a manifest whose bytes
                // say `version.workspace = true`. A provider that pins its own
                // literal version has different manifest bytes and therefore a
                // different digest, so it can never reach a `None` row.
                None => true,
            }
    })
}

fn regular_file_sha256(path: &Path) -> Result<String, String> {
    let before = fs::symlink_metadata(path)
        .map_err(|error| format!("cannot inspect `{}`: {error}", path.display()))?;
    if !before.file_type().is_file() || before.file_type().is_symlink() {
        return Err(format!(
            "`{}` is not a regular non-symlink file",
            path.display()
        ));
    }
    let file =
        File::open(path).map_err(|error| format!("cannot open `{}`: {error}", path.display()))?;
    let opened = file
        .metadata()
        .map_err(|error| format!("cannot inspect open `{}`: {error}", path.display()))?;
    let mut hasher = Sha256::new();
    hasher
        .update_file(&file)
        .map_err(|error| format!("cannot hash `{}`: {error}", path.display()))?;
    let after = fs::symlink_metadata(path)
        .map_err(|error| format!("cannot re-inspect `{}`: {error}", path.display()))?;
    let stable = after.file_type().is_file()
        && !after.file_type().is_symlink()
        && before.len() == opened.len()
        && opened.len() == after.len()
        && before.modified().ok() == opened.modified().ok()
        && opened.modified().ok() == after.modified().ok();
    #[cfg(unix)]
    let stable = {
        use std::os::unix::fs::MetadataExt as _;

        stable
            && before.dev() == opened.dev()
            && opened.dev() == after.dev()
            && before.ino() == opened.ino()
            && opened.ino() == after.ino()
    };
    if !stable {
        return Err(format!(
            "`{}` changed while its audited source identity was captured",
            path.display()
        ));
    }
    Ok(hasher.finish_hex())
}

pub(super) fn capture_audited_trust_spec_proc_macro(
    package: &Package,
    target: &Target,
) -> Result<Option<AuditedTrustSpecCapture>, String> {
    if !target.proc_macro() || target.name() != "trust" {
        return Ok(None);
    }
    let package_name = package.name().as_str();
    let version = package.version().to_string();
    let Some(audited) = audited_trust_spec_source(package_name, &version) else {
        return Ok(None);
    };

    if !package.dependencies().is_empty() {
        return Err(format!(
            "audited Trust spec provider `{package_name}@{version}` unexpectedly has dependencies"
        ));
    }
    if package.targets().iter().any(Target::is_custom_build) {
        return Err(format!(
            "audited Trust spec provider `{package_name}@{version}` unexpectedly has a build script"
        ));
    }
    let expected_lib = package.root().join("src/lib.rs");
    let Some(actual_lib) = target.src_path().path() else {
        return Err(format!(
            "audited Trust spec provider `{package_name}@{version}` has no source path"
        ));
    };
    if actual_lib != expected_lib {
        return Err(format!(
            "audited Trust spec provider `{package_name}@{version}` has unexpected library source `{}`",
            actual_lib.display()
        ));
    }

    let capture = AuditedTrustSpecCapture {
        package_identity: format!("{package_name}@{version}"),
        manifest_path: package.manifest_path().to_path_buf(),
        lib_path: actual_lib.to_path_buf(),
        expected_manifest_sha256: audited.manifest_sha256,
        expected_lib_sha256: audited.lib_sha256,
    };
    capture.verify_unchanged()?;
    Ok(Some(capture))
}

pub(super) fn audited_trust_spec_requires_fresh_build(
    verified_targo: bool,
    audited_spec_provider: bool,
) -> bool {
    verified_targo && audited_spec_provider
}

fn reject_verified_targo_compiler_wrappers(
    verified_targo: bool,
    wrapper: Option<&Path>,
    workspace_wrapper: Option<&Path>,
) -> Result<(), String> {
    if !verified_targo {
        return Ok(());
    }
    // An empty wrapper path (e.g. from `RUSTC_WRAPPER=""` /
    // `CARGO_BUILD_RUSTC_WRAPPER=""`, which orchestration sets to CLEAR an
    // inherited wrapper) is definitionally "no wrapper": it is never spawned
    // and cannot rewrite argv or forge transport. Only a real, non-empty
    // wrapper program is a threat. Treat empty as absent.
    if let Some(wrapper) = wrapper.filter(|p| !p.as_os_str().is_empty()) {
        return Err(format!(
            "verified Targo refuses compiler wrapper `{}`: a wrapper runs after final argv validation and can rewrite arguments or forge proof transport",
            wrapper.display()
        ));
    }
    if let Some(wrapper) = workspace_wrapper.filter(|p| !p.as_os_str().is_empty()) {
        return Err(format!(
            "verified Targo refuses workspace compiler wrapper `{}`: a wrapper runs after final argv validation and can rewrite arguments or forge proof transport",
            wrapper.display()
        ));
    }
    Ok(())
}

/// Prepares flags and environments we can compute for a `rustc` invocation
/// before the job queue starts compiling any unit.
///
/// This builds a static view of the invocation. Flags depending on the
/// completion of other units will be added later in runtime, such as flags
/// from build scripts.
///
/// Trust: the tuple return carries the admission decisions the exec edge in
/// `rustc()` has to re-check once build-script output has landed. They are
/// returned rather than stored on the command because a `ProcessBuilder` is
/// exactly what a wrapper or a late `@response-file` could rewrite.
#[tracing::instrument(skip_all)]
fn prepare_rustc(
    build_runner: &BuildRunner<'_, '_>,
    unit: &Unit,
) -> CargoResult<(
    ProcessBuilder,
    Option<AuthenticatedTargoProcessAuthority>,
    Option<VerifiedTargoCompilerPolicy>,
    Vec<AuditedTrustSpecCapture>,
    HashSet<PathBuf>,
    CertifiedMonitorCompilerClosure,
    Option<String>,
    bool,
    bool,
    CertifiedMonitorSeal,
)> {
    let gctx = build_runner.bcx.gctx;
    let verified_targo = verified_targo_protocol_active();
    // Trust: retain the assertion in Unit rustflags (identity, graph sharing
    // and fingerprints), but never pass it to rustc as activation authority.
    require_trust_unit_verification_assertion(build_runner, unit)?;
    let compiler_unit_rustflags = if verified_targo {
        compiler_flags_without_verification_assertion(&unit.rustflags)
            .map_err(anyhow::Error::msg)?
    } else {
        unit.rustflags.to_vec()
    };
    let extra_compiler_args = build_runner.bcx.extra_args_for(unit);
    let proof_session = if verified_targo {
        Some(
            verified_targo_proof_session(
                &unit.rustflags,
                extra_compiler_args.map(Vec::as_slice).unwrap_or_default(),
            )
            .map_err(anyhow::Error::msg)?,
        )
    } else {
        None
    };
    // Trust: the lane decides what an evidence-grade boundary does when it is
    // crossed — refuse (a lane that claims proof authority) or forfeit and
    // record (a lane that claims none). Outside a proof session every boundary
    // below is already off, so the answer is irrelevant and defaults to the
    // strict reading rather than parsing ordinary Cargo's rustflags.
    let claims_proof_authority = proof_session.is_none()
        || trust_policy_claims_proof_authority(
            &unit.rustflags,
            extra_compiler_args.map(Vec::as_slice).unwrap_or_default(),
        )
        .map_err(anyhow::Error::msg)?;
    // Trust (D21): where this unit's proc macros expand. Outside a proof
    // session the boundary below is off and the answer is unused.
    let (proc_macro_expansion, proc_macro_isolation_spelled) = if proof_session.is_some() {
        trust_proc_macro_expansion(
            PROC_MACRO_ISOLATION_HOST,
            &unit.rustflags,
            extra_compiler_args.map(Vec::as_slice).unwrap_or_default(),
        )
        .map_err(anyhow::Error::msg)?
    } else {
        (ProcMacroExpansion::InProcess, false)
    };
    let is_trust_test_execution_subject =
        proof_session.is_some() && trust_unit_test_execution_subject(build_runner, unit);
    let is_trust_certified_monitor_subject = proof_session.is_some()
        && trust_unit_certified_monitor_subject(
            build_runner,
            unit,
            is_trust_test_execution_subject,
        );
    reject_verified_targo_compiler_wrappers(
        verified_targo,
        build_runner.bcx.rustc().wrapper.as_deref(),
        build_runner.bcx.rustc().workspace_wrapper.as_deref(),
    )
    .map_err(anyhow::Error::msg)?;
    let mut audited_trust_spec_sources = Vec::new();
    let mut audited_proc_macro_externs = HashSet::default();
    let mut audited_proc_macro_unit = false;
    if verified_targo {
        if let Some(capture) = capture_audited_trust_spec_proc_macro(&unit.pkg, &unit.target)
            .map_err(anyhow::Error::msg)?
        {
            audited_proc_macro_unit = true;
            audited_trust_spec_sources.push(capture);
        }
    }
    // Cargo's package-primary bit is broader than the exact proof root, but it
    // is also the first half of the certified-monitor unit selector. Compute
    // these identities before the proc-macro boundary so monitor-only normal
    // libraries receive the same in-process-code protection as static roots.
    let is_primary_package = build_runner.is_primary_package(unit);
    let is_trust_primary_unit = is_resolved_root_unit(unit, &build_runner.bcx.roots);
    let selected_runtime_unit = trust_selected_runtime_unit(build_runner, unit);
    let monitor_authority_present = gctx
        .get_env_os(TRUST_TARGO_TEST_MONITOR_AUTHORITY_SESSION)
        .is_some();
    let monitor_proc_macro_tcb_in_scope = monitor_authority_present && selected_runtime_unit;
    // The certified-monitor execution TCB is an evidence-grade claim about the
    // test executable. The monitor MIR and its session marker stay exactly as
    // they are in every lane (the runtime checks are the point of an advisory
    // run); only the graph-wide SEALS that would otherwise refuse the build —
    // no dynamic linkage, no unaudited proc macro in the closure, sealed
    // loader environment, no custom target — are forfeited with the lane. The
    // scan itself keeps its monitor scope so the forfeiture warning names the
    // same macros the strict lane refuses.
    let execution_tcb_enforced = monitor_authority_present && claims_proof_authority;

    // A monitor-authorized Cargo graph is an execution TCB even where proof
    // reporting is scoped out. A proc macro in any dependency unit can spawn a
    // writer or alter an rlib that the selected test later authenticates. A
    // transitive derive reexport can also execute inside the selected rustc
    // without appearing as a direct `--extern`. Therefore every graph unit
    // rejects direct unaudited proc macros, and selected runtime units audit the
    // complete transitive closure so fresh facade artifacts cannot hide one.
    let proc_macro_tcb_in_scope = verified_targo
        && (monitor_authority_present || {
            // The in-process proc-macro TCB boundary only has meaning for a unit Targo
            // will actually VERIFY: a proc-macro shares rustc's argv/memory/stderr and
            // could forge THAT unit's proof transport. Compiler stdout is rejected
            // separately on every authenticated Targo unit because it is Cargo's
            // reserved canonical JSON channel. A proc-macro loaded while compiling a
            // scoped-out dependency (compiled with `-Ztrust-verify=off`, emitting no
            // TRUSTJSON) therefore has no proof envelope to forge, so refusing it there
            // is a false positive that aborts the whole build the moment a facade-derive
            // dependency (serde→serde_derive, thiserror→thiserror-impl, zeroize→
            // zeroize_derive, …) is reached. Scope the refusal to verified units,
            // matching `trust_unit_protocol_args`'s own off-switch decision: scoped-out
            // derives compile, while every proc macro a verified unit's rustc loads —
            // direct, through a facade re-export, or privately derived in a dependency
            // (`rustc_loaded_dependency_closure`, PM-1) — is still refused.
            //
            // Trust: include-dependencies also verifies the provider's compilation.
            // Its existing audited admission still checks that it has no dependencies.
            let include_dependencies = resolve_trust_include_dependencies(
                &unit.rustflags,
                build_runner
                    .bcx
                    .extra_args_for(unit)
                    .map(Vec::as_slice)
                    .unwrap_or_default(),
            )
            .map_err(anyhow::Error::msg)?;
            trust_unit_verification_enabled(
                unit.target.is_custom_build(),
                is_resolved_root_unit(unit, &build_runner.bcx.roots),
                is_trust_test_execution_subject,
                include_dependencies,
            )
        });
    let dependency_units = if !proc_macro_tcb_in_scope {
        Vec::new()
    } else if monitor_proc_macro_tcb_in_scope {
        let mut seen = HashSet::default();
        let mut stack = build_runner
            .unit_deps(unit)
            .iter()
            .map(|dependency| dependency.unit.clone())
            .collect::<Vec<_>>();
        let mut closure = Vec::new();
        while let Some(dependency) = stack.pop() {
            if !seen.insert(dependency.clone()) {
                continue;
            }
            stack.extend(
                build_runner
                    .unit_deps(&dependency)
                    .iter()
                    .map(|nested| nested.unit.clone()),
            );
            closure.push(dependency);
        }
        closure
    } else {
        rustc_loaded_dependency_closure(build_runner, unit)
    };
    let mut unaudited_proc_macros = Vec::new();
    if proc_macro_tcb_in_scope {
        for dependency in dependency_units
            .iter()
            .filter(|unit| unit.target.proc_macro())
        {
            if let Some(capture) =
                capture_audited_trust_spec_proc_macro(&dependency.pkg, &dependency.target)
                    .map_err(anyhow::Error::msg)?
            {
                audited_trust_spec_sources.push(capture);
                for output in build_runner.outputs(dependency)?.iter() {
                    if output.flavor == FileFlavor::Linkable {
                        audited_proc_macro_externs.insert(output.path.clone());
                    }
                }
                continue;
            }
            unaudited_proc_macros.push(format!(
                "{}::{}",
                dependency.pkg.package_id(),
                dependency.target.name()
            ));
        }
    }
    if let Some(forfeiture) = admit_in_process_proc_macro_tcb(
        proc_macro_tcb_in_scope,
        claims_proof_authority,
        proc_macro_expansion,
        &format!("{}::{}", unit.pkg.package_id(), unit.target.name()),
        unaudited_proc_macros,
    )
    .map_err(anyhow::Error::msg)?
    {
        // The record: Cargo's warning channel is the child's stderr, which
        // targo-trust echoes and files into report.json as a `warning`
        // diagnostic (`parse_untrusted_cargo_stderr`), so the forfeiture is
        // visible on the terminal and in the report with no transport change.
        gctx.shell().warn(forfeiture)?;
    }
    reject_certified_monitor_dynamic_unit_dependencies(
        execution_tcb_enforced,
        dependency_units.iter().filter_map(|dependency| {
            if dependency.target.proc_macro() {
                // Proc macros are a compile-time in-process TCB handled by the
                // audited-source/no-unaudited-macro boundary above. They are
                // never loaded by the resulting test executable.
                return None;
            }
            let dynamic_types = dependency
                .target
                .rustc_crate_types()
                .into_iter()
                .filter(CrateType::is_dynamic)
                .map(|crate_type| crate_type.as_str().to_string())
                .collect::<Vec<_>>()
                .join("+");
            (!dynamic_types.is_empty()).then(|| {
                format!(
                    "{}::{} ({dynamic_types})",
                    dependency.pkg.package_id(),
                    dependency.target.name()
                )
            })
        }),
    )
    .map_err(anyhow::Error::msg)?;
    if verified_targo {
        reject_verified_custom_target_llvm_args(unit.kind)?;
    }
    // Cargo's `CARGO_PRIMARY_PACKAGE` contract is package-wide, but Trust's
    // authenticated proof subject is narrower: only an exact resolved root
    // unit is primary. A selected package can also occur in the graph as a
    // host/build dependency or proc macro, and those distinct units must not
    // claim the root target's terminal summary.
    let is_workspace = build_runner.bcx.ws.is_member(&unit.pkg);

    let (mut base, rustc_process_role) =
        build_runner
            .compilation
            .rustc_process(unit, is_primary_package, is_workspace)?;
    // Package-specific profile rustflags apply to dependency units too. A
    // dependency can carry an attacker-selected `--extern`/`-L` into its rlib,
    // and a native archive member hidden behind that metadata can reach the
    // selected executable without appearing in the root unit's argv. Seal
    // every graph unit while the global monitor authority is active; only the
    // compiler marker itself remains scoped to selected runtime units.
    reject_certified_monitor_presnapshot_closure_controls(
        execution_tcb_enforced,
        &unit.profile.rustflags,
        "profile rustflags",
    )
    .map_err(anyhow::Error::msg)?;
    let authenticated_targo = crate::is_targo_invocation();
    if verified_targo {
        // Tuple targets have already been proven to be compiler built-ins, and
        // explicit JSON targets are passed by canonical path with a byte digest.
        // The ambient named-custom search path is therefore unnecessary and must
        // not become a late, untracked input to the compiler process.
        base.env_remove("RUST_TARGET_PATH");
    }
    if authenticated_targo && rustc_process_role.is_primary_override() {
        if let Some(workspace_wrapper) = build_runner
            .bcx
            .rustc()
            .workspace_wrapper
            .as_deref()
            .filter(|wrapper| !wrapper.as_os_str().is_empty())
        {
            // The primary fix proxy, rather than Cargo itself, launches the
            // workspace wrapper. Materialize the resolved identity so a late
            // environment overlay cannot substitute or erase it.
            base.env(RUSTC_WORKSPACE_WRAPPER_ENV, workspace_wrapper);
        } else {
            base.env_remove(RUSTC_WORKSPACE_WRAPPER_ENV);
        }
    }
    append_rustc_base_and_deps(
        &RustcCommandContext::for_runner(build_runner),
        &mut base,
        unit,
        &build_runner.jobserver,
    )?;
    let cargo_compiler_closure = if execution_tcb_enforced {
        CertifiedMonitorCompilerClosure::capture(&base).map_err(anyhow::Error::msg)?
    } else {
        CertifiedMonitorCompilerClosure::default()
    };
    append_rustc_caller_flags(
        &RustcCommandContext::for_runner(build_runner),
        &mut base,
        unit,
        &compiler_unit_rustflags,
    );
    // Trust verification scope is a property of Cargo's resolved compilation
    // unit, not of a user-controlled crate name or ambient compiler process
    // environment. The complete verified host policy is injected while target
    // information is built, before Unit construction and fingerprinting. At
    // invocation time Cargo appends reporting metadata plus the resolved
    // per-unit off-switch, when needed, after every caller-controlled source.
    let certified_monitor_session = resolve_certified_monitor_unit_session(
        verified_targo,
        gctx.get_env_os(TRUST_TARGO_TEST_MONITOR_AUTHORITY_SESSION),
        proof_session.as_deref(),
        selected_runtime_unit,
    )
    .map_err(anyhow::Error::msg)?;
    reject_certified_monitor_custom_target(execution_tcb_enforced, unit.kind)
        .map_err(anyhow::Error::msg)?;
    set_certified_monitor_session_env(&mut base, certified_monitor_session.as_deref());
    let protocol_args = if proof_session.is_some() {
        let include_dependencies = resolve_trust_include_dependencies(
            &unit.rustflags,
            extra_compiler_args.map(Vec::as_slice).unwrap_or_default(),
        )
        .map_err(anyhow::Error::msg)?;
        // The newer proof-unit inventory owns the exact primary/execution
        // identity. Retain the private phase-A monitor marker as an additional
        // compiler-domain check for the two-phase execution lane.
        let mut protocol_args = trust_unit_protocol_args(
            unit.target.is_custom_build(),
            is_trust_primary_unit,
            is_trust_test_execution_subject,
            is_trust_certified_monitor_subject,
            &unit.pkg.name().to_string(),
            include_dependencies,
        );
        // Trust: compute from the original graph inputs BEFORE adding launch-only
        // resource metadata. Hashing these carriers would be self-referential and
        // would change the existing cache/freshness contract.
        if let (Some(session), Some(proof_unit)) = (
            proof_session.as_deref(),
            trust_proof_unit_identity(build_runner, unit)?,
        ) {
            let unit_digest = trust_declared_unit_identity_sha256(build_runner, unit)?;
            protocol_args.extend(native_admission_metadata_args(
                session,
                &unit_digest,
                &proof_unit.semantics_sha256,
                &proof_unit.role,
                &scoped_unit_compile_target(&build_runner.bcx, unit)?,
            ));
            // Trust: rebind the output-only request to the same graph metadata
            // already declared in the complete proof/exclusion inventory.
            if let Some(request) = verifier_input_export_request(
                &compiler_unit_rustflags,
                extra_compiler_args.map(Vec::as_slice).unwrap_or_default(),
                session,
            )? {
                protocol_args.extend(crate::util::verifier_input_export::unit_args(
                    &request,
                    &crate::util::verifier_input_export::ExportUnit {
                        session: session.to_owned(),
                        unit_sha256: unit_digest,
                        semantics_sha256: proof_unit.semantics_sha256.clone(),
                        package_name: proof_unit.package_name.clone(),
                        role: proof_unit.role.to_owned(),
                        graph_role: trust_unit_graph_role(build_runner, unit).to_owned(),
                        exclusion_reason: None,
                        mode: proof_unit.mode.to_owned(),
                        verification_enabled: trust_proof_unit_role_for_policy(
                            build_runner,
                            unit,
                            include_dependencies,
                        )
                        .is_some(),
                    },
                )?);
            }
        }
        if certified_monitor_session.is_some() {
            protocol_args.extend(["-Z".to_string(), "trust-targo-test-monitor".to_string()]);
        }
        // Trust (cross-crate composition): declare the foreign bundling scope
        // for THIS unit — the workspace-internal library dependencies this same
        // build compiled itself.
        //
        // The compiler uses the list to decide whether a foreign callee's BODY
        // may be pulled into this unit's lowered verification bundle and its
        // obligations re-derived here. It transports no verdict and cannot: a
        // foreign proof result is not readable in any compilation, because
        // `trust_proof_results` has no extern provider and no disk cache.
        //
        // It is a CALLER-side declaration on purpose. The cross-crate admission
        // hole this repo closed in August keyed on `#[automatically_derived]`,
        // a callee SELF-CLAIM that is stable, ungated and user-writable. "Units
        // this build compiled from a path source in this workspace" is not a
        // claim the callee makes about itself, and it keeps registry code —
        // where the bundle ceilings and the `core::fmt` wall bind immediately —
        // out of scope.
        let bundle_scope = trust_unit_foreign_bundle_scope(build_runner, unit);
        if !bundle_scope.is_empty() {
            protocol_args.extend([
                "-Z".to_string(),
                format!("trust-bundle-foreign-crate={}", bundle_scope.join(",")),
            ]);
        }
        // Bind the exact bytes rustc parses, not merely the mutable path Cargo
        // observed before and after the child process. rustc compares this
        // Cargo-owned digest against the TargetTuple contents it loaded in one
        // read, closing an A -> B -> A same-path mutation race.
        if let Some(digest) = exact_unit_compile_target_spec_sha256(unit.kind)? {
            protocol_args.extend([
                "-Z".to_string(),
                format!("trust-verify-target-spec-sha256={digest}"),
            ]);
        }
        // Trust (PM-1): the crate-loader proc-macro boundary for every unit whose
        // in-process proc-macro TCB Targo scoped in above, admitting exactly the
        // audited provider dylibs it resolved. rustc then refuses (advisory:
        // reports) any other proc macro its loader meets before opening it — the
        // backstop for load paths this unit graph does not model. Only with the
        // session the driver requires the boundary to bind.
        if proc_macro_tcb_in_scope && proof_session.is_some() {
            protocol_args.extend(["-Z".to_string(), "trust-proc-macro-boundary".to_string()]);
            let mut audited = audited_proc_macro_externs.iter().collect::<Vec<_>>();
            audited.sort();
            for path in audited {
                protocol_args.extend([
                    "-Z".to_string(),
                    format!("trust-audited-proc-macro={}", path.display()),
                ]);
            }
        }
        // Trust (D21): every unit whose proc-macro TCB is in scope expands its
        // macros in the sandboxed worker wherever the host has one. This is
        // what the admission above relied on, so it is passed under exactly
        // the same condition; a lane that spelled the option already carries
        // it in the unit's flags.
        if proc_macro_tcb_in_scope
            && proof_session.is_some()
            && proc_macro_expansion == ProcMacroExpansion::IsolatedWorker
            && !proc_macro_isolation_spelled
        {
            protocol_args.extend(["-Z".to_string(), PROC_MACRO_ISOLATION_OPTION.to_string()]);
        }
        base.args(&protocol_args);
        protocol_args
    } else {
        Vec::new()
    };
    append_rustc_output_and_runtime(
        &RustcCommandContext::for_runner(build_runner),
        &mut base,
        unit,
        authenticated_targo,
        verified_targo,
        rustc_process_role,
    )?;

    let verified_policy = if proof_session.is_some() {
        let policy = VerifiedTargoCompilerPolicy::new(&compiler_unit_rustflags, &protocol_args)
            .map_err(anyhow::Error::msg)?;
        if let Some(extra) = extra_compiler_args {
            policy
                .reject_parallel_source(extra, "cargo rustc extra compiler arguments")
                .map_err(anyhow::Error::msg)?;
        }
        policy
            .reject_parallel_source(&unit.profile.rustflags, "profile rustflags")
            .map_err(anyhow::Error::msg)?;
        validate_verified_targo_compiler_argument_boundaries(&base, &policy)
            .map_err(anyhow::Error::msg)?;
        Some(policy)
    } else {
        None
    };

    validate_certified_monitor_command_env(&base, certified_monitor_session.as_deref())
        .map_err(anyhow::Error::msg)?;
    // Trust: the one loader search value the seal below reinstalls, derived
    // from the authenticated startup closure of the authenticated compiler —
    // not from `base`, whose value `fill_env` extended with Cargo's `deps`.
    let certified_monitor_seal = CertifiedMonitorSeal::capture(
        execution_tcb_enforced,
        build_runner.compilation.authenticated_compiler_program(),
        build_runner.bcx.gctx,
    )?;
    seal_certified_monitor_graph_compiler_environment(
        &mut base,
        &certified_monitor_seal,
        certified_monitor_session.as_deref(),
    )
    .map_err(anyhow::Error::msg)?;
    reject_certified_monitor_dynamic_rust_linkage_with_audited_proc_macro(
        &base,
        execution_tcb_enforced,
        &audited_proc_macro_externs,
        &cargo_compiler_closure,
        audited_proc_macro_unit,
    )
    .map_err(anyhow::Error::msg)?;

    // Capture the complete process authority only after the certified-monitor
    // lane has applied its stricter environment and linker closure.
    action_sandbox::apply(build_runner, unit, &mut base)?;
    let process_authority = AuthenticatedTargoProcessAuthority::capture_if_authenticated(
        &base,
        authenticated_targo,
        rustc_process_role,
        is_primary_package,
    )?;

    Ok((
        base,
        process_authority,
        verified_policy,
        audited_trust_spec_sources,
        audited_proc_macro_externs,
        cargo_compiler_closure,
        certified_monitor_session,
        execution_tcb_enforced,
        audited_proc_macro_unit,
        certified_monitor_seal,
    ))
}

/// Independent DATA preparation for the explicitly closed native profile.
/// Verified/monitor/script/sandbox paths are refused before entering here;
/// their authority cannot be synthesized from this resolved context.
#[cfg(any(target_os = "linux", target_os = "macos"))]
fn prepare_native_rustc_command<L: std::borrow::Borrow<layout::LayoutPaths>>(
    context: &RustcCommandContext<'_, '_, '_, L>,
    unit: &Unit,
    jobserver: &cargo_util::Jobserver,
) -> CargoResult<ProcessBuilder> {
    anyhow::ensure!(
        !verified_targo_protocol_active()
            && !context.bcx.action_sandbox
            && context
                .bcx
                .gctx
                .get_env_os(TRUST_TARGO_TEST_MONITOR_AUTHORITY_SESSION)
                .is_none()
            && !unit.target.is_custom_build()
            && !unit.target.proc_macro()
            && !unit.target.is_test()
            && !unit.target.is_bench()
            && !unit.pkg.manifest().is_embedded()
            && context.bcx.rustc().wrapper.is_none()
            && context.bcx.rustc().workspace_wrapper.is_none(),
        "independent command context exceeds closed native profile"
    );
    prepare_unverified_rustc_recipe(context, unit, jobserver)
}

/// Trust: shared unverified compiler recipe, independent of candidate target
/// admission. Callers retain their own transport/profile guards and owners.
#[cfg(any(target_os = "linux", target_os = "macos"))]
fn prepare_unverified_rustc_recipe<L: std::borrow::Borrow<layout::LayoutPaths>>(
    context: &RustcCommandContext<'_, '_, '_, L>,
    unit: &Unit,
    jobserver: &cargo_util::Jobserver,
) -> CargoResult<ProcessBuilder> {
    let (mut command, role) = context.compilation.rustc_process(
        unit,
        context.is_primary_package(unit),
        context.bcx.ws.is_member(&unit.pkg),
    )?;
    anyhow::ensure!(
        role == compilation::RustcProcessRole::Compiler,
        "independent command context selected another compiler role"
    );
    append_rustc_base_and_deps(context, &mut command, unit, jobserver)?;
    append_rustc_caller_flags(context, &mut command, unit, &unit.rustflags);
    set_certified_monitor_session_env(&mut command, None);
    append_rustc_output_and_runtime(
        context,
        &mut command,
        unit,
        crate::is_targo_invocation(),
        false,
        role,
    )?;
    validate_certified_monitor_command_env(&command, None).map_err(anyhow::Error::msg)?;
    Ok(command)
}

/// Trust: exact early Rustc-parent PATH/cwd data for the ordinary native
/// transport. A failure only refuses cache reuse; actual command execution,
/// script scheduling and publication remain at their existing owning edges.
#[cfg(any(target_os = "linux", target_os = "macos"))]
pub(super) fn tool_input_parent_command(
    build_runner: &BuildRunner<'_, '_>,
    unit: &Unit,
) -> CargoResult<ProcessBuilder> {
    validate_tool_input_profile(build_runner, unit)?;
    tool_input_parent_command_for_profile(build_runner, unit)
}

/// Static transport admission is also used before a cold compile. A missing
/// cached build-script recipe can be repaired by real execution; an unknown
/// executor/profile cannot acquire receipt authority that way.
#[cfg(any(target_os = "linux", target_os = "macos"))]
pub(super) fn validate_tool_input_profile(
    build_runner: &BuildRunner<'_, '_>,
    unit: &Unit,
) -> CargoResult<trust_fs_observation::tool_lookup::Profile> {
    anyhow::ensure!(
        crate::is_targo_invocation()
            && crate::trust_no_verify_fast()
            && build_runner.native_tool_inputs
            && !crate::resource_worker_v3()
            && !verified_targo_protocol_active()
            && !build_runner.bcx.action_sandbox
            && build_runner
                .bcx
                .gctx
                .get_env_os(TRUST_TARGO_TEST_MONITOR_AUTHORITY_SESSION)
                .is_none()
            && !unit.pkg.manifest().is_embedded()
            && build_runner.bcx.rustc().wrapper.is_none()
            && build_runner.bcx.rustc().workspace_wrapper.is_none()
            && !build_runner.bcx.gctx.cli_unstable().section_timings
            && matches!(
                unit.mode,
                CompileMode::Build | CompileMode::Check { .. } | CompileMode::Test
            ),
        "tool-input parent reconstruction exceeds ordinary native profile"
    );
    build_runner
        .tool_input_transport_profile()
        .ok_or_else(|| anyhow::anyhow!("selected runtime has no local tool-input profile"))
}

#[cfg(any(target_os = "linux", target_os = "macos"))]
fn tool_input_parent_command_for_profile(
    build_runner: &BuildRunner<'_, '_>,
    unit: &Unit,
) -> CargoResult<ProcessBuilder> {
    // Target kinds such as build-script compilations, tests, benches and proc
    // macros are ordinary compiler units here. Candidate-only exclusions
    // would make their otherwise valid terminal tool records perpetually dirty.
    let mut command = prepare_unverified_rustc_recipe(
        &RustcCommandContext::for_runner(build_runner),
        unit,
        &build_runner.jobserver,
    )?;
    if let Some(scripts) = build_runner.build_scripts.get(unit) {
        let script_metadatas = build_runner.find_build_script_metadatas(unit);
        let mut required = scripts
            .to_link
            .iter()
            .map(|(_, metadata)| *metadata)
            .chain(scripts.plugins.iter().map(|(_, metadata)| *metadata))
            .collect::<std::collections::BTreeSet<_>>();
        required.extend(script_metadatas.iter().flatten().copied());
        let outputs = custom_build::planning_command_outputs(
            build_runner,
            &required.into_iter().collect::<Vec<_>>(),
        )?;
        append_build_script_overlays(
            &mut command,
            &outputs,
            BuildScriptOverlay {
                scripts,
                pass_l_flag: unit.target.is_lib() || !unit.pkg.targets().iter().any(|t| t.is_lib()),
                target: &unit.target,
                current_id: unit.pkg.package_id(),
                mode: unit.mode,
                root_output: build_runner.files().host_dest(),
                script_metadatas,
            },
            None,
            true,
        )?;
    }
    anyhow::ensure!(
        !command.has_process_executor(),
        "hosted compiler parent transport cannot reuse native tool inputs"
    );
    Ok(command)
}

#[cfg(not(any(target_os = "linux", target_os = "macos")))]
pub(super) fn validate_tool_input_profile(
    _build_runner: &BuildRunner<'_, '_>,
    _unit: &Unit,
) -> CargoResult<trust_fs_observation::tool_lookup::Profile> {
    anyhow::bail!("native tool-input profile is unavailable on this host")
}

#[cfg(not(any(target_os = "linux", target_os = "macos")))]
pub(super) fn tool_input_parent_command(
    _build_runner: &BuildRunner<'_, '_>,
    _unit: &Unit,
) -> CargoResult<ProcessBuilder> {
    anyhow::bail!("native tool-input parent reconstruction is unavailable on this host")
}

/// Shared ordinary command recipe. Its caller retains all actual owners.
fn append_rustc_base_and_deps<L: std::borrow::Borrow<layout::LayoutPaths>>(
    build_runner: &RustcCommandContext<'_, '_, '_, L>,
    base: &mut ProcessBuilder,
    unit: &Unit,
    jobserver: &cargo_util::Jobserver,
) -> CargoResult<()> {
    let gctx = build_runner.bcx.gctx;
    build_base_args_context(build_runner, base, unit)?;
    if unit.pkg.manifest().is_embedded() {
        if !gctx.cli_unstable().script {
            anyhow::bail!(
                "parsing `{}` requires `-Zscript`",
                unit.pkg.manifest_path().display()
            );
        }
        base.arg("-Z").arg("crate-attr=feature(frontmatter)");
        base.arg("-Z").arg("crate-attr=allow(unused_features)");
    }

    base.inherit_jobserver(jobserver);
    build_deps_args_context(base, build_runner, unit)?;
    Ok(())
}

fn append_rustc_caller_flags<L: std::borrow::Borrow<layout::LayoutPaths>>(
    build_runner: &RustcCommandContext<'_, '_, '_, L>,
    base: &mut ProcessBuilder,
    unit: &Unit,
    compiler_unit_rustflags: &[String],
) {
    add_cap_lints(build_runner.bcx, unit, base);
    if let Some(args) = build_runner.bcx.extra_args_for(unit) {
        base.args(args);
    }
    base.args(compiler_unit_rustflags);
}

fn set_certified_monitor_session_env(base: &mut ProcessBuilder, session: Option<&str>) {
    base.env_remove(TRUST_TARGO_TEST_MONITOR_SESSION);
    if let Some(session) = session {
        base.env(TRUST_TARGO_TEST_MONITOR_SESSION, session);
    }
}

fn append_rustc_output_and_runtime<L: std::borrow::Borrow<layout::LayoutPaths>>(
    build_runner: &RustcCommandContext<'_, '_, '_, L>,
    base: &mut ProcessBuilder,
    unit: &Unit,
    authenticated_targo: bool,
    verified_targo: bool,
    rustc_process_role: compilation::RustcProcessRole,
) -> CargoResult<()> {
    let gctx = build_runner.bcx.gctx;
    let is_primary_package = build_runner.is_primary_package(unit);
    // Trust: source-only checksums cannot establish a cache hit when a used
    // binary supplied through --extern (or resolved through -L) changes at the
    // same path. Let the producer report the binaries it actually consumed,
    // with the same checksums as its source inputs. The native default's
    // capability probe requires both options; compatibility Cargo keeps its
    // existing explicit opt-in.
    if gctx.cli_unstable().binary_dep_depinfo
        || (crate::is_targo_invocation()
            && build_runner.bcx.source_fingerprint == FingerprintMethod::Content)
    {
        base.arg("-Z").arg("binary-dep-depinfo");
    }
    if build_runner.bcx.source_fingerprint == FingerprintMethod::Content {
        base.arg("-Z").arg("checksum-hash-algorithm=blake3");
        if authenticated_targo
            && !verified_targo
            && !rustc_process_role.is_primary_override()
            && build_runner.bcx.rustc().supports_tool_input_depinfo(gctx)?
        {
            base.arg("-Ztrust-tool-inputs");
        }
    }

    if is_primary_package {
        base.env(CARGO_PRIMARY_PACKAGE_ENV, "1");
        let file_list = build_runner.sbom_output_files(unit)?;
        if !file_list.is_empty() {
            let file_list = std::env::join_paths(file_list)?;
            base.env("CARGO_SBOM_PATH", file_list);
        }
    } else if authenticated_targo {
        // Ambient or project-controlled values must not turn dependencies
        // into Tippy primary packages. Ordinary Cargo retains its historical
        // inheritance behavior.
        base.env_remove(CARGO_PRIMARY_PACKAGE_ENV);
    }

    if unit.target.is_test() || unit.target.is_bench() {
        let tmp = build_runner
            .files()
            .layout(unit.kind)
            .build_dir()
            .prepare_tmp()?;
        base.env("CARGO_TARGET_TMPDIR", tmp.display().to_string());
    }

    // Added last to reduce the risk of RUSTFLAGS or `[lints]` from interfering with
    // `unused_dependencies` tracking
    base.arg("--force-warn=unused_crate_dependencies");

    // Trust: the native frontend otherwise remains serial even when Targo's
    // admitted jobserver has idle capacity. Its pool acquires shared tokens;
    // this ceiling therefore also helps a single large crate without creating
    // a second independent worker budget. Never alter proof-session policy.
    // An explicitly stable child must not receive an inferred nightly option.
    // fill_env already applied configured and captured inherited environment.
    if let Some(jobs) = resource_budget::frontend_jobs(
        authenticated_targo
            && !verified_targo
            && !rustc_process_role.is_primary_override()
            && base.get_env("RUSTC_BOOTSTRAP").as_deref() != Some(OsStr::new("-1"))
            && build_runner
                .bcx
                .rustc()
                .verbose_version
                .lines()
                .any(|line| line.starts_with("trust: ")),
        build_runner.bcx.jobs(),
        base.get_args().map(|arg| arg.as_os_str()),
    ) {
        base.arg(format!("-Zthreads={jobs}"));
    }

    Ok(())
}

fn prefixed_compiler_options<S: AsRef<str>>(
    args: &[S],
    prefix: &str,
) -> Result<Vec<(String, Option<String>)>, String> {
    let mut options = Vec::new();
    let mut index = 0;
    while index < args.len() {
        let argument = args[index].as_ref();
        let (option, consumed) = if argument == prefix {
            let option = args.get(index + 1).ok_or_else(|| {
                format!("verified Targo compiler arguments end with incomplete `{prefix}`")
            })?;
            (Some(option.as_ref()), 2)
        } else {
            (
                argument
                    .strip_prefix(prefix)
                    .filter(|option| !option.is_empty()),
                1,
            )
        };
        if let Some(option) = option {
            let (name, value) = rustc_option_parts(option);
            options.push((name.into_owned(), value.map(str::to_string)));
        }
        index += consumed;
    }
    Ok(options)
}

fn codegen_compiler_options<S: AsRef<str>>(
    args: &[S],
) -> Result<Vec<(String, Option<String>)>, String> {
    let mut options = Vec::new();
    let mut index = 0;
    while index < args.len() {
        let argument = args[index].as_ref();
        let (option, consumed) = if matches!(argument, "-C" | "--codegen") {
            let option = args.get(index + 1).ok_or_else(|| {
                format!("verified Targo compiler arguments end with incomplete `{argument}`")
            })?;
            (Some(option.as_ref()), 2)
        } else if let Some(option) = argument
            .strip_prefix("-C")
            .filter(|option| !option.is_empty())
        {
            (Some(option), 1)
        } else {
            (argument.strip_prefix("--codegen="), 1)
        };
        if let Some(option) = option {
            let (name, value) = rustc_option_parts(option);
            options.push((name.into_owned(), value.map(str::to_string)));
        }
        index += consumed;
    }
    Ok(options)
}

fn is_verified_targo_z_authority(name: &str) -> bool {
    name == "codegen_backend" || name.starts_with("trust_")
}

fn is_verified_targo_retired_z(name: &str) -> bool {
    // The inherited upstream exec/logic projection is not part of Trust's
    // verifier policy.  Reject it from every Cargo compiler-argument source
    // instead of allowing profile/[host]/future late flags to reach trustc and
    // relying on the compiler's final domain check.
    name == "contract_checks"
}

/// Options that make rustc return before it can produce evidence.
///
/// `trust_dump` needs its value: only the `mir-only` sink truncates the compile,
/// while the other sinks publish an artifact from an otherwise normal run.
fn is_verified_targo_early_exit_z(name: &str, value: Option<&str>) -> bool {
    if name == "trust_dump" {
        return value.is_some_and(|value| value.starts_with("mir-only:"));
    }
    matches!(
        name,
        "help" | "link_only" | "ls" | "no_analysis" | "parse_crate_root_only" | "unpretty"
    )
}

fn is_verified_targo_in_process_plugin_z(name: &str) -> bool {
    name == "llvm_plugins"
}

fn is_verified_targo_safety_c(name: &str) -> bool {
    matches!(name, "overflow_checks" | "debug_assertions")
}

fn is_verified_targo_early_exit_c(name: &str) -> bool {
    name == "help"
}

fn is_trust_cg_contract_c(name: &str) -> bool {
    matches!(
        name,
        "panic" | "debuginfo" | "codegen_units" | "incremental"
    )
}

#[derive(Clone, Debug)]
struct VerifiedTargoCompilerPolicy {
    z: BTreeMap<String, Option<String>>,
    c: BTreeMap<String, Option<String>>,
    trust_cg: bool,
}

// Trust: rustc permits separate artifact sinks to repeat -Ztrust-dump. Keep
// each sink's exact path in the authenticated policy instead of collapsing it.
fn verified_targo_z_authority_key(name: &str, value: Option<&str>) -> Result<String, String> {
    if name != "trust_dump" {
        return Ok(name.to_owned());
    }
    let (sink, path) = value
        .and_then(|v| v.split_once(':'))
        .ok_or_else(|| "verified artifact sink requires a typed nonempty path".to_owned())?;
    if !matches!(sink, "mir" | "native-bundle" | "ir" | "spec-clean") || path.is_empty() {
        return Err(
            "verified artifact export requires an existing nontruncating typed sink".to_owned(),
        );
    }
    Ok(format!("trust_dump:{sink}"))
}

impl VerifiedTargoCompilerPolicy {
    fn new(unit_rustflags: &[String], protocol_args: &[String]) -> Result<Self, String> {
        let mut z = BTreeMap::new();
        let unit_z = prefixed_compiler_options(unit_rustflags, "-Z")?;
        if let Some((name, _)) = unit_z.iter().find(|(name, value)| {
            is_verified_targo_retired_z(name)
                || is_verified_targo_early_exit_z(name, value.as_deref())
                || is_verified_targo_in_process_plugin_z(name)
        }) {
            if is_verified_targo_retired_z(name) {
                return Err(format!(
                    "verified Targo policy cannot contain retired `-Z{name}`; certified monitors are selected automatically"
                ));
            }
            return Err(format!(
                "verified Targo policy cannot contain unsafe/early-exit `-Z{name}`"
            ));
        }
        for (name, value) in unit_z
            .into_iter()
            .filter(|(name, _)| is_verified_targo_z_authority(name))
            .chain(
                prefixed_compiler_options(protocol_args, "-Z")?
                    .into_iter()
                    .filter(|(name, _)| is_verified_targo_z_authority(name)),
            )
        {
            let value = if name == "codegen_backend" {
                value.map(|value| canonical_codegen_backend_value(&value).to_string())
            } else {
                value
            };
            let key = verified_targo_z_authority_key(&name, value.as_deref())?;
            if z.insert(key, value).is_some() {
                return Err(format!(
                    "verified Targo policy contains duplicate rustc-equivalent `-Z{name}` authority"
                ));
            }
        }
        let trust_cg = z.get("codegen_backend").and_then(Option::as_deref) == Some("trust-cg");
        if trust_cg && unit_rustflags.iter().any(|argument| argument == "-g") {
            return Err(
                "verified trust-cg policy cannot contain `-g`; debuginfo must remain disabled"
                    .to_string(),
            );
        }

        let mut c = BTreeMap::new();
        for (name, value) in codegen_compiler_options(unit_rustflags)? {
            if is_verified_targo_early_exit_c(&name) {
                return Err(
                    "verified Targo policy cannot contain `-Chelp`: compilation must reach proof transport"
                        .to_string(),
                );
            }
            if name == "llvm_args" {
                return Err(
                    "verified Targo policy cannot contain `-Cllvm-args`: LLVM plugins are outside the proof TCB"
                        .to_string(),
                );
            }
            if !is_verified_targo_safety_c(&name) && !(trust_cg && is_trust_cg_contract_c(&name)) {
                continue;
            }
            if trust_cg && name == "incremental" {
                return Err(
                    "verified trust-cg policy cannot contain `-Cincremental`; absence is the required contract"
                        .to_string(),
                );
            }
            if c.insert(name.clone(), value).is_some() {
                return Err(format!(
                    "verified Targo policy contains duplicate rustc-equivalent `-C{name}` authority"
                ));
            }
        }
        if trust_cg {
            for (name, expected) in [
                ("panic", "abort"),
                ("debuginfo", "0"),
                ("codegen_units", "1"),
            ] {
                if c.get(name).and_then(Option::as_deref) != Some(expected) {
                    return Err(format!(
                        "verified trust-cg policy requires canonical `-C{name}={expected}`"
                    ));
                }
            }
        }
        Ok(Self { z, c, trust_cg })
    }

    fn reject_parallel_source<S: AsRef<str>>(
        &self,
        args: &[S],
        source: &str,
    ) -> Result<(), String> {
        if let Some((name, _)) =
            prefixed_compiler_options(args, "-Z")?
                .into_iter()
                .find(|(name, value)| {
                    is_verified_targo_retired_z(name)
                        || is_verified_targo_z_authority(name)
                        || is_verified_targo_early_exit_z(name, value.as_deref())
                        || is_verified_targo_in_process_plugin_z(name)
                        || name == "valtree_node_limit"
                })
        {
            if name == "valtree_node_limit" {
                return Err(format!(
                    "{source} uses retired `-Zvaltree-node-limit`; verified compilations enforce rustc's fixed valtree resource limit"
                ));
            }
            if is_verified_targo_retired_z(&name) {
                return Err(format!(
                    "{source} uses retired `-Z{name}`; certified monitors are selected automatically"
                ));
            }
            return Err(format!(
                "{source} cannot set rustc-equivalent `-Z{name}` during a verified Targo invocation"
            ));
        }
        if let Some((name, _)) = codegen_compiler_options(args)?
            .into_iter()
            .find(|(name, _)| {
                is_verified_targo_early_exit_c(name)
                    || name == "llvm_args"
                    || self.c.contains_key(name)
                    || (self.trust_cg && is_trust_cg_contract_c(name))
            })
        {
            return Err(format!(
                "{source} cannot override authenticated `-C{name}` verifier policy"
            ));
        }
        if self.trust_cg && args.iter().any(|argument| argument.as_ref() == "-g") {
            return Err(format!(
                "{source} cannot override authenticated trust-cg debuginfo policy with `-g`"
            ));
        }
        Ok(())
    }

    fn validate_final(&self, args: &[&str]) -> Result<(), String> {
        let mut actual_z = BTreeMap::new();
        let final_z = prefixed_compiler_options(args, "-Z")?;
        if let Some((name, _)) = final_z.iter().find(|(name, value)| {
            is_verified_targo_retired_z(name)
                || is_verified_targo_early_exit_z(name, value.as_deref())
                || is_verified_targo_in_process_plugin_z(name)
        }) {
            if is_verified_targo_retired_z(name) {
                return Err(format!(
                    "final verified rustc argv contains retired `-Z{name}`"
                ));
            }
            return Err(format!(
                "final verified rustc argv contains early-exit `-Z{name}`"
            ));
        }
        for (name, value) in final_z
            .into_iter()
            .filter(|(name, _)| is_verified_targo_z_authority(name))
        {
            let value = if name == "codegen_backend" {
                value.map(|value| canonical_codegen_backend_value(&value).to_string())
            } else {
                value
            };
            let key = verified_targo_z_authority_key(&name, value.as_deref())?;
            if actual_z.insert(key, value).is_some() {
                return Err(format!(
                    "final verified rustc argv contains duplicate `-Z{name}` authority"
                ));
            }
        }
        if actual_z != self.z {
            return Err(
                "final verified rustc argv does not match Targo's authenticated `-Z` policy"
                    .to_string(),
            );
        }

        let mut actual_c = BTreeMap::new();
        for (name, value) in codegen_compiler_options(args)? {
            if is_verified_targo_early_exit_c(&name) {
                return Err("final verified rustc argv contains early-exit `-Chelp`".to_string());
            }
            if name == "llvm_args" {
                return Err(
                    "final verified rustc argv contains forbidden `-Cllvm-args`".to_string()
                );
            }
            actual_c.insert(name, value);
        }
        if self.trust_cg && actual_c.contains_key("incremental") {
            return Err(
                "final verified trust-cg argv contains forbidden `-Cincremental`".to_string(),
            );
        }
        if self.trust_cg && args.contains(&"-g") {
            return Err("final verified trust-cg argv contains forbidden `-g`".to_string());
        }
        for (name, expected) in &self.c {
            if actual_c.get(name) != Some(expected) {
                return Err(format!(
                    "final verified rustc argv overrides authenticated `-C{name}` policy"
                ));
            }
        }
        Ok(())
    }
}

/// Reject compiler arguments whose executed token stream differs from the
/// ProcessBuilder vector audited by Targo. This check intentionally runs after
/// all Cargo/user/profile/config vectors have been assembled: validating only
/// inherited RUSTFLAGS leaves `[host]`, profile rustflags, and future sources
/// as parallel argfile/separator bypasses.
fn validate_verified_targo_compiler_argument_boundaries(
    command: &ProcessBuilder,
    policy: &VerifiedTargoCompilerPolicy,
) -> Result<(), String> {
    let arguments = command
        .get_args()
        .enumerate()
        .map(|(index, argument)| {
            argument.to_str().ok_or_else(|| {
                format!(
                    "verified Targo compiler argument {index} is not valid Unicode; its option boundaries cannot be authenticated"
                )
            })
        })
        .collect::<Result<Vec<_>, _>>()?;
    for (index, argument) in arguments.iter().copied().enumerate() {
        if argument.starts_with('@') {
            return Err(format!(
                "verified Targo compiler argument {index} contains response or shell argfile `{argument}`; pass explicit compiler arguments"
            ));
        }
        if argument == "--" {
            return Err(format!(
                "verified Targo compiler argument {index} is a semantic `--` separator; canonical verifier policy must remain in rustc's option stream"
            ));
        }
    }
    for (name, _) in prefixed_compiler_options(&arguments, "-Z")? {
        if name == "valtree_node_limit" {
            return Err(
                "verified Targo compiler argv uses retired `-Zvaltree-node-limit`; verified compilations enforce rustc's fixed valtree resource limit"
                    .to_string(),
            );
        }
    }
    policy.validate_final(&arguments)
}

pub(crate) fn trust_verification_session(rustflags: &[String]) -> Result<Option<String>, String> {
    let mut session = None;
    for value in trust_z_option_values(rustflags) {
        let (name, candidate) = rustc_option_parts(value);
        if name != "trust_verify_session" {
            continue;
        }
        let candidate = candidate
            .ok_or_else(|| "-Ztrust-verify-session requires a non-empty value".to_string())?;
        if candidate.is_empty() || candidate.trim() != candidate {
            return Err("-Ztrust-verify-session requires a non-empty, trimmed value".to_string());
        }
        if let Some(previous) = session.as_deref() {
            if previous != candidate {
                return Err(format!(
                    "conflicting -Ztrust-verify-session values `{previous}` and `{candidate}`"
                ));
            }
            return Err("duplicate -Ztrust-verify-session options are not allowed".to_string());
        }
        session = Some(candidate.to_string());
    }
    Ok(session)
}

/// Trust: whether the resolved `-Ztrust-policy` lane claims proof authority
/// for this unit's evidence.
///
/// This is the one fact the admission layer needed and did not have: every
/// "evidence-grade" boundary in this file exists to protect a proof claim, and
/// a lane that makes no such claim forfeits the boundary instead of refusing
/// the build. `advisory` — what `targo trust … --allow-l0-gaps` and `--survey`
/// place on the graph-wide rustflags (targo-trust `TrustPolicySelection`) — is
/// the compiler's own non-fatal policy: every obligation is still verified and
/// reported, nothing fails closed. The absent default (`strict`), `certify`
/// and `memory-safe` all claim authority.
///
/// Read from the same rustflags the compiler receives, so Targo and trustc can
/// never disagree about the lane, and already tracked in the unit fingerprint
/// (`-Ztrust-policy` is host policy), so a lane change re-fingerprints the
/// unit like any policy change.
fn trust_policy_claims_proof_authority(
    unit_rustflags: &[String],
    extra_compiler_args: &[String],
) -> Result<bool, String> {
    let policy = resolve_per_unit_protocol_value(
        "trust-policy",
        trust_policy_option(unit_rustflags)?,
        trust_policy_option(extra_compiler_args)?,
    )?;
    Ok(policy.as_deref() != Some("advisory"))
}

fn trust_policy_option(rustflags: &[String]) -> Result<Option<String>, String> {
    let mut policy = None;
    for value in trust_z_option_values(rustflags) {
        let (name, candidate) = rustc_option_parts(value);
        if name != "trust_policy" {
            continue;
        }
        let candidate = candidate
            .filter(|candidate| !candidate.is_empty())
            .ok_or_else(|| "-Ztrust-policy requires a non-empty value".to_string())?;
        if let Some(previous) = policy.as_deref() {
            if previous != candidate {
                return Err(format!(
                    "conflicting -Ztrust-policy values `{previous}` and `{candidate}`"
                ));
            }
            return Err("duplicate -Ztrust-policy options are not allowed".to_string());
        }
        policy = Some(candidate.to_string());
    }
    Ok(policy)
}

const TRUST_TARGO_PREPARED_TEST_SESSION: &str = "TRUST_TARGO_PREPARED_TEST_SESSION";
const TRUST_TARGO_TEST_MONITOR_AUTHORITY_SESSION: &str =
    "TRUST_TARGO_TEST_MONITOR_AUTHORITY_SESSION";
const TRUST_TARGO_TEST_MONITOR_SESSION: &str = "TRUST_TARGO_TEST_MONITOR_SESSION";

/// Whether `unit` is a runtime unit of a selected package: the units that get
/// the certified-monitor session marker when the outer driver grants monitor
/// authority. `prepare_rustc` and `trust_unit_id` share this one decision.
fn trust_selected_runtime_unit(build_runner: &BuildRunner<'_, '_>, unit: &Unit) -> bool {
    trust_selected_runtime_unit_context(
        build_runner.bcx,
        unit,
        build_runner.is_primary_package(unit),
    )
}

fn trust_selected_runtime_unit_context(
    bcx: &BuildContext<'_, '_>,
    unit: &Unit,
    is_primary_package: bool,
) -> bool {
    trust_test_monitor_unit_selected(
        is_primary_package,
        unit.mode,
        unit.target.is_custom_build(),
        unit.target.proc_macro(),
        bcx.roots
            .iter()
            .any(|root| root.pkg.package_id() == unit.pkg.package_id() && root.kind == unit.kind),
    )
}

fn trust_test_monitor_unit_selected(
    is_primary_package: bool,
    mode: CompileMode,
    is_custom_build: bool,
    is_proc_macro: bool,
    matches_selected_root_kind: bool,
) -> bool {
    is_primary_package
        && matches!(mode, CompileMode::Build | CompileMode::Test)
        && !is_custom_build
        && (!is_proc_macro || mode == CompileMode::Test)
        && matches_selected_root_kind
}

/// Translate the outer driver's session authority into the compiler marker
/// only for runtime units of a canonically selected package.  The authority is
/// validated even for units that remain unmarked, so a stale or ambient value
/// can never be ignored on part of the graph.
fn resolve_certified_monitor_unit_session(
    verified_targo: bool,
    authority: Option<&OsStr>,
    proof_session: Option<&str>,
    selected_runtime_unit: bool,
) -> Result<Option<String>, String> {
    let Some(authority) = authority else {
        return Ok(None);
    };
    if !verified_targo {
        return Err(format!(
            "{TRUST_TARGO_TEST_MONITOR_AUTHORITY_SESSION} is reserved for branded verified Targo test sessions"
        ));
    }
    let authority = authority.to_str().ok_or_else(|| {
        format!("{TRUST_TARGO_TEST_MONITOR_AUTHORITY_SESSION} is not valid Unicode")
    })?;
    if authority.is_empty() || authority.trim() != authority {
        return Err(format!(
            "{TRUST_TARGO_TEST_MONITOR_AUTHORITY_SESSION} must be a non-empty trimmed session nonce"
        ));
    }
    let Some(proof_session) = proof_session else {
        return Err(format!(
            "{TRUST_TARGO_TEST_MONITOR_AUTHORITY_SESSION} requires -Ztrust-verify-session"
        ));
    };
    if authority != proof_session {
        return Err(format!(
            "{TRUST_TARGO_TEST_MONITOR_AUTHORITY_SESSION} does not match -Ztrust-verify-session"
        ));
    }
    Ok(selected_runtime_unit.then(|| authority.to_string()))
}

fn validate_certified_monitor_command_env(
    command: &ProcessBuilder,
    expected: Option<&str>,
) -> Result<(), String> {
    let actual = command.get_env(TRUST_TARGO_TEST_MONITOR_SESSION);
    match (actual.as_deref(), expected) {
        (None, None) => Ok(()),
        (Some(actual), Some(expected)) if actual == OsStr::new(expected) => Ok(()),
        (Some(_), None) => Err(format!(
            "late compiler environment injected reserved {TRUST_TARGO_TEST_MONITOR_SESSION} into an unselected Cargo unit"
        )),
        (None, Some(_)) => Err(format!(
            "selected Cargo unit lost its authenticated {TRUST_TARGO_TEST_MONITOR_SESSION} marker"
        )),
        (Some(_), Some(_)) => Err(format!(
            "late compiler environment changed authenticated {TRUST_TARGO_TEST_MONITOR_SESSION}"
        )),
    }
}

fn reject_certified_monitor_custom_target(
    monitor_selected: bool,
    kind: CompileKind,
) -> Result<(), String> {
    if !monitor_selected {
        return Ok(());
    }
    let CompileKind::Target(CompileTarget::Json { path, .. }) = kind else {
        return Ok(());
    };
    Err(format!(
        "evidence-grade certified-monitor tests reject custom target specification `{path}` because its linker, pre/post link arguments, objects, and link environment are not an audited execution TCB"
    ))
}

fn reject_certified_monitor_custom_build_unit(
    monitor_authority_present: bool,
    custom_build_unit: bool,
    unit_identity: &str,
) -> Result<(), String> {
    if !monitor_authority_present || !custom_build_unit {
        return Ok(());
    }
    Err(format!(
        "evidence-grade certified-monitor tests reject custom build unit {unit_identity}: arbitrary build-script processes and background side effects are not an authenticated compilation/execution TCB"
    ))
}

fn certified_monitor_sensitive_environment(name: &str) -> bool {
    let name = name.to_ascii_uppercase();
    name.starts_with("TRUST_")
        || name.starts_with("TRUSTD_")
        || name.starts_with("LD_")
        || name.starts_with("DYLD_")
        || name.starts_with("CCC_")
        || name.starts_with("CLANG_CONFIG_")
        || matches!(
            name.as_str(),
            "LIBPATH"
                | "SHLIB_PATH"
                | "LDR_PRELOAD"
                | "LIBRARY_PATH"
                | "COMPILER_PATH"
                | "GCC_EXEC_PREFIX"
                | "SDKROOT"
                | "DEVELOPER_DIR"
                | "TOOLCHAINS"
        )
        || crate::util::process_authority::is_compiler_flag_environment(&name)
}

#[cfg(test)]
fn seal_certified_monitor_compiler_environment(
    command: &mut ProcessBuilder,
    monitor_session: Option<&str>,
) -> Result<(), String> {
    // An enforced seal with no verified exec edge reinstalls no loader value.
    let seal =
        CertifiedMonitorSeal::capture_for_test(monitor_session.is_some(), false, Path::new("/"))
            .map_err(|error| format!("{error:#}"))?;
    seal_certified_monitor_graph_compiler_environment(command, &seal, monitor_session)
}

// Trust (D2): `seal` carries both the enforcement decision and the one loader
// value and validated memory endpoint to reinstall; see `trust_certified_monitor_seal`.
fn seal_certified_monitor_graph_compiler_environment(
    command: &mut ProcessBuilder,
    seal: &CertifiedMonitorSeal,
    selected_monitor_session: Option<&str>,
) -> Result<(), String> {
    if !seal.is_enforced() {
        return Ok(());
    }

    // `cargo::rustc-env` is appended after the static command is prepared.
    // Delete every current/future Trust control and every loader/linker search
    // channel at the final exec edge, then reinstall the captured admission
    // endpoint and immutable per-unit monitor nonce. Ambient or late values
    // never select the compiler's memory authority.
    #[allow(clippy::disallowed_methods)]
    let inherited = env::vars_os();
    let names = inherited
        .filter_map(|(name, _)| name.into_string().ok())
        .chain(command.get_envs().keys().cloned())
        .filter(|name| certified_monitor_sensitive_environment(name))
        .collect::<BTreeSet<_>>();
    for name in names {
        command.env_remove(&name);
    }
    // Trust (D2, 2026-09-28): then reinstall EXACTLY ONE loader value — the
    // platform search variable, set to the authenticated toolchain closure
    // plus `/usr/lib` (`CertifiedMonitorSeal::capture`), which
    // the verified exec edge requires and re-validates after this seal. Every
    // other channel stays deleted: preload/insert/audit, `DYLD_LIBRARY_PATH`,
    // framework paths, and any late overlay of this same variable, since the
    // value comes from the caller's capture, never from `command`.
    //
    // It is deliberately NARROWER than `Compilation::fill_env`'s value, which
    // also appends Cargo's caller-owned `target/<profile>/deps`. The monitor
    // lane refuses dynamic Rust linkage, and a proc macro is opened by its
    // absolute `--extern` path. Measured 2026-09-28 on the 4d9a20e3daf pack: a
    // proc-macro dylib this toolchain builds (the audited `trust-spec` one and
    // a local one alike) links only `/usr/lib/libSystem.B.dylib`, and trustc
    // loads it and expands it under exactly this value, with no `deps` entry.
    // (Verified lanes no longer pass Cargo's host `-C prefer-dynamic` to a
    // proc-macro unit — `cargo_prefers_dynamic_rust_linkage` — so an audited
    // provider such as `trust-spec` now compiles in the strict lane too and its
    // dylib is loaded under exactly this value.)
    if let Some(search) = seal.authenticated_loader_search() {
        command.env(paths::dylib_path_envvar(), search);
    }
    if let Some(socket) = seal.authenticated_memory_socket() {
        command.env(trust_certified_monitor_seal::MEMORY_SOCKET_ENV, socket);
    }
    if let Some(monitor_session) = selected_monitor_session {
        command.env(TRUST_TARGO_TEST_MONITOR_SESSION, monitor_session);
    }

    #[cfg(unix)]
    {
        // rustc's default linker and any subordinate linker tools are resolved
        // through PATH. Do not let a caller's PATH replace `cc`, `ld`, or a
        // helper after Cargo has authenticated argv. The OS tool directories
        // are part of the compiler/platform TCB; hosts without this baseline
        // fail at link time instead of falling back to ambient tools.
        command.env("PATH", "/usr/bin:/bin");
        command.env("CLANG_NO_DEFAULT_CONFIG", "1");
        Ok(())
    }
    #[cfg(not(unix))]
    {
        let _ = command;
        Err(
            "evidence-grade certified-monitor tests require an authenticated linker tool path; this platform is not yet supported"
                .to_string(),
        )
    }
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
struct CertifiedMonitorCompilerClosure {
    externs: Vec<String>,
    dependency_search_paths: Vec<String>,
    targets: Vec<String>,
    sysroots: Vec<String>,
    emits: Vec<String>,
    output_files: Vec<String>,
    output_directories: Vec<String>,
    extra_filenames: Vec<Option<String>>,
    incremental_directories: Vec<Option<String>>,
}

impl CertifiedMonitorCompilerClosure {
    fn capture(command: &ProcessBuilder) -> Result<Self, String> {
        Ok(Self {
            externs: compiler_external_crate_specs(command)?,
            dependency_search_paths: compiler_argument_values(command, "-L")?
                .into_iter()
                .filter(|value| value.starts_with("dependency="))
                .collect(),
            targets: compiler_argument_values(command, "--target")?,
            sysroots: compiler_argument_values(command, "--sysroot")?,
            emits: compiler_argument_values(command, "--emit")?,
            output_files: compiler_argument_values(command, "-o")?,
            output_directories: compiler_argument_values(command, "--out-dir")?,
            extra_filenames: compiler_codegen_option_values(command, "extra_filename")?,
            incremental_directories: compiler_codegen_option_values(command, "incremental")?,
        })
    }
}

fn compiler_codegen_option_values(
    command: &ProcessBuilder,
    option_name: &str,
) -> Result<Vec<Option<String>>, String> {
    let arguments = command
        .get_args()
        .enumerate()
        .map(|(index, argument)| {
            argument.to_str().ok_or_else(|| {
                format!("Cargo-generated compiler argument {index} is not valid Unicode")
            })
        })
        .collect::<Result<Vec<_>, _>>()?;
    Ok(codegen_compiler_options(&arguments)?
        .into_iter()
        .filter_map(|(name, value)| (name == option_name).then_some(value))
        .collect())
}

fn reject_certified_monitor_presnapshot_closure_controls<S: AsRef<str>>(
    monitor_selected: bool,
    arguments: &[S],
    source: &str,
) -> Result<(), String> {
    if !monitor_selected {
        return Ok(());
    }
    let arguments = arguments.iter().map(AsRef::as_ref).collect::<Vec<_>>();
    for flag in [
        "--emit",
        "--extern",
        "--out-dir",
        "--sysroot",
        "--target",
        "-L",
        "-o",
    ] {
        if !compiler_argument_values_from_slice(&arguments, flag)?.is_empty() {
            return Err(format!(
                "evidence-grade certified-monitor {source} cannot set compiler closure control {flag}"
            ));
        }
    }
    if let Some((name, _)) = codegen_compiler_options(&arguments)?
        .into_iter()
        .find(|(name, _)| matches!(name.as_str(), "extra_filename" | "incremental"))
    {
        return Err(format!(
            "evidence-grade certified-monitor {source} cannot set compiler closure control -C{name}"
        ));
    }
    Ok(())
}

fn compiler_argument_values(command: &ProcessBuilder, flag: &str) -> Result<Vec<String>, String> {
    let arguments = command
        .get_args()
        .enumerate()
        .map(|(index, argument)| {
            argument.to_str().ok_or_else(|| {
                format!("Cargo-generated compiler argument {index} is not valid Unicode")
            })
        })
        .collect::<Result<Vec<_>, _>>()?;
    compiler_argument_values_from_slice(&arguments, flag)
}

fn compiler_argument_values_from_slice<S: AsRef<str>>(
    arguments: &[S],
    flag: &str,
) -> Result<Vec<String>, String> {
    let mut values = Vec::new();
    let mut index = 0;
    while index < arguments.len() {
        let argument = arguments[index].as_ref();
        let value = if argument == flag {
            let value = arguments.get(index + 1).ok_or_else(|| {
                format!("Cargo-generated compiler arguments end with incomplete {flag}")
            })?;
            index += 1;
            Some(value.as_ref())
        } else if flag.starts_with("--") {
            argument
                .strip_prefix(flag)
                .and_then(|value| value.strip_prefix('='))
        } else {
            argument
                .strip_prefix(flag)
                .filter(|value| !value.is_empty())
        };
        if let Some(value) = value {
            values.push(value.to_string());
        }
        index += 1;
    }
    Ok(values)
}

#[cfg(test)]
fn reject_certified_monitor_dynamic_rust_linkage(
    command: &ProcessBuilder,
    monitor_selected: bool,
    audited_proc_macro_externs: &HashSet<PathBuf>,
    cargo_compiler_closure: &CertifiedMonitorCompilerClosure,
) -> Result<(), String> {
    reject_certified_monitor_dynamic_rust_linkage_with_audited_proc_macro(
        command,
        monitor_selected,
        audited_proc_macro_externs,
        cargo_compiler_closure,
        false,
    )
}

fn reject_certified_monitor_dynamic_rust_linkage_with_audited_proc_macro(
    command: &ProcessBuilder,
    monitor_authority_present: bool,
    audited_proc_macro_externs: &HashSet<PathBuf>,
    cargo_compiler_closure: &CertifiedMonitorCompilerClosure,
    audited_proc_macro_unit: bool,
) -> Result<(), String> {
    if !monitor_authority_present {
        return Ok(());
    }
    let arguments = command
        .get_args()
        .enumerate()
        .map(|(index, argument)| {
            argument.to_str().ok_or_else(|| {
                format!(
                    "certified-monitor compiler argument {index} is not valid Unicode and cannot be checked for dynamic linkage"
                )
            })
        })
        .collect::<Result<Vec<_>, _>>()?;
    let codegen_options = codegen_compiler_options(&arguments)?;
    if let Some((name, _)) = codegen_options.iter().find(|(name, _)| {
        matches!(
            name.as_str(),
            "default_linker_libraries"
                | "instrument_coverage"
                | "link_arg"
                | "link_args"
                | "link_self_contained"
                | "linker"
                | "linker_features"
                | "linker_flavor"
                | "linker_plugin_lto"
                | "no_prepopulate_passes"
                | "passes"
                | "prefer_dynamic"
                | "profile_generate"
                | "profile_use"
                | "rpath"
        )
    }) {
        return Err(format!(
            "evidence-grade certified-monitor tests do not yet authenticate caller-selected link/runtime or custom LLVM-pass closure; -C{name} is unavailable"
        ));
    }
    if let Some((_, Some(features))) = codegen_options.iter().find(|(name, value)| {
        name == "target_feature"
            && value.as_deref().is_some_and(|features| {
                features
                    .split(',')
                    .any(|feature| matches!(feature.trim(), "+crt-static" | "-crt-static"))
            })
    }) {
        return Err(format!(
            "evidence-grade certified-monitor tests pin the platform runtime closure; -Ctarget-feature={features} cannot change crt-static"
        ));
    }
    if let Some((name, _)) =
        prefixed_compiler_options(&arguments, "-Z")?
            .iter()
            .find(|(name, _)| {
                matches!(
                    name.as_str(),
                    "external_clangrt"
                        | "instrument_mcount"
                        | "instrument_xray"
                        | "mir_enable_passes"
                        | "no_leak_check"
                        | "no_profiler_runtime"
                        | "offload"
                        | "pre_link_arg"
                        | "pre_link_args"
                        | "profiler_runtime"
                        | "sanitizer"
                        | "sanitizer_recover"
                        | "unleash_the_miri_inside_of_you"
                        | "unsound_mir_opts"
                )
            })
    {
        return Err(format!(
            "evidence-grade certified-monitor tests do not yet authenticate caller-selected link/runtime closure; -Z{name} is unavailable"
        ));
    }
    let mut observed_externs = Vec::new();
    let mut index = 0;
    while index < arguments.len() {
        let argument = arguments[index];
        let value_after = |flag: &str| {
            if argument == flag {
                arguments.get(index + 1).copied()
            } else if flag.starts_with("--") {
                argument
                    .strip_prefix(flag)
                    .and_then(|value| value.strip_prefix('='))
            } else {
                argument
                    .strip_prefix(flag)
                    .filter(|value| !value.is_empty())
            }
        };
        if let Some(crate_types) = value_after("--crate-type") {
            if crate_types.split(',').any(|kind| {
                matches!(kind, "dylib" | "cdylib")
                    || (kind == "proc-macro" && !audited_proc_macro_unit)
            }) {
                return Err(format!(
                    "evidence-grade certified-monitor tests do not yet authenticate dynamic crate type `{crate_types}`"
                ));
            }
        }
        if let Some(extern_spec) = value_after("--extern") {
            observed_externs.push(extern_spec.to_string());
            if extern_spec == "proc_macro" {
                index += if argument == "--extern" { 2 } else { 1 };
                continue;
            }
            let Some((_, path)) = extern_spec.split_once('=') else {
                return Err(format!(
                    "evidence-grade certified-monitor tests require every --extern to be an exact Cargo-graph artifact path, not `{extern_spec}`"
                ));
            };
            let path = Path::new(path);
            let extension = path
                .extension()
                .and_then(OsStr::to_str)
                .map(str::to_ascii_lowercase);
            if !audited_proc_macro_externs.contains(path)
                && !matches!(extension.as_deref(), Some("rlib" | "rmeta"))
            {
                return Err(format!(
                    "evidence-grade certified-monitor tests allow only Cargo-graph rlib/rmeta artifacts or exact audited proc macros, not --extern artifact `{}`",
                    path.display()
                ));
            }
        }
        if argument == "-l" || (argument.starts_with("-l") && argument.len() > 2) {
            return Err(
                "evidence-grade certified-monitor tests do not yet authenticate native -l libraries"
                    .to_string(),
            );
        }
        if let Some(search) = value_after("-L") {
            if !search.starts_with("dependency=") {
                return Err(format!(
                    "evidence-grade certified-monitor tests allow only Cargo's static dependency search path, not -L{search}"
                ));
            }
        }
        index += if matches!(argument, "--crate-type" | "--extern" | "-L" | "-l") {
            2
        } else {
            1
        };
    }
    if observed_externs != cargo_compiler_closure.externs {
        return Err(format!(
            "evidence-grade certified-monitor compiler --extern inventory changed after Cargo graph resolution (expected {:?}, observed {observed_externs:?})",
            cargo_compiler_closure.externs,
        ));
    }
    let observed = CertifiedMonitorCompilerClosure::capture(command)?;
    for (surface, expected, actual) in [
        (
            "-Ldependency",
            &cargo_compiler_closure.dependency_search_paths,
            &observed.dependency_search_paths,
        ),
        (
            "--target",
            &cargo_compiler_closure.targets,
            &observed.targets,
        ),
        (
            "--sysroot",
            &cargo_compiler_closure.sysroots,
            &observed.sysroots,
        ),
        ("--emit", &cargo_compiler_closure.emits, &observed.emits),
        (
            "-o",
            &cargo_compiler_closure.output_files,
            &observed.output_files,
        ),
        (
            "--out-dir",
            &cargo_compiler_closure.output_directories,
            &observed.output_directories,
        ),
    ] {
        if actual != expected {
            return Err(format!(
                "evidence-grade certified-monitor compiler {surface} inventory changed after Cargo unit resolution (expected {expected:?}, observed {actual:?})"
            ));
        }
    }
    for (surface, expected, actual) in [
        (
            "-Cextra-filename",
            &cargo_compiler_closure.extra_filenames,
            &observed.extra_filenames,
        ),
        (
            "-Cincremental",
            &cargo_compiler_closure.incremental_directories,
            &observed.incremental_directories,
        ),
    ] {
        if actual != expected {
            return Err(format!(
                "evidence-grade certified-monitor compiler {surface} inventory changed after Cargo unit resolution (expected {expected:?}, observed {actual:?})"
            ));
        }
    }
    Ok(())
}

fn compiler_external_crate_specs(command: &ProcessBuilder) -> Result<Vec<String>, String> {
    let arguments = command.get_args().collect::<Vec<_>>();
    let mut externs = Vec::new();
    let mut index = 0;
    while index < arguments.len() {
        let argument = &arguments[index];
        if *argument == OsStr::new("--extern") {
            let value = arguments.get(index + 1).ok_or_else(|| {
                "Cargo-generated compiler arguments end with incomplete --extern".to_string()
            })?;
            let value = value.to_str().ok_or_else(|| {
                "Cargo-generated --extern is not valid Unicode and cannot be authenticated"
                    .to_string()
            })?;
            externs.push(value.to_string());
            index += 2;
            continue;
        }
        if let Some(value) = argument
            .to_str()
            .and_then(|argument| argument.strip_prefix("--extern="))
        {
            externs.push(value.to_string());
        }
        index += 1;
    }
    Ok(externs)
}

fn reject_certified_monitor_dynamic_unit_dependencies(
    monitor_selected: bool,
    dynamic_dependencies: impl IntoIterator<Item = String>,
) -> Result<(), String> {
    if !monitor_selected {
        return Ok(());
    }
    let mut dynamic_dependencies = dynamic_dependencies.into_iter().collect::<Vec<_>>();
    dynamic_dependencies.sort();
    dynamic_dependencies.dedup();
    if dynamic_dependencies.is_empty() {
        return Ok(());
    }
    Err(format!(
        "evidence-grade certified-monitor tests do not yet authenticate dynamic Rust dependency units [{}]",
        dynamic_dependencies.join(", ")
    ))
}

/// Trust: whether Cargo's own argv asks rustc for `-C prefer-dynamic`.
///
/// Upstream Cargo passes the flag to every host unit that is not a build
/// script, which in practice means every proc-macro unit. That is a holdover
/// from compiler plugins, which had to share rustc's `libstd`.
///
/// For the `proc-macro` crate type the flag changes no linkage.
/// `rustc_metadata::dependency_format::calculate_type` pins
/// `CrateType::ProcMacro` to `Linkage::Static`. Measured 2026-09-28 on
/// aarch64-apple-darwin, building the audited `trust-spec` both ways under the
/// same output name: the same size, load commands, imports and symbol names.
/// Every differing byte (the count varies with the setup; two independent
/// measurements saw 96 and 551) lies in the Mach-O header (the LC_UUID and, in
/// one run, one other byte), in `__DATA`, which holds the `.rustc` metadata
/// that embeds the crate hash (the option is `[TRACKED]`), or in the code
/// signature.
///
/// For the same target in `Test` mode the flag is load-bearing. The unit is an
/// executable, and the flag links it against `@rpath/libstd-*.dylib` with no
/// LC_RPATH. It then runs only under an ambient `DYLD_*` search path, which the
/// certified-monitor test-execution edge strips.
///
/// Only the certified-monitor lane (`targo trust test`) requires a static Rust
/// closure, through two checks: Targo's argv check
/// (`reject_certified_monitor_dynamic_rust_linkage_with_audited_proc_macro`,
/// every graph unit while the seal is enforced, i.e. the strict lane) and
/// rustc's `-Ztrust-targo-test-monitor` check (every monitor-selected unit in
/// either lane, including a proc-macro crate's own lib test). Both refused the
/// flag Cargo itself added, so no proc-macro unit, not even the audited
/// `trust-spec` provider, could pass that lane.
///
/// The carve-out keys on `verified_targo_protocol_active()`, which is also
/// true for `targo trust check` and `targo trust build`, so a proc-macro
/// unit's argv loses the flag there too. Nothing in those lanes needs it, and
/// the change is harmless there (measured 2026-09-28): a strict
/// `targo trust check` of a crate using the audited `trust-spec` gave the same
/// verdict and counts with and without the flag, and the dylib differs only in
/// the bytes listed above. The unverified lane keeps upstream's argv byte for
/// byte (measured with `-vv`). A caller-supplied `-Cprefer-dynamic` is not
/// affected by this and is still refused by both checks.
fn cargo_prefers_dynamic_rust_linkage(
    verified_targo: bool,
    for_host: bool,
    custom_build: bool,
    proc_macro: bool,
    contains_dylib: bool,
    primary_package: bool,
) -> bool {
    let host_unit = for_host && !custom_build && !(verified_targo && proc_macro);
    host_unit || (contains_dylib && !primary_package)
}

/// Prepared execution consumes an already-authorized native plan. It must
/// never enter compilation, even if every queued unit would have been Fresh.
fn reject_compilation_during_prepared_execution(marker: Option<&OsStr>) -> Result<(), String> {
    if marker.is_some() {
        return Err("prepared test execution cannot enter the compiler".into());
    }
    Ok(())
}

fn trust_proof_artifact_root(rustflags: &[String]) -> Result<Option<String>, String> {
    let mut root = None;
    for value in trust_z_option_values(rustflags) {
        let (name, candidate) = rustc_option_parts(value);
        if name != "trust_proof_artifact_root" {
            continue;
        }
        let candidate = candidate.ok_or_else(|| {
            "-Ztrust-proof-artifact-root requires a non-empty absolute path".to_string()
        })?;
        if candidate.is_empty()
            || candidate.trim() != candidate
            || !Path::new(candidate).is_absolute()
        {
            return Err(
                "-Ztrust-proof-artifact-root requires one non-empty, trimmed absolute path"
                    .to_string(),
            );
        }
        if root.replace(candidate.to_string()).is_some() {
            return Err(
                "duplicate -Ztrust-proof-artifact-root options are not allowed".to_string(),
            );
        }
    }
    Ok(root)
}

fn resolve_per_unit_protocol_value(
    option: &str,
    unit: Option<String>,
    extra: Option<String>,
) -> Result<Option<String>, String> {
    match (unit.as_deref(), extra.as_deref()) {
        (Some(unit), Some(extra)) if unit != extra => Err(format!(
            "conflicting per-unit -Z{option} values `{unit}` and `{extra}`"
        )),
        (Some(_), Some(_)) => Err(format!(
            "duplicate per-unit -Z{option} options are not allowed"
        )),
        (Some(unit), None) => Ok(Some(unit.to_string())),
        (None, Some(extra)) => Ok(Some(extra.to_string())),
        (None, None) => Ok(None),
    }
}

// Trust: optional observational output consumes only the existing authenticated
// session/root carrier, never a parallel host-policy or environment flag.
fn verifier_input_export_request(
    unit: &[String],
    extra: &[String],
    session: &str,
) -> CargoResult<Option<crate::util::verifier_input_export::ExportRequest>> {
    let Some(root) = resolved_trust_proof_artifact_root(unit, extra).map_err(anyhow::Error::msg)?
    else {
        return Ok(None);
    };
    Ok(crate::util::verifier_input_export::request(
        Path::new(&root),
        session,
    )?)
}

// Trust: export consumes exactly the same root resolution contract as proof sessions.
fn resolved_trust_proof_artifact_root(
    unit: &[String],
    extra: &[String],
) -> Result<Option<String>, String> {
    resolve_per_unit_protocol_value(
        "trust-proof-artifact-root",
        trust_proof_artifact_root(unit)?,
        trust_proof_artifact_root(extra)?,
    )
}

// Trust: a positive assertion requires the graph's existing verification scope;
// it cannot activate a unit. Keep the original token in Unit rustflags so graph
// sharing and every cache/identity path retain the requirement. In particular,
// final CompileKind::Host does not identify a flag's original config source.
fn required_trust_verification_assertion(flags: &[String]) -> Result<bool, String> {
    let mut required = false;
    for (name, value) in prefixed_compiler_options(flags, "-Z")? {
        if name == "no_trust_verify" {
            return Err(
                "-Zno-trust-verify is reserved for Targo's resolved compilation-unit scope"
                    .to_string(),
            );
        }
        if name != "trust_verify" {
            continue;
        }
        if required {
            return Err("duplicate -Ztrust-verify assertions are not allowed".to_string());
        }
        if !matches!(value.as_deref(), Some("on" | "yes" | "true" | "y")) {
            return Err(
                "-Ztrust-verify is reserved for Targo's resolved compilation-unit scope; resolved unit flags may only assert an explicit positive value such as `=on`"
                    .to_string(),
            );
        }
        required = true;
    }
    Ok(required)
}

// Trust: this projection is for real rustc argv only, after graph admission.
// Do not use it for Unit construction, semantic identities or fingerprints.
fn compiler_flags_without_verification_assertion(flags: &[String]) -> Result<Vec<String>, String> {
    if !required_trust_verification_assertion(flags)? {
        return Ok(flags.to_vec());
    }
    let mut compiler_flags = Vec::with_capacity(flags.len());
    let mut index = 0;
    while index < flags.len() {
        let (option, consumed) = if flags[index] == "-Z" {
            (flags.get(index + 1).map(String::as_str), 2)
        } else {
            (flags[index].strip_prefix("-Z"), 1)
        };
        if option.is_some_and(|option| rustc_option_parts(option).0 == "trust_verify") {
            index += consumed;
            continue;
        }
        compiler_flags.extend_from_slice(&flags[index..index + consumed]);
        index += consumed;
    }
    Ok(compiler_flags)
}

fn resolve_trust_verification_protocol(
    unit_rustflags: &[String],
    extra_compiler_args: &[String],
) -> Result<Option<String>, String> {
    for flags in [unit_rustflags, extra_compiler_args] {
        if let Some(reserved) = caller_supplied_trust_unit_metadata(flags) {
            return Err(format!(
                "-Z{reserved} is reserved for Targo's resolved compilation-unit metadata"
            ));
        }
        if let Some(external) = caller_supplied_external_crate(flags) {
            return Err(format!(
                "caller-supplied --extern={external} is forbidden in verified Targo compiler flags: only Cargo graph dependencies can be classified against the enforced no-proc-macro TCB boundary"
            ));
        }
    }

    let session = resolve_per_unit_protocol_value(
        "trust-verify-session",
        trust_verification_session(unit_rustflags)?,
        trust_verification_session(extra_compiler_args)?,
    )?;
    // Trust: only the resolved unit vector can carry an assertion. Parallel
    // compiler/profile sources remain forbidden, and no assertion supplies a
    // session. A positive token is removed from actual argv after graph checks.
    let required_verification = required_trust_verification_assertion(unit_rustflags)?;
    if required_verification && session.is_none() {
        return Err(
            "-Ztrust-verify=on assertion requires an authenticated proof session".to_string(),
        );
    }
    if session.is_some() {
        if trust_bool_option(extra_compiler_args, "trust-verify")?.is_some() {
            return Err(
                "extra compiler arguments cannot set -Ztrust-verify; activation is reserved for Targo's resolved compilation-unit scope"
                    .to_string(),
            );
        }
        for flags in [unit_rustflags, extra_compiler_args] {
            // The compiler still honours the retired `-Zno-trust-verify` alias
            // (a one-seed-generation bridge: bare/`=on` means verification OFF)
            // and rewrites it to `trust-verify` before anything downstream can
            // tell the two apart. A caller-supplied alias is therefore the same
            // off-switch under another name and is refused for the same reason;
            // `per_unit_sessions_are_unique_and_caller_metadata_stays_reserved`
            // pins it.
            if trust_bool_option(flags, "no_trust-verify")?.is_some() {
                return Err(
                    "-Zno-trust-verify (the retired spelling of -Ztrust-verify=off) is reserved \
                     for Targo's resolved compilation-unit scope"
                        .to_string(),
                );
            }
        }
    }

    let proof_artifact_root =
        resolved_trust_proof_artifact_root(unit_rustflags, extra_compiler_args)?;
    match (session.as_ref(), proof_artifact_root.as_ref()) {
        (Some(_), None) => {
            return Err(
                "verified Targo policy is missing -Ztrust-proof-artifact-root=<absolute-path>"
                    .to_string(),
            );
        }
        (None, Some(_)) => {
            return Err(
                "-Ztrust-proof-artifact-root requires -Ztrust-verify-session=<nonce>".to_string(),
            );
        }
        _ => {}
    }

    Ok(session)
}

fn verified_targo_proof_session(
    unit_rustflags: &[String],
    extra_compiler_args: &[String],
) -> Result<String, String> {
    resolve_trust_verification_protocol(unit_rustflags, extra_compiler_args)?.ok_or_else(|| {
        "TRUST_TARGO_VERIFY requires one -Ztrust-verify-session=<nonce> and one \
         -Ztrust-proof-artifact-root=<absolute-path>"
            .to_string()
    })
}

fn caller_supplied_external_crate<S: AsRef<str>>(flags: &[S]) -> Option<String> {
    flags.iter().enumerate().find_map(|(index, flag)| {
        let flag = flag.as_ref();
        (flag == "--extern")
            .then(|| {
                flags
                    .get(index + 1)
                    .map(|flag| flag.as_ref().to_owned())
                    .unwrap_or_else(|| "<missing>".to_string())
            })
            .or_else(|| flag.strip_prefix("--extern=").map(str::to_string))
    })
}

pub(super) fn verified_targo_protocol_active() -> bool {
    crate::is_targo_invocation() && crate::trust_verified_targo()
}

fn trust_bool_option(flags: &[String], option_name: &str) -> Result<Option<bool>, String> {
    let mut parsed = None;
    let expected_name = rustc_option_parts(option_name).0;
    for option in trust_z_option_values(flags) {
        let (name, value) = rustc_option_parts(option);
        if name != expected_name {
            continue;
        }
        let value = match value {
            None | Some("y" | "yes" | "on" | "true") => true,
            Some("n" | "no" | "off" | "false") => false,
            Some(value) => {
                return Err(format!(
                    "-Z{option_name} has invalid boolean value `{value}`"
                ));
            }
        };
        if parsed.replace(value).is_some() {
            return Err(format!("duplicate -Z{option_name} options are not allowed"));
        }
    }
    Ok(parsed)
}

fn resolve_trust_include_dependencies(
    unit_rustflags: &[String],
    extra_compiler_args: &[String],
) -> Result<bool, String> {
    let unit = trust_bool_option(unit_rustflags, "trust-verify-include-dependencies")?;
    let extra = trust_bool_option(extra_compiler_args, "trust-verify-include-dependencies")?;
    match (unit, extra) {
        (Some(unit), Some(extra)) if unit != extra => Err(format!(
            "conflicting -Ztrust-verify-include-dependencies values `{unit}` and `{extra}`"
        )),
        (Some(_), Some(_)) => {
            Err("duplicate -Ztrust-verify-include-dependencies options are not allowed".to_string())
        }
        (Some(value), None) | (None, Some(value)) => Ok(value),
        (None, None) => Ok(false),
    }
}

fn trust_unit_role(is_custom_build: bool, is_primary: bool) -> &'static str {
    if is_custom_build {
        // Trust: build.rs compilation keeps its reporting role even when it
        // is included as a dependency proof subject. It is not a primary root.
        "build-script"
    } else if is_primary {
        "primary"
    } else {
        "dependency"
    }
}

/// Root authority is unit identity, not package identity. Keeping this helper
/// generic makes the equality rule independently testable without constructing
/// Cargo's large interned `Unit` graph in a unit test.
fn is_resolved_root_unit<T: PartialEq>(unit: &T, roots: &[T]) -> bool {
    roots.contains(unit)
}

/// Whether this exact non-root unit is executable code selected by Cargo's
/// test graph. Integration tests and doctests do not link the `--test` library
/// root: Cargo builds a second `CompileMode::Build` library with `cfg(test)`
/// disabled. Integration tests and benches also build same-package binary
/// targets for `CARGO_BIN_EXE_*`. Every such distinct execution unit must be
/// statically verified in its own right and carry certified runtime monitors.
fn trust_unit_test_execution_subject(build_runner: &BuildRunner<'_, '_>, unit: &Unit) -> bool {
    trust_unit_test_execution_subject_context(build_runner.bcx, unit)
}

fn trust_unit_test_execution_subject_context(bcx: &BuildContext<'_, '_>, unit: &Unit) -> bool {
    // Package selection and execution reachability are separate graph facts.
    // In a workspace, package A's integration test can directly execute
    // selected package B's ordinary Build-mode library. Requiring the same root
    // to prove both facts would silently exclude B; requiring only reachability
    // would incorrectly promote unselected external dependencies.
    let unit_package_is_selected = bcx
        .roots
        .iter()
        .any(|root| root.pkg.package_id() == unit.pkg.package_id());
    let linked_from_executing_test_root = bcx.roots.iter().any(|root| {
        root.mode.is_any_test() && bcx.unit_graph[root].iter().any(|dep| dep.unit == *unit)
    });
    trust_test_execution_subject_enabled(
        matches!(
            bcx.build_config.intent,
            UserIntent::Test | UserIntent::Doctest | UserIntent::Bench
        ),
        unit.mode == CompileMode::Build,
        unit.target.is_linkable() || unit.target.is_bin(),
        unit.target.proc_macro(),
        unit_package_is_selected,
        linked_from_executing_test_root,
    )
}

/// Pure policy seam for the Cargo graph-derived execution-subject decision.
fn trust_test_execution_subject_enabled(
    is_executing_test_intent: bool,
    is_build_mode: bool,
    is_library_or_binary_execution_target: bool,
    is_proc_macro: bool,
    unit_package_is_selected: bool,
    linked_from_executing_test_root: bool,
) -> bool {
    is_executing_test_intent
        && is_build_mode
        && is_library_or_binary_execution_target
        && !is_proc_macro
        && unit_package_is_selected
        && linked_from_executing_test_root
}

/// Whether Cargo must explicitly authorize certified monitor codegen for this
/// exact unit. A distinct Build-mode library/binary execution subject needs
/// the option because it is not compiled as a native test. So does an exact
/// selected `CompileMode::Test` root with `harness = false`: Cargo executes
/// that root, but deliberately passes only `--cfg test`, not rustc's `--test`
/// switch that otherwise enables monitors inside the compiler.
///
/// This decision remains Cargo-owned and graph-derived. It does not widen
/// verification scope or proof roles, and the union is materialized as one
/// boolean so a unit satisfying both predicates receives exactly one option.
fn trust_unit_certified_monitor_subject(
    build_runner: &BuildRunner<'_, '_>,
    unit: &Unit,
    is_test_execution_subject: bool,
) -> bool {
    trust_certified_monitor_subject_enabled(
        is_test_execution_subject,
        matches!(
            build_runner.bcx.build_config.intent,
            UserIntent::Test | UserIntent::Bench
        ),
        is_resolved_root_unit(unit, &build_runner.bcx.roots),
        unit.mode == CompileMode::Test,
        unit.target.harness(),
    )
}

/// Pure policy seam for Cargo's certified-monitor codegen decision.
fn trust_certified_monitor_subject_enabled(
    is_test_execution_subject: bool,
    is_executing_test_or_bench_intent: bool,
    is_resolved_root: bool,
    is_test_mode: bool,
    uses_native_test_harness: bool,
) -> bool {
    is_test_execution_subject
        || (is_executing_test_or_bench_intent
            && is_resolved_root
            && is_test_mode
            && !uses_native_test_harness)
}

fn trust_compile_mode_name(mode: CompileMode) -> &'static str {
    match mode {
        CompileMode::Test => "test",
        CompileMode::Build => "build",
        CompileMode::Check { test: true } => "check-test",
        CompileMode::Check { test: false } => "check",
        CompileMode::Doc => "doc",
        CompileMode::Doctest => "doctest",
        CompileMode::Docscrape => "docscrape",
        CompileMode::RunCustomBuild => "run-custom-build",
    }
}

fn trust_unit_frontend(mode: CompileMode) -> &'static str {
    match mode {
        CompileMode::Build | CompileMode::Test | CompileMode::Check { .. } => "rustc",
        CompileMode::Doc | CompileMode::Doctest | CompileMode::Docscrape => "rustdoc",
        CompileMode::RunCustomBuild => "cargo-control",
    }
}

fn canonical_trust_string_set(
    label: &str,
    values: impl IntoIterator<Item = String>,
) -> Result<Vec<String>, String> {
    let mut values = values.into_iter().collect::<Vec<_>>();
    values.sort();
    if let Some(duplicate) = values.windows(2).find(|pair| pair[0] == pair[1]) {
        return Err(format!(
            "resolved Cargo Unit has duplicate {label} value {:?}",
            duplicate[0]
        ));
    }
    Ok(values)
}

fn trust_profile_lto_name(lto: ProfileLto) -> String {
    match lto {
        ProfileLto::Off => "off".to_string(),
        ProfileLto::Bool(value) => value.to_string(),
        ProfileLto::Named(value) => value.to_string(),
    }
}

fn trust_effective_lto_name(lto: lto::Lto) -> String {
    match lto {
        lto::Lto::Run(None) => "fat".to_string(),
        lto::Lto::Run(Some(value)) => format!("run:{value}"),
        lto::Lto::Off => "off".to_string(),
        lto::Lto::OnlyBitcode => "only-bitcode".to_string(),
        lto::Lto::ObjectAndBitcode => "object-and-bitcode".to_string(),
        lto::Lto::OnlyObject => "only-object".to_string(),
    }
}

fn is_trust_semantic_transport_z(name: &str) -> bool {
    matches!(
        name,
        "trust_verify_session" | "trust_proof_artifact_root" | "trust_verify_include_dependencies"
    )
}

/// Remove only invocation nonces/output locations from the semantic argument
/// projection. All options that can affect compilation or verification remain
/// byte-for-byte and in order. This keeps saved reports comparable across
/// invocations without erasing policy such as the backend or verify level.
fn trust_semantic_compiler_args(args: &[String]) -> Result<Vec<String>, String> {
    let mut semantic = Vec::with_capacity(args.len());
    let mut index = 0;
    while index < args.len() {
        let argument = &args[index];
        if argument == "-Z" {
            let value = args.get(index + 1).ok_or_else(|| {
                "resolved Cargo Unit rustflags end with incomplete `-Z`".to_string()
            })?;
            let (name, _) = rustc_option_parts(value);
            if !is_trust_semantic_transport_z(&name) {
                semantic.push(argument.clone());
                semantic.push(value.clone());
            }
            index += 2;
            continue;
        }
        if let Some(value) = argument
            .strip_prefix("-Z")
            .filter(|value| !value.is_empty())
        {
            let (name, _) = rustc_option_parts(value);
            if !is_trust_semantic_transport_z(&name) {
                semantic.push(argument.clone());
            }
        } else {
            semantic.push(argument.clone());
        }
        index += 1;
    }
    Ok(semantic)
}

fn trust_effective_codegen_backend(
    unit: &Unit,
    extra_compiler_args: &[String],
) -> Result<String, String> {
    if unit.mode == CompileMode::RunCustomBuild {
        return Ok("not-applicable".to_string());
    }

    let mut candidates = Vec::new();
    if let Some(value) = unit.profile.codegen_backend {
        candidates.push(("profile codegen-backend", value.to_string()));
    }
    fn append_candidates<S: AsRef<str>>(
        candidates: &mut Vec<(&'static str, String)>,
        source: &'static str,
        args: &[S],
    ) -> Result<(), String> {
        for (name, value) in prefixed_compiler_options(args, "-Z")? {
            if name != "codegen_backend" {
                continue;
            }
            let value = value
                .filter(|value| !value.is_empty())
                .ok_or_else(|| format!("{source} contains `-Zcodegen-backend` without a value"))?;
            candidates.push((source, canonical_codegen_backend_value(&value).to_string()));
        }
        Ok(())
    }
    append_candidates(
        &mut candidates,
        "profile rustflags",
        &unit.profile.rustflags,
    )?;
    append_candidates(
        &mut candidates,
        "extra compiler arguments",
        extra_compiler_args,
    )?;
    append_candidates(&mut candidates, "unit rustflags", &unit.rustflags)?;
    if candidates.len() > 1 {
        return Err(format!(
            "resolved Cargo Unit has duplicate codegen-backend authorities: {}",
            candidates
                .iter()
                .map(|(source, value)| format!("{source}={value}"))
                .collect::<Vec<_>>()
                .join(", ")
        ));
    }
    Ok(candidates
        .pop()
        .map(|(_, value)| value)
        .unwrap_or_else(|| "rustc-default".to_string()))
}

fn trust_unit_semantics(
    build_runner: &BuildRunner<'_, '_>,
    unit: &Unit,
) -> CargoResult<machine_message::TrustUnitSemantics> {
    let features = canonical_trust_string_set(
        "enabled feature",
        unit.features.iter().map(ToString::to_string),
    )
    .map_err(anyhow::Error::msg)?;
    let target_cfg = canonical_trust_string_set(
        "target cfg",
        build_runner
            .bcx
            .target_data
            .cfg(unit.kind)
            .iter()
            .map(ToString::to_string),
    )
    .map_err(anyhow::Error::msg)?;
    let target_crate_types = canonical_trust_string_set(
        "target crate type",
        unit.target
            .rustc_crate_types()
            .iter()
            .map(|crate_type| crate_type.as_str().to_string()),
    )
    .map_err(anyhow::Error::msg)?;
    let extra_compiler_args = build_runner
        .bcx
        .extra_args_for(unit)
        .cloned()
        .unwrap_or_default();
    let effective_codegen_backend =
        trust_effective_codegen_backend(unit, &extra_compiler_args).map_err(anyhow::Error::msg)?;
    let profile = &unit.profile;
    let effective_lto = build_runner.lto.get(unit).copied().ok_or_else(|| {
        anyhow::format_err!(
            "resolved Cargo Unit {} target {:?} has no graph-resolved LTO semantics",
            unit.pkg.package_id(),
            unit.target.name()
        )
    })?;
    let manifest_lint_rustflags = if unit.mode == CompileMode::RunCustomBuild
        || matches!(
            compute_cap_lints(build_runner.bcx, unit),
            Some(CapLints::Allow)
        ) {
        Vec::new()
    } else {
        unit.pkg.manifest().lint_rustflags().to_vec()
    };
    let rustc = build_runner.bcx.rustc();
    let semantics = machine_message::TrustUnitSemantics {
        schema: machine_message::TRUST_UNIT_SEMANTICS_SCHEMA_V1,
        features,
        target_cfg,
        cfg_test: unit.mode.is_any_test(),
        target_edition: unit.target.edition().to_string(),
        target_crate_types,
        target_harness: unit.target.harness(),
        target_proc_macro: unit.target.proc_macro(),
        profile: machine_message::TrustUnitProfileSemantics {
            opt_level: profile.opt_level.to_string(),
            requested_lto: trust_profile_lto_name(profile.lto),
            effective_lto: trust_effective_lto_name(effective_lto),
            codegen_backend: profile.codegen_backend.map(|value| value.to_string()),
            codegen_units: profile.codegen_units,
            debuginfo: profile.debuginfo.into_inner().to_string(),
            split_debuginfo: profile.split_debuginfo.map(|value| value.to_string()),
            debug_assertions: profile.debug_assertions,
            overflow_checks: profile.overflow_checks,
            rpath: profile.rpath,
            incremental: profile.incremental,
            panic: profile.panic.to_string(),
            strip: profile.strip.into_inner().to_string(),
            rustflags: profile.rustflags.iter().map(ToString::to_string).collect(),
            trim_paths: (!profile.trim_paths.is_none()).then(|| profile.trim_paths.to_string()),
            hint_mostly_unused: profile.hint_mostly_unused,
        },
        compiler: machine_message::TrustUnitCompilerSemantics {
            frontend: trust_unit_frontend(unit.mode),
            codegen_backend: effective_codegen_backend,
            rustc_release: rustc.version.to_string(),
            rustc_commit_hash: rustc.commit_hash.clone(),
            rustc_host: rustc.host.to_string(),
            rustc_verbose_version_sha256: Sha256::new()
                .update(rustc.verbose_version.as_bytes())
                .finish_hex(),
        },
        unit_rustflags: trust_semantic_compiler_args(&unit.rustflags)
            .map_err(anyhow::Error::msg)?,
        manifest_lint_rustflags,
        extra_compiler_args: trust_semantic_compiler_args(&extra_compiler_args)
            .map_err(anyhow::Error::msg)?,
    };
    semantics.validate_canonical().map_err(anyhow::Error::msg)?;
    Ok(semantics)
}

/// Cargo graph entries that do not run a compiler through this job queue and
/// therefore can never produce a compiler-message/artifact/coverage terminal
/// set. They remain in the invocation inventory with an exact reason instead
/// of being misdeclared as proof units or silently dropped from the Unit graph.
fn trust_non_proof_unit_exclusion_reason(unit: &Unit) -> Option<&'static str> {
    trust_non_proof_exclusion_reason(unit.mode, unit.skip_non_compile_time_dep)
}

fn trust_non_proof_exclusion_reason(
    mode: CompileMode,
    skip_non_compile_time_dep: bool,
) -> Option<&'static str> {
    // Preserve an intrinsic control/deferred mode reason when Cargo also marks
    // that Unit filtered under `--compile-time-deps`; consumers validate the
    // reason/mode pair. The graph-only filter applies only to modes that would
    // otherwise be proof-capable compiler jobs.
    trust_non_proof_mode_exclusion_reason(mode).or_else(|| {
        skip_non_compile_time_dep
            .then_some(machine_message::TRUST_EXCLUSION_COMPILE_TIME_DEPS_FILTERED)
    })
}

fn trust_non_proof_mode_exclusion_reason(mode: CompileMode) -> Option<&'static str> {
    match mode {
        CompileMode::RunCustomBuild => {
            Some(machine_message::TRUST_EXCLUSION_BUILD_SCRIPT_EXECUTION)
        }
        CompileMode::Doctest => Some(machine_message::TRUST_EXCLUSION_DEFERRED_DOCTEST),
        // Cargo runs these entries through rustdoc, but the authenticated
        // per-Unit Trust session, fingerprint, and terminal proof protocol is
        // currently wired only for rustc jobs. Calling them proof units would
        // promise evidence that this graph entry cannot emit. Keep them in the
        // exact graph inventory as an explicit conditional exclusion instead.
        CompileMode::Doc | CompileMode::Docscrape => {
            Some(machine_message::TRUST_EXCLUSION_DOCUMENTATION)
        }
        _ => None,
    }
}

fn trust_excluded_unit_reason(
    unit: &Unit,
    include_dependencies: bool,
) -> CargoResult<&'static str> {
    if let Some(reason) = trust_non_proof_unit_exclusion_reason(unit) {
        return Ok(reason);
    }
    if !include_dependencies {
        return Ok(machine_message::TRUST_EXCLUSION_DEPENDENCY_POLICY);
    }
    anyhow::bail!(
        "proof-capable Cargo Unit {} target {:?} mode {} was excluded despite include-dependencies=true",
        unit.pkg.package_id(),
        unit.target.name(),
        trust_compile_mode_name(unit.mode),
    )
}

fn trust_unit_graph_role(build_runner: &BuildRunner<'_, '_>, unit: &Unit) -> &'static str {
    if !unit.target.is_custom_build() && is_resolved_root_unit(unit, &build_runner.bcx.roots) {
        "primary"
    } else if trust_unit_test_execution_subject(build_runner, unit) {
        "test-execution"
    } else if unit.mode == CompileMode::RunCustomBuild {
        "control"
    } else {
        "dependency"
    }
}

/// Construct the Cargo-authenticated proof-unit identity carried outside the
/// compiler payload. A compiler diagnostic cannot promote itself into this
/// set: only the resolved Cargo graph can choose `primary`, `test-execution`,
/// or an explicitly requested `dependency` here.
fn trust_proof_unit_role_for_policy(
    build_runner: &BuildRunner<'_, '_>,
    unit: &Unit,
    include_dependencies: bool,
) -> Option<&'static str> {
    if trust_non_proof_unit_exclusion_reason(unit).is_some() {
        return None;
    }
    let role = trust_unit_graph_role(build_runner, unit);
    // Trust: inventory and compiler flags share the same scope decision.
    if !trust_unit_verification_enabled(
        unit.target.is_custom_build(),
        role == "primary",
        role == "test-execution",
        include_dependencies,
    ) {
        return None;
    }
    // Trust: dependency coverage includes every compiler unit, including the
    // compile of build.rs and host-only dependencies. RunCustomBuild is already
    // excluded above because it executes an artifact rather than compiling one.
    debug_assert_ne!(
        role, "control",
        "control units are excluded before proof identity"
    );
    Some(role)
}

// Trust: assertions constrain admission; they never change roles or exclusions.
// The graph-derived role is the same one used by proof inventory and envelopes.
fn require_trust_unit_verification_assertion(
    build_runner: &BuildRunner<'_, '_>,
    unit: &Unit,
) -> CargoResult<()> {
    if !verified_targo_protocol_active()
        || !required_trust_verification_assertion(&unit.rustflags).map_err(anyhow::Error::msg)?
    {
        return Ok(());
    }
    let extra_args = build_runner
        .bcx
        .extra_args_for(unit)
        .map(Vec::as_slice)
        .unwrap_or_default();
    verified_targo_proof_session(&unit.rustflags, extra_args).map_err(anyhow::Error::msg)?;
    for (name, _) in
        prefixed_compiler_options(&unit.profile.rustflags, "-Z").map_err(anyhow::Error::msg)?
    {
        if matches!(name.as_str(), "trust_verify" | "no_trust_verify") {
            anyhow::bail!(
                "profile rustflags cannot set -Z{name} during a verified Targo invocation"
            );
        }
    }
    let include_dependencies = resolve_trust_include_dependencies(&unit.rustflags, extra_args)
        .map_err(anyhow::Error::msg)?;
    let exclusion =
        if trust_proof_unit_role_for_policy(build_runner, unit, include_dependencies).is_some() {
            None
        } else {
            Some(trust_excluded_unit_reason(unit, include_dependencies)?)
        };
    require_trust_verification_eligibility(exclusion)
        .map_err(anyhow::Error::msg)
        .with_context(|| {
            format!(
                "cannot satisfy -Ztrust-verify=on assertion for {} target {:?} mode {}",
                unit.pkg.package_id(),
                unit.target.name(),
                trust_compile_mode_name(unit.mode),
            )
        })
}

fn require_trust_verification_eligibility(exclusion: Option<&str>) -> Result<(), String> {
    match exclusion {
        None => Ok(()),
        Some(reason) => Err(format!("required verification is unavailable: {reason}")),
    }
}

fn trust_proof_unit_identity_from_semantics_sha256(
    build_runner: &BuildRunner<'_, '_>,
    unit: &Unit,
    role: &'static str,
    semantics_sha256: String,
) -> machine_message::TrustProofUnit {
    machine_message::TrustProofUnit {
        schema: machine_message::TRUST_PROOF_UNIT_SCHEMA_V2,
        index: build_runner.bcx.unit_to_index[unit].0,
        mode: trust_compile_mode_name(unit.mode),
        role,
        package_name: unit.pkg.name().to_string(),
        semantics_sha256,
    }
}

fn trust_proof_unit_identity(
    build_runner: &BuildRunner<'_, '_>,
    unit: &Unit,
) -> CargoResult<Option<machine_message::TrustProofUnit>> {
    if !verified_targo_protocol_active() {
        return Ok(None);
    }
    let include_dependencies = resolve_trust_include_dependencies(
        &unit.rustflags,
        build_runner
            .bcx
            .extra_args_for(unit)
            .map(Vec::as_slice)
            .unwrap_or_default(),
    )
    .map_err(anyhow::Error::msg)?;
    let Some(role) = trust_proof_unit_role_for_policy(build_runner, unit, include_dependencies)
    else {
        return Ok(None);
    };
    let semantics_sha256 = trust_unit_semantics(build_runner, unit)?
        .sha256()
        .map_err(anyhow::Error::msg)?;
    Ok(Some(trust_proof_unit_identity_from_semantics_sha256(
        build_runner,
        unit,
        role,
        semantics_sha256,
    )))
}

fn trust_target_kind_names(target: &Target) -> Vec<String> {
    let mut kinds = match target.kind() {
        TargetKind::Lib(kinds) => kinds.iter().map(ToString::to_string).collect(),
        TargetKind::Bin => vec!["bin".to_string()],
        TargetKind::Test => vec!["test".to_string()],
        TargetKind::Bench => vec!["bench".to_string()],
        TargetKind::ExampleLib(_) | TargetKind::ExampleBin => vec!["example".to_string()],
        TargetKind::CustomBuild => vec!["custom-build".to_string()],
    };
    kinds.sort();
    kinds.dedup();
    kinds
}

fn canonicalize_trust_proof_inventory(
    mut units: Vec<machine_message::TrustProofInventoryUnit>,
    mut excluded_units: Vec<machine_message::TrustExcludedUnit>,
    expected_indices: impl IntoIterator<Item = u64>,
) -> Result<
    (
        Vec<machine_message::TrustProofInventoryUnit>,
        Vec<machine_message::TrustExcludedUnit>,
    ),
    String,
> {
    units.sort_by_key(|unit| unit.trust_proof_unit.index);
    excluded_units.sort_by_key(|unit| unit.index);

    let mut actual_indices = units
        .iter()
        .map(|unit| unit.trust_proof_unit.index)
        .chain(excluded_units.iter().map(|unit| unit.index))
        .collect::<Vec<_>>();
    actual_indices.sort_unstable();
    if let Some(duplicate) = actual_indices.windows(2).find(|pair| pair[0] == pair[1]) {
        return Err(format!(
            "resolved Cargo graph assigned duplicate Cargo Unit index {}",
            duplicate[0]
        ));
    }

    let mut expected_indices = expected_indices.into_iter().collect::<Vec<_>>();
    expected_indices.sort_unstable();
    if actual_indices != expected_indices {
        return Err(format!(
            "Trust proof and exclusion inventories did not exactly cover the resolved Cargo Unit graph (expected_indices={expected_indices:?}, actual_indices={actual_indices:?})"
        ));
    }
    Ok((units, excluded_units))
}

fn require_uniform_trust_include_dependencies(
    policies: impl IntoIterator<Item = (u64, bool)>,
) -> Result<bool, String> {
    let mut policies = policies.into_iter().collect::<Vec<_>>();
    policies.sort_unstable_by_key(|(index, _)| *index);
    let mut resolved = None;
    for (index, policy) in policies {
        if let Some(expected) = resolved {
            if expected != policy {
                return Err(format!(
                    "resolved Cargo graph has inconsistent -Ztrust-verify-include-dependencies policy at unit index {index}: expected {expected}, found {policy}"
                ));
            }
        } else {
            resolved = Some(policy);
        }
    }
    Ok(resolved.unwrap_or(false))
}

/// Snapshot the complete Cargo-authenticated proof subject before any
/// compiler process can emit evidence. This iterates the resolved Unit graph,
/// and delegates admission to the same function used for compiler-message and
/// artifact envelopes, preventing the declaration and per-unit roles from
/// drifting apart.
pub(super) fn trust_proof_inventory(
    build_runner: &BuildRunner<'_, '_>,
) -> CargoResult<Option<machine_message::TrustProofInventory>> {
    if !verified_targo_protocol_active() {
        return Ok(None);
    }

    // Trust: the output request belongs to this invocation's primary root, not
    // to an excluded unit (which need not carry compiler session flags).
    let mut export_request = None;
    for root in &build_runner.bcx.roots {
        let extra = build_runner
            .bcx
            .extra_args_for(root)
            .map(Vec::as_slice)
            .unwrap_or_default();
        let session = resolve_per_unit_protocol_value(
            "trust-verify-session",
            trust_verification_session(&root.rustflags).map_err(anyhow::Error::msg)?,
            trust_verification_session(extra).map_err(anyhow::Error::msg)?,
        )
        .map_err(anyhow::Error::msg)?;
        if let Some(session) = session {
            if let Some(request) = verifier_input_export_request(&root.rustflags, extra, &session)?
            {
                export_request = Some((session, request));
                break;
            }
        }
    }

    let mut policies = Vec::with_capacity(build_runner.bcx.unit_to_index.len());
    let mut units = Vec::new();
    let mut excluded_units = Vec::new();
    // A graph can contain hundreds of units for one custom target. Hash its
    // exact JSON bytes once for this inventory snapshot, then reuse the digest
    // for every unit with that CompileKind.
    let mut compile_target_spec_digests: HashMap<CompileKind, Option<String>> = HashMap::default();
    for (unit, index) in &build_runner.bcx.unit_to_index {
        let include_dependencies = resolve_trust_include_dependencies(
            &unit.rustflags,
            build_runner
                .bcx
                .extra_args_for(unit)
                .map(Vec::as_slice)
                .unwrap_or_default(),
        )
        .map_err(anyhow::Error::msg)?;
        policies.push((index.0, include_dependencies));

        let target_name = unit.target.name().to_string();
        let target_kinds = trust_target_kind_names(&unit.target);
        let compile_target = scoped_unit_compile_target(&build_runner.bcx, unit)?;
        let compile_target_spec_sha256 =
            if let Some(digest) = compile_target_spec_digests.get(&unit.kind) {
                digest.clone()
            } else {
                let digest = exact_unit_compile_target_spec_sha256(unit.kind)?;
                compile_target_spec_digests.insert(unit.kind, digest.clone());
                digest
            };
        let semantics = trust_unit_semantics(build_runner, unit)?;
        let semantics_sha256 = semantics.sha256().map_err(anyhow::Error::msg)?;
        let trust_compile_mode = exact_unit_compile_mode(unit.mode);
        let trust_compile_kind = exact_unit_compile_kind(unit.kind);
        let captured = exact_unit::capture(build_runner, unit)?;
        captured.require_spec(unit.kind, compile_target_spec_sha256.as_deref())?;
        let trust_unit_identity_sha256 = captured.digest.clone();
        let role = trust_proof_unit_role_for_policy(build_runner, unit, include_dependencies);
        // Trust: inventory includes excluded and reused units before any child can
        // emit an artifact. Exporting never activates those units or changes scope.
        if let Some((session, request)) = export_request.as_ref() {
            crate::util::verifier_input_export::unit_args(
                &request,
                &crate::util::verifier_input_export::ExportUnit {
                    session: session.clone(),
                    unit_sha256: trust_unit_identity_sha256.clone(),
                    semantics_sha256: semantics_sha256.clone(),
                    package_name: unit.pkg.name().to_string(),
                    role: role.unwrap_or("excluded").to_owned(),
                    graph_role: trust_unit_graph_role(build_runner, unit).to_owned(),
                    exclusion_reason: if role.is_none() {
                        Some(trust_excluded_unit_reason(unit, include_dependencies)?.to_owned())
                    } else {
                        None
                    },
                    mode: trust_compile_mode_name(unit.mode).to_owned(),
                    verification_enabled: role.is_some(),
                },
            )?;
        }
        let Some(role) = role else {
            let exclusion_reason = trust_excluded_unit_reason(unit, include_dependencies)?;
            excluded_units.push(machine_message::TrustExcludedUnit {
                index: index.0,
                mode: trust_compile_mode_name(unit.mode),
                graph_role: trust_unit_graph_role(build_runner, unit),
                package_id: unit.pkg.package_id().to_spec(),
                package_name: unit.pkg.name().to_string(),
                target_name,
                target_kinds,
                compile_target,
                trust_compile_mode,
                trust_compile_kind,
                trust_unit_identity_sha256,
                compile_target_spec_sha256,
                exclusion_reason,
                semantics_sha256,
                semantics,
            });
            continue;
        };
        let trust_proof_unit = trust_proof_unit_identity_from_semantics_sha256(
            build_runner,
            unit,
            role,
            semantics_sha256,
        );
        units.push(machine_message::TrustProofInventoryUnit {
            trust_proof_unit,
            semantics,
            package_id: unit.pkg.package_id().to_spec(),
            target_name,
            target_kinds,
            compile_target,
            trust_compile_mode,
            trust_compile_kind,
            trust_unit_identity_sha256,
            compile_target_spec_sha256,
        });
    }

    let include_dependencies =
        require_uniform_trust_include_dependencies(policies).map_err(anyhow::Error::msg)?;
    let (units, excluded_units) = canonicalize_trust_proof_inventory(
        units,
        excluded_units,
        build_runner.bcx.unit_to_index.values().map(|index| index.0),
    )
    .map_err(anyhow::Error::msg)?;
    Ok(Some(machine_message::TrustProofInventory {
        schema: machine_message::TRUST_PROOF_INVENTORY_SCHEMA_V2,
        include_dependencies,
        units,
        excluded_units,
    }))
}

fn trust_unit_metadata_args(
    is_custom_build: bool,
    is_primary: bool,
    package_name: &str,
) -> [String; 4] {
    let role = trust_unit_role(is_custom_build, is_primary);
    [
        "-Z".to_string(),
        format!("trust-verify-crate-role={role}"),
        "-Z".to_string(),
        format!("trust-verify-package-name={package_name}"),
    ]
}

/// Trust (cross-crate composition): the crate names this unit may bundle
/// foreign bodies from, sorted and deduplicated.
///
/// Membership is decided from Cargo's own resolved unit graph, never from a
/// name a package writes about itself. A dependency qualifies only when this
/// build compiled it, from a path source in this workspace, as an ordinary
/// linkable library for the SAME compile kind as the unit that will read it.
/// Build scripts, proc-macro units, doc units and registry packages are all
/// outside it: the first three are not in the callee position this lane is
/// about, and the last is a much larger question than one workspace's own code.
///
/// Sorted so the emitted value — which is `[TRACKED]` in the compiler and
/// therefore enters the crate hash — cannot vary with dependency iteration
/// order and spuriously rebuild the world.
fn trust_unit_foreign_bundle_scope(build_runner: &BuildRunner<'_, '_>, unit: &Unit) -> Vec<String> {
    let mut scope: Vec<String> = build_runner
        .unit_deps(unit)
        .iter()
        .filter(|dep| {
            dep.unit.is_local()
                && dep.unit.kind == unit.kind
                && !dep.unit.mode.is_run_custom_build()
                && !dep.unit.mode.is_doc()
                && !dep.unit.target.is_custom_build()
                && !dep.unit.target.proc_macro()
                && dep.unit.target.is_lib()
        })
        .map(|dep| dep.unit.target.crate_name())
        .collect();
    scope.sort();
    scope.dedup();
    scope
}

/// Trust: the compiler's verification off-switch, the one `-Z` option Targo
/// itself spells to turn verification off. Every place Targo emits the switch
/// builds it from this constant: `trust_unit_protocol_args` (a compiler unit
/// outside the requested proof scope), `custom_build.rs` (the runtime
/// `CARGO_ENCODED_RUSTFLAGS` of every build script it executes) and
/// `target_info.rs` (the `TRUST_NO_VERIFY` fast lane), so they cannot disagree
/// about how "off" is spelled.
pub(crate) const TRUST_VERIFY_OFF_OPTION: &str = "trust-verify=off";

/// Trust (T14a, DECISION_QUEUE T14-APPEND-1): the one private variable in
/// which `targo trust` hands its Cargo child the lane's rustflags, in Cargo's
/// encoded form (`\x1f`-separated). A branded invocation appends them to the
/// project's flags, resolved by Cargo's own precedence (`extra_args` in
/// `build_context/target_info.rs`), so a unit's flags are `<project> <lane>`.
/// It is read only in a branded invocation and scrubbed from every child.
pub(crate) const TRUST_TARGO_LANE_RUSTFLAGS_ENV: &str = "TRUST_TARGO_LANE_RUSTFLAGS";

fn trust_unit_protocol_args(
    is_custom_build: bool,
    is_primary: bool,
    is_test_execution_subject: bool,
    is_certified_monitor_subject: bool,
    package_name: &str,
    include_dependencies: bool,
) -> Vec<String> {
    let mut args = trust_unit_metadata_args(is_custom_build, is_primary, package_name).to_vec();
    // Role/package strings are reporting metadata, not verifier authority. The
    // explicit compiler off-switch is the only way Targo excludes a resolved
    // unit. Append it after every caller-controlled source and only for graph
    // units outside the requested scope. Under include-dependencies, build.rs
    // compilation is in scope even though its graph role remains dependency.
    if !trust_unit_verification_enabled(
        is_custom_build,
        is_primary,
        is_test_execution_subject,
        include_dependencies,
    ) {
        args.extend(["-Z".to_string(), TRUST_VERIFY_OFF_OPTION.to_string()]);
    }
    if is_certified_monitor_subject {
        args.extend([
            "-Z".to_string(),
            "trust-certified-test-monitors".to_string(),
        ]);
    }
    // Trust (cross-crate composition): ship every unit's MIR in its metadata.
    //
    // Without this a caller cannot RE-DERIVE a dependency's obligations from the
    // dependency's own body, because the body is not there to read. Measured on
    // the real artifact a `targo trust check` produced:
    // `is_mir_available(trust_ratio::percent)` was FALSE. Nothing in
    // `should_encode_mir` fires for the shape these crates have — they are
    // non-generic, non-`#[inline]`, non-`const fn` `pub fn`s — and the last
    // route, `cross_crate_inlinable`, short-circuits false whenever incremental
    // is on, which is the dev profile this lane runs under. Raising `opt-level`
    // is NOT a substitute: the verified lane pipelines with `--emit=metadata`,
    // where `should_codegen()` is false and the route closes at any opt-level.
    //
    // ON EVERY UNIT, NEVER ONE LANE OF TWO SHARING A TARGET DIR. Rustflags are
    // hashed into Cargo's `unit_id` but NOT into `-Cmetadata`, so a partial
    // application forks a crate into two artifacts carrying one StableCrateId,
    // and that surfaces as "found crates (`core` and `core`) with colliding
    // StableCrateId values" followed by an E0463 that points at nothing related.
    // The same rule is written down where std's own copy of this flag is applied
    // in bootstrap. Appending it HERE — the one per-unit function every
    // compilation of a proof session goes through — is what makes "every unit"
    // structural rather than a thing to remember.
    args.extend(["-Z".to_string(), "always-encode-mir".to_string()]);
    args
}

#[cfg(test)]
fn trust_proof_primary_unit(is_resolved_root_unit: bool, has_certified_monitor: bool) -> bool {
    is_resolved_root_unit || has_certified_monitor
}

/// Trust: compiler-unit eligibility. This does not classify Cargo execution
/// jobs: the inventory excludes RunCustomBuild before choosing a proof role.
/// Dependency coverage includes build.rs compilation, its dependency closure,
/// and spec-provider compilation. Macro admission is a separate boundary.
fn trust_unit_verification_enabled(
    is_custom_build: bool,
    is_primary: bool,
    is_test_execution_subject: bool,
    include_dependencies: bool,
) -> bool {
    include_dependencies || (!is_custom_build && (is_primary || is_test_execution_subject))
}

fn caller_supplied_trust_unit_metadata(rustflags: &[String]) -> Option<&'static str> {
    trust_z_option_values(rustflags).find_map(|value| match rustc_option_parts(value).0.as_ref() {
        "trust_verify_crate_role" => Some("trust-verify-crate-role"),
        "trust_verify_package_name" => Some("trust-verify-package-name"),
        "trust_verify_target_spec_sha256" => Some("trust-verify-target-spec-sha256"),
        "trust_admission_run_digest" => Some("trust-admission-run-digest"),
        "trust_admission_unit_digest" => Some("trust-admission-unit-digest"),
        "trust_admission_semantics_digest" => Some("trust-admission-semantics-digest"),
        "trust_admission_unit_role" => Some("trust-admission-unit-role"),
        "trust_admission_compile_target" => Some("trust-admission-compile-target"),
        "trust_certified_test_monitors" => Some("trust-certified-test-monitors"),
        "trust_proc_macro_boundary" => Some("trust-proc-macro-boundary"),
        "trust_audited_proc_macro" => Some("trust-audited-proc-macro"),
        _ => None,
    })
}

// Trust: keep this domain byte-identical to trust_types::native_admission::RUN_DOMAIN.
// Native Targo does not depend on the compiler's Trust-owned type crate.
fn native_admission_metadata_args(
    session: &str,
    unit: &str,
    semantics: &str,
    role: &str,
    target: &str,
) -> Vec<String> {
    let mut bytes = b"trust.native-admission.run.v1\0".to_vec();
    bytes.extend_from_slice(session.as_bytes());
    let run = Sha256::new().update(&bytes).finish_hex();
    [
        format!("trust-admission-run-digest={run}"),
        format!("trust-admission-unit-digest={unit}"),
        format!("trust-admission-semantics-digest={semantics}"),
        format!("trust-admission-unit-role={role}"),
        format!("trust-admission-compile-target={target}"),
    ]
    .into_iter()
    .flat_map(|arg| ["-Z".to_string(), arg])
    .collect()
}

#[cfg(test)]
mod native_admission_metadata_tests {
    use super::*;

    #[test]
    fn launch_metadata_keeps_unit_and_semantics_and_hides_the_nonce() {
        let unit = "a".repeat(64);
        let semantics = "b".repeat(64);
        let first = native_admission_metadata_args(
            "private-run-one",
            &unit,
            &semantics,
            "primary",
            "aarch64-apple-darwin",
        );
        let second = native_admission_metadata_args(
            "private-run-two",
            &unit,
            &semantics,
            "primary",
            "aarch64-apple-darwin",
        );
        assert_eq!(&first[2..], &second[2..]);
        assert_ne!(first[1], second[1]);
        assert!(!first.join(" ").contains("private-run-one"));
        assert_eq!(first[3], format!("trust-admission-unit-digest={unit}"));
        assert_eq!(
            first[5],
            format!("trust-admission-semantics-digest={semantics}")
        );
    }

    #[test]
    fn caller_cannot_supply_any_native_admission_carrier_spelling() {
        for name in [
            "run-digest",
            "unit-digest",
            "semantics-digest",
            "unit-role",
            "compile-target",
        ] {
            for alias in [
                format!("trust-admission-{name}"),
                format!("trust_admission_{}", name.replace('-', "_")),
            ] {
                for flags in [
                    vec![format!("-Z{alias}=forged")],
                    vec!["-Z".into(), format!("{alias}=forged")],
                ] {
                    assert!(
                        caller_supplied_trust_unit_metadata(&flags).is_some(),
                        "{flags:?}"
                    );
                }
            }
        }
    }

    #[test]
    fn custom_target_launch_uses_the_exact_inventory_path_without_lossy_conversion() {
        let path = "/owned/targets/日本語 directory/custom.json";
        let target = CompileKind::Target(CompileTarget::Json {
            short: "custom".into(),
            path: path.into(),
        });
        let inventory_target = exact_unit_compile_target(target, "aarch64-apple-darwin".into());
        let args = native_admission_metadata_args(
            "session",
            "unit",
            "semantics",
            "primary",
            &inventory_target,
        );
        assert_eq!(inventory_target, path);
        assert_eq!(args[9], format!("trust-admission-compile-target={path}"));
        let host = exact_unit_compile_target(CompileKind::Host, "aarch64-apple-darwin".into());
        assert_eq!(host, "aarch64-apple-darwin");
    }
}

fn trust_z_option_values(rustflags: &[String]) -> impl Iterator<Item = &str> {
    rustflags.iter().enumerate().filter_map(|(index, flag)| {
        if flag == "-Z" {
            rustflags.get(index + 1).map(String::as_str)
        } else {
            flag.strip_prefix("-Z").filter(|value| !value.is_empty())
        }
    })
}

#[cfg(test)]
mod trust_verification_role_tests {
    use super::{
        AuthenticatedTargoProcessAuthority, CLIPPY_ARGS_ENV, CertifiedMonitorCompilerClosure,
        CertifiedMonitorSeal, CompileKind, CompileMode, CompileTarget, ProcMacroExpansion,
        ReservedTippyArgs, RustcProcessRole, TIPPY_ENCODED_ARGS_ENV,
        TRUST_TARGO_TEST_MONITOR_SESSION, VerifiedTargoCompilerPolicy,
        admit_in_process_proc_macro_tcb, apply_build_script_env,
        audited_trust_spec_requires_fresh_build, audited_trust_spec_source,
        caller_supplied_trust_unit_metadata, canonical_trust_string_set,
        canonicalize_trust_proof_inventory, cargo_prefers_dynamic_rust_linkage,
        compiler_flags_without_verification_assertion,
        ensure_exact_unit_compile_target_spec_unchanged, exact_unit_compile_kind,
        exact_unit_compile_target_spec_sha256, is_resolved_root_unit,
        reject_certified_monitor_custom_build_unit, reject_certified_monitor_custom_target,
        reject_certified_monitor_dynamic_rust_linkage,
        reject_certified_monitor_dynamic_rust_linkage_with_audited_proc_macro,
        reject_certified_monitor_dynamic_unit_dependencies,
        reject_certified_monitor_presnapshot_closure_controls,
        reject_compilation_during_prepared_execution, reject_in_process_proc_macro_tcb,
        reject_verified_custom_target_llvm_args, reject_verified_targo_compiler_wrappers,
        require_trust_verification_eligibility, require_uniform_trust_include_dependencies,
        required_trust_verification_assertion, resolve_certified_monitor_unit_session,
        resolve_trust_include_dependencies, resolve_trust_verification_protocol,
        resolved_trust_proof_artifact_root, seal_certified_monitor_compiler_environment,
        seal_certified_monitor_graph_compiler_environment,
        snapshot_reserved_tippy_args_for_invocation, trust_certified_monitor_subject_enabled,
        trust_non_proof_exclusion_reason, trust_non_proof_mode_exclusion_reason,
        trust_policy_claims_proof_authority, trust_proc_macro_expansion, trust_proof_artifact_root,
        trust_proof_primary_unit, trust_semantic_compiler_args,
        trust_test_execution_subject_enabled, trust_test_monitor_unit_selected,
        trust_unit_metadata_args, trust_unit_protocol_args, trust_unit_role,
        trust_unit_verification_enabled, trust_verification_session,
        validate_certified_monitor_command_env,
        validate_verified_targo_compiler_argument_boundaries, verified_targo_proof_session,
    };
    use crate::util::data_structures::HashSet;
    use crate::util::machine_message::{
        TRUST_PROOF_UNIT_SCHEMA_V2, TRUST_UNIT_SEMANTICS_SCHEMA_V1, TrustExcludedUnit,
        TrustProofInventoryUnit, TrustProofUnit, TrustUnitCompilerSemantics,
        TrustUnitProfileSemantics, TrustUnitSemantics,
    };
    use crate::util::process_authority::{
        BROKEN_CODE_ENV_INTERNAL, CARGO_PRIMARY_PACKAGE_ENV, FIX_ENV_INTERNAL,
        FIX_YOLO_ENV_INTERNAL, RUSTC_WORKSPACE_WRAPPER_ENV,
    };
    use crate::util::tippy_arg_protocol::encode_args;
    use cargo_util::ProcessBuilder;
    use cargo_util_schemas::core::PackageIdSpec;
    use std::ffi::OsStr;
    use std::fs;
    use std::path::{Path, PathBuf};

    fn flags(values: &[&str]) -> Vec<String> {
        values.iter().map(|value| (*value).to_string()).collect()
    }

    fn inventory_semantics() -> TrustUnitSemantics {
        TrustUnitSemantics {
            schema: TRUST_UNIT_SEMANTICS_SCHEMA_V1,
            features: Vec::new(),
            target_cfg: Vec::new(),
            cfg_test: false,
            target_edition: "2024".to_string(),
            target_crate_types: vec!["rlib".to_string()],
            target_harness: true,
            target_proc_macro: false,
            profile: TrustUnitProfileSemantics {
                opt_level: "0".to_string(),
                requested_lto: "false".to_string(),
                effective_lto: "only-object".to_string(),
                codegen_backend: None,
                codegen_units: None,
                debuginfo: "0".to_string(),
                split_debuginfo: None,
                debug_assertions: false,
                overflow_checks: false,
                rpath: false,
                incremental: false,
                panic: "unwind".to_string(),
                strip: "none".to_string(),
                rustflags: Vec::new(),
                trim_paths: None,
                hint_mostly_unused: None,
            },
            compiler: TrustUnitCompilerSemantics {
                frontend: "rustc",
                codegen_backend: "trust-cg".to_string(),
                rustc_release: "1.99.0-nightly".to_string(),
                rustc_commit_hash: None,
                rustc_host: "x86_64-unknown-linux-gnu".to_string(),
                rustc_verbose_version_sha256: "a".repeat(64),
            },
            unit_rustflags: Vec::new(),
            manifest_lint_rustflags: Vec::new(),
            extra_compiler_args: Vec::new(),
        }
    }

    fn host_absolute_proof_root(name: &str) -> String {
        let root = std::env::current_dir()
            .expect("test working directory is available")
            .join(name);
        assert!(root.is_absolute(), "test proof root must be host-absolute");
        root.to_string_lossy().into_owned()
    }

    fn host_absolute_proof_root_flag(name: &str) -> String {
        format!(
            "-Ztrust-proof-artifact-root={}",
            host_absolute_proof_root(name)
        )
    }

    fn boundary_policy(command: &ProcessBuilder) -> VerifiedTargoCompilerPolicy {
        let args = command
            .get_args()
            .filter_map(|argument| argument.to_str().map(str::to_string))
            .collect::<Vec<_>>();
        VerifiedTargoCompilerPolicy::new(&args, &[]).expect("test policy is unique")
    }

    #[test]
    fn verified_targo_rejects_in_process_proc_macro_transport_forgery_boundary() {
        let error = reject_in_process_proc_macro_tcb(
            true,
            "selected@0.1.0::selected",
            [
                "derive-b@1.0.0::derive_b".to_string(),
                "derive-a@1.0.0::derive_a".to_string(),
                "derive-a@1.0.0::derive_a".to_string(),
            ],
        )
        .expect_err("verified unit must not execute in-process proc macros");
        assert!(error.contains("compiler-message/TRUSTJSON"), "{error}");
        assert!(error.contains("no-proc-macro TCB boundary"), "{error}");
        assert!(
            error.contains("derive-a@1.0.0::derive_a, derive-b@1.0.0::derive_b"),
            "dependency inventory must be canonical and deduplicated: {error}"
        );

        reject_in_process_proc_macro_tcb(true, "plain@0.1.0::plain", std::iter::empty())
            .expect("verified unit without proc macros is inside the enforced TCB");
        reject_in_process_proc_macro_tcb(
            false,
            "ordinary@0.1.0::ordinary",
            ["ordinary-derive@1.0.0::ordinary_derive".to_string()],
        )
        .expect("ordinary Cargo compatibility domain must remain unchanged");
    }

    #[test]
    fn trust_policy_lane_decides_whether_proof_authority_is_claimed() {
        // The absent default is the compiler's strict policy: authority claimed.
        assert_eq!(trust_policy_claims_proof_authority(&[], &[]), Ok(true));
        for authority_lane in [
            "-Ztrust-policy=strict",
            "-Ztrust-policy=certify",
            "-Ztrust-policy=memory-safe",
        ] {
            assert_eq!(
                trust_policy_claims_proof_authority(&flags(&[authority_lane]), &[]),
                Ok(true),
                "{authority_lane}"
            );
        }
        // `advisory` is what `--allow-l0-gaps` and `--survey` put on the
        // graph-wide rustflags; every rustc-equivalent spelling must agree.
        for advisory in [
            &["-Ztrust-policy=advisory"][..],
            &["-Z", "trust-policy=advisory"],
            &["-Ztrust_policy=advisory"],
            &[
                "-Ztrust-verify-level=2",
                "-Ztrust-policy=advisory",
                "-Ztrust-verify-output=json",
            ],
        ] {
            assert_eq!(
                trust_policy_claims_proof_authority(&flags(advisory), &[]),
                Ok(false),
                "{advisory:?}"
            );
        }
        assert_eq!(
            trust_policy_claims_proof_authority(&[], &flags(&["-Ztrust-policy=advisory"])),
            Ok(false)
        );
        // Fail closed on an ambiguous lane: a second source can never loosen
        // the first, and an empty value is not a lane.
        assert!(
            trust_policy_claims_proof_authority(
                &flags(&["-Ztrust-policy=certify"]),
                &flags(&["-Ztrust-policy=advisory"]),
            )
            .is_err()
        );
        assert!(
            trust_policy_claims_proof_authority(
                &flags(&["-Ztrust-policy=advisory", "-Ztrust_policy=advisory"]),
                &[],
            )
            .is_err()
        );
        assert!(trust_policy_claims_proof_authority(&flags(&["-Ztrust-policy="]), &[]).is_err());
    }

    #[test]
    fn advisory_lane_forfeits_proc_macro_tcb_instead_of_refusing() {
        let derives = || {
            [
                "derive-b@1.0.0::derive_b".to_string(),
                "derive-a@1.0.0::derive_a".to_string(),
                "derive-a@1.0.0::derive_a".to_string(),
            ]
        };
        // A lane that claims proof authority: the refusal is byte-for-byte the
        // existing one.
        let refused = admit_in_process_proc_macro_tcb(
            true,
            true,
            ProcMacroExpansion::InProcess,
            "selected@0.1.0::selected",
            derives(),
        )
        .expect_err("an authority-claiming lane must still refuse");
        assert_eq!(
            refused,
            reject_in_process_proc_macro_tcb(true, "selected@0.1.0::selected", derives())
                .expect_err("reference refusal")
        );
        assert!(refused.contains("no-proc-macro TCB boundary"), "{refused}");

        // The advisory lane: the unit compiles, and the forfeiture is a warning
        // that names the unit and the canonical, deduplicated macro inventory.
        let forfeiture = admit_in_process_proc_macro_tcb(
            true,
            false,
            ProcMacroExpansion::InProcess,
            "selected@0.1.0::selected",
            derives(),
        )
        .expect("advisory lane must not refuse")
        .expect("advisory lane must record the forfeiture");
        assert!(
            forfeiture.contains("forfeits proof authority"),
            "{forfeiture}"
        );
        assert!(
            forfeiture.contains("selected@0.1.0::selected"),
            "{forfeiture}"
        );
        assert!(
            forfeiture.contains("derive-a@1.0.0::derive_a, derive-b@1.0.0::derive_b"),
            "{forfeiture}"
        );
        assert!(forfeiture.contains("not evidence-grade"), "{forfeiture}");

        // Nothing to forfeit: a clean boundary, or a unit outside the scan's
        // scope, records nothing in either lane.
        for claims_proof_authority in [true, false] {
            assert_eq!(
                admit_in_process_proc_macro_tcb(
                    true,
                    claims_proof_authority,
                    ProcMacroExpansion::InProcess,
                    "plain@0.1.0::plain",
                    std::iter::empty(),
                ),
                Ok(None)
            );
            assert_eq!(
                admit_in_process_proc_macro_tcb(
                    false,
                    claims_proof_authority,
                    ProcMacroExpansion::InProcess,
                    "ordinary@0.1.0::ordinary",
                    derives(),
                ),
                Ok(None)
            );
        }
    }

    /// RL-05: a unit whose proc macros expand in the isolated worker has no
    /// in-process dependency, on every lane; the same unit expanding in
    /// process is refused exactly as before (the negative control).
    #[test]
    fn isolated_expansion_is_admitted_on_every_lane_and_in_process_is_still_refused() {
        let derives = || {
            [
                "serde_derive@1.0.0::serde_derive".to_string(),
                "thiserror-impl@2.0.0::thiserror_impl".to_string(),
            ]
        };
        // strict, certify and memory-safe claim proof authority; advisory
        // claims none. Isolated: no refusal and no forfeiture on any of them.
        for claims_proof_authority in [true, false] {
            assert_eq!(
                admit_in_process_proc_macro_tcb(
                    true,
                    claims_proof_authority,
                    ProcMacroExpansion::IsolatedWorker,
                    "codex-cli@0.0.0::codex",
                    derives(),
                ),
                Ok(None)
            );
        }
        let refused = admit_in_process_proc_macro_tcb(
            true,
            true,
            ProcMacroExpansion::InProcess,
            "codex-cli@0.0.0::codex",
            derives(),
        )
        .expect_err("in-process expansion keeps the refusal");
        assert_eq!(
            refused,
            reject_in_process_proc_macro_tcb(true, "codex-cli@0.0.0::codex", derives())
                .expect_err("reference refusal")
        );
        assert!(
            refused.contains(
                "in-process proc-macro dependencies [serde_derive@1.0.0::serde_derive, thiserror-impl@2.0.0::thiserror_impl]"
            ),
            "{refused}"
        );
    }

    #[test]
    fn proc_macro_expansion_defaults_to_the_host_and_the_lane_can_only_turn_it_off() {
        use ProcMacroExpansion::{InProcess, IsolatedWorker};
        let flags = |values: &[&str]| values.iter().map(|v| v.to_string()).collect::<Vec<_>>();
        let none = flags(&[]);
        // Unspelled: the host decides, and Targo passes the option itself.
        assert_eq!(
            trust_proc_macro_expansion(true, &none, &none),
            Ok((IsolatedWorker, false))
        );
        assert_eq!(
            trust_proc_macro_expansion(false, &none, &none),
            Ok((InProcess, false))
        );
        // The lane's off-switch, in every spelling rustc reads.
        for off in [
            flags(&["-Z", "trust-proc-macro-isolation=no"]),
            flags(&["-Ztrust-proc-macro-isolation=off"]),
            flags(&["-Ztrust_proc_macro_isolation=false"]),
        ] {
            for host in [true, false] {
                assert_eq!(
                    trust_proc_macro_expansion(host, &off, &none),
                    Ok((InProcess, true)),
                    "{off:?}"
                );
            }
        }
        // Spelled on: honoured where the worker exists, never read as
        // in-process where it does not.
        let on = flags(&["-Ztrust-proc-macro-isolation"]);
        assert_eq!(
            trust_proc_macro_expansion(true, &on, &none),
            Ok((IsolatedWorker, true))
        );
        let refused = trust_proc_macro_expansion(false, &on, &none).unwrap_err();
        assert!(refused.contains("refused on this host"), "{refused}");
        assert!(trust_proc_macro_expansion(true, &on, &on).is_err());
        assert!(
            trust_proc_macro_expansion(
                true,
                &flags(&["-Ztrust-proc-macro-isolation=maybe"]),
                &none
            )
            .is_err()
        );
    }

    #[test]
    fn verified_targo_trust_proc_macro_exemption_requires_audited_package_identity() {
        // `trust-spec` inherits its version (`version.workspace = true`, since
        // `c9a8f1f481`), so, like `ny-contracts` below, any resolved version
        // must look up — the pre-`c9a8f1f481` `Some("0.1.1")` key missed the
        // 0.10.0 the workspace resolves and dropped the provider off the list
        // with no error — and every lookup must still attest the exact audited
        // bytes, which is where the identity lives.
        for version in ["0.1.1", "0.10.0", "0.11.0", "1.0.0"] {
            let audited = audited_trust_spec_source("trust-spec", version)
                .unwrap_or_else(|| panic!("trust-spec@{version} must stay audited"));
            assert_eq!(
                audited.manifest_sha256,
                "fada73aa63928043b5985b75ae6a9f407014db215b59058c6245bd15bdad4430",
                "trust-spec@{version} must attest the audited manifest bytes"
            );
            assert_eq!(
                audited.lib_sha256,
                "853603e08995c6008b852a8eaa8886658bba1f834f71212a8177af27df0dcca6",
                "trust-spec@{version} must attest the audited library bytes"
            );
        }

        assert!(audited_trust_spec_source("ny-contracts", "0.1.0").is_some());
        assert!(audited_trust_spec_source("ny-contracts", "0.2.0").is_some());
        assert!(audited_trust_spec_source("ny-contracts", "0.3.0").is_some());

        // The three ny-contracts entries are the SAME audited artifact under three
        // version strings (two bare workspace bumps). Pin that: if a future edit
        // lets these hashes drift apart, one of them is no longer the reviewed
        // crate and the allowlist has silently widened.
        let ny = ["0.1.0", "0.2.0", "0.3.0"]
            .map(|v| audited_trust_spec_source("ny-contracts", v).expect("audited above"));
        for entry in &ny {
            assert_eq!(entry.manifest_sha256, ny[0].manifest_sha256);
            assert_eq!(entry.lib_sha256, ny[0].lib_sha256);
        }

        // `ny-contracts` inherits its version from a workspace root that NEITHER
        // digest covers, so the version is not audit evidence for it and an
        // unrelated `pub bump` must not expire the carve-out. THIS IS THE CASE
        // THE OLD RULE GOT WRONG: it enumerated resolved versions, so every bump
        // silently dropped the provider back to a no-proc-macro TCB refusal
        // naming a crate whose bytes had not changed. Any resolved version must
        // now match, and must still attest the exact audited bytes.
        for version in ["0.1.0", "0.2.0", "0.3.0", "1.4.7", "99.0.0-rc.1"] {
            let audited = audited_trust_spec_source("ny-contracts", version)
                .unwrap_or_else(|| panic!("ny-contracts@{version} must stay audited"));
            assert_eq!(
                audited.manifest_sha256,
                "83569caf993ba8a93f6cd7af9d3ba23440f69baa23e6fe1cf053679eb82f42aa",
                "ny-contracts@{version} must attest the audited manifest bytes"
            );
            assert_eq!(
                audited.lib_sha256,
                "af8f868e0706b3084e4ee0911aa9256b8c46ba8c0d0db50f44703d4013380a29",
                "ny-contracts@{version} must attest the audited library bytes"
            );
        }

        // Dropping the version as a matching key must not let a NAME through:
        // the package name is still exact, and the digests still decide.
        for (package, version) in [
            ("hostile-shadow", "0.1.1"),
            ("trust", "0.1.1"),
            // Trust: MERGE (b62 <- origin/main; squash d24c671211): our ("ny-contracts",
            // "0.1.1"/"0.3.1"/"0.4.0") entries are DROPPED. They asserted those versions are NOT
            // audited, which was true under the OLD enumerate-the-resolved-versions rule our
            // commits were patching one bump at a time (6906ae2948 added 0.3.0). Upstream
            // replaced that rule with a version-agnostic one keyed on the audited
            // manifest/lib digests, so ny-contracts is audited at ANY version and those
            // three assertions are now false by construction (the loop above asserts
            // 99.0.0-rc.1 IS audited). Upstream's rule is at least as strict on the
            // security property -- the exact digests still decide, so a hostile
            // ny-contracts of any version is still refused -- and it removes the
            // silent-refusal-on-bare-bump failure mode. Only the name test remains here.
            ("ny-contracts-shim", "0.1.0"),
            ("ny-trust-spec", "0.1.0"),
        ] {
            assert!(
                audited_trust_spec_source(package, version).is_none(),
                "crate/lib naming alone must not authorize {package}@{version}"
            );
        }

        // Trust: compiling an audited provider now requires ordinary evidence;
        // admission of macros used by a verified unit remains unchanged.
        let error = reject_in_process_proc_macro_tcb(
            true,
            "ny-cert@0.1.0::ny_cert",
            ["hostile-shadow@0.1.1::trust".to_string()],
        )
        .expect_err("an unaudited proc macro must still hit the no-proc-macro TCB refusal");
        assert!(error.contains("no-proc-macro TCB boundary"), "{error}");
        assert!(error.contains("hostile-shadow@0.1.1::trust"), "{error}");
    }

    #[test]
    fn verified_targo_never_reuses_an_audited_proc_macro_artifact() {
        assert!(audited_trust_spec_requires_fresh_build(true, true));
        assert!(!audited_trust_spec_requires_fresh_build(true, false));
        assert!(!audited_trust_spec_requires_fresh_build(false, true));
    }

    #[test]
    fn verified_targo_rejects_post_validation_compiler_wrappers() {
        for (wrapper, workspace_wrapper) in [
            (Some(Path::new("/tmp/forged-wrapper")), None),
            (None, Some(Path::new("/tmp/forged-workspace-wrapper"))),
        ] {
            let error = reject_verified_targo_compiler_wrappers(true, wrapper, workspace_wrapper)
                .expect_err("verified compiler wrapper must fail closed");
            assert!(error.contains("after final argv validation"), "{error}");
            assert!(error.contains("forge proof transport"), "{error}");
        }
        reject_verified_targo_compiler_wrappers(
            false,
            Some(Path::new("/tmp/non-verified-wrapper")),
            None,
        )
        .expect("ordinary Cargo/Tippy wrapper behavior remains unchanged");
        reject_verified_targo_compiler_wrappers(true, Some(Path::new("")), Some(Path::new("")))
            .expect("empty wrapper overrides are definitionally absent");
    }

    #[test]
    fn verified_targo_rejects_caller_externs_outside_the_classified_cargo_graph() {
        for injected in [
            flags(&[
                "-Ztrust-verify-session=proof-run",
                "--extern=attacker=/tmp/libattacker.so",
            ]),
            flags(&[
                "-Ztrust-verify-session=proof-run",
                "--extern",
                "attacker=/tmp/libattacker.so",
            ]),
        ] {
            let error = resolve_trust_verification_protocol(&injected, &[])
                .expect_err("caller extern may load an unclassified proc macro");
            assert!(error.contains("no-proc-macro TCB boundary"), "{error}");
            assert!(error.contains("attacker=/tmp/libattacker.so"), "{error}");
        }
    }

    #[test]
    fn custom_target_spec_identity_hashes_exact_bytes_and_changes_at_same_path() {
        let path = std::env::temp_dir().join(format!(
            "targo-custom-target-{}-{}.json",
            std::process::id(),
            std::thread::current().name().unwrap_or("unnamed")
        ));
        fs::write(&path, b"{\"llvm-target\":\"before\"}\n").expect("write target spec");
        let target = CompileTarget::new(path.to_str().expect("Unicode path"), true)
            .expect("construct custom target");
        let before = exact_unit_compile_target_spec_sha256(CompileKind::Target(target))
            .expect("hash target")
            .expect("custom target digest");
        assert_eq!(before.len(), 64);

        fs::write(&path, b"{\"llvm-target\":\"after\"}\n").expect("mutate target spec");
        let mismatch = ensure_exact_unit_compile_target_spec_unchanged(
            CompileKind::Target(target),
            Some(&before),
        )
        .expect_err("same-path mutation between Work construction and execution must fail");
        assert!(
            mismatch
                .to_string()
                .contains("changed between compiler-work construction"),
            "{mismatch:#}"
        );
        let after = exact_unit_compile_target_spec_sha256(CompileKind::Target(target))
            .expect("rehash target")
            .expect("custom target digest");
        assert_ne!(
            before, after,
            "same target path must not mask changed spec bytes"
        );
        assert_eq!(
            exact_unit_compile_target_spec_sha256(CompileKind::Host).unwrap(),
            None
        );
        fs::write(
            &path,
            b"{\"llvm-target\":\"plugin\",\"llvm-args\":[\"-load=/tmp/attacker.dylib\"]}\n",
        )
        .expect("write LLVM plugin target spec");
        let error = reject_verified_custom_target_llvm_args(CompileKind::Target(target))
            .expect_err("custom target LLVM arguments must remain outside the proof TCB");
        assert!(
            error.to_string().contains("LLVM plugin loading"),
            "{error:#}"
        );
        let _ = fs::remove_file(path);
    }

    #[test]
    fn proof_session_detection_accepts_joined_and_split_nonempty_nonce() {
        assert_eq!(
            trust_verification_session(&flags(&["-Ztrust-verify-session=proof-run-1"])),
            Ok(Some("proof-run-1".to_string()))
        );
        assert_eq!(
            trust_verification_session(&flags(&["-Z", "trust-verify-session=proof-run-2"])),
            Ok(Some("proof-run-2".to_string()))
        );
        assert_eq!(
            trust_verification_session(&flags(&["-Ztrust_verify-session=proof-run-3"])),
            Ok(Some("proof-run-3".to_string()))
        );
        assert!(
            trust_verification_session(&flags(&[
                "-Ztrust-verify-session=proof-run-4",
                "-Ztrust_verify_session=proof-run-4",
            ]))
            .is_err(),
            "rustc-equivalent spellings must not evade duplicate-session rejection"
        );
        assert_eq!(
            trust_verification_session(&flags(&[
                "-Ztrust-verify-output=json",
                "-Ztrust-verify-level=2",
                "-Ztrust-policy=advisory",
            ])),
            Ok(None)
        );
        assert!(trust_verification_session(&flags(&["-Ztrust-verify-session="])).is_err());
        assert!(trust_verification_session(&flags(&["-Ztrust-verify-session= padded"])).is_err());
        // Deleted activators are not protocol authority. Mixed-version callers
        // fail in rustc option parsing instead of receiving authenticated role
        // metadata from Targo.
        assert_eq!(
            trust_verification_session(&flags(&["-Ztrust-verify"])),
            Ok(None)
        );
        assert_eq!(
            trust_verification_session(&flags(&["-Z", "trust-verify-full"])),
            Ok(None)
        );
    }

    #[test]
    fn prepared_execution_never_enters_compilation() {
        assert!(reject_compilation_during_prepared_execution(None).is_ok());
        for marker in ["", "current-session", "stale-session"] {
            assert!(
                reject_compilation_during_prepared_execution(Some(OsStr::new(marker))).is_err()
            );
        }
    }

    #[test]
    fn proof_artifact_root_requires_one_absolute_path() {
        let proof_root = host_absolute_proof_root("proof-run-1");
        let proof_root_option = format!("trust-proof-artifact-root={proof_root}");
        assert_eq!(
            trust_proof_artifact_root(&flags(&["-Z", &proof_root_option])),
            Ok(Some(proof_root))
        );
        let duplicate_one = host_absolute_proof_root_flag("proof-run-duplicate-one");
        let duplicate_two = host_absolute_proof_root("proof-run-duplicate-two");
        let duplicate_two = format!("-Ztrust_proof_artifact_root={duplicate_two}");
        for malformed in [
            flags(&["-Ztrust-proof-artifact-root="]),
            flags(&["-Ztrust-proof-artifact-root=relative"]),
            flags(&[&duplicate_one, &duplicate_two]),
        ] {
            assert!(trust_proof_artifact_root(&malformed).is_err());
        }
    }

    #[test]
    fn verified_marker_requires_a_complete_session_and_artifact_root_pair() {
        let proof_root_flag = host_absolute_proof_root_flag("proof-run-complete");
        for incomplete in [
            flags(&[]),
            flags(&["-Ztrust-verify-session=proof-run"]),
            flags(&[&proof_root_flag]),
        ] {
            assert!(verified_targo_proof_session(&incomplete, &[]).is_err());
        }
        assert_eq!(
            verified_targo_proof_session(
                &flags(&["-Ztrust-verify-session=proof-run", &proof_root_flag]),
                &[],
            ),
            Ok("proof-run".to_string())
        );
    }

    #[test]
    fn certified_monitor_authority_is_nonce_bound_and_selected_unit_scoped() {
        let authority = Some(OsStr::new("proof-run-1"));
        assert_eq!(
            resolve_certified_monitor_unit_session(true, authority, Some("proof-run-1"), true,),
            Ok(Some("proof-run-1".to_string()))
        );
        assert_eq!(
            resolve_certified_monitor_unit_session(true, authority, Some("proof-run-1"), false,),
            Ok(None),
            "authenticated authority must not mark an unrelated dependency"
        );
        assert!(
            resolve_certified_monitor_unit_session(true, authority, Some("proof-run-2"), true,)
                .expect_err("stale authority must fail")
                .contains("does not match")
        );
        assert!(
            resolve_certified_monitor_unit_session(false, authority, Some("proof-run-1"), true)
                .expect_err("unbranded authority must fail")
                .contains("reserved")
        );
    }

    #[test]
    fn certified_monitor_unit_selection_preserves_native_host_library_tests() {
        for mode in [CompileMode::Build, CompileMode::Test] {
            assert!(trust_test_monitor_unit_selected(
                true, mode, false, false, true
            ));
        }
        assert!(trust_test_monitor_unit_selected(
            true,
            CompileMode::Test,
            false,
            true,
            true,
        ));
        assert!(!trust_test_monitor_unit_selected(
            true,
            CompileMode::Build,
            false,
            true,
            true,
        ));
        for excluded in [
            trust_test_monitor_unit_selected(false, CompileMode::Build, false, false, true),
            trust_test_monitor_unit_selected(true, CompileMode::Build, true, false, true),
            trust_test_monitor_unit_selected(true, CompileMode::Build, false, false, false),
            trust_test_monitor_unit_selected(
                true,
                CompileMode::Check { test: true },
                false,
                false,
                true,
            ),
        ] {
            assert!(!excluded);
        }
    }

    #[test]
    fn certified_monitor_runtime_views_are_proof_roots_even_without_exact_cargo_root_identity() {
        assert!(trust_proof_primary_unit(true, false));
        assert!(trust_proof_primary_unit(false, true));
        assert!(!trust_proof_primary_unit(false, false));

        let selected_runtime = trust_unit_protocol_args(
            false,
            trust_proof_primary_unit(false, true),
            true,
            true,
            "selected",
            false,
        );
        assert!(
            !selected_runtime.iter().any(|arg| arg == "trust-verify=off"),
            "monitor-selected normal library must be statically verified: {selected_runtime:?}"
        );
        assert!(
            selected_runtime
                .windows(2)
                .any(|args| args == ["-Z", "trust-verify-crate-role=primary"]),
            "monitor-selected unit must emit primary target evidence: {selected_runtime:?}"
        );
    }

    #[test]
    fn cargo_host_and_target_compile_contexts_remain_explicitly_distinct() {
        assert_eq!(exact_unit_compile_kind(CompileKind::Host), "host");
        let target =
            CompileKind::Target(CompileTarget::new("x86_64-unknown-linux-gnu", false).unwrap());
        assert_eq!(exact_unit_compile_kind(target), "target");
    }

    #[test]
    fn late_rustc_env_cannot_replace_or_add_monitor_marker() {
        let mut selected = ProcessBuilder::new("rustc");
        selected.env("TRUST_TARGO_TEST_MONITOR_SESSION", "proof-run-1");
        validate_certified_monitor_command_env(&selected, Some("proof-run-1"))
            .expect("exact selected-unit marker");
        selected.env("TRUST_TARGO_TEST_MONITOR_SESSION", "forged");
        assert!(
            validate_certified_monitor_command_env(&selected, Some("proof-run-1"))
                .expect_err("late replacement must fail")
                .contains("changed")
        );

        let mut dependency = ProcessBuilder::new("rustc");
        dependency.env_remove("TRUST_TARGO_TEST_MONITOR_SESSION");
        validate_certified_monitor_command_env(&dependency, None)
            .expect("unselected unit marker absent");
        dependency.env("TRUST_TARGO_TEST_MONITOR_SESSION", "proof-run-1");
        assert!(
            validate_certified_monitor_command_env(&dependency, None)
                .expect_err("late dependency injection must fail")
                .contains("unselected")
        );
    }

    #[test]
    fn certified_monitor_unit_rejects_dynamic_rust_linkage() {
        for argument in [
            "-Cprefer-dynamic",
            "-Clink-arg=/tmp/unbound.dylib",
            "-Clinker-plugin-lto=/tmp/evil.dylib",
            "-Cno-prepopulate-passes",
            "-Cpasses=lower-expect",
            "-Cprofile-generate=/tmp/profile",
            "-Cinstrument-coverage",
            "-Ctarget-feature=+crt-static",
            "-Zpre-link-arg=/tmp/evil.o",
            "-Zpre-link-args=/tmp/evil.o",
            "-Zsanitizer=address",
            "-Zinstrument-xray=yes",
            "-Zinstrument-mcount=yes",
            "-Zmir-enable-passes=+GVN",
            "-Zno-leak-check",
            "-Zoffload=Enable",
            "-Zunleash-the-miri-inside-of-you",
            "-Zunsound-mir-opts=yes",
            "--crate-type=dylib",
            "--extern=dep=/tmp/libdep.dylib",
            "--extern=dep=/tmp/libdep.DLL",
            "--extern=dep",
            "--extern=dep=/tmp/renamed-dependency.bin",
            "-lnative",
            "-Lnative=/tmp/unbound",
        ] {
            let mut dynamic = ProcessBuilder::new("rustc");
            dynamic.arg(argument);
            let cargo_compiler_closure =
                CertifiedMonitorCompilerClosure::capture(&dynamic).unwrap();
            reject_certified_monitor_dynamic_rust_linkage(
                &dynamic,
                true,
                &HashSet::default(),
                &cargo_compiler_closure,
            )
            .expect_err("runtime dylib/native closure is not authenticated");
        }
        for arguments in [
            ["-C", "linker-plugin-lto=/tmp/evil.dylib"],
            ["-C", "no-prepopulate-passes"],
            ["-C", "passes=lower-expect"],
            ["-C", "profile-generate=/tmp/profile"],
            ["-C", "instrument-coverage=yes"],
            ["-C", "target-feature=-crt-static"],
            ["-Z", "pre-link-arg=/tmp/evil.o"],
            ["-Z", "pre-link-args=/tmp/evil.o"],
            ["-Z", "sanitizer=address"],
            ["-Z", "instrument-xray=yes"],
            ["-Z", "instrument-mcount=yes"],
            ["-Z", "mir-enable-passes=+GVN"],
            ["-Z", "no-leak-check"],
            ["-Z", "offload=Enable"],
            ["-Z", "unleash-the-miri-inside-of-you"],
            ["-Z", "unsound-mir-opts=yes"],
        ] {
            let mut dynamic = ProcessBuilder::new("rustc");
            dynamic.args(&arguments);
            let cargo_compiler_closure =
                CertifiedMonitorCompilerClosure::capture(&dynamic).unwrap();
            reject_certified_monitor_dynamic_rust_linkage(
                &dynamic,
                true,
                &HashSet::default(),
                &cargo_compiler_closure,
            )
            .expect_err("split runtime/linker option must be rejected");
        }
        let mut dynamic = ProcessBuilder::new("rustc");
        dynamic.arg("-Cprefer-dynamic");
        reject_certified_monitor_dynamic_rust_linkage(
            &dynamic,
            false,
            &HashSet::default(),
            &CertifiedMonitorCompilerClosure::default(),
        )
        .expect("ordinary Cargo lane remains unchanged");
        let mut static_rust = ProcessBuilder::new("rustc");
        static_rust
            .arg("--crate-type=rlib")
            .arg("--extern=dep=/tmp/libdep.rlib")
            .arg("-Ldependency=/tmp/deps");
        let static_closure = CertifiedMonitorCompilerClosure::capture(&static_rust).unwrap();
        reject_certified_monitor_dynamic_rust_linkage(
            &static_rust,
            true,
            &HashSet::default(),
            &static_closure,
        )
        .expect("default static Rust dependency linkage is admissible");

        let proc_macro_path = PathBuf::from("/tmp/libtrust_spec.dylib");
        let mut proc_macro = ProcessBuilder::new("rustc");
        proc_macro.arg(format!("--extern=trust_spec={}", proc_macro_path.display()));
        let proc_macro_closure = CertifiedMonitorCompilerClosure::capture(&proc_macro).unwrap();
        reject_certified_monitor_dynamic_rust_linkage(
            &proc_macro,
            true,
            &[proc_macro_path].into_iter().collect(),
            &proc_macro_closure,
        )
        .expect("the exact audited proc-macro artifact is compile-time TCB, not runtime linkage");

        let mut builtin_proc_macro = ProcessBuilder::new("rustc");
        builtin_proc_macro.arg("--extern").arg("proc_macro");
        let builtin_closure =
            CertifiedMonitorCompilerClosure::capture(&builtin_proc_macro).unwrap();
        reject_certified_monitor_dynamic_rust_linkage(
            &builtin_proc_macro,
            true,
            &HashSet::default(),
            &builtin_closure,
        )
        .expect("proc-macro test units receive rustc's exact builtin proc_macro extern");

        let mut injected = static_rust.clone();
        injected.arg("--extern=evil=/tmp/evil.rlib");
        reject_certified_monitor_dynamic_rust_linkage(
            &injected,
            true,
            &HashSet::default(),
            &static_closure,
        )
        .expect_err("a suffix-compatible extern outside the Cargo graph must fail");
    }

    /// CB5 (2026-09-28): every proc-macro unit in the sealed `targo trust test`
    /// lane, including the audited `trust-spec`, was refused with
    /// "-Cprefer_dynamic is unavailable". Cargo itself added the flag to every
    /// host unit, so the audited proc-macro admission below was unreachable.
    #[test]
    fn the_proc_macro_scan_walks_what_rustc_loads() {
        // PM-1 / B2 (MEASURED 2026-09-28): a facade re-export and a privately
        // deriving dependency both load their macro into the verified rustc.
        let deps = |n: &&str| -> Vec<&str> {
            match *n {
                "facade" => vec!["derive"],
                "private-user" => vec!["initializer", "private-user-build"],
                "private-user-build" => vec!["build-macro"],
                "derive" => vec!["macro-helper-macro", "syn"],
                "lib" => vec!["facade", "private-user"],
                _ => vec![],
            }
        };
        let proc_macro = |n: &&str| {
            matches!(
                *n,
                "derive" | "initializer" | "build-macro" | "macro-helper-macro"
            )
        };
        let build_script = |n: &&str| n.ends_with("-build");
        let mut closure = super::loader_closure(["lib"], deps, build_script, proc_macro);
        closure.sort();
        // `build-macro` runs in the build script's rustc; a proc macro's own
        // dependencies (`macro-helper-macro`, `syn`) are never resolved by rustc.
        assert_eq!(
            closure,
            ["derive", "facade", "initializer", "lib", "private-user"]
        );
        let macros: Vec<_> = closure.iter().filter(|n| proc_macro(n)).collect();
        assert_eq!(macros, [&"derive", &"initializer"]);
    }

    #[test]
    fn verified_proc_macro_units_are_compiled_with_a_static_rust_closure() {
        // Every input combination. The oracle is upstream Cargo's expression,
        // copied verbatim from the `build_base_args` line this helper replaced.
        let upstream = |for_host: bool, custom_build: bool, contains_dylib: bool, primary: bool| {
            (for_host && !custom_build) || (contains_dylib && !primary)
        };
        for bits in 0u8..64 {
            let bit = |index: u8| bits & (1 << index) != 0;
            let (verified, for_host, custom_build) = (bit(0), bit(1), bit(2));
            let (proc_macro, contains_dylib, primary) = (bit(3), bit(4), bit(5));
            let actual = cargo_prefers_dynamic_rust_linkage(
                verified,
                for_host,
                custom_build,
                proc_macro,
                contains_dylib,
                primary,
            );
            let expected = if verified && proc_macro {
                // Verified lanes: the host-unit term never applies to a
                // proc-macro unit, in Build or Test mode. The dylib term is
                // upstream's, so a graph with a dylib keeps the flag and stays
                // refused by the monitor's crate-type check.
                contains_dylib && !primary
            } else {
                // The unverified lane, and every non-proc-macro unit in a
                // verified lane, keep upstream's argv exactly.
                upstream(for_host, custom_build, contains_dylib, primary)
            };
            assert_eq!(
                actual, expected,
                "verified={verified} for_host={for_host} custom_build={custom_build} \
                 proc_macro={proc_macro} contains_dylib={contains_dylib} primary={primary}"
            );
        }
        // The two shapes Cargo actually produces for a proc-macro unit
        // (`for_host`, not a build script, no dylib in the graph), primary or
        // not: upstream (and the unverified lane) add the flag, verified lanes
        // do not.
        for primary in [false, true] {
            assert!(cargo_prefers_dynamic_rust_linkage(
                false, true, false, true, false, primary
            ));
            assert!(!cargo_prefers_dynamic_rust_linkage(
                true, true, false, true, false, primary
            ));
        }

        // The Cargo-shaped argv of the audited provider unit under the sealed
        // lane. Before the fix it carried `-C prefer-dynamic` and was refused.
        let mut audited_unit = ProcessBuilder::new("rustc");
        audited_unit
            .arg("--crate-name")
            .arg("trust")
            .arg("--crate-type")
            .arg("proc-macro")
            .arg("--emit=dep-info,link")
            .arg("--extern")
            .arg("proc_macro")
            .arg("-L")
            .arg("dependency=/cargo/deps");
        let closure = CertifiedMonitorCompilerClosure::capture(&audited_unit).unwrap();
        reject_certified_monitor_dynamic_rust_linkage_with_audited_proc_macro(
            &audited_unit,
            true,
            &HashSet::default(),
            &closure,
            true,
        )
        .expect("the audited proc-macro unit compiles in the sealed lane");

        let mut upstream_argv = audited_unit.clone();
        upstream_argv.arg("-C").arg("prefer-dynamic");
        let error = reject_certified_monitor_dynamic_rust_linkage_with_audited_proc_macro(
            &upstream_argv,
            true,
            &HashSet::default(),
            &closure,
            true,
        )
        .expect_err("a caller-selected -C prefer-dynamic stays refused");
        assert!(error.contains("-Cprefer_dynamic is unavailable"), "{error}");

        reject_certified_monitor_dynamic_rust_linkage_with_audited_proc_macro(
            &audited_unit,
            true,
            &HashSet::default(),
            &closure,
            false,
        )
        .expect_err("an unaudited proc-macro unit stays refused by crate type");
    }

    #[test]
    fn certified_monitor_pins_cargo_compiler_closure_arguments() {
        let mut cargo = ProcessBuilder::new("rustc");
        cargo
            .arg("-Ldependency=/cargo/deps")
            .arg("--target=aarch64-apple-darwin")
            .arg("--sysroot")
            .arg("/toolchain")
            .arg("--emit=dep-info,link")
            .arg("--out-dir")
            .arg("/cargo/out")
            .arg("-Cextra-filename=-cargo")
            .arg("-C")
            .arg("incremental=/cargo/incremental");
        let authenticated = CertifiedMonitorCompilerClosure::capture(&cargo).unwrap();

        for injected in [
            vec!["-Ldependency=/attacker"],
            vec!["-L", "dependency=/attacker"],
            vec!["--target=attacker.json"],
            vec!["--target", "attacker.json"],
            vec!["--sysroot=/attacker"],
            vec!["--sysroot", "/attacker"],
            vec!["--emit=link=/toolchain/bin/targo"],
            vec!["--emit", "link=/toolchain/bin/targo"],
            vec!["--emit=dep-info,link"],
            vec!["-o/toolchain/bin/targo"],
            vec!["-o", "/toolchain/bin/targo"],
            vec!["--out-dir=/toolchain/bin"],
            vec!["--out-dir", "/toolchain/bin"],
            vec!["--out-dir", "/cargo/out"],
            vec!["-Cextra-filename=../../toolchain/bin/targo"],
            vec!["-C", "extra-filename=../../toolchain/bin/targo"],
            vec!["-Cextra-filename=-cargo"],
            vec!["-Cincremental=/toolchain/incremental"],
            vec!["-C", "incremental=/toolchain/incremental"],
            vec!["-C", "incremental=/cargo/incremental"],
        ] {
            let mut changed = cargo.clone();
            changed.args(&injected);
            reject_certified_monitor_dynamic_rust_linkage(
                &changed,
                true,
                &HashSet::default(),
                &authenticated,
            )
            .expect_err("caller must not change Cargo's authenticated compiler closure");
        }

        reject_certified_monitor_dynamic_rust_linkage(
            &cargo,
            true,
            &HashSet::default(),
            &authenticated,
        )
        .expect("the exact Cargo-generated dependency/target/sysroot/output closure is admissible");
    }

    #[test]
    fn certified_monitor_rejects_presnapshot_closure_controls_in_every_graph_profile() {
        for arguments in [
            vec!["--extern=evil=/tmp/evil.rlib"],
            vec!["--extern", "evil=/tmp/evil.rlib"],
            vec!["-Ldependency=/tmp/evil"],
            vec!["-L", "dependency=/tmp/evil"],
            vec!["--target=/tmp/evil.json"],
            vec!["--target", "/tmp/evil.json"],
            vec!["--sysroot=/tmp/evil"],
            vec!["--sysroot", "/tmp/evil"],
            vec!["--emit=link=/toolchain/bin/targo"],
            vec!["--emit", "link=/toolchain/bin/targo"],
            vec!["-o/toolchain/bin/targo"],
            vec!["-o", "/toolchain/bin/targo"],
            vec!["--out-dir=/toolchain/bin"],
            vec!["--out-dir", "/toolchain/bin"],
            vec!["-Cextra-filename=../../toolchain/bin/targo"],
            vec!["-C", "extra-filename=../../toolchain/bin/targo"],
            vec!["-Cincremental=/toolchain/incremental"],
            vec!["-C", "incremental=/toolchain/incremental"],
        ] {
            for source in [
                "selected-package profile rustflags",
                "dependency profile rustflags",
            ] {
                reject_certified_monitor_presnapshot_closure_controls(true, &arguments, source)
                    .expect_err(
                        "pre-snapshot caller closure controls in any graph unit must never be authenticated as Cargo output",
                    );
            }
        }
        reject_certified_monitor_presnapshot_closure_controls(
            false,
            &["--emit=link=/ordinary/cargo-rustc"],
            "profile rustflags",
        )
        .expect("ordinary Cargo output behavior remains unchanged");
    }

    #[test]
    fn certified_monitor_unit_rejects_dynamic_cargo_graph_dependencies() {
        let error = reject_certified_monitor_dynamic_unit_dependencies(
            true,
            ["dynamic@1.0.0::dynamic (dylib)".to_string()],
        )
        .expect_err("runtime dynamic Cargo units are not authenticated");
        assert!(error.contains("dynamic@1.0.0::dynamic (dylib)"), "{error}");
        reject_certified_monitor_dynamic_unit_dependencies(true, std::iter::empty())
            .expect("a static Cargo graph is admissible");
        reject_certified_monitor_dynamic_unit_dependencies(
            false,
            ["ordinary@1.0.0::ordinary (dylib)".to_string()],
        )
        .expect("ordinary Cargo behavior remains unchanged");
    }

    #[test]
    fn certified_monitor_unit_rejects_custom_targets_and_seals_linker_path() {
        let directory = tempfile::tempdir().unwrap();
        let target = directory.path().join("hostile.json");
        fs::write(&target, b"{}").unwrap();
        let custom = CompileKind::Target(
            CompileTarget::new(target.to_str().unwrap(), true).expect("custom target identity"),
        );
        let error = reject_certified_monitor_custom_target(true, custom)
            .expect_err("custom target linker controls are outside the audited TCB");
        assert!(error.contains("custom target specification"), "{error}");
        reject_certified_monitor_custom_target(false, custom)
            .expect("ordinary Cargo custom targets remain unchanged");
        reject_certified_monitor_custom_target(true, CompileKind::Host)
            .expect("the built-in host target is admissible");

        let mut command = ProcessBuilder::new("rustc");
        command
            .env("PATH", "/tmp/attacker-first")
            .env("LD_PRELOAD", "/tmp/forge-transport.so")
            .env("TRUST_FUTURE_AUTHORITY", "forged")
            .env("CCC_OVERRIDE_OPTIONS", "+-Wl,/tmp/evil.o")
            .env("CLANG_CONFIG_FILE_USER_DIR", "/tmp/attacker-config")
            .env("SDKROOT", "/tmp/attacker-sdk");
        seal_certified_monitor_compiler_environment(&mut command, Some("monitor-session")).unwrap();
        #[cfg(unix)]
        assert_eq!(
            command.get_env("PATH").as_deref(),
            Some(OsStr::new("/usr/bin:/bin"))
        );
        for name in [
            "LD_PRELOAD",
            "TRUST_FUTURE_AUTHORITY",
            "CCC_OVERRIDE_OPTIONS",
            "CLANG_CONFIG_FILE_USER_DIR",
            "SDKROOT",
        ] {
            assert_eq!(command.get_env(name), None, "{name}");
        }
        #[cfg(unix)]
        assert_eq!(
            command.get_env("CLANG_NO_DEFAULT_CONFIG").as_deref(),
            Some(OsStr::new("1"))
        );
        assert_eq!(
            command.get_env(TRUST_TARGO_TEST_MONITOR_SESSION).as_deref(),
            Some(OsStr::new("monitor-session"))
        );

        let mut ordinary = ProcessBuilder::new("rustc");
        ordinary.env("PATH", "/tmp/ordinary");
        seal_certified_monitor_compiler_environment(&mut ordinary, None).unwrap();
        assert_eq!(
            ordinary.get_env("PATH").as_deref(),
            Some(OsStr::new("/tmp/ordinary"))
        );

        let error = reject_certified_monitor_custom_build_unit(
            true,
            true,
            "fixture@0.1.0::build-script-build",
        )
        .expect_err("arbitrary build-script processes are outside the execution TCB");
        assert!(error.contains("background side effects"), "{error}");
        reject_certified_monitor_custom_build_unit(false, true, "ordinary@0.1.0::build")
            .expect("ordinary Cargo build scripts remain unchanged");
    }

    /// D2 (2026-09-28): the certified-monitor seal and the verified exec-edge
    /// validator must AGREE on the same command. Before the fix the seal
    /// deleted every loader variable and the validator, which runs right after
    /// it, refused the command for missing its authenticated closure — so every
    /// unit of an evidence-grade `targo trust test` failed. This drives the
    /// real sequence: capture from the authenticated compiler, seal a command
    /// carrying hostile late loader values, then validate with the exec-edge
    /// predicate against the same startup closure.
    #[cfg(unix)]
    #[test]
    fn certified_monitor_seal_and_exec_edge_validator_agree() {
        use crate::util::process_authority::{
            caller_clean_fixture_root, caller_owned_toolchain_fixture,
            validate_command_runtime_library_search,
        };

        let Some(root) = caller_clean_fixture_root() else {
            eprintln!("skipping: no caller-clean fixture root on this host");
            return;
        };
        let (compiler, lib) = caller_owned_toolchain_fixture(&root, "d2-seal-agreement-stage2");
        std::fs::write(lib.join("librustc_driver-fixture.dylib"), b"fixture").unwrap();
        let startup_closure = vec![lib.canonicalize().unwrap()];
        let search = cargo_util::paths::dylib_path_envvar();

        let seal = CertifiedMonitorSeal::capture_for_test(true, true, &compiler)
            .expect("the authenticated closure derives");
        let authenticated = seal
            .authenticated_loader_search()
            .expect("a monitor-lane command with a non-empty closure gets a value")
            .to_os_string();
        let mut expected = startup_closure.clone();
        if cfg!(target_os = "macos") {
            expected.push(std::path::PathBuf::from("/usr/lib"));
        }
        assert_eq!(
            std::env::split_paths(&authenticated).collect::<Vec<_>>(),
            expected,
            "exactly the authenticated closure (+ /usr/lib on macOS), no Cargo-owned deps dir"
        );

        let hostile = [
            (search, "/tmp/attacker-late-overlay"),
            ("DYLD_INSERT_LIBRARIES", "/tmp/evil.dylib"),
            ("DYLD_LIBRARY_PATH", "/tmp/evil-first"),
            ("DYLD_FRAMEWORK_PATH", "/tmp/evil-frameworks"),
            ("LD_PRELOAD", "/tmp/evil.so"),
            ("LD_AUDIT", "/tmp/evil-audit.so"),
        ];
        let mut command = ProcessBuilder::new(&compiler);
        for (name, value) in hostile {
            command.env(name, value);
        }
        // The validator is not a rubber stamp: the hostile late value fails it.
        let error = validate_command_runtime_library_search(&command, &startup_closure)
            .expect_err("a late overlay of the search variable is refused");
        assert!(
            format!("{error:#}").contains("no longer begins with the exact authenticated"),
            "{error:#}"
        );

        seal_certified_monitor_graph_compiler_environment(
            &mut command,
            &seal,
            Some("monitor-session"),
        )
        .unwrap();
        validate_command_runtime_library_search(&command, &startup_closure).unwrap_or_else(
            |error| panic!("the sealed command must pass the exec-edge validator: {error:#}"),
        );
        assert_eq!(
            command.get_env(search).as_deref(),
            Some(authenticated.as_os_str()),
            "the late overlay is replaced by the pre-seal authenticated value"
        );
        for (name, _) in hostile {
            if name != search {
                assert_eq!(command.get_env(name), None, "{name} survived the seal");
            }
        }

        // Without the reinstall (the pre-fix seal: an enforced seal carrying
        // no loader value, which production code can no longer construct in
        // the verified lane), the same validator refuses the sealed command:
        // this is the D2 failure, reproduced in-process.
        let unfixed_seal = CertifiedMonitorSeal::capture_for_test(true, false, &compiler)
            .expect("an enforced seal without a verified exec edge");
        assert!(unfixed_seal.is_enforced());
        assert_eq!(unfixed_seal.authenticated_loader_search(), None);
        let mut unfixed = ProcessBuilder::new(&compiler);
        unfixed.env(search, "/tmp/attacker-late-overlay");
        seal_certified_monitor_graph_compiler_environment(
            &mut unfixed,
            &unfixed_seal,
            Some("monitor-session"),
        )
        .unwrap();
        let error = validate_command_runtime_library_search(&unfixed, &startup_closure)
            .expect_err("a sealed command with no reinstalled closure is refused");
        assert!(
            format!("{error:#}").contains("missing its authenticated"),
            "{error:#}"
        );

        // Outside the monitor lane the seal is a no-op and installs nothing.
        let ordinary_seal = CertifiedMonitorSeal::capture_for_test(false, true, &compiler)
            .expect("an unenforced seal");
        assert!(!ordinary_seal.is_enforced());
        let mut ordinary = ProcessBuilder::new(&compiler);
        seal_certified_monitor_graph_compiler_environment(&mut ordinary, &ordinary_seal, None)
            .unwrap();
        assert_eq!(ordinary.get_envs().get(search), None);
        let _ = std::fs::remove_dir_all(root.join("d2-seal-agreement-stage2"));
    }

    #[cfg(unix)]
    #[test]
    fn certified_monitor_seal_restores_only_captured_memory_authority() {
        use super::trust_certified_monitor_seal::MEMORY_SOCKET_ENV;
        use crate::util::process_authority::{
            caller_clean_fixture_root, caller_owned_toolchain_fixture,
        };

        let Some(root) = caller_clean_fixture_root() else {
            return;
        };
        let (compiler, _) = caller_owned_toolchain_fixture(&root, "sealed-memory-authority");
        let socket = OsStr::new("/trusted/coordinator.sock");
        let seal =
            CertifiedMonitorSeal::capture_for_test_with_memory(true, true, &compiler, Some(socket))
                .unwrap();
        let mut command = ProcessBuilder::new(&compiler);
        command
            .env(MEMORY_SOCKET_ENV, "/attacker/coordinator.sock")
            .env("TRUST_MEMORY_JOBSERVER", "/attacker/tokens")
            .env("TRUSTD_DISABLE", "1");
        seal_certified_monitor_graph_compiler_environment(
            &mut command,
            &seal,
            Some("monitor-session"),
        )
        .unwrap();
        assert_eq!(command.get_env(MEMORY_SOCKET_ENV).as_deref(), Some(socket));
        assert_eq!(command.get_env("TRUST_MEMORY_JOBSERVER"), None);
        assert_eq!(command.get_env("TRUSTD_DISABLE"), None);

        // Reapplying the final exec-edge seal also repairs a late removal;
        // neither an overlay nor its absence can select another authority.
        command.env_remove(MEMORY_SOCKET_ENV);
        seal_certified_monitor_graph_compiler_environment(
            &mut command,
            &seal,
            Some("monitor-session"),
        )
        .unwrap();
        assert_eq!(command.get_env(MEMORY_SOCKET_ENV).as_deref(), Some(socket));
        for invalid in [
            None,
            Some(OsStr::new("relative.sock")),
            Some(OsStr::new("")),
        ] {
            assert!(
                CertifiedMonitorSeal::capture_for_test_with_memory(true, true, &compiler, invalid,)
                    .is_err()
            );
        }
        let _ = std::fs::remove_dir_all(root.join("sealed-memory-authority"));
    }

    /// D2 wiring: the capture `prepare_rustc` hands to both seals carries a
    /// loader value whenever the seal is active and the exec-edge validator
    /// will run — a regression that returned `None` there reintroduces D2 —
    /// and none wherever there is no seal or no validator to satisfy. The seal
    /// call sites take a `CertifiedMonitorSeal`, so they cannot substitute a
    /// missing value for the capture (a compile error, not a test).
    #[cfg(unix)]
    #[test]
    fn certified_monitor_loader_search_capture_is_some_in_the_monitor_lane() {
        use crate::util::process_authority::{
            caller_clean_fixture_root, caller_owned_toolchain_fixture,
        };

        let Some(root) = caller_clean_fixture_root() else {
            eprintln!("skipping: no caller-clean fixture root on this host");
            return;
        };
        let (compiler, lib) = caller_owned_toolchain_fixture(&root, "d2-seal-capture-stage2");
        let capture = |enforced, verified| {
            let seal = CertifiedMonitorSeal::capture_for_test(enforced, verified, &compiler)
                .expect("capture");
            assert_eq!(
                seal.is_enforced(),
                enforced,
                "the seal keeps its lane decision"
            );
            seal.authenticated_loader_search().map(OsStr::to_os_string)
        };
        let monitor = capture(true, true).expect("monitor lane + verified exec edge captures");
        assert!(
            std::env::split_paths(&monitor).any(|path| path == lib.canonicalize().unwrap()),
            "{monitor:?}"
        );
        assert_eq!(capture(false, true), None, "advisory lane: the seal is off");
        assert_eq!(
            capture(true, false),
            None,
            "unverified: the validator is off"
        );
        assert!(
            CertifiedMonitorSeal::capture_for_test(true, true, Path::new("bin/trustc")).is_err(),
            "a relative compiler path cannot name the authenticated toolchain"
        );
        let _ = std::fs::remove_dir_all(root.join("d2-seal-capture-stage2"));
    }

    #[test]
    fn caller_supplied_unit_metadata_is_detected_in_both_forms() {
        // PM-1: a caller cannot widen or forge the crate-loader proc-macro boundary.
        assert_eq!(
            caller_supplied_trust_unit_metadata(&flags(&[
                "-Ztrust-audited-proc-macro=/tmp/libforged.dylib",
            ])),
            Some("trust-audited-proc-macro")
        );
        assert_eq!(
            caller_supplied_trust_unit_metadata(&flags(&["-Z", "trust-proc-macro-boundary"])),
            Some("trust-proc-macro-boundary")
        );
        assert_eq!(
            caller_supplied_trust_unit_metadata(&flags(&["-Ztrust-verify-crate-role=primary",])),
            Some("trust-verify-crate-role")
        );
        assert_eq!(
            caller_supplied_trust_unit_metadata(&flags(&[
                "-Z",
                "trust-verify-package-name=forged",
            ])),
            Some("trust-verify-package-name")
        );
        assert_eq!(
            caller_supplied_trust_unit_metadata(&flags(&["-Ztrust_verify-crate_role=primary",])),
            Some("trust-verify-crate-role")
        );
        assert_eq!(
            caller_supplied_trust_unit_metadata(&flags(&[
                "-Z",
                "trust_verify_package_name=forged",
            ])),
            Some("trust-verify-package-name")
        );
        assert_eq!(
            caller_supplied_trust_unit_metadata(&flags(&[
                "-Ztrust-verify-target-spec-sha256=aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
            ])),
            Some("trust-verify-target-spec-sha256")
        );
        assert_eq!(
            caller_supplied_trust_unit_metadata(&flags(&["-Ztrust-verify"])),
            None
        );
    }

    #[test]
    fn authenticated_targo_rejects_every_build_script_process_authority_channel() {
        for name in [
            "LD_PRELOAD",
            "ld_preload",
            "TRUST_NO_VERIFY",
            "TRUST_TARGO_PAIRED_COMPILER_PROFILE",
            "TRUST_TARGO_NESTED_UNVERIFIED_BROKER",
            "TRUST_TARGO_NESTED_UNVERIFIED_ENDPOINT",
            "trust_no_verify",
            "RUSTFLAGS",
            "rustdocflags_for_target",
            "RUSTC_OVERRIDE_VERSION_STRING",
            "rustc_force_rustc_version",
            "RUST_TARGET_PATH",
            "rust_target_path",
            "__CARGO_FIX_YOLO",
            "__cargo_fix_broken_code",
            "CARGO_FIX_MAX_RETRIES",
            TIPPY_ENCODED_ARGS_ENV,
            "tippy_encoded_args",
            CLIPPY_ARGS_ENV,
            "clippy_args",
            CARGO_PRIMARY_PACKAGE_ENV,
            "cargo_primary_package",
            "CARGO",
            "cargo",
            "SAFE_λ",
        ] {
            let mut command = ProcessBuilder::new("trustc");
            let error = apply_build_script_env(&mut command, true, name, "attacker")
                .expect_err("authenticated Targo authority injection must fail closed");
            assert!(error.to_string().contains(name), "{name}: {error:#}");
            assert!(
                !command.get_envs().contains_key(name),
                "rejection must precede mutation for {name}"
            );
        }

        let mut authenticated = ProcessBuilder::new("trustc");
        apply_build_script_env(&mut authenticated, true, "SAFE_ENV", "retained")
            .expect("non-authority build-script environment remains supported");
        assert_eq!(authenticated.get_env("SAFE_ENV"), Some("retained".into()));

        // Ordinary Cargo preserves upstream behavior, including names that
        // only become authority inside the authenticated Targo boundary.
        let mut ordinary = ProcessBuilder::new("rustc");
        apply_build_script_env(&mut ordinary, false, "clippy_args", "ordinary")
            .expect("ordinary Cargo accepts the historical channel");
        apply_build_script_env(&mut ordinary, false, "SAFE_λ", "ordinary-unicode")
            .expect("ordinary Cargo accepts platform-native Unicode names");
        apply_build_script_env(&mut ordinary, false, "CARGO", "ordinary-cargo")
            .expect("ordinary Cargo retains its historical CARGO overlay behavior");
        apply_build_script_env(&mut ordinary, false, "RUST_TARGET_PATH", "ordinary-targets")
            .expect("ordinary Cargo retains named custom-target build-script compatibility");
        assert_eq!(ordinary.get_env("clippy_args"), Some("ordinary".into()));
        assert_eq!(ordinary.get_env("SAFE_λ"), Some("ordinary-unicode".into()));
        assert_eq!(ordinary.get_env("CARGO"), Some("ordinary-cargo".into()));
        assert_eq!(
            ordinary.get_env("RUST_TARGET_PATH"),
            Some("ordinary-targets".into())
        );
    }

    #[test]
    fn primary_override_preserves_fix_wrapper_tippy_and_primary_state() {
        let encoded = encode_args(false, &["--warn=valid"]);
        let authoritative = ReservedTippyArgs::capture_if_present(
            |name| match name {
                TIPPY_ENCODED_ARGS_ENV => Some(encoded.clone().into()),
                CLIPPY_ARGS_ENV => Some("--warn=valid__CLIPPY_HACKERY__".into()),
                _ => None,
            },
            "test process",
        )
        .expect("both protected channels are well formed")
        .expect("both protected channels are present");
        let role = RustcProcessRole::PrimaryOverride {
            downstream_workspace_wrapper: true,
        };
        let mut command = ProcessBuilder::new("/selected/bin/targo-fix-proxy");
        command
            .env(crate::CARGO_ENV, "/selected/bin/targo")
            .env(CARGO_PRIMARY_PACKAGE_ENV, "1")
            .env(FIX_ENV_INTERNAL, "127.0.0.1:1234")
            .env(BROKEN_CODE_ENV_INTERNAL, "1")
            .env(FIX_YOLO_ENV_INTERNAL, "1")
            .env(RUSTC_WORKSPACE_WRAPPER_ENV, "/selected/bin/tippy-driver");
        command
            .env(TIPPY_ENCODED_ARGS_ENV, &authoritative.encoded)
            .env(CLIPPY_ARGS_ENV, &authoritative.legacy);
        let process_authority = AuthenticatedTargoProcessAuthority::capture_if_authenticated(
            &command, true, role, true,
        )
        .expect("complete proxy authority is valid")
        .expect("authenticated Targo captures authority");
        apply_build_script_env(&mut command, true, "SAFE_ENV", "retained")
            .expect("safe build-script environment remains supported");
        process_authority
            .validate_final_overlay(&command)
            .expect("safe overlay preserves every authority channel");

        for (name, value) in [
            (BROKEN_CODE_ENV_INTERNAL, "forged-broken"),
            (FIX_YOLO_ENV_INTERNAL, "forged-yolo"),
            (RUSTC_WORKSPACE_WRAPPER_ENV, "/attacker/wrapper"),
            (CLIPPY_ARGS_ENV, "--sysroot=/attacker"),
            (CARGO_PRIMARY_PACKAGE_ENV, "forged-primary"),
            (crate::CARGO_ENV, "/attacker/cargo"),
        ] {
            let mut forged = command.clone();
            forged.env(name, value);
            let error = process_authority
                .validate_final_overlay(&forged)
                .expect_err("final overlay validation must detect authority mutation");
            assert!(error.to_string().contains(name) || name == CLIPPY_ARGS_ENV);
        }

        // Ambient protocol-looking variables do not brand an unrelated
        // compiler. This keeps direct authenticated Targo compatible with a
        // user's shell environment while reserving fail-closed handling for
        // the actual workspace wrapper.
        let mut unrelated_compiler = ProcessBuilder::new("/selected/bin/tippy-driver");
        unrelated_compiler
            .env(CLIPPY_ARGS_ENV, "ambient-legacy-only")
            .env_remove(TIPPY_ENCODED_ARGS_ENV);
        assert_eq!(
            snapshot_reserved_tippy_args_for_invocation(
                &unrelated_compiler,
                true,
                Some(RustcProcessRole::Compiler),
            )
            .expect("unrelated compilers ignore ambient Tippy channels"),
            None
        );
        assert_eq!(
            snapshot_reserved_tippy_args_for_invocation(
                &command,
                true,
                Some(RustcProcessRole::WorkspaceWrapper),
            )
            .expect("the complete wrapper protocol is valid"),
            Some(authoritative.clone())
        );
        assert_eq!(
            snapshot_reserved_tippy_args_for_invocation(
                &command,
                false,
                Some(RustcProcessRole::WorkspaceWrapper),
            )
            .expect("ordinary Cargo does not claim Tippy protocol authority"),
            None
        );
        assert_eq!(
            snapshot_reserved_tippy_args_for_invocation(&command, true, Some(role),)
                .expect("the primary override retains its downstream wrapper protocol"),
            Some(authoritative.clone())
        );

        let mut direct_fix = ProcessBuilder::new("/selected/bin/targo-fix-proxy");
        direct_fix
            .env(crate::CARGO_ENV, "/selected/bin/targo")
            .env(CARGO_PRIMARY_PACKAGE_ENV, "1")
            .env(FIX_ENV_INTERNAL, "127.0.0.1:1234")
            .env_remove(RUSTC_WORKSPACE_WRAPPER_ENV);
        AuthenticatedTargoProcessAuthority::capture_if_authenticated(
            &direct_fix,
            true,
            RustcProcessRole::PrimaryOverride {
                downstream_workspace_wrapper: false,
            },
            true,
        )
        .expect("a direct fix proxy has canonical absent-wrapper state")
        .expect("authenticated Targo captures direct proxy authority");

        let mut plain_wrapper = ProcessBuilder::new("/selected/bin/plain-workspace-wrapper");
        plain_wrapper
            .env(crate::CARGO_ENV, "/selected/bin/targo")
            .env(CARGO_PRIMARY_PACKAGE_ENV, "1")
            .env_remove(TIPPY_ENCODED_ARGS_ENV)
            .env_remove(CLIPPY_ARGS_ENV);
        let absent_tippy_authority = AuthenticatedTargoProcessAuthority::capture_if_authenticated(
            &plain_wrapper,
            true,
            RustcProcessRole::WorkspaceWrapper,
            true,
        )
        .expect("a non-Tippy workspace wrapper has canonical absent channels")
        .expect("authenticated Targo captures absent Tippy state");
        plain_wrapper
            .env(TIPPY_ENCODED_ARGS_ENV, &authoritative.encoded)
            .env(CLIPPY_ARGS_ENV, &authoritative.legacy);
        assert!(
            absent_tippy_authority
                .validate_final_overlay(&plain_wrapper)
                .is_err(),
            "the final overlay cannot introduce Tippy authority into another wrapper"
        );

        let mut non_primary = ProcessBuilder::new("trustc");
        non_primary
            .env(crate::CARGO_ENV, "/selected/bin/targo")
            .env_remove(CARGO_PRIMARY_PACKAGE_ENV);
        let non_primary_authority = AuthenticatedTargoProcessAuthority::capture_if_authenticated(
            &non_primary,
            true,
            RustcProcessRole::Compiler,
            false,
        )
        .expect("canonical non-primary state is valid")
        .expect("authenticated Targo captures primary-package state");
        non_primary.env(CARGO_PRIMARY_PACKAGE_ENV, "1");
        assert!(
            non_primary_authority
                .validate_final_overlay(&non_primary)
                .is_err(),
            "a dependency cannot become a Tippy primary package"
        );

        let mut incomplete_wrapper = ProcessBuilder::new("/selected/bin/tippy-driver");
        incomplete_wrapper
            .env(TIPPY_ENCODED_ARGS_ENV, encode_args::<&str>(false, &[]))
            .env_remove(CLIPPY_ARGS_ENV);
        assert!(
            snapshot_reserved_tippy_args_for_invocation(
                &incomplete_wrapper,
                true,
                Some(RustcProcessRole::WorkspaceWrapper),
            )
            .is_err(),
            "the actual wrapper must reject a partial protected protocol"
        );

        assert_eq!(
            ReservedTippyArgs::capture_if_present(|_| None, "test process")
                .expect("two absent channels identify a non-Tippy process"),
            None
        );
        let missing_canonical = ReservedTippyArgs::capture_if_present(
            |name| (name == CLIPPY_ARGS_ENV).then(|| "legacy".into()),
            "test process",
        )
        .expect_err("one protected channel is malformed")
        .to_string();
        assert!(missing_canonical.contains(TIPPY_ENCODED_ARGS_ENV));
        let missing_legacy = ReservedTippyArgs::capture_if_present(
            |name| (name == TIPPY_ENCODED_ARGS_ENV).then(|| encode_args::<&str>(false, &[]).into()),
            "test process",
        )
        .expect_err("one protected channel is malformed")
        .to_string();
        assert!(missing_legacy.contains(CLIPPY_ARGS_ENV));
    }

    #[test]
    fn verified_compiler_argv_rejects_argfiles_and_semantic_separator_from_every_source() {
        for forbidden in ["@policy.args", "@shell:policy.args", "@", "--"] {
            let mut command = ProcessBuilder::new("trustc");
            command.args(&["--crate-name", "selected", forbidden]);
            let error = validate_verified_targo_compiler_argument_boundaries(
                &command,
                &boundary_policy(&command),
            )
            .expect_err("uninspectable compiler argv must fail closed");
            assert!(
                error.contains("argfile") || error.contains("semantic `--` separator"),
                "{forbidden}: {error}"
            );
        }

        let mut explicit = ProcessBuilder::new("trustc");
        explicit.args(&[
            "--crate-name",
            "selected",
            "-Z",
            "trust-verify-session=proof",
        ]);
        validate_verified_targo_compiler_argument_boundaries(
            &explicit,
            &boundary_policy(&explicit),
        )
        .expect("explicit Unicode compiler argv is inspectable");
    }

    #[test]
    fn verified_compiler_argv_rejects_retired_valtree_limit_from_every_source_and_identity() {
        for (source, retired) in [
            (
                "unit/config/ambient joined",
                vec!["-Zvaltree-node-limit=200000"],
            ),
            (
                "unit/config/ambient split",
                vec!["-Z", "valtree-node-limit=200000"],
            ),
            ("profile joined", vec!["-Zvaltree-node-limit=200000"]),
            (
                "extra compiler args split",
                vec!["-Z", "valtree-node-limit=200000"],
            ),
            (
                "rustc-equivalent underscore joined",
                vec!["-Zvaltree_node_limit=200000"],
            ),
            (
                "rustc-equivalent mixed split",
                vec!["-Z", "valtree_node-limit=200000"],
            ),
        ] {
            let mut command = ProcessBuilder::new("trustc");
            // A caller-selected package can forge every descriptive identity
            // string. The resource policy therefore depends only on the final
            // compiler argv, never package/workspace/primary classification.
            command.args(&[
                "--crate-name",
                "trust_ir",
                "-Z",
                "trust-verify-crate-role=primary",
                "-Z",
                "trust-verify-package-name=trust-ir",
            ]);
            command.args(&retired);
            let error = validate_verified_targo_compiler_argument_boundaries(
                &command,
                &boundary_policy(&command),
            )
            .expect_err("retired valtree limit must fail closed for every argument source");
            assert!(
                error.contains("retired `-Zvaltree-node-limit`"),
                "{source}: {error}"
            );
            assert!(
                error.contains("fixed valtree resource limit"),
                "{source}: {error}"
            );
        }

        let mut unrelated = ProcessBuilder::new("trustc");
        unrelated.args(&[
            "--cfg",
            "valtree-node-limit=metadata-only",
            "-C",
            "metadata=valtree-node-limit=200000",
        ]);
        validate_verified_targo_compiler_argument_boundaries(
            &unrelated,
            &boundary_policy(&unrelated),
        )
        .expect("only the retired rustc -Z option is reserved");
    }

    #[test]
    fn verifier_export_root_preserves_both_existing_protocol_vectors() {
        let root = flags(&["-Ztrust-proof-artifact-root=/owned/run"]);
        assert_eq!(
            resolved_trust_proof_artifact_root(&root, &[])
                .unwrap()
                .as_deref(),
            Some("/owned/run")
        );
        assert_eq!(
            resolved_trust_proof_artifact_root(&[], &root)
                .unwrap()
                .as_deref(),
            Some("/owned/run")
        );
        assert_eq!(resolved_trust_proof_artifact_root(&[], &[]).unwrap(), None);
        assert!(resolved_trust_proof_artifact_root(&root, &root).is_err());
        assert!(
            resolved_trust_proof_artifact_root(
                &root,
                &flags(&["-Ztrust-proof-artifact-root=/other/run"])
            )
            .is_err()
        );
    }

    #[test]
    fn verified_policy_binds_distinct_owned_export_sinks_without_parallel_authority() {
        let owned = flags(&[
            "-Ztrust-dump=mir:/owned/mir",
            "-Ztrust-dump=native-bundle:/owned/native",
        ]);
        let policy = VerifiedTargoCompilerPolicy::new(&[], &owned).unwrap();
        for sink in ["ir", "spec-clean"] {
            let supported = flags(&[&format!("-Ztrust-dump={sink}:/owned/output")]);
            let supported_policy = VerifiedTargoCompilerPolicy::new(&[], &supported).unwrap();
            supported_policy
                .validate_final(&supported.iter().map(String::as_str).collect::<Vec<_>>())
                .unwrap();
        }
        let final_args = owned.iter().map(String::as_str).collect::<Vec<_>>();
        policy.validate_final(&final_args).unwrap();
        for parallel in [
            flags(&["-Ztrust-dump=mir:/other"]),
            flags(&["-Ztrust_dump=native-bundle:/other"]),
        ] {
            assert!(
                policy
                    .reject_parallel_source(&parallel, "Cargo rustc arguments")
                    .is_err()
            );
        }
        assert!(
            policy
                .validate_final(&[
                    "-Ztrust-dump=mir:/owned/mir",
                    "-Ztrust-dump=native-bundle:/other"
                ])
                .is_err()
        );
        assert!(
            VerifiedTargoCompilerPolicy::new(
                &[],
                &flags(&["-Ztrust-dump=mir:/a", "-Ztrust_dump=mir:/b"])
            )
            .is_err()
        );
        assert!(
            VerifiedTargoCompilerPolicy::new(&[], &flags(&["-Ztrust-dump=mir-only:/a"])).is_err()
        );
    }

    #[test]
    fn verified_policy_rejects_retired_contract_checks_from_every_cargo_flag_source() {
        let spellings = [
            flags(&["-Zcontract-checks"]),
            flags(&["-Zcontract-checks=yes"]),
            flags(&["-Zcontract_checks=no"]),
            flags(&["-Z", "contract_checks=unexpected"]),
        ];

        for retired in &spellings {
            let error = VerifiedTargoCompilerPolicy::new(retired, &[])
                .expect_err("unit/config/ambient retired projection must fail closed");
            assert!(
                error.contains("retired `-Zcontract_checks`"),
                "{retired:?}: {error}"
            );
            assert!(error.contains("certified monitors"), "{retired:?}: {error}");
        }

        let policy =
            VerifiedTargoCompilerPolicy::new(&flags(&["-Ztrust-verify-session=proof"]), &[])
                .expect("canonical minimal verified policy");
        for source in ["profile rustflags", "cargo rustc extra compiler arguments"] {
            for retired in &spellings {
                let error = policy
                    .reject_parallel_source(retired, source)
                    .expect_err("parallel retired projection must fail closed");
                assert!(error.contains(source), "{retired:?}: {error}");
                assert!(
                    error.contains("retired `-Zcontract_checks`"),
                    "{retired:?}: {error}"
                );
            }
        }

        for retired in &spellings {
            let mut command = ProcessBuilder::new("trustc");
            command.arg("-Ztrust-verify-session=proof");
            command.args(retired);
            let error = validate_verified_targo_compiler_argument_boundaries(&command, &policy)
                .expect_err("future late retired projection source must fail closed");
            assert!(
                error.contains("retired `-Zcontract_checks`"),
                "{retired:?}: {error}"
            );
        }

        let mut unrelated = ProcessBuilder::new("trustc");
        unrelated.args(&[
            "-Ztrust-verify-session=proof",
            "--cfg",
            "contract_checks=metadata-only",
            "-Cmetadata=contract-checks=no",
        ]);
        validate_verified_targo_compiler_argument_boundaries(&unrelated, &policy)
            .expect("only the retired rustc -Z option is reserved");
    }

    #[test]
    fn verified_policy_rejects_parallel_profile_and_extra_authority_overrides() {
        let policy = VerifiedTargoCompilerPolicy::new(
            &flags(&[
                "-Ztrust-verify-session=proof",
                "-Ztrust-proof-artifact-root=/tmp/proof",
                "-Ztrust-verify-level=2",
                "-Ztrust-verify-output=json",
                "-Zcodegen-backend=trust_cg",
                "-Ztrust-cg-output-gate=strict",
                "-Coverflow-checks=yes",
                "-Cdebug-assertions=yes",
                "-Cpanic=abort",
                "-Cdebuginfo=0",
                "-Ccodegen-units=1",
            ]),
            &flags(&[
                "-Ztrust-verify-crate-role=primary",
                "-Ztrust-verify-package-name=selected",
            ]),
        )
        .expect("canonical policy");

        for (source, override_args) in [
            ("profile rustflags", flags(&["-Ztrust_verify_level=0"])),
            ("profile rustflags", flags(&["-Ztrust_policy=advisory"])),
            ("profile rustflags", flags(&["-Ztrust_verify=off"])),
            ("profile rustflags", flags(&["-Zno_analysis"])),
            ("profile rustflags", flags(&["-Zparse_crate-root_only"])),
            (
                "profile rustflags",
                flags(&["-Zllvm_plugins=/tmp/attacker"]),
            ),
            (
                "cargo rustc extra compiler arguments",
                flags(&["-Zcodegen_backend=llvm"]),
            ),
            ("profile rustflags", flags(&["-Coverflow_checks=no"])),
            ("profile rustflags", flags(&["-Ccodegen_units=8"])),
            (
                "profile rustflags",
                flags(&["--codegen=overflow_checks=no"]),
            ),
            (
                "cargo rustc extra compiler arguments",
                flags(&["--codegen", "codegen_units=8"]),
            ),
            (
                "cargo rustc extra compiler arguments",
                flags(&["--codegen=llvm_args=-load=/tmp/attacker"]),
            ),
            ("profile rustflags", flags(&["--codegen", "help"])),
            ("profile rustflags", flags(&["-Cincremental=/tmp/cache"])),
        ] {
            let error = policy
                .reject_parallel_source(&override_args, source)
                .expect_err("parallel compiler policy source must not own verified semantics");
            assert!(error.contains(source), "{error}");
        }

        let mut command = ProcessBuilder::new("trustc");
        command.args(&[
            "-Ztrust-verify-session=proof",
            "-Ztrust-proof-artifact-root=/tmp/proof",
            "-Ztrust-verify-level=2",
            "-Ztrust-verify-output=json",
            "-Zcodegen-backend=trust-cg",
            "-Ztrust-cg-output-gate=strict",
            "-Coverflow-checks=yes",
            "-Cdebug-assertions=yes",
            "-Cpanic=abort",
            "-Cdebuginfo=0",
            "-Ccodegen-units=1",
            "-Ztrust-verify-crate-role=primary",
            "-Ztrust-verify-package-name=selected",
            "--codegen=codegen_units=8",
        ]);
        let error = validate_verified_targo_compiler_argument_boundaries(&command, &policy)
            .expect_err("a future late source must not override authenticated codegen policy");
        assert!(
            error.contains("overrides authenticated `-Ccodegen_units`"),
            "{error}"
        );

        let command_args = command.get_args().cloned().collect::<Vec<_>>();
        let mut early_exit = ProcessBuilder::new("trustc");
        early_exit.args(&command_args);
        early_exit.arg("-Ztrust_dump=mir-only:/tmp/dump");
        let error = validate_verified_targo_compiler_argument_boundaries(&early_exit, &policy)
            .expect_err("late early-exit options must not produce a proof invocation");
        assert!(error.contains("early-exit `-Ztrust_dump`"), "{error}");

        let mut debug = ProcessBuilder::new("trustc");
        debug.args(&command_args);
        debug.arg("-g");
        let error = validate_verified_targo_compiler_argument_boundaries(&debug, &policy)
            .expect_err("trust-cg must reject every debug-info shorthand source");
        assert!(error.contains("forbidden `-g`"), "{error}");
    }

    #[cfg(unix)]
    #[test]
    fn verified_compiler_argv_rejects_non_unicode_argument() {
        use std::ffi::OsString;
        use std::os::unix::ffi::OsStringExt as _;

        let mut command = ProcessBuilder::new("trustc");
        command.arg(OsString::from_vec(b"--cfg=feature=\xff".to_vec()));
        let error = validate_verified_targo_compiler_argument_boundaries(
            &command,
            &boundary_policy(&command),
        )
        .expect_err("non-Unicode compiler argv must fail closed");
        assert!(error.contains("not valid Unicode"), "{error}");
    }

    #[test]
    fn resolved_unit_role_prioritizes_build_scripts_then_primary_then_dependency() {
        assert_eq!(trust_unit_role(false, true), "primary");
        assert_eq!(trust_unit_role(false, false), "dependency");
        assert_eq!(trust_unit_role(true, true), "build-script");
        assert_eq!(trust_unit_role(true, false), "build-script");
    }

    #[test]
    fn only_exact_resolved_root_unit_is_primary_when_package_has_dual_roles() {
        #[derive(Debug, PartialEq, Eq)]
        struct UnitIdentity {
            package: &'static str,
            target: &'static str,
            compile_kind: &'static str,
        }

        let root = UnitIdentity {
            package: "selected-package",
            target: "selected_package",
            compile_kind: "target",
        };
        let roots = [root];
        let host_dependency = UnitIdentity {
            package: "selected-package",
            target: "selected_package",
            compile_kind: "host",
        };

        assert!(is_resolved_root_unit(&roots[0], &roots));
        assert!(!is_resolved_root_unit(&host_dependency, &roots));
        assert_eq!(
            trust_unit_role(false, is_resolved_root_unit(&roots[0], &roots)),
            "primary"
        );
        assert_eq!(
            trust_unit_role(false, is_resolved_root_unit(&host_dependency, &roots)),
            "dependency"
        );
    }

    #[test]
    fn unit_metadata_follows_the_proof_session_as_a_complete_ordered_tuple() {
        for (custom_build, primary, expected_role) in [
            (false, true, "primary"),
            (false, false, "dependency"),
            (true, true, "build-script"),
        ] {
            let mut rustc_args = flags(&["-Z", "trust-verify-session=proof-run-1"]);
            assert_eq!(
                trust_verification_session(&rustc_args),
                Ok(Some("proof-run-1".to_string()))
            );
            rustc_args.extend(trust_unit_metadata_args(
                custom_build,
                primary,
                "selected-package",
            ));
            assert_eq!(
                rustc_args,
                flags(&[
                    "-Z",
                    "trust-verify-session=proof-run-1",
                    "-Z",
                    &format!("trust-verify-crate-role={expected_role}"),
                    "-Z",
                    "trust-verify-package-name=selected-package",
                ])
            );
        }
    }

    #[test]
    fn cross_target_host_units_use_early_session_and_keep_non_root_roles() {
        // target_info injects the closed verifier policy before Unit creation;
        // the late invocation layer must only derive Cargo-owned metadata.
        let proof_root_flag = host_absolute_proof_root_flag("proof-run-cross");
        let host_unit_flags = flags(&[
            "-Ztrust-verify-output=json",
            "-Z",
            "trust-verify-session=proof-run-cross",
            &proof_root_flag,
        ]);
        let session = resolve_trust_verification_protocol(&host_unit_flags, &[])
            .expect("early host policy is valid")
            .expect("host Unit carries the proof session");
        assert_eq!(session, "proof-run-cross");

        let mut build_script_args = host_unit_flags.clone();
        build_script_args.extend(trust_unit_protocol_args(
            true,
            false,
            false,
            false,
            "selected-package",
            false,
        ));
        assert_eq!(
            build_script_args,
            flags(&[
                "-Ztrust-verify-output=json",
                "-Z",
                "trust-verify-session=proof-run-cross",
                &proof_root_flag,
                "-Z",
                "trust-verify-crate-role=build-script",
                "-Z",
                "trust-verify-package-name=selected-package",
                "-Z",
                "trust-verify=off",
                // Trust (cross-crate composition): every unit of a proof
                // session, build scripts included. A partial application forks
                // a crate into two artifacts sharing one StableCrateId.
                "-Z",
                "always-encode-mir",
            ])
        );

        let mut host_dependency_args = host_unit_flags;
        host_dependency_args.extend(trust_unit_protocol_args(
            false,
            false,
            false,
            false,
            "selected-package",
            false,
        ));
        assert_eq!(
            host_dependency_args,
            flags(&[
                "-Ztrust-verify-output=json",
                "-Z",
                "trust-verify-session=proof-run-cross",
                &proof_root_flag,
                "-Z",
                "trust-verify-crate-role=dependency",
                "-Z",
                "trust-verify-package-name=selected-package",
                "-Z",
                "trust-verify=off",
                "-Z",
                "always-encode-mir",
            ])
        );
    }

    // Trust: this matrix includes custom-build compiles and ordinary host
    // dependencies. Package name, reachability and macro audit are not inputs
    // that can remove a compiler unit from include-dependencies coverage.
    #[test]
    fn resolved_unit_scope_uses_only_the_explicit_compiler_off_switch() {
        for custom_build in [false, true] {
            for primary in [false, true] {
                for execution_subject in [false, true] {
                    for include_dependencies in [false, true] {
                        let expected = include_dependencies
                            || (!custom_build && (primary || execution_subject));
                        assert_eq!(
                            trust_unit_verification_enabled(
                                custom_build,
                                primary,
                                execution_subject,
                                include_dependencies,
                            ),
                            expected,
                        );
                        let args = trust_unit_protocol_args(
                            custom_build,
                            primary,
                            execution_subject,
                            false,
                            "selected",
                            include_dependencies,
                        );
                        assert_eq!(
                            args.windows(2)
                                .any(|pair| pair == ["-Z", "trust-verify=off"]),
                            !expected,
                            "compiler unit scope disagrees with its final flags: {args:?}",
                        );
                    }
                }
            }
        }

        for (primary, execution_subject) in [(true, false), (false, true)] {
            let args = trust_unit_protocol_args(
                false,
                primary,
                execution_subject,
                true,
                "selected",
                false,
            );
            assert!(!args.iter().any(|arg| arg == "trust-verify=off"));
            assert_eq!(
                args.windows(2)
                    .filter(|pair| pair == &["-Z", "trust-certified-test-monitors"])
                    .count(),
                1
            );
        }
    }

    /// Trust (cross-crate composition): `-Zalways-encode-mir` must reach EVERY
    /// unit of a proof session, not the verified ones only.
    ///
    /// This is pinned rather than left to review because the failure it guards
    /// is invisible at the seam that causes it: rustflags are hashed into
    /// Cargo's `unit_id` but NOT into `-Cmetadata`, so a partial application
    /// forks a crate into two artifacts sharing one StableCrateId and surfaces
    /// as an E0463 that names nothing related to this file.
    #[test]
    fn always_encode_mir_reaches_every_proof_session_unit() {
        for is_custom_build in [false, true] {
            for is_primary in [false, true] {
                for is_execution_subject in [false, true] {
                    for include_dependencies in [false, true] {
                        let args = trust_unit_protocol_args(
                            is_custom_build,
                            is_primary,
                            is_execution_subject,
                            false,
                            "selected",
                            include_dependencies,
                        );
                        assert!(
                            args.windows(2)
                                .any(|pair| pair == ["-Z", "always-encode-mir"]),
                            "unit (custom_build={is_custom_build}, primary={is_primary}, \
                             execution_subject={is_execution_subject}, \
                             include_dependencies={include_dependencies}) did not receive \
                             -Zalways-encode-mir: {args:?}"
                        );
                        assert_eq!(
                            args.windows(2)
                                .filter(|pair| pair == &["-Z", "always-encode-mir"])
                                .count(),
                            1,
                            "-Zalways-encode-mir must be injected exactly once: {args:?}"
                        );
                    }
                }
            }
        }
    }

    #[test]
    fn test_execution_subject_requires_exact_runtime_library_graph_role() {
        assert!(trust_test_execution_subject_enabled(
            true, true, true, false, true, true
        ));
        for rejected in [
            (false, true, true, false, true, true),
            (true, false, true, false, true, true),
            (true, true, false, false, true, true),
            (true, true, true, true, true, true),
            (true, true, true, false, false, true),
            (true, true, true, false, true, false),
        ] {
            assert!(!trust_test_execution_subject_enabled(
                rejected.0, rejected.1, rejected.2, rejected.3, rejected.4, rejected.5,
            ));
        }
    }

    #[test]
    fn certified_monitor_subject_covers_execution_units_and_harnessless_roots() {
        // A distinct Build-mode execution subject always needs explicit
        // monitor authorization; the remaining root-only inputs are irrelevant.
        assert!(trust_certified_monitor_subject_enabled(
            true, false, false, false, true
        ));

        // An executing Test-mode root needs the option exactly when Cargo will
        // not pass rustc's native `--test` switch.
        assert!(trust_certified_monitor_subject_enabled(
            false, true, true, true, false
        ));
        for rejected in [
            (false, false, true, true, false),
            (false, true, false, true, false),
            (false, true, true, false, false),
            (false, true, true, true, true),
        ] {
            assert!(!trust_certified_monitor_subject_enabled(
                rejected.0, rejected.1, rejected.2, rejected.3, rejected.4,
            ));
        }
    }

    #[test]
    fn include_dependencies_policy_is_boolean_unique_and_fail_closed() {
        assert_eq!(
            resolve_trust_include_dependencies(
                &flags(&["-Ztrust-verify-include-dependencies=yes"]),
                &[],
            ),
            Ok(true)
        );
        assert_eq!(
            resolve_trust_include_dependencies(
                &flags(&["-Ztrust_verify-include_dependencies=yes"]),
                &[],
            ),
            Ok(true)
        );
        assert_eq!(
            resolve_trust_include_dependencies(
                &flags(&["-Z", "trust-verify-include-dependencies=no"]),
                &[],
            ),
            Ok(false)
        );
        assert!(
            resolve_trust_include_dependencies(
                &flags(&["-Ztrust-verify-include-dependencies=maybe"]),
                &[],
            )
            .is_err()
        );
        assert!(
            resolve_trust_include_dependencies(
                &flags(&["-Ztrust-verify-include-dependencies=yes"]),
                &flags(&["-Ztrust-verify-include-dependencies=no"]),
            )
            .is_err()
        );
    }

    #[test]
    fn cargo_modes_without_authenticated_proof_have_explicit_exclusion_reasons() {
        assert_eq!(
            trust_non_proof_mode_exclusion_reason(CompileMode::RunCustomBuild),
            Some(crate::util::machine_message::TRUST_EXCLUSION_BUILD_SCRIPT_EXECUTION)
        );
        assert_eq!(
            trust_non_proof_mode_exclusion_reason(CompileMode::Doctest),
            Some(crate::util::machine_message::TRUST_EXCLUSION_DEFERRED_DOCTEST)
        );
        for mode in [CompileMode::Doc, CompileMode::Docscrape] {
            assert_eq!(
                trust_non_proof_mode_exclusion_reason(mode),
                Some(crate::util::machine_message::TRUST_EXCLUSION_DOCUMENTATION)
            );
        }
        for mode in [
            CompileMode::Build,
            CompileMode::Test,
            CompileMode::Check { test: false },
            CompileMode::Check { test: true },
        ] {
            assert_eq!(
                trust_non_proof_mode_exclusion_reason(mode),
                None,
                "{mode:?}"
            );
        }
        assert_eq!(
            trust_non_proof_exclusion_reason(CompileMode::Build, true),
            Some(crate::util::machine_message::TRUST_EXCLUSION_COMPILE_TIME_DEPS_FILTERED)
        );
        assert_eq!(
            trust_non_proof_exclusion_reason(CompileMode::Doctest, true),
            Some(crate::util::machine_message::TRUST_EXCLUSION_DEFERRED_DOCTEST)
        );
        assert_eq!(
            trust_non_proof_exclusion_reason(CompileMode::Doc, true),
            Some(crate::util::machine_message::TRUST_EXCLUSION_DOCUMENTATION)
        );
    }

    fn proof_inventory_unit(index: u64) -> TrustProofInventoryUnit {
        let semantics = inventory_semantics();
        let semantics_sha256 = semantics.sha256().unwrap();
        TrustProofInventoryUnit {
            trust_proof_unit: TrustProofUnit {
                schema: TRUST_PROOF_UNIT_SCHEMA_V2,
                index,
                mode: "build",
                role: "primary",
                package_name: format!("package-{index}"),
                semantics_sha256,
            },
            semantics,
            package_id: PackageIdSpec::new(format!("package-{index}")),
            target_name: format!("target-{index}"),
            target_kinds: vec!["lib".to_string()],
            compile_target: "x86_64-unknown-linux-gnu".to_string(),
            trust_compile_mode: "build",
            trust_compile_kind: "target",
            trust_unit_identity_sha256: "b".repeat(64),
            compile_target_spec_sha256: None,
        }
    }

    fn excluded_inventory_unit(index: u64) -> TrustExcludedUnit {
        let semantics = inventory_semantics();
        let semantics_sha256 = semantics.sha256().unwrap();
        TrustExcludedUnit {
            index,
            mode: "build",
            graph_role: "dependency",
            package_id: PackageIdSpec::new(format!("excluded-{index}")),
            package_name: format!("excluded-{index}"),
            target_name: format!("excluded-target-{index}"),
            target_kinds: vec!["lib".to_string()],
            compile_target: "x86_64-unknown-linux-gnu".to_string(),
            trust_compile_mode: "build",
            trust_compile_kind: "target",
            trust_unit_identity_sha256: "b".repeat(64),
            compile_target_spec_sha256: None,
            exclusion_reason: crate::util::machine_message::TRUST_EXCLUSION_DEPENDENCY_POLICY,
            semantics_sha256,
            semantics,
        }
    }

    #[test]
    fn proof_inventory_is_canonical_and_duplicate_indices_fail_closed() {
        let (units, excluded) = canonicalize_trust_proof_inventory(
            vec![proof_inventory_unit(9), proof_inventory_unit(2)],
            vec![excluded_inventory_unit(5), excluded_inventory_unit(1)],
            [1, 2, 5, 9],
        )
        .unwrap();
        assert_eq!(
            units
                .iter()
                .map(|unit| unit.trust_proof_unit.index)
                .collect::<Vec<_>>(),
            [2, 9]
        );
        assert_eq!(
            excluded.iter().map(|unit| unit.index).collect::<Vec<_>>(),
            [1, 5]
        );

        let error = canonicalize_trust_proof_inventory(
            vec![proof_inventory_unit(4)],
            vec![excluded_inventory_unit(4)],
            [4, 4],
        )
        .expect_err("duplicate proof-unit indices must be rejected");
        assert!(error.contains("duplicate Cargo Unit index 4"), "{error}");

        let error = canonicalize_trust_proof_inventory(
            vec![proof_inventory_unit(2)],
            vec![excluded_inventory_unit(5)],
            [2, 4, 5],
        )
        .expect_err("the proof/exclusion union must exactly cover the resolved graph");
        assert!(error.contains("did not exactly cover"), "{error}");
    }

    #[test]
    fn proof_inventory_semantic_sets_and_transport_flags_are_canonical() {
        assert_eq!(
            canonical_trust_string_set("feature", ["serde".to_string(), "default".to_string()]),
            Ok(vec!["default".to_string(), "serde".to_string()])
        );
        let error =
            canonical_trust_string_set("feature", ["serde".to_string(), "serde".to_string()])
                .expect_err("duplicate feature identities must fail closed");
        assert!(error.contains("duplicate feature"), "{error}");

        assert_eq!(
            trust_semantic_compiler_args(&flags(&[
                "-Ztrust-verify-session=nonce",
                "-Z",
                "trust-proof-artifact-root=/tmp/proofs",
                "-Ztrust-verify-include-dependencies=yes",
                "--cfg",
                "feature=\"serde\"",
                "-Zcodegen-backend=trust-cg",
            ])),
            Ok(flags(&[
                "--cfg",
                "feature=\"serde\"",
                "-Zcodegen-backend=trust-cg",
            ]))
        );
        assert!(trust_semantic_compiler_args(&flags(&["-Z"])).is_err());
    }

    #[test]
    fn proof_inventory_include_dependencies_policy_must_be_graph_wide() {
        assert_eq!(
            require_uniform_trust_include_dependencies([(8, true), (2, true), (5, true)]),
            Ok(true)
        );
        assert_eq!(
            require_uniform_trust_include_dependencies(std::iter::empty()),
            Ok(false)
        );
        let error = require_uniform_trust_include_dependencies([(2, false), (8, true)])
            .expect_err("mixed graph policy must be rejected");
        assert!(error.contains("unit index 8"), "{error}");
    }

    // Trust: the assertion is identity-bearing input, never final activation.
    #[test]
    fn host_policy_assertion_retains_identity_but_not_compiler_authority() {
        let proof_root = host_absolute_proof_root_flag("required-host");
        let policy = flags(&[
            "-Ztrust-verify-session=required-host",
            &proof_root,
            "-Ztrust-policy=certify",
            "-Ztrust-verify-level=2",
            "-Ztrust-verify-profile=unix_hardened",
            "-Ztrust-ir-lower=strict",
        ]);
        for assertion in [
            flags(&["-Ztrust-verify=on"]),
            flags(&["-Z", "trust-verify=on"]),
            flags(&["-Ztrust_verify=true"]),
            flags(&["-Z", "trust_verify=yes"]),
        ] {
            let mut unit = policy.clone();
            unit.extend(assertion.clone());
            let original = unit.clone();
            assert!(required_trust_verification_assertion(&unit).unwrap());
            assert_eq!(
                resolve_trust_verification_protocol(&unit, &[]).unwrap(),
                Some("required-host".to_string())
            );
            let semantic = trust_semantic_compiler_args(&unit).unwrap();
            assert!(
                semantic.ends_with(&assertion),
                "identity must retain the assertion"
            );
            let compiler = compiler_flags_without_verification_assertion(&unit).unwrap();
            assert_eq!(compiler, policy);
            assert_eq!(unit, original, "never erase the stored requirement");
            let exact = VerifiedTargoCompilerPolicy::new(&compiler, &[]).unwrap();
            exact
                .validate_final(&compiler.iter().map(String::as_str).collect::<Vec<_>>())
                .unwrap();
            let mut forged_final = compiler.iter().map(String::as_str).collect::<Vec<_>>();
            forged_final.push("-Ztrust-verify=on");
            assert!(exact.validate_final(&forged_final).is_err());
            assert!(
                exact
                    .reject_parallel_source(&assertion, "profile rustflags")
                    .is_err()
            );
            assert!(resolve_trust_verification_protocol(&policy, &assertion).is_err());
        }
        assert!(!required_trust_verification_assertion(&policy).unwrap());
        assert_eq!(
            compiler_flags_without_verification_assertion(&policy).unwrap(),
            policy
        );
    }

    #[test]
    fn host_policy_assertion_refuses_duplicates_missing_authority_and_off_switches() {
        for rejected in [
            flags(&["-Ztrust-verify"]),
            flags(&["-Ztrust_verify="]),
            flags(&["-Ztrust-verify=off"]),
            flags(&["-Z", "trust_verify=false"]),
            flags(&["-Zno-trust-verify"]),
            flags(&["-Zno_trust_verify=off"]),
            flags(&["-Ztrust-verify=on", "-Z", "trust_verify=on"]),
            flags(&["-Ztrust-verify=on", "-Ztrust-verify=off"]),
            flags(&["-Ztrust-verify=on", "-Z"]),
        ] {
            assert!(
                required_trust_verification_assertion(&rejected).is_err(),
                "{rejected:?}"
            );
            assert!(
                compiler_flags_without_verification_assertion(&rejected).is_err(),
                "{rejected:?}"
            );
        }
        assert!(
            resolve_trust_verification_protocol(&flags(&["-Ztrust-verify=on"]), &[])
                .unwrap_err()
                .contains("proof session")
        );
        assert!(
            resolve_trust_verification_protocol(
                &flags(&["-Ztrust-verify=on", "-Ztrust-verify-session=missing-root"]),
                &[]
            )
            .unwrap_err()
            .contains("proof-artifact-root")
        );
    }

    #[test]
    fn host_policy_assertion_does_not_expand_graph_eligibility() {
        // Trust: a positive host assertion cannot admit a compiler dependency
        // when dependency coverage is off, but every compiler dependency is
        // eligible when the authenticated policy explicitly includes it.
        for custom_build in [false, true] {
            assert!(!trust_unit_verification_enabled(
                custom_build,
                false,
                false,
                false
            ));
            assert!(trust_unit_verification_enabled(
                custom_build,
                false,
                false,
                true
            ));
        }
        require_trust_verification_eligibility(None).unwrap();
        let reason = crate::util::machine_message::TRUST_EXCLUSION_DEPENDENCY_POLICY;
        assert!(
            require_trust_verification_eligibility(Some(reason))
                .unwrap_err()
                .contains(reason)
        );
        for mode in [
            CompileMode::RunCustomBuild,
            CompileMode::Doc,
            CompileMode::Docscrape,
            CompileMode::Doctest,
        ] {
            let reason = trust_non_proof_mode_exclusion_reason(mode).unwrap();
            assert!(
                require_trust_verification_eligibility(Some(reason))
                    .unwrap_err()
                    .contains(reason)
            );
        }
    }

    #[test]
    fn per_unit_sessions_are_unique_and_caller_metadata_stays_reserved() {
        let proof_root_flag = host_absolute_proof_root_flag("proof-run-1");
        let unit = flags(&["-Ztrust-verify-session=proof-run-1", &proof_root_flag]);
        assert_eq!(
            resolve_trust_verification_protocol(&unit, &[]).unwrap(),
            Some("proof-run-1".to_string())
        );

        let duplicate = resolve_trust_verification_protocol(
            &flags(&["-Ztrust-verify-session=proof-run-1"]),
            &flags(&["-Ztrust-verify-session=proof-run-1"]),
        )
        .expect_err("the session must have one canonical per-unit source");
        assert!(duplicate.contains("duplicate per-unit"), "{duplicate}");

        let mismatch = resolve_trust_verification_protocol(
            &flags(&["-Ztrust-verify-session=forged"]),
            &flags(&["-Ztrust-verify-session=proof-run-1"]),
        )
        .expect_err("per-unit session sources cannot disagree");
        assert!(mismatch.contains("conflicting per-unit"), "{mismatch}");

        let reserved = resolve_trust_verification_protocol(
            &flags(&["-Ztrust-verify-crate-role=primary"]),
            &[],
        )
        .expect_err("caller metadata is rejected even without a session");
        assert!(reserved.contains("reserved for Targo"), "{reserved}");

        let forged_role = resolve_trust_verification_protocol(
            &flags(&[
                "-Ztrust-verify-session=proof-run-1",
                "-Ztrust-verify-crate-role=dependency",
            ]),
            &[],
        )
        .expect_err("a caller-declared role must never weaken resolved unit scope");
        assert!(forged_role.contains("reserved for Targo"), "{forged_role}");

        let forged_off_switch = resolve_trust_verification_protocol(
            &flags(&["-Ztrust-verify-session=proof-run-1", "-Zno_trust-verify"]),
            &[],
        )
        .expect_err("rustc-equivalent spelling must not let callers disable a proof unit");
        assert!(forged_off_switch.contains("resolved compilation-unit scope"));
    }
}

/// Prepares flags and environments we can compute for a `rustdoc` invocation
/// before the job queue starts compiling any unit.
///
/// This builds a static view of the invocation. Flags depending on the
/// completion of other units will be added later in runtime, such as flags
/// from build scripts.
#[tracing::instrument(skip_all)]
fn prepare_rustdoc(build_runner: &BuildRunner<'_, '_>, unit: &Unit) -> CargoResult<ProcessBuilder> {
    let bcx = build_runner.bcx;
    // script_metadata is not needed here, it is only for tests.
    let mut rustdoc = build_runner.compilation.rustdoc_process(unit, None)?;
    if verified_targo_protocol_active() {
        // Trust: keep excluded documentation units on the same closed
        // target-origin boundary as proof-producing rustc units — a doc unit
        // shares the target directory with them.
        rustdoc.env_remove("RUST_TARGET_PATH");
    }
    let wants_json_output = build_runner.bcx.build_config.intent.wants_doc_json_output();
    if unit.pkg.manifest().is_embedded() {
        if !bcx.gctx.cli_unstable().script {
            anyhow::bail!(
                "parsing `{}` requires `-Zscript`",
                unit.pkg.manifest_path().display()
            );
        }
        rustdoc.arg("-Z").arg("crate-attr=feature(frontmatter)");
        rustdoc.arg("-Z").arg("crate-attr=allow(unused_features)");
    }
    rustdoc.inherit_jobserver(&build_runner.jobserver);
    let crate_name = unit.target.crate_name();
    rustdoc.arg("--crate-name").arg(&crate_name);
    add_path_args(bcx.ws, unit, &mut rustdoc);
    add_cap_lints(bcx, unit, &mut rustdoc);

    unit.kind.add_target_arg(&mut rustdoc);

    let doc_dir = if wants_json_output {
        // Always use new layout for '--output-format=json'.
        // In fix for https://github.com/rust-lang/cargo/issues/16291

        build_runner.files().out_dir_new_layout(unit)
    } else {
        build_runner.files().output_dir(unit)
    };

    rustdoc.arg("-o").arg(&doc_dir);
    rustdoc.args(&features_args(unit));
    rustdoc.args(&check_cfg_args(unit));

    add_error_format_and_color(build_runner.bcx, &mut rustdoc);
    add_allow_features(build_runner.bcx, &mut rustdoc);

    if build_runner.bcx.gctx.cli_unstable().rustdoc_depinfo {
        // html-static-files is required for keeping the shared styling resources
        // html-non-static-files is required for keeping the original rustdoc emission
        let mut arg = if wants_json_output {
            OsString::from("--emit=dep-info=")
        } else if build_runner.bcx.gctx.cli_unstable().rustdoc_mergeable_info {
            // toolchain resources are written at the end, at the same time as merging
            OsString::from("--emit=html-non-static-files,dep-info=")
        } else {
            // if not using mergeable CCI, everything is written every time
            OsString::from("--emit=html-static-files,html-non-static-files,dep-info=")
        };
        arg.push(rustdoc_dep_info_loc(build_runner, unit));
        rustdoc.arg(arg);

        if build_runner.bcx.gctx.cli_unstable().checksum_freshness {
            match build_runner
                .bcx
                .gctx
                .build_config()?
                .fingerprint
                .unwrap_or_default()
            {
                FingerprintMethod::Content => {
                    rustdoc.arg("-Z").arg("checksum-hash-algorithm=blake3");
                }
                FingerprintMethod::Mtime => {}
            }
        }
    } else if build_runner.bcx.gctx.cli_unstable().rustdoc_mergeable_info && !wants_json_output {
        // toolchain resources are written at the end, at the same time as merging
        rustdoc.arg("--emit=html-non-static-files");
    }

    if build_runner.bcx.gctx.cli_unstable().rustdoc_mergeable_info && !wants_json_output {
        // write out mergeable data to be imported
        rustdoc.arg("-Zunstable-options");
        let mut arg = OsString::from("--write-doc-meta-dir=");
        // `-Zrustdoc-mergeable-info` always uses the new layout.
        arg.push(build_runner.files().out_dir_new_layout(unit));
        rustdoc.arg(arg);
    }

    trim_paths_args_rustdoc(&mut rustdoc, build_runner, unit, &unit.profile.trim_paths)?;

    rustdoc.args(unit.pkg.manifest().lint_rustflags());

    let metadata = build_runner.metadata_for_doc_units[unit];
    rustdoc
        .arg("-C")
        .arg(format!("metadata={}", metadata.c_metadata()));

    if unit.mode.is_doc_scrape() {
        debug_assert!(build_runner.bcx.scrape_units.contains(unit));

        if unit.target.is_test() {
            rustdoc.arg("--scrape-tests");
        }

        rustdoc.arg("-Zunstable-options");

        rustdoc
            .arg("--scrape-examples-output-path")
            .arg(scrape_output_path(build_runner, unit)?);

        // Only scrape example for items from crates in the workspace, to reduce generated file size
        for pkg in build_runner.bcx.packages.packages() {
            let names = pkg
                .targets()
                .iter()
                .map(|target| target.crate_name())
                .collect::<HashSet<_>>();
            for name in names {
                rustdoc.arg("--scrape-examples-target-crate").arg(name);
            }
        }
    }

    if should_include_scrape_units(build_runner.bcx, unit) {
        rustdoc.arg("-Zunstable-options");
    }

    build_deps_args_context(
        &mut rustdoc,
        &RustcCommandContext::for_runner(build_runner),
        unit,
    )?;
    rustdoc::add_root_urls(build_runner, unit, &mut rustdoc)?;

    rustdoc::add_output_format(build_runner, &mut rustdoc)?;

    if let Some(args) = build_runner.bcx.extra_args_for(unit) {
        rustdoc.args(args);
    }
    rustdoc.args(&unit.rustdocflags);

    if !crate_version_flag_already_present(&rustdoc) {
        append_crate_version_flag(unit, &mut rustdoc);
    }

    Ok(rustdoc)
}

/// Creates a unit of work invoking `rustdoc` for documenting the `unit`.
#[tracing::instrument(skip_all)]
fn rustdoc(build_runner: &mut BuildRunner<'_, '_>, unit: &Unit) -> CargoResult<Work> {
    let mut rustdoc = prepare_rustdoc(build_runner, unit)?;

    let crate_name = unit.target.crate_name();
    let is_json_output = build_runner.bcx.build_config.intent.wants_doc_json_output();
    let doc_dir = build_runner.files().output_dir(unit);
    // Create the documentation directory ahead of time as rustdoc currently has
    // a bug where concurrent invocations will race to create this directory if
    // it doesn't already exist.
    paths::create_dir_all(&doc_dir)?;

    let target_desc = unit.target.description_named();
    let name = unit.pkg.name();
    let build_script_outputs = Arc::clone(&build_runner.build_script_outputs);
    let package_id = unit.pkg.package_id();
    let target = Target::clone(&unit.target);
    let manifest = ManifestErrorContext::new(build_runner, unit)?;

    let rustdoc_dep_info_loc = rustdoc_dep_info_loc(build_runner, unit);
    let dep_info_loc = fingerprint::dep_info_loc(build_runner, unit);
    let build_dir = build_runner.bcx.ws.build_dir().into_path_unlocked();
    let pkg_root = unit.pkg.root().to_path_buf();
    let ws_root = build_runner.bcx.ws.root().to_path_buf();
    let cwd = rustdoc
        .get_cwd()
        .unwrap_or_else(|| build_runner.bcx.gctx.cwd())
        .to_path_buf();
    let fingerprint_dir = build_runner.files().fingerprint_dir(unit);
    let is_local = unit.is_local();
    let env_config = Arc::clone(build_runner.bcx.gctx.env_config()?);
    let capture_rusage = build_runner.bcx.capture_rusage();
    let rustdoc_depinfo_enabled = build_runner.bcx.gctx.cli_unstable().rustdoc_depinfo;
    // Trust: EW-9 relocation roots for the translated dep-info.
    let relocation_roots = build_runner
        .bcx
        .gctx
        .cli_unstable()
        .trust_relocation_roots
        .clone();

    let mut output_options = OutputOptions::for_dirty(build_runner, unit);
    let script_metadatas = build_runner.find_build_script_metadatas(unit);
    let scrape_outputs = if should_include_scrape_units(build_runner.bcx, unit) {
        Some(
            build_runner
                .bcx
                .scrape_units
                .iter()
                .map(|unit| {
                    Ok((
                        build_runner.files().metadata(unit).unit_id(),
                        scrape_output_path(build_runner, unit)?,
                    ))
                })
                .collect::<CargoResult<HashMap<_, _>>>()?,
        )
    } else {
        None
    };

    let failed_scrape_units = Arc::clone(&build_runner.failed_scrape_units);
    let hide_diagnostics_for_scrape_unit = build_runner.bcx.unit_can_fail_for_docscraping(unit)
        && !matches!(
            build_runner.bcx.gctx.shell().verbosity(),
            Verbosity::Verbose
        );
    let failed_scrape_diagnostic = hide_diagnostics_for_scrape_unit.then(|| {
        make_failed_scrape_diagnostic(
            build_runner,
            unit,
            format_args!("failed to scan {target_desc} in package `{name}` for example code usage"),
        )
    });
    if hide_diagnostics_for_scrape_unit {
        output_options.show_diagnostics = false;
    }
    // Trust: rustdoc is launched through a sysroot shim rather than executed
    // directly, so the binary Cargo resolved and the binary that runs are two
    // different files. Carry the launcher's identity into the closure and check
    // it on both sides of the spawn.
    let verified_rustdoc_launcher = build_runner.verified_rustdoc_launcher.clone();

    Ok(Work::new(move |state| {
        add_custom_flags(
            &mut rustdoc,
            None,
            crate::is_targo_invocation(),
            &build_script_outputs.lock().unwrap(),
            script_metadatas,
        )?;

        // Add the output of scraped examples to the rustdoc command.
        // This action must happen after the unit's dependencies have finished,
        // because some of those deps may be Docscrape units which have failed.
        // So we dynamically determine which `--with-examples` flags to pass here.
        if let Some(scrape_outputs) = scrape_outputs {
            let failed_scrape_units = failed_scrape_units.lock().unwrap();
            for (metadata, output_path) in &scrape_outputs {
                if !failed_scrape_units.contains(metadata) {
                    rustdoc.arg("--with-examples").arg(output_path);
                }
            }
        }

        if !is_json_output {
            let crate_dir = doc_dir.join(&crate_name);
            if crate_dir.exists() {
                // Remove output from a previous build. This ensures that stale
                // files for removed items are removed.
                debug!("removing pre-existing doc directory {:?}", crate_dir);
                paths::remove_dir_all(&crate_dir)?;
            }
        };
        state.running(&rustdoc);
        let timestamp = paths::set_invocation_time(&fingerprint_dir)?;

        validate_verified_command_runtime_library_authority(&rustdoc)?;
        if let Some(identity) = &verified_rustdoc_launcher {
            identity.ensure_current()?;
        }

        let (stats, result) = exec_with_targo_streaming_policy(
            &rustdoc,
            &mut |line| on_stdout_line(state, line, package_id, &target),
            &mut |line| {
                on_stderr_line(
                    state,
                    line,
                    package_id,
                    &manifest,
                    &target,
                    &mut output_options,
                )
            },
            false,
            capture_rusage,
        );
        let result = result
            .map_err(verbose_if_simple_exit_code)
            .with_context(|| format!("could not document `{}`", name));

        // Trust: recheck even when rustdoc failed. Path immutability was
        // established separately before the spawn; this hash comparison is an
        // additional integrity diagnostic, with the child error retained as
        // context so a swap is never reported as a plain documentation failure.
        let post_identity = verified_rustdoc_launcher
            .as_ref()
            .map(|identity| identity.ensure_current())
            .transpose();

        if let Some(peak_memory) = stats.peak_rss {
            state.peak_memory(peak_memory);
        }
        if let Some(times) = stats.cpu_times {
            state.cpu_times(times);
        }

        if let Err(e) = result {
            if let Some(diagnostic) = failed_scrape_diagnostic {
                state.warning(diagnostic);
            }
            if let Err(identity_error) = post_identity {
                return Err(identity_error.context(format!(
                    "the documentation child also failed before its verified trustdoc launcher endpoint check: {e:#}"
                )));
            }
            return Err(e);
        }
        if let Err(identity_error) = post_identity {
            return Err(identity_error);
        }

        if rustdoc_depinfo_enabled && rustdoc_dep_info_loc.exists() {
            fingerprint::translate_dep_info(
                &rustdoc_dep_info_loc,
                &dep_info_loc,
                &cwd,
                &pkg_root,
                &build_dir,
                &ws_root,
                &rustdoc,
                // Should we track source file for doc gen?
                is_local,
                false,
                &env_config,
                relocation_roots.as_ref(),
            )
            .with_context(|| {
                internal(format_args!(
                    "could not parse/generate dep info at: {}",
                    rustdoc_dep_info_loc.display()
                ))
            })?;
            // This mtime shift allows Cargo to detect if a source file was
            // modified in the middle of the build.
            paths::set_file_time_no_err(dep_info_loc, timestamp);
        }

        Ok(())
    }))
}

// The --crate-version flag could have already been passed in RUSTDOCFLAGS
// or as an extra compiler argument for rustdoc
fn crate_version_flag_already_present(rustdoc: &ProcessBuilder) -> bool {
    rustdoc.get_args().any(|flag| {
        flag.to_str()
            .map_or(false, |flag| flag.starts_with(RUSTDOC_CRATE_VERSION_FLAG))
    })
}

fn append_crate_version_flag(unit: &Unit, rustdoc: &mut ProcessBuilder) {
    rustdoc
        .arg(RUSTDOC_CRATE_VERSION_FLAG)
        .arg(unit.pkg.version().to_string());
}

enum CapLints {
    Allow,
    Warn,
}

fn compute_cap_lints(bcx: &BuildContext<'_, '_>, unit: &Unit) -> Option<CapLints> {
    // If this is an upstream dep we don't want warnings from, turn off all
    // lints.
    if !unit.show_warnings(bcx.gctx) {
        Some(CapLints::Allow)
    // If this is an upstream dep but we *do* want warnings, make sure that they
    // don't fail compilation.
    } else if !unit.is_local() {
        Some(CapLints::Warn)
    } else {
        None
    }
}

/// Adds [`--cap-lints`] to the command to execute.
///
/// [`--cap-lints`]: https://doc.rust-lang.org/nightly/rustc/lints/levels.html#capping-lints
fn add_cap_lints(bcx: &BuildContext<'_, '_>, unit: &Unit, cmd: &mut ProcessBuilder) {
    if let Some(cap_lints) = compute_cap_lints(bcx, unit) {
        match cap_lints {
            CapLints::Allow => {
                cmd.arg("--cap-lints").arg("allow");
            }
            CapLints::Warn => {
                cmd.arg("--cap-lints").arg("warn");
            }
        }
    }
}

/// Forwards [`-Zallow-features`] if it is set for cargo.
///
/// [`-Zallow-features`]: https://doc.rust-lang.org/nightly/cargo/reference/unstable.html#allow-features
fn add_allow_features(bcx: &BuildContext<'_, '_>, cmd: &mut ProcessBuilder) {
    if let Some(allow) = &bcx.gctx.cli_unstable().allow_features {
        use std::fmt::Write;
        let mut arg = String::from("-Zallow-features=");
        for f in allow {
            let _ = write!(&mut arg, "{f},");
        }
        cmd.arg(arg.trim_end_matches(','));
    }
}

/// Adds [`--error-format`] to the command to execute.
///
/// Cargo always uses JSON output. This has several benefits, such as being
/// easier to parse, handles changing formats (for replaying cached messages),
/// ensures atomic output (so messages aren't interleaved), allows for
/// intercepting messages like rmeta artifacts, etc. rustc includes a
/// "rendered" field in the JSON message with the message properly formatted,
/// which Cargo will extract and display to the user.
///
/// [`--error-format`]: https://doc.rust-lang.org/nightly/rustc/command-line-arguments.html#--error-format-control-how-errors-are-produced
fn add_error_format_and_color(bcx: &BuildContext<'_, '_>, cmd: &mut ProcessBuilder) {
    let enable_timings = bcx.gctx.cli_unstable().section_timings && bcx.logger.is_some();
    if enable_timings {
        cmd.arg("-Zunstable-options");
    }

    cmd.arg("--error-format=json");

    let mut json = String::from(
        "--json=diagnostic-rendered-ansi,artifacts,future-incompat,unused-externs-silent",
    );
    if let MessageFormat::Short | MessageFormat::Json { short: true, .. } =
        bcx.build_config.message_format
    {
        json.push_str(",diagnostic-short");
    } else if bcx.gctx.shell().err_unicode() && bcx.gctx.cli_unstable().rustc_unicode {
        json.push_str(",diagnostic-unicode");
    }
    if enable_timings {
        json.push_str(",timings");
    }
    cmd.arg(json);

    let gctx = bcx.gctx;
    if let Some(width) = gctx.shell().err_width().diagnostic_terminal_width() {
        cmd.arg(format!("--diagnostic-width={width}"));
    }
}

/// Adds essential rustc flags and environment variables to the command to execute.
fn build_base_args_context<L: std::borrow::Borrow<layout::LayoutPaths>>(
    build_runner: &RustcCommandContext<'_, '_, '_, L>,
    cmd: &mut ProcessBuilder,
    unit: &Unit,
) -> CargoResult<()> {
    assert!(!unit.mode.is_run_custom_build());

    let bcx = build_runner.bcx;
    let Profile {
        ref opt_level,
        codegen_backend,
        codegen_units,
        debuginfo,
        debug_assertions,
        split_debuginfo,
        overflow_checks,
        rpath,
        ref panic,
        incremental,
        strip,
        rustflags: profile_rustflags,
        trim_paths,
        hint_mostly_unused: profile_hint_mostly_unused,
        ..
    } = unit.profile.clone();
    let hints = unit.pkg.hints().cloned().unwrap_or_default();
    let test = unit.mode.is_any_test();

    cmd.arg("--crate-name").arg(&unit.target.crate_name());

    let edition = unit.target.edition();
    edition.cmd_edition_arg(cmd);

    add_path_args(bcx.ws, unit, cmd);
    add_error_format_and_color(build_runner.bcx, cmd);
    add_allow_features(build_runner.bcx, cmd);

    let mut contains_dy_lib = false;
    if !test {
        for crate_type in &unit.target.rustc_crate_types() {
            cmd.arg("--crate-type").arg(crate_type.as_str());
            contains_dy_lib |= crate_type == &CrateType::Dylib;
        }
    }

    if unit.mode.is_check() {
        cmd.arg("--emit=dep-info,metadata");
    } else if !build_runner
        .bcx
        .target_data
        .info(unit.kind)
        .should_embed_metadata()
    {
        // Nightly rustc supports the -Zembed-metadata=no flag, which tells it to avoid including
        // full metadata in rlib/dylib artifacts, to save space on disk. In this case, metadata
        // will only be stored in .rmeta files.
        // When we use this flag, we should also pass --emit=metadata to all artifacts that
        // contain useful metadata (rlib/dylib/proc macros), so that a .rmeta file is actually
        // generated. If we didn't do this, the full metadata would not get written anywhere.
        // However, we do not want to pass --emit=metadata to artifacts that never produce useful
        // metadata, such as binaries, because that would just unnecessarily create empty .rmeta
        // files on disk.
        if unit.benefits_from_no_embed_metadata() {
            cmd.arg("--emit=dep-info,metadata,link");
            cmd.args(&["-Z", "embed-metadata=no"]);
        } else {
            cmd.arg("--emit=dep-info,link");
        }
    } else {
        // If we don't use -Zembed-metadata=no, we emit .rmeta files only for rlib outputs.
        // This metadata may be used in this session for a pipelined compilation, or it may
        // be used in a future Cargo session as part of a pipelined compile.
        if !unit.requires_upstream_objects() {
            cmd.arg("--emit=dep-info,metadata,link");
        } else {
            cmd.arg("--emit=dep-info,link");
        }
    }

    // Trust: verified lanes never emit `-C prefer-dynamic` for a proc-macro
    // unit; see `cargo_prefers_dynamic_rust_linkage`.
    let prefer_dynamic = cargo_prefers_dynamic_rust_linkage(
        verified_targo_protocol_active(),
        unit.target.for_host(),
        unit.target.is_custom_build(),
        unit.target.proc_macro(),
        contains_dy_lib,
        build_runner.is_primary_package(unit),
    );
    if prefer_dynamic {
        cmd.arg("-C").arg("prefer-dynamic");
    }

    if opt_level.as_str() != "0" {
        cmd.arg("-C").arg(&format!("opt-level={}", opt_level));
    }

    if *panic != PanicStrategy::Unwind {
        cmd.arg("-C").arg(format!("panic={}", panic));
    }
    if *panic == PanicStrategy::ImmediateAbort {
        cmd.arg("-Z").arg("unstable-options");
    }

    cmd.args(&lto_args_context(build_runner, unit));

    if let Some(backend) = codegen_backend {
        cmd.arg("-Z").arg(&format!("codegen-backend={}", backend));
    }

    if let Some(n) = codegen_units {
        cmd.arg("-C").arg(&format!("codegen-units={}", n));
    }

    let debuginfo = debuginfo.into_inner();
    // Shorten the number of arguments if possible.
    if debuginfo != TomlDebugInfo::None {
        cmd.arg("-C").arg(format!("debuginfo={debuginfo}"));
        // This is generally just an optimization on build time so if we don't
        // pass it then it's ok. The values for the flag (off, packed, unpacked)
        // may be supported or not depending on the platform, so availability is
        // checked per-value. For example, at the time of writing this code, on
        // Windows the only stable valid value for split-debuginfo is "packed",
        // while on Linux "unpacked" is also stable.
        if let Some(split) = split_debuginfo {
            if build_runner
                .bcx
                .target_data
                .info(unit.kind)
                .supports_debuginfo_split(split)
            {
                cmd.arg("-C").arg(format!("split-debuginfo={split}"));
            }
        }
    }

    trim_paths::trim_paths_args(cmd, build_runner.bcx, unit, &trim_paths)?;

    match compute_cap_lints(bcx, unit) {
        None | Some(CapLints::Warn) => {
            cmd.args(unit.pkg.manifest().lint_rustflags());
        }
        // If we pass --cap-lints=allow, there is no point in making the CLI larger by including
        // potentially a lot of --warn lint flags.
        Some(CapLints::Allow) => {}
    }
    cmd.args(&profile_rustflags);

    // `-C overflow-checks` is implied by the setting of `-C debug-assertions`,
    // so we only need to provide `-C overflow-checks` if it differs from
    // the value of `-C debug-assertions` we would provide.
    if opt_level.as_str() != "0" {
        if debug_assertions {
            cmd.args(&["-C", "debug-assertions=on"]);
            if !overflow_checks {
                cmd.args(&["-C", "overflow-checks=off"]);
            }
        } else if overflow_checks {
            cmd.args(&["-C", "overflow-checks=on"]);
        }
    } else if !debug_assertions {
        cmd.args(&["-C", "debug-assertions=off"]);
        if overflow_checks {
            cmd.args(&["-C", "overflow-checks=on"]);
        }
    } else if !overflow_checks {
        cmd.args(&["-C", "overflow-checks=off"]);
    }

    if test && unit.target.harness() {
        cmd.arg("--test");

        // Cargo has historically never compiled `--test` binaries with
        // `panic=abort` because the `test` crate itself didn't support it.
        // Support is now upstream, however, but requires an unstable flag to be
        // passed when compiling the test. We require, in Cargo, an unstable
        // flag to pass to rustc, so register that here. Eventually this flag
        // will simply not be needed when the behavior is stabilized in the Rust
        // compiler itself.
        if *panic == PanicStrategy::Abort || *panic == PanicStrategy::ImmediateAbort {
            cmd.arg("-Z").arg("panic-abort-tests");
        }
    } else if test {
        cmd.arg("--cfg").arg("test");
    }

    cmd.args(&features_args(unit));
    cmd.args(&check_cfg_args(unit));

    let meta = build_runner.files().metadata(unit);
    cmd.arg("-C")
        .arg(&format!("metadata={}", meta.c_metadata()));
    if let Some(c_extra_filename) = meta.c_extra_filename() {
        cmd.arg("-C")
            .arg(&format!("extra-filename=-{c_extra_filename}"));
    }

    if rpath {
        cmd.arg("-C").arg("rpath");
    }

    cmd.arg("--out-dir")
        .arg(&build_runner.files().output_dir(unit));

    unit.kind.add_target_arg(cmd);

    add_codegen_linker_context(cmd, build_runner, unit, bcx.gctx.target_applies_to_host()?);

    if incremental {
        add_codegen_incremental(cmd, build_runner, unit)
    }

    let pkg_hint_mostly_unused = match hints.mostly_unused {
        Some(toml::Value::Boolean(b)) => Some(b),
        // Unsupported values and ignored hints are reported before the build, see
        // `crate::diagnostics::rules::PARSE_PASS_RULES`.
        _ => None,
    };
    if profile_hint_mostly_unused
        .or(pkg_hint_mostly_unused)
        .unwrap_or(false)
        && bcx.gctx.cli_unstable().profile_hint_mostly_unused
    {
        cmd.arg("-Zhint-mostly-unused");
    }

    let strip = strip.into_inner();
    if strip != StripInner::None {
        cmd.arg("-C").arg(format!("strip={}", strip));
    }

    if unit.is_std {
        // -Zforce-unstable-if-unmarked prevents the accidental use of
        // unstable crates within the sysroot (such as "extern crate libc" or
        // any non-public crate in the sysroot).
        //
        // RUSTC_BOOTSTRAP allows unstable features on stable.
        cmd.arg("-Z")
            .arg("force-unstable-if-unmarked")
            .env("RUSTC_BOOTSTRAP", "1");
    }

    if let Some(version) = unit.pkg.manifest().rust_version()
        && bcx.gctx.cli_unstable().hint_msrv
    {
        cmd.arg("-Z").arg(format!("hint-msrv={version}"));
    }

    Ok(())
}

/// All active features for the unit passed as `--cfg features=<feature-name>`.
fn features_args(unit: &Unit) -> Vec<OsString> {
    let mut args = Vec::with_capacity(unit.features.len() * 2);

    for feat in &unit.features {
        args.push(OsString::from("--cfg"));
        args.push(OsString::from(format!("feature=\"{}\"", feat)));
    }

    args
}

/// Generates the `--check-cfg` arguments for the `unit`.
fn check_cfg_args(unit: &Unit) -> Vec<OsString> {
    // The routine below generates the --check-cfg arguments. Our goals here are to
    // enable the checking of conditionals and pass the list of declared features.
    //
    // In the simplified case, it would resemble something like this:
    //
    //   --check-cfg=cfg() --check-cfg=cfg(feature, values(...))
    //
    // but having `cfg()` is redundant with the second argument (as well-known names
    // and values are implicitly enabled when one or more `--check-cfg` argument is
    // passed) so we don't emit it and just pass:
    //
    //   --check-cfg=cfg(feature, values(...))
    //
    // This way, even if there are no declared features, the config `feature` will
    // still be expected, meaning users would get "unexpected value" instead of name.
    // This wasn't always the case, see rust-lang#119930 for some details.

    let gross_cap_estimation = unit.pkg.summary().features().len() * 7 + 25;
    let mut arg_feature = OsString::with_capacity(gross_cap_estimation);

    arg_feature.push("cfg(feature, values(");
    for (i, feature) in unit.pkg.summary().features().keys().enumerate() {
        if i != 0 {
            arg_feature.push(", ");
        }
        arg_feature.push("\"");
        arg_feature.push(feature);
        arg_feature.push("\"");
    }
    arg_feature.push("))");

    // In addition to the package features, we also include the `test` cfg (since
    // compiler-team#785, as to be able to someday apply it conditionally), as well
    // the `docsrs` cfg from the docs.rs service.
    //
    // We include `docsrs` here (in Cargo) instead of rustc, since there is a much closer
    // relationship between Cargo and docs.rs than rustc and docs.rs. In particular, all
    // users of docs.rs use Cargo, but not all users of rustc (like Rust-for-Linux) use docs.rs.

    vec![
        OsString::from("--check-cfg"),
        OsString::from("cfg(docsrs,test)"),
        OsString::from("--check-cfg"),
        arg_feature,
    ]
}

/// Adds LTO related codegen flags.
fn lto_args(build_runner: &BuildRunner<'_, '_>, unit: &Unit) -> Vec<OsString> {
    lto_args_context(&RustcCommandContext::for_runner(build_runner), unit)
}

fn lto_args_context<L: std::borrow::Borrow<layout::LayoutPaths>>(
    build_runner: &RustcCommandContext<'_, '_, '_, L>,
    unit: &Unit,
) -> Vec<OsString> {
    let mut result = Vec::new();
    let mut push = |arg: &str| {
        result.push(OsString::from("-C"));
        result.push(OsString::from(arg));
    };
    match build_runner.lto[unit] {
        lto::Lto::Run(None) => push("lto"),
        lto::Lto::Run(Some(s)) => push(&format!("lto={}", s)),
        lto::Lto::Off => {
            push("lto=off");
            push("embed-bitcode=no");
        }
        lto::Lto::ObjectAndBitcode => {} // this is rustc's default
        lto::Lto::OnlyBitcode => push("linker-plugin-lto"),
        lto::Lto::OnlyObject => push("embed-bitcode=no"),
    }
    result
}

/// Adds dependency-relevant rustc flags and environment variables
/// to the command to execute, such as [`-L`] and [`--extern`].
///
/// [`-L`]: https://doc.rust-lang.org/nightly/rustc/command-line-arguments.html#-l-add-a-directory-to-the-library-search-path
/// [`--extern`]: https://doc.rust-lang.org/nightly/rustc/command-line-arguments.html#--extern-specify-where-an-external-library-is-located
fn build_deps_args_context<L: std::borrow::Borrow<layout::LayoutPaths>>(
    cmd: &mut ProcessBuilder,
    build_runner: &RustcCommandContext<'_, '_, '_, L>,
    unit: &Unit,
) -> CargoResult<()> {
    let bcx = build_runner.bcx;

    for arg in lib_search_paths_context(build_runner, unit)? {
        cmd.arg(arg);
    }

    let deps = build_runner.unit_deps(unit);

    // If there is not one linkable target but should, rustc fails later
    // on if there is an `extern crate` for it. This may turn into a hard
    // error in the future (see PR #4797).
    if !deps
        .iter()
        .any(|dep| !dep.unit.mode.is_doc() && dep.unit.target.is_linkable())
    {
        if let Some(dep) = deps.iter().find(|dep| {
            !dep.unit.mode.is_doc() && dep.unit.target.is_lib() && !dep.unit.artifact.is_true()
        }) {
            let dep_name = dep.unit.target.crate_name();
            let name = unit.target.crate_name();
            bcx.gctx.shell().print_report(&[
                Level::WARNING.secondary_title(format!("the package `{dep_name}` provides no linkable target"))
                    .elements([
                        Level::NOTE.message(format!("this might cause `{name}` to fail compilation")),
                        Level::NOTE.message("this warning might turn into a hard error in the future"),
                        Level::HELP.message(format!("consider adding 'dylib' or 'rlib' to key 'crate-type' in `{dep_name}`'s Cargo.toml"))
                    ])
            ], false)?;
        }
    }

    let mut unstable_opts = false;

    // Add `OUT_DIR` environment variables for build scripts
    let first_custom_build_dep = deps.iter().find(|dep| dep.unit.mode.is_run_custom_build());
    if let Some(dep) = first_custom_build_dep {
        let out_dir = if bcx.gctx.cli_unstable().build_dir_new_layout {
            build_runner.files().out_dir_new_layout(&dep.unit)
        } else {
            build_runner.files().build_script_out_dir(&dep.unit)
        };
        cmd.env("OUT_DIR", &out_dir);
    }

    // Adding output directory for each build script
    let is_multiple_build_scripts_enabled = unit
        .pkg
        .manifest()
        .unstable_features()
        .require(Feature::multiple_build_scripts())
        .is_ok();

    if is_multiple_build_scripts_enabled {
        for dep in deps {
            if dep.unit.mode.is_run_custom_build() {
                let out_dir = if bcx.gctx.cli_unstable().build_dir_new_layout {
                    build_runner.files().out_dir_new_layout(&dep.unit)
                } else {
                    build_runner.files().build_script_out_dir(&dep.unit)
                };
                let target_name = dep.unit.target.name();
                let out_dir_prefix = target_name
                    .strip_prefix("build-script-")
                    .unwrap_or(target_name);
                let out_dir_name = format!("{out_dir_prefix}_OUT_DIR");
                cmd.env(&out_dir_name, &out_dir);
            }
        }
    }
    for arg in extern_args_context(build_runner, unit, &mut unstable_opts)? {
        cmd.arg(arg);
    }

    for (var, env) in artifact::get_env_context(build_runner, unit, deps)? {
        cmd.env(&var, env);
    }

    // This will only be set if we're already using a feature
    // requiring nightly rust
    if unstable_opts {
        cmd.arg("-Z").arg("unstable-options");
    }

    Ok(())
}

/// Adds extra rustc flags and environment variables collected from the output
/// of a build-script to the command to execute, include custom environment
/// variables and `cfg`.
fn add_custom_flags(
    cmd: &mut ProcessBuilder,
    process_authority: Option<&AuthenticatedTargoProcessAuthority>,
    authenticated_targo: bool,
    build_script_outputs: &BuildScriptOutputs,
    metadata_vec: Option<Vec<UnitHash>>,
) -> CargoResult<()> {
    // Trust: validate every late environment directive before mutating argv or
    // env. This keeps rejection atomic — an authority collision cannot leave
    // cfgs from the same build-script output on the command that eventually
    // runs. Upstream applies directives as it walks them, which would leave the
    // command half-mutated on refusal.
    if let Some(metadata_vec) = metadata_vec.as_deref() {
        for metadata in metadata_vec {
            if let Some(output) = build_script_outputs.get(*metadata) {
                for (name, _) in &output.env {
                    validate_build_script_env_name(authenticated_targo, name)?;
                }
            }
        }
    }

    if let Some(metadata_vec) = metadata_vec {
        for metadata in metadata_vec {
            if let Some(output) = build_script_outputs.get(metadata) {
                for cfg in output.cfgs.iter() {
                    cmd.arg("--cfg").arg(cfg);
                }
                for check_cfg in &output.check_cfgs {
                    cmd.arg("--check-cfg").arg(check_cfg);
                }
                for (name, value) in output.env.iter() {
                    apply_build_script_env(cmd, authenticated_targo, name, value)?;
                }
            }
        }
    }

    // Trust: build-script output is the only thing that reaches the command
    // after `prepare_rustc` decided the process authority, so this is the last
    // point at which the overlay can still be compared against that decision.
    if let Some(authority) = process_authority {
        authority.validate_final_overlay(cmd)?;
    }

    Ok(())
}

fn suppress_native_argfile_output_observation(
    command: &ProcessBuilder,
    observation: &mut Option<output_observation::Observer>,
) {
    if command
        .get_args()
        .any(|arg| arg.as_encoded_bytes().starts_with(b"@"))
    {
        *observation = None;
    }
}

#[cfg(test)]
mod native_argfile_output_tests {
    use super::output_observation::{Emit, Observer};
    use super::suppress_native_argfile_output_observation;
    use cargo_util::ProcessBuilder;

    fn covered(root: &std::path::Path) -> Observer {
        let output = root.join("lib.rmeta");
        let mut observer =
            Observer::new(vec![(output.clone(), Emit::Metadata)], root.to_path_buf());
        observer.observe(
            &serde_json::json!({
                "$message_type": "artifact",
                "artifact": output,
                "emit": "metadata"
            })
            .to_string(),
        );
        observer
    }

    #[test]
    fn late_original_argfiles_withhold_native_coverage_without_changing_argv() {
        let root = tempfile::tempdir().unwrap();
        for option in ["--cfg", "--check-cfg"] {
            for operand in ["@missing.args", "@shell:missing.args", "@"] {
                let mut command = ProcessBuilder::new("trustc");
                command.args(&["--crate-name", "subject", option, operand]);
                let original = command
                    .get_args()
                    .map(ToOwned::to_owned)
                    .collect::<Vec<_>>();
                let mut observer = Some(covered(root.path()));
                suppress_native_argfile_output_observation(&command, &mut observer);
                assert!(observer.is_none(), "{option} {operand}");
                assert_eq!(
                    command
                        .get_args()
                        .map(ToOwned::to_owned)
                        .collect::<Vec<_>>(),
                    original
                );
            }
        }
    }

    #[test]
    fn explicit_cfg_and_embedded_at_signs_keep_native_coverage() {
        let root = tempfile::tempdir().unwrap();
        for (option, operand) in [
            ("--cfg", "literal"),
            ("--cfg", "literal=\"@embedded\""),
            ("--check-cfg", "cfg(literal, values(\"@embedded\"))"),
        ] {
            let mut command = ProcessBuilder::new("trustc");
            command.args(&[option, operand]);
            let mut observer = Some(covered(root.path()));
            suppress_native_argfile_output_observation(&command, &mut observer);
            assert!(observer.and_then(Observer::finish).is_some());
        }
    }

    #[cfg(unix)]
    #[test]
    fn non_unicode_original_argfile_cannot_keep_native_coverage() {
        use std::os::unix::ffi::OsStringExt as _;

        let root = tempfile::tempdir().unwrap();
        let mut command = ProcessBuilder::new("trustc");
        command.arg(std::ffi::OsString::from_vec(vec![b'@', 0xff]));
        let mut observer = Some(covered(root.path()));
        suppress_native_argfile_output_observation(&command, &mut observer);
        assert!(observer.is_none());
    }
}

fn apply_build_script_env(
    cmd: &mut ProcessBuilder,
    authenticated_targo: bool,
    name: &str,
    value: &str,
) -> CargoResult<()> {
    validate_build_script_env_name(authenticated_targo, name)?;
    cmd.env(name, value);
    Ok(())
}

fn validate_build_script_env_name(authenticated_targo: bool, name: &str) -> CargoResult<()> {
    if authenticated_targo
        && is_authenticated_targo_process_authority_env(name)
        // A crate's own build.rs may bake benign provenance stamps (git SHA /
        // dirty flag for its `--version`) into itself via `env!()`; these are
        // never read by trustc/Targo as authority, so the authority guard's
        // `TRUST_`-prefix default-deny is over-broad for them. Exact-name
        // allowlist only — no prefix — so no authority channel slips through.
        && !is_benign_build_script_provenance_env(name)
    {
        anyhow::bail!(
            "authenticated Targo refuses build-script `cargo::rustc-env` authority variable `{name}`"
        );
    }
    Ok(())
}

/// Immutable process state selected by authenticated Targo before dependency
/// build-script output is overlaid at execution time.
///
/// Trust: `add_custom_flags` is upstream's late-mutation point and a build
/// script is arbitrary code, so the authority has to be captured before that
/// overlay and re-compared after it rather than read off the final command.
#[derive(Clone, Debug, PartialEq, Eq)]
struct AuthenticatedTargoProcessAuthority {
    role: RustcProcessRole,
    is_primary_package: bool,
    immutable_env: Vec<(&'static str, Option<OsString>)>,
    reserved_tippy_args: Option<ReservedTippyArgs>,
}

impl AuthenticatedTargoProcessAuthority {
    fn capture_if_authenticated(
        cmd: &ProcessBuilder,
        authenticated_targo: bool,
        role: RustcProcessRole,
        is_primary_package: bool,
    ) -> CargoResult<Option<Self>> {
        if !authenticated_targo {
            return Ok(None);
        }

        let expected_primary = is_primary_package.then(|| OsString::from("1"));
        if cmd.get_env(CARGO_PRIMARY_PACKAGE_ENV) != expected_primary {
            anyhow::bail!(
                "authenticated Targo failed to establish canonical {CARGO_PRIMARY_PACKAGE_ENV} state for a {}primary package",
                if is_primary_package { "" } else { "non-" }
            );
        }

        let cargo_frontend = cmd.get_env(crate::CARGO_ENV).ok_or_else(|| {
            anyhow::format_err!(
                "authenticated Targo failed to establish canonical {} state for a compiler process",
                crate::CARGO_ENV
            )
        })?;
        let mut immutable_env = vec![
            (CARGO_PRIMARY_PACKAGE_ENV, expected_primary),
            (crate::CARGO_ENV, Some(cargo_frontend)),
        ];
        if role.is_primary_override() {
            if cmd.get_env(FIX_ENV_INTERNAL).is_none() {
                anyhow::bail!(
                    "authenticated Targo primary compiler override is missing its internal {FIX_ENV_INTERNAL} fix-proxy channel"
                );
            }
            immutable_env.extend(
                FIX_PROXY_CONTROL_ENVS
                    .iter()
                    .map(|&name| (name, cmd.get_env(name))),
            );

            let downstream_wrapper = cmd.get_env(RUSTC_WORKSPACE_WRAPPER_ENV);
            if role.has_downstream_workspace_wrapper() != downstream_wrapper.is_some() {
                anyhow::bail!(
                    "authenticated Targo primary compiler override has inconsistent {RUSTC_WORKSPACE_WRAPPER_ENV} state"
                );
            }
            immutable_env.push((RUSTC_WORKSPACE_WRAPPER_ENV, downstream_wrapper));
        }

        let reserved_tippy_args =
            snapshot_reserved_tippy_args_for_invocation(cmd, true, Some(role))?;
        Ok(Some(Self {
            role,
            is_primary_package,
            immutable_env,
            reserved_tippy_args,
        }))
    }

    fn validate_final_overlay(&self, cmd: &ProcessBuilder) -> CargoResult<()> {
        for (name, expected) in &self.immutable_env {
            let actual = cmd.get_env(name);
            if actual != *expected {
                anyhow::bail!(
                    "authenticated Targo's final build-script overlay changed immutable process authority `{name}` for role {:?}: expected {expected:?}, got {actual:?}",
                    self.role
                );
            }
        }
        if self.role.uses_workspace_wrapper() {
            let actual = ReservedTippyArgs::capture_if_present(
                |name| cmd.get_env(name),
                "final compiler process",
            )?;
            if actual.as_ref() != self.reserved_tippy_args.as_ref() {
                anyhow::bail!(
                    "authenticated Targo's final build-script overlay changed immutable Tippy frontend arguments for role {:?}",
                    self.role
                );
            }
        }
        debug_assert_eq!(
            cmd.get_env(CARGO_PRIMARY_PACKAGE_ENV).is_some(),
            self.is_primary_package
        );
        Ok(())
    }
}

/// One immutable snapshot of the protected frontend argument channels across
/// late build-script environment application. Authenticated Targo rejects
/// these names in project `[env]` configuration before any process is built.
#[derive(Clone, Debug, PartialEq, Eq)]
struct ReservedTippyArgs {
    encoded: OsString,
    legacy: OsString,
}

impl ReservedTippyArgs {
    fn capture_if_present(
        mut get: impl FnMut(&str) -> Option<OsString>,
        process: &str,
    ) -> CargoResult<Option<Self>> {
        let encoded = get(TIPPY_ENCODED_ARGS_ENV);
        let legacy = get(CLIPPY_ARGS_ENV);
        match (encoded, legacy) {
            (None, None) => Ok(None),
            (Some(encoded), Some(legacy)) => Ok(Some(Self { encoded, legacy })),
            (None, Some(_)) => Err(anyhow::format_err!(
                "Tippy {process} has {CLIPPY_ARGS_ENV} but is missing its internal {TIPPY_ENCODED_ARGS_ENV} frontend channel"
            )),
            (Some(_), None) => Err(anyhow::format_err!(
                "Tippy {process} has {TIPPY_ENCODED_ARGS_ENV} but is missing its protected {CLIPPY_ARGS_ENV} compatibility channel"
            )),
        }
    }
}

fn snapshot_reserved_tippy_args_for_invocation(
    cmd: &ProcessBuilder,
    targo_invocation: bool,
    rustc_process_role: Option<RustcProcessRole>,
) -> CargoResult<Option<ReservedTippyArgs>> {
    if !targo_invocation
        || !rustc_process_role.is_some_and(RustcProcessRole::uses_workspace_wrapper)
    {
        return Ok(None);
    }
    ReservedTippyArgs::capture_if_present(|name| cmd.get_env(name), "compiler process")
}

/// Generate a list of `-L` arguments
#[tracing::instrument(skip_all)]
pub fn lib_search_paths(
    build_runner: &BuildRunner<'_, '_>,
    unit: &Unit,
) -> CargoResult<Vec<OsString>> {
    lib_search_paths_context(&RustcCommandContext::for_runner(build_runner), unit)
}

fn lib_search_paths_context<L: std::borrow::Borrow<layout::LayoutPaths>>(
    build_runner: &RustcCommandContext<'_, '_, '_, L>,
    unit: &Unit,
) -> CargoResult<Vec<OsString>> {
    let mut lib_search_paths = Vec::new();
    if build_runner.bcx.gctx.cli_unstable().build_dir_new_layout {
        // Add all dependency args to rustc process
        let paths = dep_paths_for_args(unit, build_runner);

        for path in paths {
            let mut deps = OsString::from("dependency=");
            deps.push(path);
            lib_search_paths.extend(["-L".into(), deps]);
        }
    } else {
        let mut deps = OsString::from("dependency=");
        deps.push(build_runner.files().deps_dir(unit));
        lib_search_paths.extend(["-L".into(), deps]);
    }

    // Be sure that the host path is also listed. This'll ensure that proc macro
    // dependencies are correctly found (for reexported macros).
    if !unit.kind.is_host() {
        let mut deps = OsString::from("dependency=");
        deps.push(build_runner.files().host_deps(unit));
        lib_search_paths.extend(["-L".into(), deps]);
    }

    Ok(lib_search_paths)
}

/// Generate a list of paths for the rustc `-L` args.
///
/// To generate the list of paths we walk the dependency graph using DFS with a stack.
///
/// We try to avoid bloating the amount of args passed rustc as it can cause issues with OS limits
/// for large projects. (and generally just makes the rustc command ugly!).
/// Below are the rules for excluding build units from the args.
/// 1. Don't include build script out dir in the args to reduce rustc command bloat.
/// 2. Proc macros are statically linked, so when including a proc-macro dependency we can skip
///    adding it's dependencies. Note that we still do add them when we are compiling the
///    proc-macro itself.
/// 3. Don't include direct dependencies because they are passed with `--extern` and rustc does not
///    need `-L` if it was already passed as `--extern`
fn dep_paths_for_args<L: std::borrow::Borrow<layout::LayoutPaths>>(
    unit: &Unit,
    build_runner: &RustcCommandContext<'_, '_, '_, L>,
) -> Vec<PathBuf> {
    let direct = build_runner.unit_deps(unit);
    if direct.is_empty() {
        return Vec::new();
    }
    let mut indirect = HashSet::default();
    let mut visited = HashSet::default();
    let mut stack: Vec<&Unit> = direct
        .iter()
        .filter(|d| !d.unit.target.is_custom_build())
        .map(|d| &d.unit)
        .collect();
    while let Some(u) = stack.pop() {
        if !visited.insert(u.clone()) {
            continue;
        }
        if u.target.proc_macro() {
            continue;
        }
        for dep in build_runner.unit_deps(u) {
            let v = &dep.unit;
            if v.target.is_custom_build() {
                continue;
            }
            indirect.insert(v.clone());
            if v.target.proc_macro() {
                continue;
            }
            if !visited.contains(v) {
                stack.push(v);
            }
        }
    }

    let mut paths: Vec<PathBuf> = indirect
        .into_iter()
        .map(|u| build_runner.files().deps_dir(&u))
        .collect();

    // We are in the hot path that needs to always run (even for rebuilds)
    // There could be a potentially large amount of paths for large workspaces.
    // We want to sort and dedup the paths but doing so is a bit expsensive when comparing PathBufs
    // directly. So instead we only sort valid Utf8 paths as &str's which is a bit faster.
    // We do not allow non utf8 paths when building, so we take advantage of that by treating them
    // as a single value when sorting/deduplicating.
    //
    // For reference this saves about ~30ms on Zed
    paths.sort_unstable_by(|a, b| match (a.to_str(), b.to_str()) {
        (Some(a), Some(b)) => a.cmp(b),
        (Some(_), None) => std::cmp::Ordering::Less,
        (None, Some(_)) => std::cmp::Ordering::Greater,
        (None, None) => std::cmp::Ordering::Less,
    });
    paths.dedup_by(|a, b| matches!((a.to_str(), b.to_str()), (Some(x), Some(y)) if x == y));

    paths
}

fn is_public_dependency_enabled(build_runner: &BuildRunner<'_, '_>, unit: &Unit) -> bool {
    is_public_dependency_enabled_context(build_runner.bcx, unit)
}

fn is_public_dependency_enabled_context(bcx: &BuildContext<'_, '_>, unit: &Unit) -> bool {
    unit.pkg
        .manifest()
        .unstable_features()
        .require(Feature::public_dependency())
        .is_ok()
        || bcx.gctx.cli_unstable().public_dependency
}

/// Generates a list of `--extern` arguments.
pub fn extern_args(
    build_runner: &BuildRunner<'_, '_>,
    unit: &Unit,
    unstable_opts: &mut bool,
) -> CargoResult<Vec<OsString>> {
    extern_args_context(
        &RustcCommandContext::for_runner(build_runner),
        unit,
        unstable_opts,
    )
}

fn extern_args_context<L: std::borrow::Borrow<layout::LayoutPaths>>(
    build_runner: &RustcCommandContext<'_, '_, '_, L>,
    unit: &Unit,
    unstable_opts: &mut bool,
) -> CargoResult<Vec<OsString>> {
    let mut result = Vec::new();
    let deps = build_runner.unit_deps(unit);

    let no_embed_metadata = !build_runner
        .bcx
        .target_data
        .info(unit.kind)
        .should_embed_metadata();
    let public_dependency_enabled = is_public_dependency_enabled_context(build_runner.bcx, unit);

    // Closure to add one dependency to `result`.
    let mut link_to = |dep: &UnitDep,
                       extern_crate_name: InternedString,
                       noprelude: bool,
                       nounused: bool|
     -> CargoResult<()> {
        let mut value = OsString::new();
        let mut opts = Vec::new();
        if !dep.public && unit.target.is_lib() && public_dependency_enabled {
            opts.push("priv");
            *unstable_opts = true;
        }
        if noprelude {
            opts.push("noprelude");
            *unstable_opts = true;
        }
        if nounused {
            opts.push("nounused");
            *unstable_opts = true;
        }
        if !opts.is_empty() {
            value.push(opts.join(","));
            value.push(":");
        }
        value.push(extern_crate_name.as_str());
        value.push("=");

        let outputs = build_runner.outputs(&dep.unit)?;
        let mut pass = |index: usize| -> CargoResult<()> {
            build_runner.record_extern(&dep.unit, &outputs, index)?;
            let mut value = value.clone();
            value.push(&outputs[index].path);
            result.push(OsString::from("--extern"));
            result.push(value);
            Ok(())
        };

        if build_runner.only_requires_rmeta(unit, &dep.unit) || dep.unit.mode.is_check() {
            // Example: rlib dependency for an rlib, rmeta is all that is required.
            let output = outputs
                .iter()
                .position(|output| output.flavor == FileFlavor::Rmeta)
                .expect("failed to find rmeta dep for pipelined dep");
            pass(output)?;
        } else {
            // Example: a bin needs `rlib` for dependencies, it cannot use rmeta.
            for (index, output) in outputs.iter().enumerate() {
                if output.flavor == FileFlavor::Linkable {
                    pass(index)?;
                }
                // If we use -Zembed-metadata=no, we also need to pass the path to the
                // corresponding .rmeta file to the linkable artifact, because the
                // normal dependency (rlib) doesn't contain the full metadata.
                else if no_embed_metadata && output.flavor == FileFlavor::Rmeta {
                    pass(index)?;
                }
            }
        }
        Ok(())
    };

    for dep in deps {
        if dep.unit.target.is_linkable() && !dep.unit.mode.is_doc() {
            link_to(dep, dep.extern_crate_name, dep.noprelude, dep.nounused)?;
        }
    }
    if unit.target.proc_macro() {
        // Automatically import `proc_macro`.
        result.push(OsString::from("--extern"));
        result.push(OsString::from("proc_macro"));
    }

    Ok(result)
}

/// Trust: one selector shared by fingerprinting and compiler argv construction.
fn configured_linker<'a>(
    compilation: &'a Compilation<'_>,
    unit: &Unit,
    target_applies_to_host: bool,
) -> Option<&'a Path> {
    if unit.target.for_host() && !target_applies_to_host {
        compilation.host_linker()
    } else {
        compilation.target_linker(unit.kind)
    }
}

/// Adds `-C linker=<path>` if specified.
fn add_codegen_linker_context<L: std::borrow::Borrow<layout::LayoutPaths>>(
    cmd: &mut ProcessBuilder,
    build_runner: &RustcCommandContext<'_, '_, '_, L>,
    unit: &Unit,
    target_applies_to_host: bool,
) {
    // Trust: fingerprinting and argv must select the exact same host/target tool.
    let linker = configured_linker(&build_runner.compilation, unit, target_applies_to_host);

    if let Some(linker) = linker {
        let mut arg = OsString::from("linker=");
        arg.push(linker.as_os_str());
        cmd.arg("-C").arg(arg);
    }
}

/// Adds `-C incremental=<path>`.
fn add_codegen_incremental<L: std::borrow::Borrow<layout::LayoutPaths>>(
    cmd: &mut ProcessBuilder,
    build_runner: &RustcCommandContext<'_, '_, '_, L>,
    unit: &Unit,
) {
    let dir = if build_runner.bcx.confines(unit) {
        build_runner.files().output_dir(unit).join("incremental")
    } else {
        build_runner.files().incremental_dir(&unit).to_path_buf()
    };
    let mut arg = OsString::from("incremental=");
    arg.push(dir.as_os_str());
    cmd.arg("-C").arg(arg);
}

fn envify(s: &str) -> String {
    s.chars()
        .flat_map(|c| c.to_uppercase())
        .map(|c| if c == '-' { '_' } else { c })
        .collect()
}

/// Configuration of the display of messages emitted by the compiler,
/// e.g. diagnostics, warnings, errors, and message caching.
struct OutputOptions {
    /// Only live native dirty compiler callbacks populate this bounded observer.
    output_observation: Option<output_observation::Observer>,
    /// Trust: legacy, native without demand, or live demanded metadata.
    metadata_readiness: metadata_readiness::MetadataReadiness,
    /// What format we're emitting from Cargo itself.
    format: MessageFormat,
    /// Where to write the JSON messages to support playback later if the unit
    /// is fresh. The file is created lazily so that in the normal case, lots
    /// of empty files are not created. If this is None, the output will not
    /// be cached (such as when replaying cached messages).
    cache_cell: Option<(PathBuf, OnceCell<File>)>,
    /// If `true`, display any diagnostics.
    /// Other types of JSON messages are processed regardless
    /// of the value of this flag.
    ///
    /// This is used primarily for cache replay. If you build with `-vv`, the
    /// cache will be filled with diagnostics from dependencies. When the
    /// cache is replayed without `-vv`, we don't want to show them.
    show_diagnostics: bool,
    /// Trust: only fresh-cache replay may retain this exact non-lint disclosure
    /// despite capped dependency warnings. Dirty docscrape suppression stays
    /// unchanged. This controls display, never authority or a proof grade.
    replay_native_disclosure: bool,
    /// Tracks the number of warnings we've seen so far.
    warnings_seen: usize,
    /// Tracks the number of errors we've seen so far.
    errors_seen: usize,
}

impl OutputOptions {
    fn for_dirty(build_runner: &BuildRunner<'_, '_>, unit: &Unit) -> OutputOptions {
        let path = build_runner.files().message_cache_path(unit);
        // Remove old cache, ignore ENOENT, which is the common case.
        drop(fs::remove_file(&path));
        let cache_cell = Some((path, OnceCell::new()));

        let show_diagnostics = true;

        let format = build_runner.bcx.build_config.message_format;

        OutputOptions {
            output_observation: None,
            metadata_readiness: metadata_readiness::MetadataReadiness::without_demand(
                crate::is_targo_invocation(),
            ),
            format,
            cache_cell,
            show_diagnostics,
            replay_native_disclosure: false,
            warnings_seen: 0,
            errors_seen: 0,
        }
    }

    fn for_fresh(build_runner: &BuildRunner<'_, '_>, unit: &Unit) -> OutputOptions {
        let cache_cell = None;

        // We always replay the output cache,
        // since it might contain future-incompat-report messages
        let show_diagnostics = unit.show_warnings(build_runner.bcx.gctx);

        let format = build_runner.bcx.build_config.message_format;

        OutputOptions {
            output_observation: None,
            metadata_readiness: metadata_readiness::MetadataReadiness::without_demand(
                crate::is_targo_invocation(),
            ),
            format,
            cache_cell,
            show_diagnostics,
            replay_native_disclosure: true,
            warnings_seen: 0,
            errors_seen: 0,
        }
    }

    // Trust: inspect structured compiler fields for display only. No authority
    // or evidence classification follows from this message.
    fn displays_diagnostic(&self, level: &str, message: &str, has_code: bool) -> bool {
        self.show_diagnostics
            || (self.replay_native_disclosure
                && level == "note"
                && !has_code
                && message == "compiled WITHOUT Trust verification — 0 obligations checked")
    }
}

#[cfg(test)]
// Trust: preserve exact disclosure, warning caps and dirty suppression.
mod native_disclosure_replay_tests {
    use super::{MessageFormat, OutputOptions};

    fn hidden(replay: bool) -> OutputOptions {
        OutputOptions {
            output_observation: None,
            metadata_readiness: super::metadata_readiness::MetadataReadiness::without_demand(false),
            format: MessageFormat::Human,
            cache_cell: None,
            show_diagnostics: false,
            replay_native_disclosure: replay,
            warnings_seen: 0,
            errors_seen: 0,
        }
    }

    #[test]
    fn replay_retains_only_the_exact_non_lint_native_disclosure() {
        let replay = hidden(true);
        let message = "compiled WITHOUT Trust verification — 0 obligations checked";
        assert!(replay.displays_diagnostic("note", message, false));
        assert!(!replay.displays_diagnostic("warning", message, false));
        assert!(!replay.displays_diagnostic("error", message, false));
        assert!(!replay.displays_diagnostic("note", message, true));
        for other in [
            format!("{message}; future field"),
            format!("prefix: {message}"),
            "proof: Certified".to_string(),
            "verdict: Unknown".to_string(),
            "another dependency warning".to_string(),
        ] {
            assert!(
                !replay.displays_diagnostic("note", &other, false),
                "{other}"
            );
        }
    }

    #[test]
    fn dirty_docscrape_suppression_and_visible_warning_policy_stay_unchanged() {
        let mut dirty = hidden(false);
        assert!(!dirty.displays_diagnostic(
            "note",
            "compiled WITHOUT Trust verification — 0 obligations checked",
            false,
        ));
        assert!(!dirty.displays_diagnostic("warning", "ordinary warning", true));
        dirty.show_diagnostics = true;
        assert!(dirty.displays_diagnostic("warning", "ordinary warning", true));
    }
}

/// Cloned and sendable context about the manifest file.
///
/// Sometimes we enrich rustc's errors with some locations in the manifest file; this
/// contains a `Send`-able copy of the manifest information that we need for the
/// enriched errors.
struct ManifestErrorContext {
    /// The path to the manifest.
    path: PathBuf,
    /// The locations of various spans within the manifest.
    spans: Option<Arc<toml::Spanned<toml::de::DeTable<'static>>>>,
    /// The raw manifest contents.
    contents: Option<String>,
    /// A lookup for all the unambiguous renamings, mapping from the original package
    /// name to the renamed one.
    rename_table: HashMap<InternedString, InternedString>,
    /// A list of targets we're compiling for, to determine which of the `[target.<something>.dependencies]`
    /// tables might be of interest.
    requested_kinds: Vec<CompileKind>,
    /// A list of all the collections of cfg values, one collection for each target, to determine
    /// which of the `[target.'cfg(...)'.dependencies]` tables might be of interest.
    cfgs: Vec<Vec<Cfg>>,
    host_name: InternedString,
    // Trust: the fields below are the Cargo-owned half of a unit's proof
    // identity. They are carried on the error context because that is the one
    // structure that survives from unit-graph construction into the job-queue
    // closures where diagnostics and artifacts are emitted.
    /// Exact rustc `--target` value for this unit, or the compiler host triple
    /// when this is a host unit. Present only in authenticated Targo JSON.
    trust_compile_target: Option<String>,
    /// Exact bytes of a custom JSON target specification at command
    /// construction time. Artifact emission independently hashes the file
    /// again, so persistent same-path mutation cannot retain one identity.
    trust_compile_target_spec_sha256: Option<String>,
    /// Exact Cargo unit mode. This is part of proof identity because one target
    /// may be compiled both normally and with `cfg(test)` in the same command.
    trust_compile_mode: Option<&'static str>,
    /// Cargo host-vs-target context, which stays distinct even when both use
    /// the same rustc target triple.
    trust_compile_kind: Option<&'static str>,
    /// SHA-256 over Cargo's complete semantic unit context, preventing two
    /// same-target/same-mode feature or profile views from sharing evidence.
    trust_unit_identity_sha256: Option<String>,
    /// Cargo-owned exact proof subject for this compiler unit. This is not
    /// sourced from rustc output and therefore cannot be self-asserted by a
    /// diagnostic or proc macro.
    trust_proof_unit: Option<machine_message::TrustProofUnit>,
    /// Cargo's working directory (for printing out a more friendly manifest path).
    cwd: PathBuf,
    /// Terminal width for formatting diagnostics.
    term_width: usize,
}

fn on_stdout_line(
    state: &JobState<'_, '_>,
    line: &str,
    package_id: PackageId,
    target: &Target,
) -> CargoResult<()> {
    if verified_targo_protocol_active() {
        // Trust: Cargo JSON stdout is the authenticated outer envelope, so this
        // upstream passthrough becomes a refusal. Forwarding a child line
        // verbatim would let a compiler plugin/proc macro forge
        // `compiler-message`, `compiler-artifact`, inventory, or terminal
        // `build-finished` records. rustc/rustdoc diagnostics belong on stderr;
        // any stdout from a real verified unit is therefore a channel breach.
        // Do not quote the attacker-controlled line in the diagnostic.
        anyhow::bail!(
            "authenticated Targo compiler unit {package_id} target {:?} emitted unexpected stdout; the canonical Cargo JSON stdout channel is reserved for Targo-owned envelopes",
            target.name()
        );
    }
    state.stdout(line.to_string())?;
    Ok(())
}

fn on_stderr_line(
    state: &JobState<'_, '_>,
    line: &str,
    package_id: PackageId,
    manifest: &ManifestErrorContext,
    target: &Target,
    options: &mut OutputOptions,
) -> CargoResult<()> {
    if on_stderr_line_inner(state, line, package_id, manifest, target, options)? {
        // Check if caching is enabled.
        if let Some((path, cell)) = &mut options.cache_cell {
            // Cache the output, which will be replayed later when Fresh.
            let f = cell.try_borrow_mut_with(|| paths::create(path))?;
            debug_assert!(!line.contains('\n'));
            f.write_all(line.as_bytes())?;
            f.write_all(&[b'\n'])?;
        }
    }
    Ok(())
}

/// Returns true if the line should be cached.
fn on_stderr_line_inner(
    state: &JobState<'_, '_>,
    line: &str,
    package_id: PackageId,
    manifest: &ManifestErrorContext,
    target: &Target,
    options: &mut OutputOptions,
) -> CargoResult<bool> {
    // We primarily want to use this function to process JSON messages from
    // rustc. The compiler should always print one JSON message per line, and
    // otherwise it may have other output intermingled (think RUST_LOG or
    // something like that), so skip over everything that doesn't look like a
    // JSON message.
    if !line.starts_with('{') {
        state.stderr(line.to_string())?;
        return Ok(true);
    }

    let mut compiler_message: Box<serde_json::value::RawValue> = match serde_json::from_str(line) {
        Ok(msg) => msg,

        // If the compiler produced a line that started with `{` but it wasn't
        // valid JSON, maybe it wasn't JSON in the first place! Forward it along
        // to stderr.
        Err(e) => {
            debug!("failed to parse json: {:?}", e);
            state.stderr(line.to_string())?;
            return Ok(true);
        }
    };

    if let Some(observation) = &mut options.output_observation {
        observation.observe(compiler_message.get());
    }

    // Trust: validate demanded artifact records before a diagnostic-shaped
    // record or malformed artifact field can bypass the readiness gate.
    if let Some(ready) = options
        .metadata_readiness
        .intercept(compiler_message.get())?
    {
        if ready {
            state.rmeta_produced();
        }
        return Ok(false);
    }

    let count_diagnostic = |level, options: &mut OutputOptions| {
        if level == "warning" {
            options.warnings_seen += 1;
        } else if level == "error" {
            options.errors_seen += 1;
        }
    };

    if let Ok(report) = serde_json::from_str::<FutureIncompatReport>(compiler_message.get()) {
        for item in &report.future_incompat_report {
            count_diagnostic(&*item.diagnostic.level, options);
        }
        state.future_incompat_report(report.future_incompat_report);
        return Ok(true);
    }

    let res = serde_json::from_str::<SectionTiming>(compiler_message.get());
    if let Ok(timing_record) = res {
        state.on_section_timing_emitted(timing_record);
        return Ok(false);
    }

    // Returns `true` if the diagnostic was modified.
    let add_pub_in_priv_diagnostic = |diag: &mut String| -> bool {
        // We are parsing the compiler diagnostic here, as this information isn't
        // currently exposed elsewhere.
        // At the time of writing this comment, rustc emits two different
        // "exported_private_dependencies" errors:
        //  - type `FromPriv` from private dependency 'priv_dep' in public interface
        //  - struct `FromPriv` from private dependency 'priv_dep' is re-exported
        // This regex matches them both. To see if it needs to be updated, grep the rust
        // source for "EXPORTED_PRIVATE_DEPENDENCIES".
        static PRIV_DEP_REGEX: LazyLock<Regex> =
            LazyLock::new(|| Regex::new("from private dependency '([A-Za-z0-9-_]+)'").unwrap());
        if let Some(crate_name) = PRIV_DEP_REGEX.captures(diag).and_then(|m| m.get(1))
            && let Some(ref contents) = manifest.contents
            && let Some(span) = manifest.find_crate_span(crate_name.as_str())
        {
            let rel_path = pathdiff::diff_paths(&manifest.path, &manifest.cwd)
                .unwrap_or_else(|| manifest.path.clone())
                .display()
                .to_string();
            let report = [Group::with_title(Level::NOTE.secondary_title(format!(
                "dependency `{}` declared here",
                crate_name.as_str()
            )))
            .element(
                Snippet::source(contents)
                    .path(rel_path)
                    .annotation(AnnotationKind::Context.span(span)),
            )];

            let rendered = Renderer::styled()
                .term_width(manifest.term_width)
                .render(&report);
            diag.push_str(&rendered);
            diag.push('\n');
            return true;
        }
        false
    };

    // Depending on what we're emitting from Cargo itself, we figure out what to
    // do with this JSON message.
    match options.format {
        // In the "human" output formats (human/short) or if diagnostic messages
        // from rustc aren't being included in the output of Cargo's JSON
        // messages then we extract the diagnostic (if present) here and handle
        // it ourselves.
        MessageFormat::Human
        | MessageFormat::Short
        | MessageFormat::Json {
            render_diagnostics: true,
            ..
        } => {
            #[derive(serde::Deserialize)]
            struct CompilerMessage<'a> {
                // `rendered` contains escape sequences, which can't be
                // zero-copy deserialized by serde_json.
                // See https://github.com/serde-rs/json/issues/742
                rendered: String,
                #[serde(borrow)]
                message: Cow<'a, str>,
                #[serde(borrow)]
                level: Cow<'a, str>,
                children: Vec<PartialDiagnostic>,
                code: Option<DiagnosticCode>,
            }

            // A partial rustfix::diagnostics::Diagnostic. We deserialize only a
            // subset of the fields because rustc's output can be extremely
            // deeply nested JSON in pathological cases involving macro
            // expansion. Rustfix's Diagnostic struct is recursive containing a
            // field `children: Vec<Self>`, and it can cause deserialization to
            // hit serde_json's default recursion limit, or overflow the stack
            // if we turn that off. Cargo only cares about the 1 field listed
            // here.
            #[derive(serde::Deserialize)]
            struct PartialDiagnostic {
                spans: Vec<PartialDiagnosticSpan>,
            }

            // A partial rustfix::diagnostics::DiagnosticSpan.
            #[derive(serde::Deserialize)]
            struct PartialDiagnosticSpan {
                suggestion_applicability: Option<Applicability>,
            }

            #[derive(serde::Deserialize)]
            struct DiagnosticCode {
                code: String,
            }

            if let Ok(mut msg) = serde_json::from_str::<CompilerMessage<'_>>(compiler_message.get())
            {
                if msg.message.starts_with("aborting due to")
                    || msg.message.ends_with("warning emitted")
                    || msg.message.ends_with("warnings emitted")
                {
                    // Skip this line; we'll print our own summary at the end.
                    return Ok(true);
                }
                // state.stderr will add a newline
                if msg.rendered.ends_with('\n') {
                    msg.rendered.pop();
                }
                let mut rendered = msg.rendered;
                if options.displays_diagnostic(&msg.level, &msg.message, msg.code.is_some()) {
                    let machine_applicable: bool = msg
                        .children
                        .iter()
                        .map(|child| {
                            child
                                .spans
                                .iter()
                                .filter_map(|span| span.suggestion_applicability)
                                .any(|app| app == Applicability::MachineApplicable)
                        })
                        .any(|b| b);
                    count_diagnostic(&msg.level, options);
                    if msg
                        .code
                        .as_ref()
                        .is_some_and(|c| c.code == "exported_private_dependencies")
                        && options.format != MessageFormat::Short
                    {
                        add_pub_in_priv_diagnostic(&mut rendered);
                    }
                    let lint = msg.code.is_some();
                    state.emit_diag(&msg.level, rendered, lint, machine_applicable)?;
                }
                return Ok(true);
            }
        }

        MessageFormat::Json { ansi, .. } => {
            #[derive(serde::Deserialize, serde::Serialize)]
            struct CompilerMessage<'a> {
                rendered: String,
                #[serde(flatten, borrow)]
                other: std::collections::BTreeMap<Cow<'a, str>, serde_json::Value>,
                code: Option<DiagnosticCode<'a>>,
            }

            #[derive(serde::Deserialize, serde::Serialize)]
            struct DiagnosticCode<'a> {
                code: String,
                #[serde(flatten, borrow)]
                other: std::collections::BTreeMap<Cow<'a, str>, serde_json::Value>,
            }

            if let Ok(mut error) =
                serde_json::from_str::<CompilerMessage<'_>>(compiler_message.get())
            {
                let modified_diag = if error
                    .code
                    .as_ref()
                    .is_some_and(|c| c.code == "exported_private_dependencies")
                {
                    add_pub_in_priv_diagnostic(&mut error.rendered)
                } else {
                    false
                };

                // Remove color information from the rendered string if color is not
                // enabled. Cargo always asks for ANSI colors from rustc. This allows
                // cached replay to enable/disable colors without re-invoking rustc.
                if !ansi {
                    error.rendered = anstream::adapter::strip_str(&error.rendered).to_string();
                }
                if !ansi || modified_diag {
                    let new_line = serde_json::to_string(&error)?;
                    compiler_message = serde_json::value::RawValue::from_string(new_line)?;
                }
            }
        }
    }

    // We always tell rustc to emit messages about artifacts being produced.
    // These messages feed into pipelined compilation, as well as timing
    // information.
    //
    // Look for a matching directive and inform Cargo internally that a
    // metadata file has been produced.
    #[derive(serde::Deserialize)]
    struct ArtifactNotification<'a> {
        #[serde(borrow)]
        artifact: Cow<'a, str>,
    }

    if let Ok(artifact) = serde_json::from_str::<ArtifactNotification<'_>>(compiler_message.get()) {
        trace!("found directive from rustc: `{}`", artifact.artifact);
        // Trust: native dirty demand requires the exact current metadata
        // report, while legacy Cargo retains its existing suffix protocol.
        if options
            .metadata_readiness
            .observe(compiler_message.get(), &artifact.artifact)?
        {
            debug!("looks like metadata finished early!");
            state.rmeta_produced();
        }
        return Ok(false);
    }

    #[derive(serde::Deserialize)]
    struct UnusedExterns {
        unused_extern_names: std::collections::BTreeSet<InternedString>,
    }
    if let Ok(uext) = serde_json::from_str::<UnusedExterns>(compiler_message.get()) {
        trace!(
            "obtained unused externs list from rustc: `{:?}`",
            uext.unused_extern_names
        );
        state.unused_externs(uext.unused_extern_names);
        return Ok(true);
    }

    // And failing all that above we should have a legitimate JSON diagnostic
    // from the compiler, so wrap it in an external Cargo JSON message
    // indicating which package it came from and then emit it.

    #[derive(serde::Deserialize)]
    struct CompilerMessage<'a> {
        #[serde(borrow)]
        message: Cow<'a, str>,
        #[serde(borrow)]
        level: Cow<'a, str>,
        // Trust: classify the cached non-lint note before the visibility gate.
        code: Option<serde_json::Value>,
        // Trust: retain the same fixability accounting as rendered diagnostics.
        children: Vec<PartialDiagnostic>,
    }

    #[derive(serde::Deserialize)]
    struct PartialDiagnostic {
        spans: Vec<PartialDiagnosticSpan>,
    }

    #[derive(serde::Deserialize)]
    struct PartialDiagnosticSpan {
        suggestion_applicability: Option<Applicability>,
    }

    let diagnostic = serde_json::from_str::<CompilerMessage<'_>>(compiler_message.get());
    let show_diagnostic = diagnostic.as_ref().map_or(options.show_diagnostics, |msg| {
        options.displays_diagnostic(&msg.level, &msg.message, msg.code.is_some())
    });
    if !show_diagnostic {
        return Ok(true);
    }

    if let Ok(msg) = diagnostic {
        if msg.message.starts_with("aborting due to")
            || msg.message.ends_with("warning emitted")
            || msg.message.ends_with("warnings emitted")
        {
            // Skip this line; we'll print our own summary at the end.
            return Ok(true);
        }
        count_diagnostic(&msg.level, options);
        // Trust: JSON output bypasses emit_diag, so report its warnings to the
        // coordinator too. Otherwise build.warnings=deny silently succeeds.
        if msg.level == "warning" {
            let fixable = msg.children.iter().any(|child| {
                child.spans.iter().any(|span| {
                    span.suggestion_applicability == Some(Applicability::MachineApplicable)
                })
            });
            state.count_json_warning(msg.code.is_some(), fixable);
        }
    }

    let msg = machine_message::FromCompiler {
        package_id: package_id.to_spec(),
        manifest_path: &manifest.path,
        target,
        trust_compile_target: manifest.trust_compile_target.as_deref(),
        trust_compile_target_spec_sha256: manifest.trust_compile_target_spec_sha256.as_deref(),
        trust_compile_mode: manifest.trust_compile_mode,
        trust_compile_kind: manifest.trust_compile_kind,
        trust_unit_identity_sha256: manifest.trust_unit_identity_sha256.as_deref(),
        trust_proof_unit: manifest.trust_proof_unit.as_ref(),
        message: compiler_message,
    }
    .to_json_string();

    // Switch json lines from rustc/rustdoc that appear on stderr to stdout
    // instead. We want the stdout of Cargo to always be machine parseable as
    // stderr has our colorized human-readable messages.
    state.stdout(msg)?;
    Ok(true)
}

impl ManifestErrorContext {
    fn new(build_runner: &BuildRunner<'_, '_>, unit: &Unit) -> CargoResult<ManifestErrorContext> {
        let mut duplicates = HashSet::default();
        let mut rename_table = HashMap::default();

        for dep in build_runner.unit_deps(unit) {
            let unrenamed_id = dep.unit.pkg.package_id().name();
            if duplicates.contains(&unrenamed_id) {
                continue;
            }
            match rename_table.entry(unrenamed_id) {
                std::collections::hash_map::Entry::Occupied(occ) => {
                    occ.remove_entry();
                    duplicates.insert(unrenamed_id);
                }
                std::collections::hash_map::Entry::Vacant(vac) => {
                    vac.insert(dep.extern_crate_name);
                }
            }
        }

        let bcx = build_runner.bcx;
        // Trust: compute unit identity once, here, where `BuildRunner` is still
        // available. The diagnostic-forwarding path that consumes it runs on a
        // job-queue thread and must not be able to recompute or influence it.
        let trust_target_identity_enabled = crate::is_targo_invocation();
        let trust_compile_target_spec_sha256 = if trust_target_identity_enabled {
            exact_unit_compile_target_spec_sha256(unit.kind)?
        } else {
            None
        };
        let trust_unit_identity_sha256 = trust_target_identity_enabled
            .then(|| {
                let captured = exact_unit::capture(build_runner, unit)?;
                captured.require_spec(unit.kind, trust_compile_target_spec_sha256.as_deref())?;
                Ok::<_, anyhow::Error>(captured.digest.clone())
            })
            .transpose()?;
        Ok(ManifestErrorContext {
            path: unit.pkg.manifest_path().to_owned(),
            spans: unit.pkg.manifest().document_rc(),
            contents: unit.pkg.manifest().contents().map(String::from),
            requested_kinds: bcx.target_data.requested_kinds().to_owned(),
            host_name: bcx.rustc().host,
            trust_compile_target: trust_target_identity_enabled
                .then(|| scoped_unit_compile_target(bcx, unit))
                .transpose()?,
            trust_compile_target_spec_sha256,
            trust_compile_mode: trust_target_identity_enabled
                .then(|| exact_unit_compile_mode(unit.mode)),
            trust_compile_kind: trust_target_identity_enabled
                .then(|| exact_unit_compile_kind(unit.kind)),
            trust_unit_identity_sha256,
            trust_proof_unit: trust_proof_unit_identity(build_runner, unit)?,
            rename_table,
            cwd: path_args(build_runner.bcx.ws, unit).1,
            cfgs: bcx
                .target_data
                .requested_kinds()
                .iter()
                .map(|k| bcx.target_data.cfg(*k).to_owned())
                .collect(),
            term_width: bcx
                .gctx
                .shell()
                .err_width()
                .diagnostic_terminal_width()
                .unwrap_or(cargo_util_terminal::report::renderer::DEFAULT_TERM_WIDTH),
        })
    }

    fn requested_target_names(&self) -> impl Iterator<Item = &str> {
        self.requested_kinds.iter().map(|kind| match kind {
            CompileKind::Host => &self.host_name,
            CompileKind::Target(target) => target.short_name(),
        })
    }

    /// Find a span for the dependency that specifies this unrenamed crate, if it's unique.
    ///
    /// rustc diagnostics (at least for public-in-private) mention the un-renamed
    /// crate: if you have `foo = { package = "bar" }`, the rustc diagnostic will
    /// say "bar".
    ///
    /// This function does its best to find a span for "bar", but it could fail if
    /// there are multiple candidates:
    ///
    /// ```toml
    /// foo = { package = "bar" }
    /// baz = { path = "../bar", package = "bar" }
    /// ```
    fn find_crate_span(&self, unrenamed: &str) -> Option<Range<usize>> {
        let Some(ref spans) = self.spans else {
            return None;
        };

        let orig_name = self.rename_table.get(unrenamed)?.as_str();

        if let Some((k, v)) = get_key_value(&spans, &["dependencies", orig_name]) {
            // We make some effort to find the unrenamed text: in
            //
            // ```
            // foo = { package = "bar" }
            // ```
            //
            // we try to find the "bar", but fall back to "foo" if we can't (which might
            // happen if the renaming took place in the workspace, for example).
            if let Some(package) = v.get_ref().as_table().and_then(|t| t.get("package")) {
                return Some(package.span());
            } else {
                return Some(k.span());
            }
        }

        // The dependency could also be in a target-specific table, like
        // [target.x86_64-unknown-linux-gnu.dependencies] or
        // [target.'cfg(something)'.dependencies]. We filter out target tables
        // that don't match a requested target or a requested cfg.
        if let Some(target) = spans
            .deref()
            .as_ref()
            .get("target")
            .and_then(|t| t.as_ref().as_table())
        {
            for (platform, platform_table) in target.iter() {
                match platform.as_ref().parse::<Platform>() {
                    Ok(Platform::Name(name)) => {
                        if !self.requested_target_names().any(|n| n == name) {
                            continue;
                        }
                    }
                    Ok(Platform::Cfg(cfg_expr)) => {
                        if !self.cfgs.iter().any(|cfgs| cfg_expr.matches(cfgs)) {
                            continue;
                        }
                    }
                    Err(_) => continue,
                }

                let Some(platform_table) = platform_table.as_ref().as_table() else {
                    continue;
                };

                if let Some(deps) = platform_table
                    .get("dependencies")
                    .and_then(|d| d.as_ref().as_table())
                {
                    if let Some((k, v)) = deps.get_key_value(orig_name) {
                        if let Some(package) = v.get_ref().as_table().and_then(|t| t.get("package"))
                        {
                            return Some(package.span());
                        } else {
                            return Some(k.span());
                        }
                    }
                }
            }
        }
        None
    }
}

// Trust: Cargo already distinguishes units by these axes, but only through
// opaque hashes meant for the target directory. Evidence has to name the exact
// axis it applies to, so the helpers below give each one a stable spelling that
// is part of the `trust.cargo-unit-identity.v2` schema and cannot drift with an
// upstream `Debug` impl or hasher change.
// Trust: per-unit evidence uses the same compiler scope as its keys/layout.
// Explicit targets retain their exact requested spelling without a host probe.
fn scoped_unit_compile_target(bcx: &BuildContext<'_, '_>, unit: &Unit) -> CargoResult<String> {
    let host = match unit.kind {
        CompileKind::Host => {
            bcx.rustc()
                .version_observation(bcx.ws.is_member(&unit.pkg))?
                .host
        }
        // The pure target spelling helper ignores host for explicit targets.
        CompileKind::Target(_) => bcx.rustc().host,
    };
    Ok(exact_unit_compile_target(unit.kind, host))
}

fn exact_unit_compile_target(kind: CompileKind, host: InternedString) -> String {
    match kind {
        CompileKind::Host => host.to_string(),
        CompileKind::Target(target) => target.rustc_target().to_string(),
    }
}

fn exact_unit_compile_mode(mode: CompileMode) -> &'static str {
    match mode {
        CompileMode::Test => "test",
        CompileMode::Build => "build",
        CompileMode::Check { test: true } => "check-test",
        CompileMode::Check { test: false } => "check",
        CompileMode::Doc => "doc",
        CompileMode::Doctest => "doctest",
        CompileMode::Docscrape => "docscrape",
        CompileMode::RunCustomBuild => "run-custom-build",
    }
}

fn exact_unit_compile_kind(kind: CompileKind) -> &'static str {
    match kind {
        CompileKind::Host => "host",
        CompileKind::Target(_) => "target",
    }
}

fn exact_unit_identity_sha256(
    unit: &Unit,
    compile_target: String,
    compile_target_spec_sha256: Option<&str>,
    extra_compiler_args: &[String],
    dependencies: &[exact_unit::Dependency],
    artifact_target_spec_sha256: Option<&str>,
) -> CargoResult<String> {
    #[derive(serde::Serialize)]
    struct Identity<'a> {
        schema: &'static str,
        package_id: String,
        target: &'a Target,
        target_harness: bool,
        profile: &'a Profile,
        compile_target: String,
        compile_target_spec_sha256: Option<&'a str>,
        compile_mode: &'static str,
        compile_kind: &'static str,
        features: Vec<&'a str>,
        dependencies: &'a [exact_unit::Dependency],
        artifact_dependency: bool,
        is_std: bool,
        rustflags: &'a [String],
        rustdocflags: &'a [String],
        links_overrides: &'a std::collections::BTreeMap<String, BuildOutput>,
        artifact_target_for_features: Option<CompileTarget>,
        artifact_target_spec_sha256: Option<&'a str>,
        skip_non_compile_time_dep: bool,
        extra_compiler_args: &'a [String],
    }

    let identity = Identity {
        schema: "trust.cargo-unit-identity.v2",
        package_id: unit.pkg.package_id().to_spec().to_string(),
        target: &unit.target,
        target_harness: unit.target.harness(),
        profile: &unit.profile,
        compile_target,
        compile_target_spec_sha256,
        compile_mode: exact_unit_compile_mode(unit.mode),
        compile_kind: exact_unit_compile_kind(unit.kind),
        features: unit
            .features
            .iter()
            .map(|feature| feature.as_str())
            .collect(),
        dependencies,
        artifact_dependency: unit.artifact.is_true(),
        is_std: unit.is_std,
        rustflags: &unit.rustflags,
        rustdocflags: &unit.rustdocflags,
        links_overrides: &unit.links_overrides,
        artifact_target_for_features: unit.artifact_target_for_features,
        artifact_target_spec_sha256,
        skip_non_compile_time_dep: unit.skip_non_compile_time_dep,
        extra_compiler_args,
    };
    let bytes = serde_json::to_vec(&identity)
        .context("failed to serialize exact Cargo unit identity for Trust evidence")?;
    Ok(Sha256::new().update(&bytes).finish_hex())
}

/// Trust: the exact `trust_unit_identity_sha256` that `trust_proof_inventory`
/// declares for `unit`, for evidence emitted about that Unit later in the run.
fn trust_declared_unit_identity_sha256(
    build_runner: &BuildRunner<'_, '_>,
    unit: &Unit,
) -> CargoResult<String> {
    Ok(exact_unit::capture(build_runner, unit)?.digest.clone())
}

fn exact_unit_compile_target_spec_sha256(kind: CompileKind) -> CargoResult<Option<String>> {
    let CompileKind::Target(CompileTarget::Json { path, .. }) = kind else {
        return Ok(None);
    };
    let digest = Sha256::new()
        .update_path(path.as_str())
        .with_context(|| {
            format!("failed to capture exact custom target specification bytes from `{path}`")
        })?
        .finish_hex();
    Ok(Some(digest))
}

/// Trust: a custom target JSON can load an LLVM plugin, which executes inside
/// the compiler and therefore inside the proof TCB — a capability no other
/// build input has, and one Cargo otherwise passes through untouched.
fn reject_verified_custom_target_llvm_args(kind: CompileKind) -> CargoResult<()> {
    let CompileKind::Target(CompileTarget::Json { path, .. }) = kind else {
        return Ok(());
    };
    let bytes = fs::read(path.as_str()).with_context(|| {
        format!("failed to inspect custom target specification `{path}` for LLVM plugin arguments")
    })?;
    let spec: serde_json::Value = serde_json::from_slice(&bytes).with_context(|| {
        format!("failed to parse custom target specification `{path}` while closing the proof TCB")
    })?;
    if spec
        .get("llvm-args")
        .or_else(|| spec.get("llvm_args"))
        .and_then(serde_json::Value::as_array)
        .is_some_and(|args| !args.is_empty())
    {
        anyhow::bail!(
            "verified Targo rejects non-empty custom-target `llvm-args`: LLVM plugin loading is outside the proof TCB"
        );
    }
    Ok(())
}

fn ensure_exact_unit_compile_target_spec_unchanged(
    kind: CompileKind,
    captured: Option<&str>,
) -> CargoResult<()> {
    let observed = exact_unit_compile_target_spec_sha256(kind)?;
    if observed.as_deref() != captured {
        anyhow::bail!(
            "custom target specification changed between compiler-work construction and artifact publication (captured_sha256={captured:?}, observed_sha256={:?})",
            observed.as_deref()
        );
    }
    Ok(())
}

/// Creates a unit of work that replays the cached compiler message.
///
/// Usually used when a job is fresh and doesn't need to recompile.
fn replay_output_cache(
    package_id: PackageId,
    manifest: ManifestErrorContext,
    target: &Target,
    path: PathBuf,
    mut output_options: OutputOptions,
) -> Work {
    let target = target.clone();
    Work::new(move |state| {
        if !path.exists() {
            // No cached output, probably didn't emit anything.
            return Ok(());
        }
        // We sometimes have gigabytes of output from the compiler, so avoid
        // loading it all into memory at once, as that can cause OOM where
        // otherwise there would be none.
        let file = paths::open(&path)?;
        let mut reader = std::io::BufReader::new(file);
        let mut line = String::new();
        loop {
            let length = reader.read_line(&mut line)?;
            if length == 0 {
                break;
            }
            let trimmed = line.trim_end_matches(&['\n', '\r'][..]);
            on_stderr_line(
                state,
                trimmed,
                package_id,
                &manifest,
                &target,
                &mut output_options,
            )?;
            line.clear();
        }
        Ok(())
    })
}

/// Provides a package name with descriptive target information,
/// e.g., '`foo` (bin "bar" test)', '`foo` (lib doctest)'.
fn descriptive_pkg_name(name: &str, target: &Target, mode: &CompileMode) -> String {
    let desc_name = target.description_named();
    let mode = if mode.is_rustc_test() && !(target.is_test() || target.is_bench()) {
        " test"
    } else if mode.is_doc_test() {
        " doctest"
    } else if mode.is_doc() {
        " doc"
    } else {
        ""
    };
    format!("`{name}` ({desc_name}{mode})")
}

/// Applies environment variables from config `[env]` to [`ProcessBuilder`].
pub(crate) fn apply_env_config(
    gctx: &crate::GlobalContext,
    cmd: &mut ProcessBuilder,
) -> CargoResult<()> {
    for (key, value) in gctx.env_config()?.iter() {
        // never override a value that has already been set by cargo
        if cmd.get_envs().contains_key(key) {
            continue;
        }
        cmd.env(key, value);
    }
    Ok(())
}

/// Checks if there are some scrape units waiting to be processed.
fn should_include_scrape_units(bcx: &BuildContext<'_, '_>, unit: &Unit) -> bool {
    unit.mode.is_doc() && bcx.scrape_units.len() > 0 && bcx.ws.unit_needs_doc_scrape(unit)
}

/// Gets the file path of function call information output from `rustdoc`.
fn scrape_output_path(build_runner: &BuildRunner<'_, '_>, unit: &Unit) -> CargoResult<PathBuf> {
    assert!(unit.mode.is_doc() || unit.mode.is_doc_scrape());
    build_runner
        .outputs(unit)
        .map(|outputs| outputs[0].path.clone())
}

/// Gets the dep-info file emitted by rustdoc.
fn rustdoc_dep_info_loc(build_runner: &BuildRunner<'_, '_>, unit: &Unit) -> PathBuf {
    let mut loc = build_runner.files().fingerprint_file_path(unit, "");
    loc.set_extension("d");
    loc
}
