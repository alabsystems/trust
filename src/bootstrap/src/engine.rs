//! The maintained Bootstrap engine called by the enclosing Targo process.
//!
//! Requests and parallelism limits are data, not resource admission. The caller
//! must retain its real execution owner and exclusively lend the original GNU
//! scheduler through this call. No executable, environment reimport, saved
//! receipt, SDK constructor or second Step graph is used here.

use std::ffi::OsString;
use std::num::NonZeroU32;
use std::path::{Path, PathBuf};
use std::sync::Arc;

use crate::core::build_steps::frontend_runtime::CompletedRuntime;
use crate::core::config::Config;

mod scope;
pub use scope::{ExecutionScope, JoinedOutcome, Preparation, UnresolvedOutcome};
mod graph;
mod preparation_configuration;
pub use graph::{
    CapturedInputs, Comparison, CompletedTask, GraphError, InputObservation, InputPair, OpenGraph,
    TaskCompletion, TaskError, TaskFailure, TaskInputs,
};
pub use preparation_configuration::ClosedFullPreparationConfiguration;
pub(crate) use preparation_configuration::capture_original_configuration;

pub use crate::core::config::InputLayout;
#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
mod full;
#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
pub(crate) use full::command_output as full_command_output;
#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
pub(crate) use full::{
    CompletedCommand, CompletedReader, command_completed as full_command_completed,
};
#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
pub use full::{
    OriginalCommand, OriginalCommandExecutor, OriginalCompilationFailure, run_original_compilation,
};

#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
pub use crate::utils::metadata_scheduler::host_graph::{
    CommittedEntry, CommittedLookup, CommittedRepository, CommittedSourceReadSet,
    DependencySourceRefusal, DependencySourceSnapshot, OriginalBootstrapCompilation,
    OriginalBootstrapMember, OriginalBootstrapMemberFailure, OriginalDependencyInputs,
    OriginalHostGraph, OriginalPreparationInputs, RetiredOriginalBootstrapMember,
    RetiredOriginalDependencyInputs, SourceRead,
};
pub use crate::utils::trust_preparation::PreparationScope;

/// Classify the exact x.py request with the maintained native parser. This is
/// routing DATA only; an original Root must parse its complete request again.
/// No source, output, SDK, CPU, readiness or completion owner is constructed.
pub fn xpy_preparation_scope(arguments: &[OsString]) -> Result<PreparationScope, String> {
    Ok(match xpy_flags(arguments)? {
        Some(flags) if !flags.dry_run => PreparationScope::for_flags(&flags),
        _ => PreparationScope::NotProducer,
    })
}

/// Read only the same complete native request's source/output selection. The
/// enclosing original Root must already hold its real source owner, then take
/// the actual selected output guard before configuration and enrollment.
/// The returned paths supply no authority and cannot enable a Full graph.
pub fn xpy_input_layout(arguments: &[OsString]) -> Result<InputLayout, String> {
    let flags = xpy_flags(arguments)?
        .ok_or_else(|| "help/version has no Bootstrap input layout".to_owned())?;
    Ok(Config::input_layout(&flags))
}

pub(crate) fn xpy_flags(
    arguments: &[OsString],
) -> Result<Option<crate::core::config::flags::Flags>, String> {
    use crate::core::config::flags::Flags;
    if arguments.is_empty() {
        return Ok(None);
    }
    let mut arguments = arguments
        .iter()
        .map(|arg| {
            arg.clone().into_string().map_err(|_| "Bootstrap arguments must be UTF-8".to_owned())
        })
        .collect::<Result<Vec<_>, _>>()?;
    // Match x.py's existing help normalization before the SAME Flags parser.
    if arguments.first().is_some_and(|arg| arg == "help") {
        arguments[0] = "--help".into();
    }
    match Flags::try_parse(&arguments) {
        Ok(flags) => Ok(Some(flags)),
        Err(error)
            if matches!(
                error.kind(),
                clap::error::ErrorKind::DisplayHelp | clap::error::ErrorKind::DisplayVersion
            ) =>
        {
            Ok(None)
        }
        Err(error) => Err(error.to_string()),
    }
}

/// Explicit arguments exclude the enclosing Targo command's own argv.
pub struct Request {
    args: Vec<OsString>,
    ceiling: NonZeroU32,
    shims: Option<PathBuf>,
}

impl Request {
    pub fn new(args: Vec<OsString>, cpu_ceiling: NonZeroU32) -> Self {
        Self { args, ceiling: cpu_ceiling, shims: None }
    }

    /// Select the original compiled Bootstrap shim directory explicitly.
    /// Targo's own executable directory is not a Bootstrap shim directory.
    /// This path is input selection, never build completion or SDK evidence.
    pub fn with_bootstrap_shims(mut self, directory: PathBuf) -> Self {
        self.shims = Some(directory);
        self
    }
}

/// Read-only observations of the actual parsed configuration. This is neither
/// a prepared job nor a release, SDK, machine admission or completion witness.
pub struct Plan {
    source: PathBuf,
    output: PathBuf,
    jobs: u32,
    llvm_link_jobs: Option<u32>,
    frontend_threads: Option<u32>,
    dry_run: bool,
    native_object_leaf: bool,
}

impl Plan {
    pub fn source(&self) -> &Path {
        &self.source
    }
    pub fn output(&self) -> &Path {
        &self.output
    }
    pub fn jobs(&self) -> u32 {
        self.jobs
    }
    pub fn llvm_link_jobs(&self) -> Option<u32> {
        self.llvm_link_jobs
    }
    pub fn frontend_threads(&self) -> Option<u32> {
        self.frontend_threads
    }
    pub fn dry_run(&self) -> bool {
        self.dry_run
    }

    /// Observation of the complete parsed first-node selection. This creates
    /// no Preparation, source/output custody, Host operation or runtime.
    pub fn is_native_object_leaf(&self) -> bool {
        self.native_object_leaf
    }

    pub(crate) fn from_config(config: &Config) -> Self {
        Self {
            source: config.src.clone(),
            output: config.out.clone(),
            jobs: config.jobs.unwrap_or(1),
            llvm_link_jobs: config.llvm_link_jobs,
            frontend_threads: config.rust_parallel_frontend_threads,
            dry_run: config.dry_run(),
            native_object_leaf: crate::core::build_steps::native_object::validate_config(config)
                .is_ok(),
        }
    }
}

/// Parsed early flags remain policy DATA. No embedded native operation may
/// skip the actual configured SDK version checks before acquiring a scope.
pub(crate) fn validate_flags(flags: &crate::core::config::flags::Flags) -> Result<(), String> {
    if flags.skip_stage0_validation {
        Err("embedded native graph cannot skip original stage0 validation".into())
    } else {
        Ok(())
    }
}

/// Keep the completed-runtime producer's selector unchanged. The independent
/// object leaf has its own closed parsed profile and produces no runtime owner.
pub(crate) fn validate_config(config: &Config) -> Result<(), String> {
    if config.paths.as_slice() == [PathBuf::from("native-object-leaf")] {
        crate::core::build_steps::native_object::validate_config(config)
    } else {
        crate::core::build_steps::frontend_runtime::validate_config(config)
    }
}

/// Retains the exact Arc produced by the actual normal Step, after all CLI
/// finalization. Fields and construction remain private to this engine.
/// Help, dry runs and other commands never manufacture a completed runtime.
pub struct Outcome {
    completed: Option<Arc<CompletedRuntime>>,
    protected: Option<ExecutionScope>,
}

impl Outcome {
    pub fn has_completed_runtime(&self) -> bool {
        self.completed.is_some()
    }

    /// The original graph is still open; no closure or release is implied.
    pub fn check_execution_scope(&self) -> Result<(), String> {
        self.protected
            .as_ref()
            .ok_or_else(|| "this invocation has no protected work scope".to_owned())?
            .check_current()
    }

    /// Seal only after the caller's whole build/verify/test/compare graph.
    /// Failure returns actual unresolved custody, never a success boolean.
    pub fn seal_graph(mut self) -> Result<JoinedOutcome, UnresolvedOutcome> {
        match self.protected.take() {
            Some(scope) => scope.seal_graph(),
            None => Err(UnresolvedOutcome::absent()),
        }
    }

    pub fn check_completed_runtime(&self) -> Result<(), String> {
        #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
        {
            self.completed
                .as_ref()
                .ok_or_else(|| "this engine invocation produced no completed runtime".to_owned())?
                .check()
        }
        #[cfg(not(all(target_os = "macos", target_arch = "aarch64")))]
        Err("completed native runtime is unsupported on this platform".into())
    }

    pub(crate) fn empty() -> Self {
        Self { completed: None, protected: None }
    }
    pub(crate) fn completed(completed: Option<Arc<CompletedRuntime>>) -> Self {
        Self { completed, protected: None }
    }

    pub(crate) fn in_scope(
        completed: Option<Arc<CompletedRuntime>>,
        mut scope: ExecutionScope,
    ) -> Self {
        scope.retain_completed(completed.clone());
        Self { completed, protected: Some(scope) }
    }
}

pub(crate) struct Policy<'a> {
    pub(crate) ceiling: NonZeroU32,
    pub(crate) shims: Option<PathBuf>,
    pub(crate) before_steps:
        &'a mut dyn for<'p> FnMut(Preparation<'p>) -> Result<ExecutionScope, String>,
    pub(crate) scope: Option<ExecutionScope>,
}

impl Policy<'_> {
    pub(crate) fn selected_shims(&self) -> Result<PathBuf, String> {
        let directory = self.shims.as_ref().ok_or_else(|| {
            "in-process Bootstrap requires its explicit original compiled shim directory".to_owned()
        })?;
        selected_shims(directory)
    }

    pub(crate) fn limit(&self, config: &mut Config) {
        limit_config(config, self.ceiling);
    }
}

// Trust: restriction only, shared by both actual enclosing owner paths.
pub(crate) fn limit_config(config: &mut Config, ceiling: NonZeroU32) {
    let ceiling = ceiling.get();
    let restrict =
        |value: Option<u32>| value.filter(|value| *value > 0).unwrap_or(ceiling).min(ceiling);
    config.jobs = Some(restrict(config.jobs));
    config.llvm_link_jobs = Some(restrict(config.llvm_link_jobs));
    config.rust_parallel_frontend_threads = Some(restrict(config.rust_parallel_frontend_threads));
}

// Trust: physical input selection only. This does not issue an executable,
// authenticate shim production, replace an actual owner or authorize spawning.
pub(crate) fn selected_shims(directory: &Path) -> Result<PathBuf, String> {
    if !directory.is_absolute()
        || std::fs::canonicalize(directory).map_err(|error| error.to_string())? != *directory
        || !std::fs::symlink_metadata(directory).map_err(|error| error.to_string())?.is_dir()
    {
        return Err("Bootstrap shim directory must be physical and absolute".into());
    }
    for name in ["rustc", "rustdoc"] {
        let path = directory.join(name);
        let metadata = std::fs::symlink_metadata(&path).map_err(|error| error.to_string())?;
        if !metadata.is_file() {
            return Err(format!("Bootstrap shim is not a regular file: {}", path.display()));
        }
        #[cfg(unix)]
        {
            use std::os::unix::fs::MetadataExt;
            if metadata.mode() & 0o111 == 0 || metadata.mode() & 0o022 != 0 {
                return Err(format!(
                    "Bootstrap shim is not a protected executable: {}",
                    path.display()
                ));
            }
        }
    }
    // Input selection only, never source/image, SDK or resource evidence.
    Ok(directory.to_path_buf())
}

#[cfg(test)]
// Trust: out-of-line unit tests, as tidy's `unit_tests` check requires.
mod tests;

/// Invoke the normal engine once with the original captured GNU owner.
///
/// The caller authenticates its real admission before invoking this function
/// (configuration may issue compiler queries), and rechecks the actual owner in
/// `before_steps`. That callback is policy, not an authority constructor. A
/// refused callback returns after the real command lease is acquired, before
/// Session creation, output locking or producer Steps. It cannot reconstruct
/// command ownership from Plan data. Ordinary fatal configuration semantics remain.
pub fn run(
    request: Request,
    original_scheduler: jobserver_utils::Jobserver,
    before_steps: impl for<'p> FnOnce(Preparation<'p>) -> Result<ExecutionScope, String>,
) -> Result<Outcome, String> {
    let args = request
        .args
        .into_iter()
        .map(|arg| arg.into_string().map_err(|_| "Bootstrap arguments must be UTF-8".to_owned()))
        .collect::<Result<Vec<_>, _>>()?;
    crate::utils::metadata_scheduler::install_original(original_scheduler)?;
    run_installed(args, request.ceiling, request.shims, before_steps)
}

/// Install the actual original native graph owner before configuration can
/// issue ANY command. Unsupported programs/profiles refuse; this is no new
/// admission, SDK, producing capability or protected-graph close.
#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
pub fn run_with_original_graph(
    request: Request,
    original: Arc<OriginalHostGraph>,
    before_steps: impl for<'p> FnOnce(Preparation<'p>) -> Result<ExecutionScope, String>,
) -> Result<Outcome, String> {
    let args = request
        .args
        .into_iter()
        .map(|arg| arg.into_string().map_err(|_| "Bootstrap arguments must be UTF-8".to_owned()))
        .collect::<Result<Vec<_>, _>>()?;
    Arc::clone(&original).install()?;
    run_installed(args, request.ceiling, request.shims, |preparation| {
        preparation.bind_original_host(Arc::clone(&original), before_steps)
    })
}

fn run_installed(
    args: Vec<String>,
    ceiling: NonZeroU32,
    shims: Option<PathBuf>,
    before_steps: impl for<'p> FnOnce(Preparation<'p>) -> Result<ExecutionScope, String>,
) -> Result<Outcome, String> {
    let mut callback = Some(before_steps);
    let mut once = |preparation: Preparation<'_>| {
        callback
            .take()
            .ok_or_else(|| "Bootstrap execution policy was already consumed".to_owned())?(
            preparation,
        )
    };
    crate::cli_main::run_explicit(
        &args,
        Some(Policy { ceiling, shims, before_steps: &mut once, scope: None }),
    )
}
