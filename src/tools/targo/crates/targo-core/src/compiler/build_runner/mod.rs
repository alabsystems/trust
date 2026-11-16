//! [`BuildRunner`] is the mutable state used during the build process.

use crate::util::data_structures::{HashMap, HashSet};
use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex};

use crate::compiler::compilation::{self, UnitOutput};
use crate::compiler::locking::LockManager;
use crate::compiler::{self, Unit, UserIntent, artifact};
use crate::util::cache_lock::{CacheLock, CacheLockMode};
use crate::util::errors::CargoResult;
use crate::workspace::PackageId;
use anyhow::{Context as _, bail};
use cargo_util::Jobserver;
use cargo_util::paths;
use cargo_util_terminal::report::{Level, Message};
use filetime::FileTime;
use itertools::Itertools;

use super::RustdocFingerprint;
use super::custom_build::{self, BuildDeps, BuildScriptOutputs, BuildScripts};
use super::fingerprint::{Checksum, Fingerprint, VerifiedRustdocLauncherIdentity};
use super::job_queue::JobQueue;
use super::layout::Layout;
use super::lto::Lto;
use super::unit_graph::UnitDep;
use super::unused_deps::UnusedDepState;
use super::{BuildContext, Compilation, CompileKind, CompileMode, Executor, FileFlavor};

#[derive(Clone, Copy)]
enum CompilationLeaseState {
    Active,
    Finalized,
    Aborted,
}

mod compilation_files;
mod layouts;
// Trust: a test plan refuses two builds of one target at one path.
mod plan_collisions;
mod workload_leases;
#[cfg(any(target_os = "linux", target_os = "macos"))]
pub(crate) use self::compilation_files::CandidateOutput;
pub(super) use self::compilation_files::CompilationFiles;
pub(crate) use self::compilation_files::UnitOutputNamespace;
#[cfg(any(target_os = "linux", target_os = "macos"))]
pub(super) use self::compilation_files::projected_outputs;
pub use self::compilation_files::{Metadata, OutputFile, UnitHash};
pub(crate) use workload_leases::OriginalOutputLeases;

/// Collection of all the stuff that is needed to perform a build.
///
/// Different from the [`BuildContext`], `Context` is a _mutable_ state used
/// throughout the entire build process. Everything is coordinated through this.
///
/// [`BuildContext`]: crate::compiler::BuildContext
pub struct BuildRunner<'a, 'gctx> {
    /// Mostly static information about the build task.
    pub bcx: &'a BuildContext<'a, 'gctx>,
    // Trust: immutable resolved-graph evidence, initialized once. Every use still
    // independently checks the contributing custom target specification bytes.
    pub(super) exact_unit_graph: std::cell::OnceCell<Result<super::exact_unit::Graph, String>>,
    /// A large collection of information about the result of the entire compilation.
    pub compilation: Compilation<'gctx>,
    /// Output from build scripts, updated after each build script runs.
    pub build_script_outputs: Arc<Mutex<BuildScriptOutputs>>,
    /// Dependencies (like rerun-if-changed) declared by a build script.
    /// This is *only* populated from the output from previous runs.
    /// If the build script hasn't ever been run, then it must be run.
    pub build_explicit_deps: HashMap<Unit, BuildDeps>,
    /// Trust: data-profile support declared by the actual compilation
    /// executor before any fingerprint planning. It grants no authority.
    pub(super) native_tool_inputs: bool,
    /// Fingerprints used to detect if a unit is out-of-date.
    pub fingerprints: HashMap<Unit, Arc<Fingerprint>>,
    pub(super) action_source_inputs:
        HashMap<PackageId, Option<Arc<super::action_inputs::SourceInputs>>>,
    pub(super) action_commands: HashMap<Unit, Arc<super::action_command::CommandInputs>>,
    /// Trust: verified-only identity of the exact selected `trustdoc`
    /// launcher. Captured once here — the only place with a whole-build
    /// lifetime — then rechecked at every documentation execution edge.
    pub(super) verified_rustdoc_launcher: Option<Arc<VerifiedRustdocLauncherIdentity>>,
    /// Cache of file mtimes to reduce filesystem hits.
    pub mtime_cache: HashMap<PathBuf, FileTime>,
    /// Cache of file checksums to reduce filesystem reads.
    pub checksum_cache: HashMap<PathBuf, Checksum>,
    /// A set used to track which units have been compiled.
    /// A unit may appear in the job graph multiple times as a dependency of
    /// multiple packages, but it only needs to run once.
    pub compiled: HashSet<Unit>,
    /// Linking information for each `Unit`.
    /// See `build_map` for details.
    pub build_scripts: HashMap<Unit, Arc<BuildScripts>>,
    /// Job server client to manage concurrency with other processes.
    pub jobserver: Jobserver,
    // Trust: actual inherited credits and original fixed claim, retained
    // together until every restricted supplementary credit retires.
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    fixed_gnu: Option<super::resource_gnu_fixed::FixedGnuBridge>,
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    pub(super) resource_runtime: Option<Arc<super::resource_runtime::ResourceRuntime>>,
    /// "Primary" packages are the ones the user selected on the command-line
    /// with `-p` flags. If no flags are specified, then it is the defaults
    /// based on the current directory and the default workspace members.
    pub(super) primary_packages: HashSet<PackageId>,
    /// An abstraction of the files and directories that will be generated by
    /// the compilation. This is `None` until after `unit_dependencies` has
    /// been computed.
    pub(super) files: Option<CompilationFiles<'a, 'gctx>>,

    /// A set of units which are compiling rlibs and are expected to produce
    /// metadata files in addition to the rlib itself.
    rmeta_required: HashSet<Unit>,

    /// Map of the LTO-status of each unit. This indicates what sort of
    /// compilation is happening (only object, only bitcode, both, etc), and is
    /// precalculated early on.
    pub lto: HashMap<Unit, Lto>,

    /// Map of Doc/Docscrape units to metadata for their -Cmetadata flag.
    /// See `Context::find_metadata_units` for more details.
    pub metadata_for_doc_units: HashMap<Unit, Metadata>,

    /// Set of metadata of Docscrape units that fail before completion, e.g.
    /// because the target has a type error. This is in an Arc<Mutex<..>>
    /// because it is continuously updated as the job progresses.
    pub failed_scrape_units: Arc<Mutex<HashSet<UnitHash>>>,

    pub unused_dep_state: UnusedDepState,

    /// Manages locks for build units when fine grain locking is enabled.
    pub lock_manager: Arc<LockManager>,
    // Trust: original executor decisions plus the reserved rebuild closure.
    pub(super) lease_forces: Option<HashMap<Unit, bool>>,
    // Trust: compilation leases retire independently from the test action
    // owners and jobserver that continue to live in this runner.
    compilation_cache_lease: Option<CacheLock<'gctx>>,
    compilation_lease_state: CompilationLeaseState,
    workload_outputs: bool,
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    pub(super) native_job: Option<Arc<super::native_job::Options>>,
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    native_finalized_leases: Option<Arc<OriginalOutputLeases>>,
    // Trust: the SAME guards move out of Layout before workload compilation.
    // Intermediate scripts and final outputs share this one live owner; no
    // FileLock/description clone or saved output record can recreate it.
    workload_output_leases: Option<Arc<OriginalOutputLeases>>,
    pub(super) workload_materializations:
        HashMap<Unit, crate::ops::cargo_test::workload::Materialization>,
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    qualification: Option<Arc<super::qualification::Options>>,
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    continued_outputs: Option<Arc<OriginalOutputLeases>>,
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    continued_inputs: Option<Arc<crate::ops::cargo_test::workload::Inputs>>,
}

impl<'a, 'gctx> BuildRunner<'a, 'gctx> {
    pub fn new(bcx: &'a BuildContext<'a, 'gctx>) -> CargoResult<Self> {
        #[cfg(any(target_os = "linux", target_os = "macos"))]
        let resource_runtime = super::resource_runtime::ResourceRuntime::new(bcx)?;
        Self::with_runtime(
            bcx,
            #[cfg(any(target_os = "linux", target_os = "macos"))]
            resource_runtime,
        )
    }
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    pub(crate) fn continued(
        bcx: &'a BuildContext<'a, 'gctx>,
        continuation: super::qualification::ContinuedGraph,
    ) -> CargoResult<Self> {
        let (runtime, outputs, inputs) = continuation.install(bcx)?;
        let mut runner = Self::with_runtime(bcx, Some(runtime))?;
        runner.continued_outputs = outputs;
        runner.continued_inputs = Some(inputs);
        Ok(runner)
    }
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    pub(crate) fn native_continued(
        bcx: &'a BuildContext<'a, 'gctx>,
        continuation: super::resource_runtime::NativeContinuedGraph,
    ) -> CargoResult<Self> {
        let (runtime, outputs, inputs) = continuation.install(bcx)?;
        let mut runner = Self::with_runtime(bcx, Some(runtime))?;
        runner.continued_outputs = outputs;
        runner.continued_inputs = Some(inputs);
        Ok(runner)
    }
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    pub(super) fn native_inputs(&self) -> Option<Arc<crate::ops::cargo_test::workload::Inputs>> {
        self.native_job
            .as_ref()
            .map(|options| options.inputs.clone())
    }
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    pub(super) fn retain_native_finalized_leases(
        &mut self,
        leases: Option<Arc<OriginalOutputLeases>>,
    ) {
        self.native_finalized_leases = leases;
    }
    fn with_runtime(
        bcx: &'a BuildContext<'a, 'gctx>,
        #[cfg(any(target_os = "linux", target_os = "macos"))] resource_runtime: Option<
            Arc<super::resource_runtime::ResourceRuntime>,
        >,
    ) -> CargoResult<Self> {
        let compilation = Compilation::new(bcx)?;
        let verified_rustdoc_launcher = compilation.verified_rustdoc_launcher();

        // Load up the jobserver that we'll use to manage our parallelism. This
        // is the same as the GNU make implementation of a jobserver, and
        // intentionally so! It's hoped that we can interact with GNU make and
        // all share the same jobserver.
        //
        // Note that if we don't have a jobserver in our environment then we
        // create our own, and we create it with `n` tokens, but immediately
        // acquire one, because one token is ourself, a running process.
        let native_jobserver = {
            #[cfg(any(target_os = "linux", target_os = "macos"))]
            {
                resource_runtime.as_ref().map(|runtime| runtime.jobserver())
            }
            #[cfg(not(any(target_os = "linux", target_os = "macos")))]
            {
                None
            }
        };
        // Trust: keep inherited GNU rights distinct from physical CPU custody.
        #[cfg(any(target_os = "linux", target_os = "macos"))]
        let fixed_gnu = match (bcx.gctx.fixed_admission()?, bcx.gctx.jobserver_from_env()?) {
            (Some(claim), Some(inherited)) => {
                claim.check_budget(std::num::NonZeroU32::new(bcx.jobs()).unwrap())?;
                Some(super::resource_gnu_fixed::FixedGnuBridge::new(
                    inherited,
                    bcx.jobs(),
                    claim.clone(),
                )?)
            }
            _ => None,
        };
        #[cfg(any(target_os = "linux", target_os = "macos"))]
        let fixed_jobserver = fixed_gnu.as_ref().map(|bridge| bridge.jobserver());
        #[cfg(not(any(target_os = "linux", target_os = "macos")))]
        let fixed_jobserver = None;
        let mut jobserver = match fixed_jobserver.or(native_jobserver) {
            Some(client) => client,
            None => match bcx.gctx.jobserver_from_env()? {
                Some(client) => client.clone(),
                None => {
                    let client = Jobserver::new(bcx.jobs() as usize)
                        .context("failed to create jobserver")?;
                    client.client().acquire_raw()?;
                    client
                }
            },
        };
        // Trust: unaware build scripts spawn stdin compiler probes with plain
        // Command. Retain a live same-pool endpoint through every child wait;
        // SP-1 continues stripping all unrequested descriptors at that spawn.
        #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
        let direct_full = bcx.gctx.original_bootstrap_full().is_some();
        #[cfg(not(all(target_os = "macos", target_arch = "aarch64")))]
        let direct_full = false;
        // Full imports the original held GNU pair directly through its native
        // member envelope; it has no local proxy child or late courier server.
        if !direct_full && let Err(error) = jobserver.enable_descendant_handoff() {
            bcx.gctx.shell().warn(format!(
                "jobserver descendant handoff unavailable: {error}; retaining the selected pool's explicit descriptor transport"
            ))?;
        }

        Ok(Self {
            bcx,
            exact_unit_graph: std::cell::OnceCell::new(),
            compilation,
            build_script_outputs: Arc::new(Mutex::new(BuildScriptOutputs::default())),
            fingerprints: HashMap::default(),
            action_source_inputs: HashMap::default(),
            action_commands: HashMap::default(),
            verified_rustdoc_launcher,
            mtime_cache: HashMap::default(),
            checksum_cache: HashMap::default(),
            compiled: HashSet::default(),
            build_scripts: HashMap::default(),
            build_explicit_deps: HashMap::default(),
            native_tool_inputs: false,
            jobserver,
            #[cfg(any(target_os = "linux", target_os = "macos"))]
            fixed_gnu,
            #[cfg(any(target_os = "linux", target_os = "macos"))]
            resource_runtime,
            primary_packages: HashSet::default(),
            files: None,
            rmeta_required: HashSet::default(),
            lto: HashMap::default(),
            metadata_for_doc_units: HashMap::default(),
            failed_scrape_units: Arc::new(Mutex::new(HashSet::default())),
            unused_dep_state: UnusedDepState::new(bcx),
            lock_manager: Arc::new(LockManager::new()),
            lease_forces: None,
            compilation_cache_lease: None,
            compilation_lease_state: CompilationLeaseState::Active,
            workload_outputs: false,
            #[cfg(any(target_os = "linux", target_os = "macos"))]
            native_job: None,
            #[cfg(any(target_os = "linux", target_os = "macos"))]
            native_finalized_leases: None,
            workload_output_leases: None,
            workload_materializations: HashMap::default(),
            #[cfg(any(target_os = "linux", target_os = "macos"))]
            qualification: None,
            #[cfg(any(target_os = "linux", target_os = "macos"))]
            continued_outputs: None,
            #[cfg(any(target_os = "linux", target_os = "macos"))]
            continued_inputs: None,
        })
    }

    pub(super) fn native_resources(&self) -> bool {
        #[cfg(any(target_os = "linux", target_os = "macos"))]
        {
            self.resource_runtime.is_some()
        }
        #[cfg(not(any(target_os = "linux", target_os = "macos")))]
        {
            false
        }
    }

    /// Data profile of the actual selected compiler transport; this grants no
    /// resource admission, process custody or permission to execute a command.
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    pub(super) fn tool_input_transport_profile(
        &self,
    ) -> Option<trust_fs_observation::tool_lookup::Profile> {
        self.resource_runtime.as_ref().map_or(
            Some(trust_fs_observation::tool_lookup::Profile::LocalUnixNativeV1),
            |runtime| runtime.tool_input_transport_profile(),
        )
    }

    /// Dry-run the compilation without actually running it.
    ///
    /// This is expected to collect information like the location of output artifacts.
    /// Please keep in sync with non-compilation part in [`BuildRunner::compile`].
    pub fn dry_run(mut self) -> CargoResult<Compilation<'gctx>> {
        let _lock = self
            .bcx
            .gctx
            .acquire_package_cache_lock(CacheLockMode::Shared)?;
        self.lto = super::lto::generate(self.bcx)?;
        self.prepare_units()?;
        self.prepare()?;
        self.check_collisions()?;

        for unit in &self.bcx.roots {
            self.collect_tests_and_executables(unit)?;
        }

        Ok(self.compilation)
    }

    /// Starts compilation, waits for it to finish, and returns information
    /// about the result of compilation.
    ///
    /// See [`ops::cargo_compile`] for a higher-level view of the compile process.
    ///
    /// [`ops::cargo_compile`]: crate::ops::cargo_compile
    #[tracing::instrument(skip_all)]
    pub fn compile(self, exec: &Arc<dyn Executor>) -> CargoResult<Compilation<'gctx>> {
        self.compile_with_tests(exec, None)
    }

    #[cfg(any(target_os = "linux", target_os = "macos"))]
    pub(crate) fn compile_native_job(
        mut self,
        options: Arc<super::native_job::Options>,
    ) -> super::native_job::Attempt {
        let result = (|| {
            options.validate(&self)?;
            self.workload_outputs = true;
            self.continued_outputs = options.registry.leases(&options.inputs)?;
            self.native_job = Some(options.clone());
            let executor = options.executor(&self)?;
            self.compile_graph(&executor, None)
        })();
        let (result, artifact) = match result {
            Ok(()) => match options.capture(&self, self.native_finalized_leases.clone()) {
                Ok(artifact) => (Ok(()), Some(artifact)),
                Err(error) => (Err(error), None),
            },
            Err(error) => (Err(error), None),
        };
        let compiler_executions = self
            .workload_materializations
            .values()
            .filter(|materialization| materialization.producer_attempt().is_some())
            .count();
        let warm_units = self
            .workload_materializations
            .values()
            .filter(|materialization| materialization.producer_attempt().is_none())
            .count();
        let continuation = self
            .resource_runtime
            .as_ref()
            .map(|runtime| runtime.suspend_native_job_graph(options.registry.clone()))
            .transpose();
        let (continuation, continuation_failure) = match continuation {
            Ok(held) => (held, None),
            Err(error) => (None, Some(format!("{error:#}"))),
        };
        super::native_job::Attempt {
            result,
            artifact,
            continuation,
            continuation_failure,
            compiler_executions,
            warm_units,
            _recorder: options.recorder(),
            produced: None,
        }
    }
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    pub(crate) fn compile_with_qualification(
        mut self,
        options: Arc<super::qualification::Options>,
    ) -> super::qualification::Attempt<'gctx> {
        let exec = options.executor();
        let inputs = options.inputs.clone();
        let result = (|| {
            options.validate_workspace(&self)?;
            self.workload_outputs = true;
            self.qualification = Some(options);
            self.compile_graph(&exec, None)
        })();
        // run/queue returning has joined all scoped children even on known
        // failure. No panic/unknown abort can construct this continuation.
        let outputs = self
            .compilation
            .qualification
            .as_ref()
            .and_then(|run| run.outputs.clone())
            .or_else(|| self.workload_output_leases.clone());
        let continuation = self
            .resource_runtime
            .as_ref()
            .map(|runtime| {
                runtime.suspend_paired_graph(
                    outputs,
                    inputs,
                    &self.bcx.ws.target_dir().into_path_unlocked(),
                )
            })
            .transpose();
        let (continuation, continuation_failure) = match continuation {
            Ok(continuation) => (continuation, None),
            Err(error) => (None, Some(format!("{error:#}"))),
        };
        super::qualification::Attempt {
            result,
            compilation: self.compilation,
            continuation,
            continuation_failure,
        }
    }
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    pub(super) fn qualification(&self) -> Option<Arc<super::qualification::Options>> {
        self.qualification.clone()
    }
    pub(super) fn records_workload_output(&self) -> bool {
        self.workload_outputs
    }

    // Trust: test actions enter the same queue before it is finalized.
    pub(crate) fn compile_with_tests(
        mut self,
        exec: &Arc<dyn Executor>,
        tests: Option<crate::ops::cargo_test::graph::TestGraphOptions>,
    ) -> CargoResult<Compilation<'gctx>> {
        self.compile_graph(exec, tests)?;
        Ok(self.compilation)
    }
    fn compile_graph(
        &mut self,
        exec: &Arc<dyn Executor>,
        tests: Option<crate::ops::cargo_test::graph::TestGraphOptions>,
    ) -> CargoResult<()> {
        // Trust: derive from the actual owner used for this entire graph,
        // including qualification/custom execution; never assume a default.
        self.native_tool_inputs = exec.supports_native_tool_inputs();
        #[cfg(any(target_os = "linux", target_os = "macos"))]
        if let Some(original) = &self.continued_inputs {
            original.validate_target(&self.bcx.ws.target_dir().into_path_unlocked())?;
            let next = tests
                .as_ref()
                .and_then(|tests| tests.workload.as_ref())
                .map(|workload| &workload.inputs)
                .or_else(|| self.qualification.as_ref().map(|options| &options.inputs))
                .or_else(|| self.native_job.as_ref().map(|options| &options.inputs));
            anyhow::ensure!(
                next.is_some_and(|next| Arc::ptr_eq(original, next)),
                "continued graph replaced its original live input/output capsule"
            );
        }
        if let Some(workload) = tests.as_ref().and_then(|tests| tests.workload.as_ref()) {
            anyhow::ensure!(
                self.native_resources() && crate::resource_worker_v3(),
                "native workload graph has no retained native host; local fallback is forbidden"
            );
            self.workload_outputs = true;
            workload
                .inputs
                .validate_target(&self.bcx.ws.target_dir().into_path_unlocked())?;
        }
        // Compilers retain the source cache until their workers and output
        // bookkeeping finish. Test actions may outlive that compile phase.
        self.compilation_cache_lease = Some(
            self.bcx
                .gctx
                .acquire_package_cache_lock(CacheLockMode::Shared)?,
        );
        let mut queue = JobQueue::new(self.bcx);
        self.lto = super::lto::generate(self.bcx)?;
        self.prepare_units()?;
        self.prepare()?;
        if self.workload_outputs {
            let guards = self
                .files
                .as_mut()
                .context("workload has no original prepared output layouts")?
                .take_compile_leases()?;
            #[cfg(any(target_os = "linux", target_os = "macos"))]
            let continued = self.continued_outputs.clone();
            #[cfg(not(any(target_os = "linux", target_os = "macos")))]
            let continued: Option<Arc<OriginalOutputLeases>> = None;
            self.workload_output_leases = Some(match continued {
                Some(original) => {
                    drop(guards);
                    original
                }
                None => Arc::new(OriginalOutputLeases::from_original_layouts(
                    guards,
                    &self.bcx.ws.target_dir().into_path_unlocked(),
                )?),
            });
            #[cfg(any(target_os = "linux", target_os = "macos"))]
            if let Some(native) = &self.native_job {
                native.registry.retain_leases(
                    &native.inputs,
                    self.workload_output_leases
                        .as_ref()
                        .expect("captured actual Layout")
                        .clone(),
                )?;
            }
            // The actual graph cannot dispatch its first compiler until the
            // SAME original native host retains every close-only Layout OFD.
            // A byte acknowledgement without this live runtime is unavailable.
            #[cfg(any(target_os = "linux", target_os = "macos"))]
            self.resource_runtime
                .as_ref()
                .context("workload lost its original retained runtime")?
                .retain_workload_outputs(
                    self.workload_output_leases
                        .as_ref()
                        .expect("just captured original Layout guards")
                        .clone(),
                    &self.bcx.ws.target_dir().into_path_unlocked(),
                )?;
            #[cfg(not(any(target_os = "linux", target_os = "macos")))]
            anyhow::bail!("native workload output custody unavailable");
        }
        custom_build::build_map(self)?;
        self.check_collisions()?;
        self.compute_metadata_for_doc_units();

        // We need to make sure that if there were any previous docs already compiled,
        // they were compiled with the same Rustc version that we're currently using.
        // See the function doc comment for more.
        if self.bcx.build_config.intent.is_doc() {
            RustdocFingerprint::check_rustdoc_fingerprint(&self)?
        }

        // Bind observations only after the actual layouts and unit hashes
        // exist, before preparing or dispatching any compiler command.
        // Trust: a parent fingerprint recursively observes child outputs. All
        // selected unit read locks must precede that first observation; locking
        // a child only when compile() later visits it leaves fresh parents stale
        // if its previous producer finishes while this graph waits for the lock.
        if self.bcx.gctx.cli_unstable().fine_grain_locking {
            let leases = Arc::clone(&self.lock_manager);
            leases.lock_selected_graph(self, exec.as_ref())?;
        }
        exec.prepare_unit_observation(self)?;
        for unit in &self.bcx.roots {
            let force_rebuild = self.bcx.build_config.force_rebuild;
            super::compile(self, &mut queue, unit, exec, force_rebuild)?;
        }

        // Now that we've got the full job queue and we've done all our
        // fingerprint analysis to determine what to run, bust all the memoized
        // fingerprint hashes to ensure that during the build they all get the
        // most up-to-date values. In theory we only need to bust hashes that
        // transitively depend on a dirty build script, but it shouldn't matter
        // that much for performance anyway.
        for fingerprint in self.fingerprints.values() {
            fingerprint.clear_memoized();
        }

        // Now that we've figured out everything that we're going to do, do it!
        let tests = tests
            .map(|request| {
                self.prepare_test_actions(&request)
                    .map(|actions| (request, actions))
            })
            .transpose()?;
        // Trust: queue return has joined its workers and returned its local
        // token guards. Retire actual original credits on failure as well.
        let executed = queue.execute(self, tests);
        #[cfg(any(target_os = "linux", target_os = "macos"))]
        let retired = self.retire_fixed_gnu();
        executed?;
        #[cfg(any(target_os = "linux", target_os = "macos"))]
        retired?;

        self.finish_compilation_and_release_leases(true)?;
        Ok(())
    }

    #[cfg(any(target_os = "linux", target_os = "macos"))]
    pub(super) fn has_fixed_gnu(&self) -> bool {
        self.fixed_gnu.is_some()
    }

    #[cfg(any(target_os = "linux", target_os = "macos"))]
    pub(super) fn check_fixed_gnu(&self) -> CargoResult<()> {
        if let Some(bridge) = &self.fixed_gnu {
            bridge.check()?;
        }
        Ok(())
    }

    #[cfg(any(target_os = "linux", target_os = "macos"))]
    fn retire_fixed_gnu(&mut self) -> CargoResult<()> {
        if let Some(bridge) = &mut self.fixed_gnu {
            anyhow::ensure!(
                bridge.try_retire()?,
                "inherited GNU credits remain outstanding after actual worker join"
            );
            bridge.check()?;
        }
        Ok(())
    }

    /// Retire compiler leases after all compiler workers have actually joined
    /// and the coordinator has finished compiler diagnostics and timing writes.
    /// No compiler action may be dispatched after this one-way transition.
    /// Tests retain this runner's jobserver, paths and execution ownership.
    pub(crate) fn finish_compilation_and_release_leases(
        &mut self,
        compile_succeeded: bool,
    ) -> CargoResult<()> {
        self.finish_compilation(compile_succeeded, false).map(drop)
    }

    pub(crate) fn finish_compilation_with_workload_leases(
        &mut self,
        compile_succeeded: bool,
    ) -> CargoResult<Option<Arc<OriginalOutputLeases>>> {
        self.finish_compilation(compile_succeeded, true)
    }
    fn finish_compilation(
        &mut self,
        compile_succeeded: bool,
        retain_outputs: bool,
    ) -> CargoResult<Option<Arc<OriginalOutputLeases>>> {
        match self.compilation_lease_state {
            CompilationLeaseState::Finalized => return Ok(None),
            CompilationLeaseState::Aborted if !compile_succeeded => return Ok(None),
            CompilationLeaseState::Aborted => bail!("compilation finalization previously failed"),
            CompilationLeaseState::Active => {}
        }
        // A failed or incomplete graph cannot collect/write predicted outputs.
        // Mark retirement before finalization so an error cannot retry it.
        self.compilation_lease_state = CompilationLeaseState::Aborted;
        let result = (|| {
            if compile_succeeded {
                self.finalize_compilation_outputs()?;
            }
            if retain_outputs && compile_succeeded {
                let leases = self
                    .workload_output_leases
                    .take()
                    .context("workload lost its original precompile output lease owner")?;
                leases.validate(&self.bcx.ws.target_dir().into_path_unlocked())?;
                Ok(Some(leases))
            } else {
                Ok(None)
            }
        })();
        // Even an output-finalization error must release its owned leases:
        // an already-running test may be waiting for a nested same-target build.
        self.lock_manager.release_all();
        if let Some(files) = self.files.as_mut() {
            files.release_compile_leases();
        }
        drop(self.workload_output_leases.take());
        drop(self.compilation_cache_lease.take());
        if compile_succeeded && result.is_ok() {
            self.compilation_lease_state = CompilationLeaseState::Finalized;
        }
        result
    }

    /// Borrow the one original precompile guard owner for an intermediate
    /// UnitOutput. The queue must independently park/join current writers and
    /// the host must authorize its actual phase before any registration/GO.
    pub(crate) fn workload_output_leases(&self) -> CargoResult<Arc<OriginalOutputLeases>> {
        anyhow::ensure!(
            self.workload_outputs
                && matches!(self.compilation_lease_state, CompilationLeaseState::Active),
            "intermediate output has no active original workload compilation"
        );
        let leases = self
            .workload_output_leases
            .as_ref()
            .context("intermediate output lost its original precompile guards")?;
        leases.validate(&self.bcx.ws.target_dir().into_path_unlocked())?;
        Ok(Arc::clone(leases))
    }

    /// Select and retain this ready RunCustomBuild's actual current compiled
    /// UnitOutput. The queue must independently join current writers and the
    /// native host must retain its original phase before any target GO.
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    pub(crate) fn capture_workload_build_script(
        &self,
        unit: &Unit,
        inputs: Arc<crate::ops::cargo_test::workload::Inputs>,
    ) -> CargoResult<Arc<crate::ops::cargo_test::workload::NativeOutput>> {
        let (compiled, executable) = super::custom_build::compiled_script_executable(self, unit)?;
        let outputs = self.outputs(&compiled)?;
        anyhow::ensure!(
            outputs
                .iter()
                .filter(
                    |output| output.flavor == FileFlavor::Normal && output.bin_dst() == &executable
                )
                .count()
                == 1,
            "ready script does not select exactly its actual compiled UnitOutput"
        );
        let materialization = *self
            .workload_materializations
            .get(&compiled)
            .context("ready script has no actual successful compiled-unit materialization")?;
        let output = self.unit_output(&compiled, &executable)?;
        crate::ops::cargo_test::workload::NativeOutput::capture(
            inputs,
            &self.compilation,
            &output,
            self.workload_output_leases()?,
            materialization,
        )
    }

    fn finalize_compilation_outputs(&mut self) -> CargoResult<()> {
        // Trust: fresh documentation units do not cross a child-process
        // endpoint, so nothing else would ever recheck them — do it once here,
        // after cache acceptance. Dirty doc/docscrape units perform the same
        // diagnostic around every child; pathname/runtime authority is
        // enforced separately.
        if let Some(identity) = &self.verified_rustdoc_launcher {
            identity.ensure_current()?;
        }

        self.populate_execution_environment()?;

        self.collect_doc_merge_info()?;

        // Collect the result of the build into `self.compilation`.
        for unit in &self.bcx.roots {
            self.collect_tests_and_executables(unit)?;

            // Collect information for `rustdoc --test`.
            if unit.mode.is_doc_test() {
                let mut unstable_opts = false;
                let mut args = compiler::extern_args(self, unit, &mut unstable_opts)?;
                args.extend(compiler::lib_search_paths(self, unit)?);
                args.extend(compiler::lto_args(self, unit));
                args.extend(compiler::features_args(unit));
                args.extend(compiler::check_cfg_args(unit));

                let script_metas = self.find_build_script_metadatas(unit);
                if let Some(meta_vec) = script_metas.clone() {
                    for meta in meta_vec {
                        if let Some(output) = self.build_script_outputs.lock().unwrap().get(meta) {
                            for cfg in &output.cfgs {
                                args.push("--cfg".into());
                                args.push(cfg.into());
                            }

                            for check_cfg in &output.check_cfgs {
                                args.push("--check-cfg".into());
                                args.push(check_cfg.into());
                            }

                            for (lt, arg) in &output.linker_args {
                                if lt.applies_to(&unit.target, unit.mode) {
                                    args.push("-C".into());
                                    args.push(format!("link-arg={}", arg).into());
                                }
                            }
                        }
                    }
                }
                args.extend(unit.rustdocflags.iter().map(Into::into));

                use super::MessageFormat;
                let format = match self.bcx.build_config.message_format {
                    MessageFormat::Short => "short",
                    MessageFormat::Human => "human",
                    MessageFormat::Json { .. } => "json",
                };
                args.push("--error-format".into());
                args.push(format.into());

                self.compilation.to_doc_test.push(compilation::Doctest {
                    unit: unit.clone(),
                    args,
                    unstable_opts,
                    linker: self
                        .compilation
                        .target_linker(unit.kind)
                        .map(|p| p.to_path_buf()),
                    script_metas,
                    env: artifact::get_env(self, unit, self.unit_deps(unit))?,
                });
            }

            super::output_depinfo(self, unit)?;
        }

        Ok(())
    }

    /// Trust: all runtime build-script prerequisites have completed before a
    /// test action calls this. Reconstruct the same final environment without
    /// accumulating duplicate OUT_DIR/env entries across ready test actions.
    fn populate_execution_environment(&mut self) -> CargoResult<()> {
        self.compilation.extra_env.clear();
        self.compilation.native_dirs.clear();
        // Add `OUT_DIR` to env vars if unit has a build script.
        let units_with_build_script = &self
            .bcx
            .roots
            .iter()
            .filter(|unit| self.build_scripts.contains_key(unit))
            .dedup_by(|x, y| x.pkg.package_id() == y.pkg.package_id())
            .collect::<Vec<_>>();
        for unit in units_with_build_script {
            for dep in &self.bcx.unit_graph[unit] {
                if dep.unit.mode.is_run_custom_build() {
                    let out_dir = if self.bcx.gctx.cli_unstable().build_dir_new_layout {
                        self.files().out_dir_new_layout(&dep.unit)
                    } else {
                        self.files().build_script_out_dir(&dep.unit)
                    };
                    let script_meta = self.get_run_build_script_metadata(&dep.unit);
                    self.compilation
                        .extra_env
                        .entry(script_meta)
                        .or_insert_with(Vec::new)
                        .push(("OUT_DIR".to_string(), out_dir.display().to_string()));
                }
            }
        }

        for (script_meta, output) in self.build_script_outputs.lock().unwrap().iter() {
            self.compilation
                .extra_env
                .entry(*script_meta)
                .or_insert_with(Vec::new)
                .extend(output.env.iter().cloned());

            for dir in output.library_paths.iter() {
                self.compilation
                    .native_dirs
                    .insert(dir.clone().into_path_buf());
            }
        }
        Ok(())
    }

    pub(crate) fn prepare_test_actions(
        &self,
        request: &crate::ops::cargo_test::graph::TestGraphOptions,
    ) -> CargoResult<Vec<crate::ops::cargo_test::graph::TestAction>> {
        use crate::ops::cargo_test::graph::{self, TestAction};
        // Trust: the private retained route is a verified test --no-run
        // compilation. Its default roots retain Cargo's Doctest metadata and
        // authenticated collect-only census; neither executes documentation
        // tests. Only ordinary Test units become queued execution actions,
        // and retained run_tests returns before legacy rustdoc execution.
        if request.retained && !matches!(self.bcx.build_config.intent, UserIntent::Test) {
            bail!(
                "retained execution requires ordinary test compilation, not documentation execution"
            );
        }
        // Native admission refuses this entire population until rustdoc's
        // complete process path has its own checked handoff. Ordinary fixed
        // tests must not leave this queue for a wider post-compile GNU pool.
        // Retained verified fixed tests preserve their existing collect-only
        // documentation metadata and return before legacy rustdoc execution.
        #[cfg(any(target_os = "linux", target_os = "macos"))]
        let fixed_execution = !request.retained && self.bcx.gctx.fixed_admission()?.is_some();
        #[cfg(not(any(target_os = "linux", target_os = "macos")))]
        let fixed_execution = false;
        if (self.native_resources() || fixed_execution)
            && self.bcx.roots.iter().any(|unit| unit.mode.is_doc_test())
        {
            bail!(
                "native worker admission for documentation tests is unavailable; select explicit native harness targets (--lib or --tests)"
            );
        }
        let mut roots = self.bcx.roots.iter().collect::<Vec<_>>();
        roots.sort();
        let plan = self.bcx.build_config.test_plan.as_deref();
        let mut actions = Vec::new();
        for unit in roots {
            if unit.mode != CompileMode::Test || unit.skip_non_compile_time_dep {
                continue;
            }
            // Trust: without a plan an executable runs once, with the
            // invocation's arguments. Under a plan it runs once per distinct
            // argument list of the requests that selected it.
            let runs = match plan {
                None => vec![(request.args.clone(), Vec::new())],
                Some(plan) => {
                    let requests = self
                        .bcx
                        .trust_root_requests
                        .get(unit)
                        .filter(|requests| !requests.is_empty())
                        .with_context(|| {
                            format!(
                                "test plan `{}`: no request selected {} of `{}`",
                                plan.path.display(),
                                unit.target.description_named(),
                                unit.pkg.name()
                            )
                        })?;
                    plan.actions(requests)
                }
            };
            for output in self.outputs(unit)?.iter() {
                if matches!(
                    output.flavor,
                    FileFlavor::DebugInfo
                        | FileFlavor::Auxiliary
                        | FileFlavor::Sbom
                        | FileFlavor::Unremap
                ) {
                    continue;
                }
                // Trust: one action per run of this executable.
                for (args, requests) in &runs {
                    actions.push(TestAction {
                        index: actions.len(),
                        total: 0,
                        unit: unit.clone(),
                        path: output.path.clone(),
                        args: args.clone(),
                        requests: requests.clone(),
                        weight: 1,
                        exclusive: false,
                        memory: 0,
                        seconds: 0,
                        workload_action: None,
                    });
                }
            }
        }
        // Trust: a plan request that selected no test executable is refused.
        if let Some(plan) = plan {
            plan.require_actions(actions.iter().flat_map(|action| &action.requests))?;
        }
        if let Some(workload) = &request.workload {
            actions = crate::ops::cargo_test::workload::expand(actions, &workload.plan)?;
        }
        let total = actions.len();
        for action in &mut actions {
            action.total = total;
        }
        // Trust: a package tested only through its doctests is tested too.
        let doctested: Vec<_> = self
            .bcx
            .roots
            .iter()
            .filter(|unit| unit.mode.is_doc_test())
            .map(|unit| &unit.pkg)
            .collect();
        // Trust: a harness policy this pool cannot grant refuses a plan's
        // run before any test: it judged nothing.
        let planned = self.bcx.build_config.test_plan.is_some();
        graph::admit_actions(
            self.bcx.gctx,
            &mut actions,
            request,
            &self.compilation,
            &doctested,
        )
        .map_err(|error| {
            if planned {
                crate::ops::cargo_test::plan_outcome::cannot_judge(error)
            } else {
                error
            }
        })?;
        Ok(actions)
    }

    pub(crate) fn test_action_command(
        &mut self,
        action: &crate::ops::cargo_test::graph::TestAction,
        request: &crate::ops::cargo_test::graph::TestGraphOptions,
    ) -> CargoResult<(String, cargo_util::ProcessBuilder)> {
        self.populate_execution_environment()?;
        let output = self.unit_output(&action.unit, &action.path)?;
        // Trust: the action's own arguments, which under a test plan are its
        // requests' and not the invocation's.
        let (display, mut command) = crate::ops::cargo_test::graph::command(
            self.bcx.gctx,
            &output,
            &action.args,
            &self.compilation,
            action.weight,
        )?;
        // Trust: a plan's built tools, for the members whose tests run them.
        if let Some(plan) = self.bcx.build_config.test_plan.as_deref() {
            plan.export_tools(action.unit.pkg.name().as_str(), &mut command);
        }
        if let Some(workload_action) = action.workload_action {
            request
                .workload
                .as_ref()
                .context("workload action has no original input owner")?
                .inputs
                .configure_harness(&mut command)?;
            crate::ops::cargo_test::workload::configure(&mut command, workload_action);
        }
        Ok((display, command))
    }

    fn collect_tests_and_executables(&mut self, unit: &Unit) -> CargoResult<()> {
        for output in self.outputs(unit)?.iter() {
            if matches!(
                output.flavor,
                FileFlavor::DebugInfo
                    | FileFlavor::Auxiliary
                    | FileFlavor::Sbom
                    | FileFlavor::Unremap
            ) {
                continue;
            }

            let bindst = output.bin_dst();

            if unit.mode == CompileMode::Test {
                self.compilation
                    .tests
                    .push(self.unit_output(unit, &output.path)?);
            } else if unit.target.is_executable() {
                self.compilation
                    .binaries
                    .push(self.unit_output(unit, bindst)?);
            } else if unit.target.is_cdylib()
                && !self.compilation.cdylibs.iter().any(|uo| uo.unit == *unit)
            {
                self.compilation
                    .cdylibs
                    .push(self.unit_output(unit, bindst)?);
            }
        }
        Ok(())
    }

    fn collect_doc_merge_info(&mut self) -> CargoResult<()> {
        if !self.bcx.gctx.cli_unstable().rustdoc_mergeable_info {
            return Ok(());
        }

        if !self.bcx.build_config.intent.is_doc() {
            return Ok(());
        }

        if self.bcx.build_config.intent.wants_doc_json_output() {
            // rustdoc JSON output doesn't support merge (yet?)
            return Ok(());
        }

        let mut doc_parts_map: HashMap<_, Vec<_>> = HashMap::default();

        let unit_iter = if self.bcx.build_config.intent.wants_deps_docs() {
            itertools::Either::Left(self.bcx.unit_graph.keys())
        } else {
            itertools::Either::Right(self.bcx.roots.iter())
        };

        for unit in unit_iter {
            if !unit.mode.is_doc() {
                continue;
            }
            // Assumption: one `rustdoc` call generates only one cross-crate info JSON.
            let outputs = self.outputs(unit)?;

            let Some(doc_parts) = outputs
                .iter()
                .find(|o| matches!(o.flavor, FileFlavor::DocParts))
            else {
                continue;
            };

            doc_parts_map
                .entry(unit.kind)
                .or_default()
                .push(doc_parts.path.to_owned());
        }

        self.compilation.rustdoc_fingerprints = Some(
            doc_parts_map
                .into_iter()
                .map(|(kind, doc_parts)| (kind, RustdocFingerprint::new(self, kind, doc_parts)))
                .collect(),
        );

        Ok(())
    }

    /// Returns the executable for the specified unit (if any).
    pub fn get_executable(&mut self, unit: &Unit) -> CargoResult<Option<PathBuf>> {
        let is_binary = unit.target.is_executable();
        let is_test = unit.mode.is_any_test();
        if !unit.mode.generates_executable() || !(is_binary || is_test) {
            return Ok(None);
        }
        Ok(self
            .outputs(unit)?
            .iter()
            .find(|o| o.flavor == FileFlavor::Normal)
            .map(|output| output.bin_dst().clone()))
    }

    #[tracing::instrument(skip_all)]
    pub fn prepare_units(&mut self) -> CargoResult<()> {
        #[cfg(any(target_os = "linux", target_os = "macos"))]
        if let Some(candidate) =
            crate::resource_v3::current().and_then(|startup| startup.candidate.clone())
        {
            super::candidate_coordinator::validate_graph(self, &candidate)?;
            anyhow::ensure!(
                self.continued_outputs.is_none(),
                "candidate cannot replace an existing graph continuation"
            );
            self.continued_outputs = crate::resource_v3::candidate_coordinator::outputs(
                &self.bcx.ws.target_dir().into_path_unlocked(),
            )?;
        }
        let dest = self.bcx.profiles.get_dir_name();
        // We try to only lock the artifact-dir if we need to.
        // For example, `cargo check` does not write any files to the artifact-dir so we don't need
        // to lock it.
        let must_take_artifact_dir_lock = compilation_files::artifact_dir_required(self.bcx);
        #[cfg(any(target_os = "linux", target_os = "macos"))]
        let continued = self.continued_outputs.as_ref();
        #[cfg(not(any(target_os = "linux", target_os = "macos")))]
        let continued = None;
        let layouts = layouts::PreparedLayouts::acquire(
            self.bcx.ws,
            &self.bcx.all_kinds,
            &dest,
            must_take_artifact_dir_lock,
            self.workload_outputs,
            continued,
        )?;
        let host_layout = layouts.host;
        let targets = layouts.targets;
        self.primary_packages
            .extend(self.bcx.roots.iter().map(|u| u.pkg.package_id()));
        self.compilation
            .root_crate_names
            .extend(self.bcx.roots.iter().map(|u| u.target.crate_name()));

        self.record_units_requiring_metadata();

        let files = CompilationFiles::new(self, host_layout, targets)?;
        self.files = Some(files);
        Ok(())
    }

    /// Prepare this context, ensuring that all filesystem directories are in
    /// place.
    #[tracing::instrument(skip_all)]
    pub fn prepare(&mut self) -> CargoResult<()> {
        self.files
            .as_mut()
            .unwrap()
            .host
            .prepare()
            .context("couldn't prepare build directories")?;
        for target in self.files.as_mut().unwrap().target.values_mut() {
            target
                .prepare()
                .context("couldn't prepare build directories")?;
        }

        let directories = self
            .compilation
            .record_output_paths(self.bcx, self.files.as_ref().unwrap());
        let private_native = self
            .bcx
            .unit_graph
            .keys()
            .any(|unit| self.files().private_unit(unit).is_some());
        for directory in directories {
            if private_native {
                // Trust: the original parent prepares actual private output
                // owners before GO. This availability check grants no path
                // ownership; the candidate never creates artifact namespaces.
                anyhow::ensure!(
                    std::fs::symlink_metadata(&directory)?.file_type().is_dir(),
                    "original parent did not prepare native unit directory {}",
                    directory.display()
                );
            } else {
                paths::create_dir_all(&directory)?;
            }
        }
        Ok(())
    }

    pub fn files(&self) -> &CompilationFiles<'a, 'gctx> {
        self.files.as_ref().unwrap()
    }

    /// Returns the filenames that the given unit will generate.
    pub fn outputs(&self, unit: &Unit) -> CargoResult<Arc<Vec<OutputFile>>> {
        self.files.as_ref().unwrap().outputs(unit, self.bcx)
    }

    /// Direct dependencies for the given unit.
    pub fn unit_deps(&self, unit: &Unit) -> &[UnitDep] {
        &self.bcx.unit_graph[unit]
    }

    /// Returns the `RunCustomBuild` Units associated with the given Unit.
    ///
    /// If the package does not have a build script, this returns None.
    pub fn find_build_script_units(&self, unit: &Unit) -> Option<Vec<Unit>> {
        if unit.mode.is_run_custom_build() {
            return Some(vec![unit.clone()]);
        }

        let build_script_units: Vec<Unit> = self.bcx.unit_graph[unit]
            .iter()
            .filter(|unit_dep| {
                unit_dep.unit.mode.is_run_custom_build()
                    && unit_dep.unit.pkg.package_id() == unit.pkg.package_id()
            })
            .map(|unit_dep| unit_dep.unit.clone())
            .collect();
        if build_script_units.is_empty() {
            None
        } else {
            Some(build_script_units)
        }
    }

    /// Returns the metadata hash for the `RunCustomBuild` Unit associated with
    /// the given unit.
    ///
    /// If the package does not have a build script, this returns None.
    pub fn find_build_script_metadatas(&self, unit: &Unit) -> Option<Vec<UnitHash>> {
        self.find_build_script_units(unit).map(|units| {
            units
                .iter()
                .map(|u| self.get_run_build_script_metadata(u))
                .collect()
        })
    }

    /// Returns the metadata hash for a `RunCustomBuild` unit.
    pub fn get_run_build_script_metadata(&self, unit: &Unit) -> UnitHash {
        assert!(unit.mode.is_run_custom_build());
        self.files().metadata(unit).unit_id()
    }

    /// Returns the list of SBOM output file paths for a given [`Unit`].
    pub fn sbom_output_files(&self, unit: &Unit) -> CargoResult<Vec<PathBuf>> {
        super::rustc_command_context::RustcCommandContext::for_runner(self).sbom_output_files(unit)
    }

    /// Returns the list of unremap file paths for a given [`Unit`].
    pub fn unremap_output_files(&self, unit: &Unit) -> CargoResult<Vec<PathBuf>> {
        Ok(self
            .outputs(unit)?
            .iter()
            .filter(|o| o.flavor == FileFlavor::Unremap)
            .map(|o| o.path.clone())
            .collect())
    }

    pub fn is_primary_package(&self, unit: &Unit) -> bool {
        self.primary_packages.contains(&unit.pkg.package_id())
    }

    /// Returns a [`UnitOutput`] which represents some information about the
    /// output of a unit.
    pub fn unit_output(&self, unit: &Unit, path: &Path) -> CargoResult<UnitOutput> {
        let script_metas = self.find_build_script_metadatas(unit);
        let env = artifact::get_env(&self, unit, self.unit_deps(unit))?;
        Ok(UnitOutput {
            unit: unit.clone(),
            path: path.to_path_buf(),
            script_metas,
            env,
        })
    }

    /// Check if any output file name collision happens.
    /// See <https://github.com/rust-lang/cargo/issues/6313> for more.
    #[tracing::instrument(skip_all)]
    fn check_collisions(&self) -> CargoResult<()> {
        // Trust: two requests of a test plan that build one target two ways
        // into one file are refused; upstream only warns, and a harness would
        // run whichever was linked last.
        plan_collisions::refuse(self)?;
        let mut output_collisions = HashMap::default();
        let describe_collision = |unit: &Unit, other_unit: &Unit| -> String {
            format!(
                "the {} target `{}` in package `{}` has the same output filename as the {} target `{}` in package `{}`",
                unit.target.kind().description(),
                unit.target.name(),
                unit.pkg.package_id(),
                other_unit.target.kind().description(),
                other_unit.target.name(),
                other_unit.pkg.package_id(),
            )
        };
        let suggestion = [
            Level::NOTE.message("this may become a hard error in the future; see <https://github.com/rust-lang/cargo/issues/6313>"),
            Level::HELP.message("consider changing their names to be unique or compiling them separately")
        ];
        let rustdoc_suggestion = [
            Level::NOTE.message("this is a known bug where multiple crates with the same name use the same path; see <https://github.com/rust-lang/cargo/issues/6313>")
        ];
        let report_collision = |unit: &Unit,
                                other_unit: &Unit,
                                path: &PathBuf,
                                messages: &[Message<'_>]|
         -> CargoResult<()> {
            if unit.target.name() == other_unit.target.name() {
                self.bcx.gctx.shell().print_report(
                    &[Level::WARNING
                        .secondary_title(format!("output filename collision at {}", path.display()))
                        .elements(
                            [Level::NOTE.message(describe_collision(unit, other_unit))]
                                .into_iter()
                                .chain(messages.iter().cloned()),
                        )],
                    false,
                )
            } else {
                self.bcx.gctx.shell().print_report(
                    &[Level::WARNING
                        .secondary_title(format!("output filename collision at {}", path.display()))
                        .elements([
                            Level::NOTE.message(describe_collision(unit, other_unit)),
                            Level::NOTE.message("if this looks unexpected, it may be a bug in Cargo. Please file a bug \
                                report at https://github.com/rust-lang/cargo/issues/ with as much information as you \
                                can provide."),
                            Level::NOTE.message(format!("cargo {} running on `{}` target `{}`",
                                crate::version(), self.bcx.host_triple(), self.bcx.target_data.short_name(&unit.kind))),
                            Level::NOTE.message(format!("first unit: {unit:?}")),
                            Level::NOTE.message(format!("second unit: {other_unit:?}")),
                        ])],
                    false,
                )
            }
        };

        fn doc_collision_error(unit: &Unit, other_unit: &Unit) -> CargoResult<()> {
            bail!(
                "document output filename collision\n\
                 The {} `{}` in package `{}` has the same name as the {} `{}` in package `{}`.\n\
                 Only one may be documented at once since they output to the same path.\n\
                 Consider documenting only one, renaming one, \
                 or marking one with `doc = false` in Cargo.toml.",
                unit.target.kind().description(),
                unit.target.name(),
                unit.pkg,
                other_unit.target.kind().description(),
                other_unit.target.name(),
                other_unit.pkg,
            );
        }

        let mut keys = self
            .bcx
            .unit_graph
            .keys()
            .filter(|unit| !unit.mode.is_run_custom_build())
            .collect::<Vec<_>>();
        // Sort for consistent error messages.
        keys.sort_unstable();
        // These are kept separate to retain compatibility with older
        // versions, which generated an error when there was a duplicate lib
        // or bin (but the old code did not check bin<->lib collisions). To
        // retain backwards compatibility, this only generates an error for
        // duplicate libs or duplicate bins (but not both). Ideally this
        // shouldn't be here, but since there isn't a complete workaround,
        // yet, this retains the old behavior.
        let mut doc_libs = HashMap::default();
        let mut doc_bins = HashMap::default();
        for unit in keys {
            if unit.mode.is_doc() && self.is_primary_package(unit) {
                // These situations have been an error since before 1.0, so it
                // is not a warning like the other situations.
                if unit.target.is_lib() {
                    if let Some(prev) = doc_libs.insert((unit.target.crate_name(), unit.kind), unit)
                    {
                        doc_collision_error(unit, prev)?;
                    }
                } else if let Some(prev) =
                    doc_bins.insert((unit.target.crate_name(), unit.kind), unit)
                {
                    doc_collision_error(unit, prev)?;
                }
            }
            for output in self.outputs(unit)?.iter() {
                if let Some(other_unit) = output_collisions.insert(output.path.clone(), unit) {
                    if unit.mode.is_doc() {
                        // See https://github.com/rust-lang/rust/issues/56169
                        // and https://github.com/rust-lang/rust/issues/61378
                        report_collision(unit, other_unit, &output.path, &rustdoc_suggestion)?;
                    } else {
                        report_collision(unit, other_unit, &output.path, &suggestion)?;
                    }
                }
                if let Some(hardlink) = output.hardlink.as_ref() {
                    if let Some(other_unit) = output_collisions.insert(hardlink.clone(), unit) {
                        report_collision(unit, other_unit, hardlink, &suggestion)?;
                    }
                }
                if let Some(ref export_path) = output.export_path {
                    if let Some(other_unit) = output_collisions.insert(export_path.clone(), unit) {
                        self.bcx.gctx.shell().print_report(
                            &[Level::WARNING
                                .secondary_title(format!(
                                    "`--artifact-dir` filename collision at {}",
                                    export_path.display()
                                ))
                                .elements(
                                    [Level::NOTE.message(describe_collision(unit, other_unit))]
                                        .into_iter()
                                        .chain(suggestion.iter().cloned()),
                                )],
                            false,
                        )?;
                    }
                }
            }
        }
        Ok(())
    }

    /// Records the list of units which are required to emit metadata.
    ///
    /// Units which depend only on the metadata of others requires the others to
    /// actually produce metadata, so we'll record that here.
    fn record_units_requiring_metadata(&mut self) {
        for (key, deps) in self.bcx.unit_graph.iter() {
            for dep in deps {
                if self.only_requires_rmeta(key, &dep.unit) {
                    self.rmeta_required.insert(dep.unit.clone());
                }
            }
        }
    }

    /// Returns whether when `parent` depends on `dep` if it only requires the
    /// metadata file from `dep`.
    pub fn only_requires_rmeta(&self, parent: &Unit, dep: &Unit) -> bool {
        // We're only a candidate for requiring an `rmeta` file if we
        // ourselves are building an rlib,
        super::rustc_command_context::only_requires_rmeta(parent, dep)
    }

    /// Returns whether when `unit` is built whether it should emit metadata as
    /// well because some compilations rely on that.
    pub fn rmeta_required(&self, unit: &Unit) -> bool {
        self.rmeta_required.contains(unit)
    }

    /// Finds metadata for Doc/Docscrape units.
    ///
    /// rustdoc needs a -Cmetadata flag in order to recognize StableCrateIds that refer to
    /// items in the crate being documented. The -Cmetadata flag used by reverse-dependencies
    /// will be the metadata of the Cargo unit that generated the current library's rmeta file,
    /// which should be a Check unit.
    ///
    /// If the current crate has reverse-dependencies, such a Check unit should exist, and so
    /// we use that crate's metadata. If not, we use the crate's Doc unit so at least examples
    /// scraped from the current crate can be used when documenting the current crate.
    #[tracing::instrument(skip_all)]
    pub fn compute_metadata_for_doc_units(&mut self) {
        for unit in self.bcx.unit_graph.keys() {
            if !unit.mode.is_doc() && !unit.mode.is_doc_scrape() {
                continue;
            }

            let matching_units = self
                .bcx
                .unit_graph
                .keys()
                .filter(|other| {
                    unit.pkg == other.pkg
                        && unit.target == other.target
                        && !other.mode.is_doc_scrape()
                })
                .collect::<Vec<_>>();
            let metadata_unit = matching_units
                .iter()
                .find(|other| other.mode.is_check())
                .or_else(|| matching_units.iter().find(|other| other.mode.is_doc()))
                .unwrap_or(&unit);
            self.metadata_for_doc_units
                .insert(unit.clone(), self.files().metadata(metadata_unit));
        }
    }
}
