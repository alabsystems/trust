//! Management of the interaction between the main `cargo` and all spawned jobs.
//!
//! ## Overview
//!
//! This module implements a job queue. A job here represents a unit of work,
//! which is roughly a rustc invocation, a build script run, or just a no-op.
//! The job queue primarily handles the following things:
//!
//! * Spawns concurrent jobs. Depending on its [`Freshness`], a job could be
//!     either executed on a spawned thread or ran on the same thread to avoid
//!     the threading overhead.
//! * Controls the number of concurrency. It allocates and manages [`jobserver`]
//!     tokens to each spawned off rustc and build scripts.
//! * Manages the communication between the main `cargo` process and its
//!     spawned jobs. Those [`Message`]s are sent over a [`Queue`] shared
//!     across threads.
//! * Schedules the execution order of each [`Job`]. Priorities are determined
//!     when calling [`JobQueue::enqueue`] to enqueue a job. The scheduling is
//!     relatively rudimentary and could likely be improved.
//!
//! A rough outline of building a queue and executing jobs is:
//!
//! 1. [`JobQueue::new`] to simply create one queue.
//! 2. [`JobQueue::enqueue`] to add new jobs onto the queue.
//! 3. Consumes the queue and executes all jobs via [`JobQueue::execute`].
//!
//! The primary loop happens insides [`JobQueue::execute`], which is effectively
//! [`DrainState::drain_the_queue`]. [`DrainState`] is, as its name tells,
//! the running state of the job queue getting drained.
//!
//! ## Jobserver
//!
//! As of Feb. 2023, Cargo and rustc have a relatively simple jobserver
//! relationship with each other. They share a single jobserver amongst what
//! is potentially hundreds of threads of work on many-cored systems.
//! The jobserver could come from either the environment (e.g., from a `make`
//! invocation), or from Cargo creating its own jobserver server if there is no
//! jobserver to inherit from.
//!
//! Cargo wants to complete the build as quickly as possible, fully saturating
//! all cores (as constrained by the `-j=N`) parameter. Cargo also must not spawn
//! more than N threads of work: the total amount of tokens we have floating
//! around must always be limited to N.
//!
//! It is not really possible to optimally choose which crate should build
//! first or last; nor is it possible to decide whether to give an additional
//! token to rustc first or rather spawn a new crate of work. The algorithm in
//! Cargo prioritizes spawning as many crates (i.e., rustc processes) as
//! possible. In short, the jobserver relationship among Cargo and rustc
//! processes is **1 `cargo` to N `rustc`**. Cargo knows nothing beyond rustc
//! processes in terms of parallelism[^parallel-rustc].
//!
//! We integrate with the [jobserver] crate, originating from GNU make
//! [POSIX jobserver], to make sure that build scripts which use make to
//! build C code can cooperate with us on the number of used tokens and
//! avoid overfilling the system we're on.
//!
//! ## Scheduling
//!
//! The current scheduling algorithm is not really polished. It is simply based
//! on a dependency graph [`DependencyQueue`]. We continue adding nodes onto
//! the graph until we finalize it. When the graph gets finalized, it finds the
//! sum of the cost of each dependencies of each node, including transitively.
//! The sum of dependency cost turns out to be the cost of each given node.
//!
//! At the time being, the cost is just passed as a fixed placeholder in
//! [`JobQueue::enqueue`]. In the future, we could explore more possibilities
//! around it. For instance, we start persisting timing information for each
//! build somewhere. For a subsequent build, we can look into the historical
//! data and perform a PGO-like optimization to prioritize jobs, making a build
//! fully pipelined.
//!
//! ## Message queue
//!
//! Each spawned thread running a process uses the message queue [`Queue`] to
//! send messages back to the main thread (the one running `cargo`).
//! The main thread coordinates everything, and handles printing output.
//!
//! It is important to be careful which messages use [`push`] vs [`push_bounded`].
//! `push` is for priority messages (like tokens, or "finished") where the
//! sender shouldn't block. We want to handle those so real work can proceed
//! ASAP.
//!
//! `push_bounded` is only for messages being printed to stdout/stderr. Being
//! bounded prevents a flood of messages causing a large amount of memory
//! being used.
//!
//! `push` also avoids blocking which helps avoid deadlocks. For example, when
//! the diagnostic server thread is dropped, it waits for the thread to exit.
//! But if the thread is blocked on a full queue, and there is a critical
//! error, the drop will deadlock. This should be fixed at some point in the
//! future. The jobserver thread has a similar problem, though it will time
//! out after 1 second.
//!
//! To access the message queue, each running `Job` is given its own [`JobState`],
//! containing everything it needs to communicate with the main thread.
//!
//! See [`Message`] for all available message kinds.
//!
//! [^parallel-rustc]: In fact, `jobserver` that Cargo uses also manages the
//!     allocation of tokens to rustc beyond the implicit token each rustc owns
//!     (i.e., the ones used for parallel LLVM work and parallel rustc threads).
//!     See also ["Rust Compiler Development Guide: Parallel Compilation"]
//!     and [this comment][rustc-codegen] in rust-lang/rust.
//!
//! ["Rust Compiler Development Guide: Parallel Compilation"]: https://rustc-dev-guide.rust-lang.org/parallel-rustc.html
//! [rustc-codegen]: https://github.com/rust-lang/rust/blob/5423745db8b434fcde54888b35f518f00cce00e4/compiler/rustc_codegen_ssa/src/back/write.rs#L1204-L1217
//! [jobserver]: https://docs.rs/jobserver
//! [POSIX jobserver]: https://www.gnu.org/software/make/manual/html_node/POSIX-Jobserver.html
//! [`push`]: Queue::push
//! [`push_bounded`]: Queue::push_bounded

mod job;
mod job_state;
mod ready_token;
mod test_action;
mod test_admission;
mod tippy_arg_protocol;
#[cfg(any(target_os = "linux", target_os = "macos"))]
mod verification_action;
mod workload_script;

use crate::util::data_structures::{HashMap, HashSet};
use std::cell::RefCell;
use std::fmt::Write as _;
use std::path::{Path, PathBuf};
use std::sync::Arc;
use std::thread::{self, Scope};
use std::time::{Duration, Instant};
use std::{env, io};

use anyhow::{Context as _, format_err};
use jobserver::{Acquired, HelperThread};
use semver::Version;
use tracing::{debug, trace};

/// Trust: how long nothing may run while admissible work waits for the
/// jobserver credits a pool Targo made should return at once.
const TOKEN_STALL: Duration = Duration::from_secs(30);

pub use self::job::Freshness::{self, Dirty, Fresh};
pub use self::job::{Job, Work};
pub use self::job_state::JobState;
use self::test_action::{CancelTestWorkers, QueueNode, QueueWork, TestState};
use self::test_admission::{Choice, Demand, Occupancy};
use self::tippy_arg_protocol::{CLIPPY_ARGS_ENV, TIPPY_ENCODED_ARGS_ENV, suggested_args_suffix};
use super::BuildContext;
use super::BuildRunner;
use super::CompileMode;
use super::Unit;
use super::UnitIndex;
use super::custom_build::Severity;
use super::timings::SectionTiming;
use super::timings::Timings;
use crate::compiler::descriptive_pkg_name;
use crate::compiler::future_incompat::{self, FutureBreakageItem, FutureIncompatReportPackage};
use crate::context::WarningHandling;
use crate::diagnostics::GlobalDiagnosticStats;
use crate::diagnostics::rules::unused_dependencies;
use crate::ops::cargo_test::graph::{TestAction, TestGraphOptions};
use crate::resolver::ResolveBehavior;
use crate::util::CargoResult;
use crate::util::diagnostic_server::{self, DiagnosticPrinter};
use crate::util::errors::AlreadyPrintedError;
use crate::util::interning::InternedString;
use crate::util::log_message::{
    EXECUTION_VERSION, ExecutionGraphOutcome, ExecutionUnitOutcome, LogMessage,
};
use crate::util::machine_message::{self, Message as _};
use crate::util::{self, internal};
use crate::util::{DependencyQueue, GlobalContext, Progress, ProgressStyle, Queue};
use crate::workspace::{PackageId, TargetKind};
use cargo_util_terminal::Shell;

/// This structure is backed by the `DependencyQueue` type and manages the
/// queueing of compilation steps for each package. Packages enqueue units of
/// work and then later on the entire graph is converted to `DrainState` and
/// executed.
pub struct JobQueue<'gctx> {
    // Trust: execution actions are real dependents in this same admitted queue.
    queue: DependencyQueue<QueueNode, Artifact, QueueWork>,
    queued_units: HashSet<Unit>,
    counts: HashMap<PackageId, usize>,
    timings: Timings<'gctx>,
}

/// This structure is backed by the `DependencyQueue` type and manages the
/// actual compilation step of each package. Packages enqueue units of work and
/// then later on the entire graph is processed and compiled.
///
/// It is created from `JobQueue` when we have fully assembled the crate graph
/// (i.e., all package dependencies are known).
struct DrainState<'gctx> {
    // Trust: independent of errors and --keep-going. Active work still drains.
    root_cancelled: bool,
    // Trust: under a test plan, the test executables running at the last
    // look (`observe_plan_stop`), for the record of an interrupted run.
    plan_running: String,
    // Trust: compiler writers retire once, independently of active test actions.
    compiler_finalized: bool,
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    workload_script: Option<workload_script::Script>,
    // Trust: explicit dispatch/terminal observations, independent of legacy
    // timing events which omit fresh/no-op jobs and are not outcome verdicts.
    execution: ExecutionSummary,
    // Trust: DC-12a. Each compile unit dispatched, and whether it was fresh or
    // built, which the runner's end-of-build receipt names.
    ran: super::build_receipt::Ledger<Unit>,
    // This is the length of the DependencyQueue when starting out
    total_units: usize,

    queue: DependencyQueue<QueueNode, Artifact, QueueWork>,
    tests: Option<TestState>,
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    verification: Option<verification_action::State>,
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    native_inputs: Option<Arc<crate::ops::cargo_test::workload::Inputs>>,
    messages: Arc<Queue<Message>>,
    /// Diagnostic deduplication support.
    diag_dedupe: DiagDedupe<'gctx>,
    /// Count of warnings, used to print a summary after the job succeeds
    warning_count: HashMap<JobId, WarningCount>,
    active: HashMap<JobId, Unit>,
    compiled: HashSet<PackageId>,
    documented: HashSet<PackageId>,
    scraped: HashSet<PackageId>,
    counts: HashMap<PackageId, usize>,
    progress: Progress<'gctx>,
    next_id: u32,
    timings: Timings<'gctx>,

    /// Map from unit index to unit, for looking up dependency information.
    index_to_unit: HashMap<UnitIndex, Unit>,

    /// Tokens that are currently owned by this Cargo, and may be "associated"
    /// with a rustc process. They may also be unused, though if so will be
    /// dropped on the next loop iteration.
    ///
    /// Note that the length of this may be zero, but we will still spawn work,
    /// as we share the implicit token given to this Cargo process with a
    /// single rustc process.
    tokens: Vec<Acquired>,
    // Imported GNU transports use one cancellable ready-only request.
    retained_tokens: ready_token::ReadyTokenAdmission,
    #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
    bootstrap_full: Option<Arc<crate::context::bootstrap_full::BootstrapFull>>,
    /// Trust: tokens requested from the jobserver helper and not yet
    /// delivered. A weighted test waits for several; a request released by
    /// an idle wait must be made again.
    token_requests: usize,
    /// Trust: the jobserver helper failed to acquire a token, or a weighted
    /// test starved; no more tokens are requested or awaited.
    token_source_failed: bool,
    /// Trust: since when nothing has run while admissible work waits for
    /// jobserver credits.
    starved_since: Option<Instant>,
    /// Trust: the credits of the pool Targo created (`-j`), the only pool a
    /// test above weight 1 is admitted on.
    pool: usize,

    /// The list of jobs that we have not yet started executing, but have
    /// retrieved from the `queue`. We eagerly pull jobs off the main queue to
    /// allow us to request jobserver tokens pretty early.
    pending_queue: Vec<(QueueNode, QueueWork, usize)>,
    print: DiagnosticPrinter<'gctx>,

    /// How many jobs we've finished
    finished: usize,
    per_package_future_incompat_reports: Vec<FutureIncompatReportPackage>,
}

#[derive(Default)]
struct ExecutionSummary {
    scheduled: u64,
    completed: u64,
    root_cancelled: bool,
    failed: bool,
    compiler_finished: Option<Duration>,
}

impl ExecutionSummary {
    fn outcome(&self) -> ExecutionGraphOutcome {
        if self.root_cancelled {
            ExecutionGraphOutcome::Cancelled
        } else if self.failed || self.completed != self.scheduled {
            ExecutionGraphOutcome::Failed
        } else {
            ExecutionGraphOutcome::Succeeded
        }
    }
}

// Trust: cancellation of the root is a graph outcome, not a reason to relabel
// successful workers or unrelated compiler defects as cancelled. Only a worker
// result carrying a typed interruption has that unit outcome.
fn execution_unit_outcome(
    result: Result<(), &anyhow::Error>,
    tolerated: bool,
    denied_warnings: bool,
) -> ExecutionUnitOutcome {
    if denied_warnings {
        return ExecutionUnitOutcome::Failed;
    }
    match result {
        Ok(()) => ExecutionUnitOutcome::Succeeded,
        Err(error)
            if error.chain().any(|cause| {
                cause
                    .downcast_ref::<io::Error>()
                    .is_some_and(|error| error.kind() == io::ErrorKind::Interrupted)
            }) =>
        {
            ExecutionUnitOutcome::Cancelled
        }
        Err(_) if tolerated => ExecutionUnitOutcome::ToleratedFailure,
        Err(_) => ExecutionUnitOutcome::Failed,
    }
}

// Trust: --keep-going controls dispatch after a diagnostic; it never relaxes
// the final compiler warning policy or permits successful lease retirement.
fn compilation_warning_policy(
    handling: WarningHandling,
    lint_warning_count: usize,
) -> CargoResult<()> {
    if handling == WarningHandling::Deny && lint_warning_count != 0 {
        anyhow::bail!("warnings are denied by `build.warnings` configuration");
    }
    Ok(())
}

/// Count of warnings, used to print a summary after the job succeeds
#[derive(Default, Clone)]
pub struct WarningCount {
    /// total number of warnings
    pub total: usize,
    /// number of lint warnings
    pub lints: usize,
    /// number of warnings that were suppressed because they
    /// were duplicates of a previous warning
    pub duplicates: usize,
    /// number of fixable warnings set to `NotAllowed`
    /// if any errors have been seen for the current
    /// target
    pub fixable: FixableWarnings,
    /// if any errors have been seen for the current
    /// target
    pub supplanted_by_errors: bool,
}

impl WarningCount {
    /// If an error is seen this should be called
    /// to set `fixable` to `NotAllowed`
    fn disallow_fixable(&mut self) {
        self.fixable = FixableWarnings::NotAllowed;
    }

    /// Checks fixable if warnings are allowed
    /// fixable warnings are allowed if no
    /// errors have been seen for the current
    /// target. If an error was seen `fixable`
    /// will be `NotAllowed`.
    fn fixable_allowed(&self) -> bool {
        match &self.fixable {
            FixableWarnings::NotAllowed => false,
            _ => true,
        }
    }
}

/// Used to keep track of how many fixable warnings there are
/// and if fixable warnings are allowed
#[derive(Default, Copy, Clone)]
pub enum FixableWarnings {
    NotAllowed,
    #[default]
    Zero,
    Positive(usize),
}

pub struct ErrorsDuringDrain {
    pub count: usize,
}

struct ErrorToHandle {
    error: anyhow::Error,

    /// This field is true for "interesting" errors and false for "mundane"
    /// errors. If false, we print the above error only if it's the first one
    /// encountered so far while draining the job queue.
    ///
    /// At most places that an error is propagated, we set this to false to
    /// avoid scenarios where Cargo might end up spewing tons of redundant error
    /// messages. For example if an i/o stream got closed somewhere, we don't
    /// care about individually reporting every thread that it broke; just the
    /// first is enough.
    ///
    /// The exception where `print_always` is true is that we do report every
    /// instance of a rustc invocation that failed with diagnostics. This
    /// corresponds to errors from `Message::Finish`.
    print_always: bool,
}

impl<E> From<E> for ErrorToHandle
where
    anyhow::Error: From<E>,
{
    fn from(error: E) -> Self {
        ErrorToHandle {
            error: anyhow::Error::from(error),
            print_always: false,
        }
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct JobId(pub u32);

impl std::fmt::Display for JobId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

/// Handler for deduplicating diagnostics.
struct DiagDedupe<'gctx> {
    seen: RefCell<HashSet<u64>>,
    gctx: &'gctx GlobalContext,
}

impl<'gctx> DiagDedupe<'gctx> {
    fn new(gctx: &'gctx GlobalContext) -> Self {
        DiagDedupe {
            seen: RefCell::new(HashSet::default()),
            gctx,
        }
    }

    /// Emits a diagnostic message.
    ///
    /// Returns `true` if the message was emitted, or `false` if it was
    /// suppressed for being a duplicate.
    fn emit_diag(&self, diag: &str) -> CargoResult<bool> {
        let h = util::hash_u64(diag);
        if !self.seen.borrow_mut().insert(h) {
            return Ok(false);
        }
        let mut shell = self.gctx.shell();
        shell.print_ansi_stderr(diag.as_bytes())?;
        shell.err().write_all(b"\n")?;
        Ok(true)
    }
}

/// Possible artifacts that can be produced by compilations, used as edge values
/// in the dependency graph.
///
/// As edge values we can have multiple kinds of edges depending on one node,
/// for example some units may only depend on the metadata for an rlib while
/// others depend on the full rlib. This `Artifact` enum is used to distinguish
/// this case and track the progress of compilations as they proceed.
#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
enum Artifact {
    /// A generic placeholder for "depends on everything run by a step" and
    /// means that we can't start the next compilation until the previous has
    /// finished entirely.
    All,

    /// A node indicating that we only depend on the metadata of a compilation,
    /// but the compilation is typically also producing an rlib. We can start
    /// our step, however, before the full rlib is available.
    Metadata,
}

enum Message {
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    VerificationFinished(super::qualification::Completion),
    OriginalCommand(super::qualification_command::Observation),
    Run(JobId, String),
    WorkloadMaterialized(JobId, crate::ops::cargo_test::workload::Materialization),
    // Trust: typed build-analysis messages returned from a worker; the
    // non-Sync BuildLogger remains exclusively on the coordinator thread.
    InputWork(crate::util::log_message::LogMessage),
    RecheckFreshness {
        id: JobId,
        force: bool,
        reply: std::sync::mpsc::Sender<CargoResult<bool>>,
    },
    Stdout(String),
    Stderr(String),

    // This is for general stderr output from subprocesses
    Diagnostic {
        id: JobId,
        level: String,
        diag: String,
        lint: bool,
        fixable: bool,
    },
    // This handles duplicate output that is suppressed, for showing
    // only a count of duplicate messages instead
    WarningCount {
        id: JobId,
        lint: bool,
        emitted: bool,
        fixable: bool,
    },
    // This is for warnings generated by Cargo's interpretation of the
    // subprocess output, e.g. scrape-examples prints a warning if a
    // unit fails to be scraped
    Warning {
        id: JobId,
        warning: String,
    },

    FixDiagnostic(diagnostic_server::Message),
    Token(io::Result<Acquired>),
    Finish(JobId, Artifact, CargoResult<()>),
    // Trust: test failures never stand in for compilation-unit completion.
    TestFinished {
        index: usize,
        result: CargoResult<()>,
        elapsed: Duration,
        workload: Option<crate::ops::cargo_test::workload::CapturedAction>,
    },
    FutureIncompatReport(JobId, Vec<FutureBreakageItem>),
    SectionTiming(JobId, SectionTiming),
    /// Peak resident set size (in bytes) of a unit's process, for `--timings`.
    PeakMemory(JobId, u64),
    CpuTimes(JobId, cargo_util::CpuTimes),
    UnusedExterns(JobId, std::collections::BTreeSet<InternedString>),
}

impl<'gctx> JobQueue<'gctx> {
    pub fn new(bcx: &BuildContext<'_, 'gctx>) -> JobQueue<'gctx> {
        JobQueue {
            queue: DependencyQueue::new(),
            queued_units: HashSet::default(),
            counts: HashMap::default(),
            timings: Timings::new(bcx),
        }
    }

    pub fn enqueue(
        &mut self,
        build_runner: &BuildRunner<'_, 'gctx>,
        unit: &Unit,
        job: Job,
    ) -> CargoResult<()> {
        let dependencies = build_runner.unit_deps(unit);
        let mut queue_deps = dependencies
            .iter()
            .filter(|dep| {
                // Binaries aren't actually needed to *compile* tests, just to run
                // them, so we don't include this dependency edge in the job graph.
                // But we shouldn't filter out dependencies being scraped for Rustdoc.
                (!dep.unit.target.is_test() && !dep.unit.target.is_bin())
                    || dep.unit.artifact.is_true()
                    || dep.unit.mode.is_doc_scrape()
            })
            .map(|dep| {
                // Handle the case here where our `unit -> dep` dependency may
                // only require the metadata, not the full compilation to
                // finish. Use the tables in `build_runner` to figure out what
                // kind of artifact is associated with this dependency.
                let artifact = if build_runner.only_requires_rmeta(unit, &dep.unit) {
                    Artifact::Metadata
                } else {
                    Artifact::All
                };
                (dep.unit.clone(), artifact)
            })
            .collect::<HashMap<_, _>>();

        // This is somewhat tricky, but we may need to synthesize some
        // dependencies for this target if it requires full upstream
        // compilations to have completed. Because of pipelining, some
        // dependency edges may be `Metadata` due to the above clause (as
        // opposed to everything being `All`). For example consider:
        //
        //    a (binary)
        //    └ b (lib)
        //        └ c (lib)
        //
        // Here the dependency edge from B to C will be `Metadata`, and the
        // dependency edge from A to B will be `All`. For A to be compiled,
        // however, it currently actually needs the full rlib of C. This means
        // that we need to synthesize a dependency edge for the dependency graph
        // from A to C. That's done here.
        //
        // This will walk all dependencies of the current target, and if any of
        // *their* dependencies are `Metadata` then we depend on the `All` of
        // the target as well. This should ensure that edges changed to
        // `Metadata` propagate upwards `All` dependencies to anything that
        // transitively contains the `Metadata` edge.
        if unit.requires_upstream_objects() {
            for dep in dependencies {
                depend_on_deps_of_deps(build_runner, &mut queue_deps, dep.unit.clone());
            }

            fn depend_on_deps_of_deps(
                build_runner: &BuildRunner<'_, '_>,
                deps: &mut HashMap<Unit, Artifact>,
                unit: Unit,
            ) {
                for dep in build_runner.unit_deps(&unit) {
                    if deps.insert(dep.unit.clone(), Artifact::All).is_none() {
                        depend_on_deps_of_deps(build_runner, deps, dep.unit.clone());
                    }
                }
            }
        }

        // For now we use a fixed placeholder value for the cost of each unit, but
        // in the future this could be used to allow users to provide hints about
        // relative expected costs of units, or this could be automatically set in
        // a smarter way using timing data from a previous compilation.
        self.queue.queue(
            QueueNode::Compile(unit.clone()),
            QueueWork::Compile(job),
            queue_deps
                .into_iter()
                .map(|(unit, artifact)| (QueueNode::Compile(unit), artifact)),
            100,
        );
        self.queued_units.insert(unit.clone());
        *self.counts.entry(unit.pkg.package_id()).or_insert(0) += 1;
        Ok(())
    }

    /// Executes all jobs necessary to build the dependency graph.
    ///
    /// This function will spawn off `config.jobs()` workers to build all of the
    /// necessary dependencies, in order. Freshness is propagated as far as
    /// possible along each dependency chain.
    #[tracing::instrument(skip_all)]
    pub fn execute(
        mut self,
        build_runner: &mut BuildRunner<'_, '_>,
        tests: Option<(TestGraphOptions, Vec<TestAction>)>,
    ) -> CargoResult<()> {
        #[cfg(any(target_os = "linux", target_os = "macos"))]
        let verification = build_runner
            .qualification()
            .map(|options| self.enqueue_verifications(build_runner, options))
            .transpose()?;
        let retained = tests.as_ref().is_some_and(|(options, _)| options.retained);
        let test_signals = tests
            .as_ref()
            .map(|_| cargo_util::StreamingProcessScope::new().map(Arc::new))
            .transpose()?;
        let tests = match tests {
            Some((options, actions)) => {
                let prerequisites = self.enqueue_tests(build_runner, &options, &actions)?;
                Some(TestState::new(
                    options,
                    actions,
                    prerequisites,
                    test_signals
                        .as_ref()
                        .expect("test cancellation scope")
                        .clone(),
                    build_runner.bcx.gctx,
                )?)
            }
            None => None,
        };
        self.queue.queue_finished();

        // Trust: declare the complete Cargo-authenticated proof subject before
        // any queued work can emit a compiler message, artifact, or
        // build-script message. Once the queue is draining, the subject would
        // be a claim made alongside its own evidence rather than ahead of it.
        // Ordinary Cargo and non-JSON Targo output remain unchanged.
        if build_runner.bcx.build_config.emit_json() {
            if let Some(inventory) = super::trust_proof_inventory(build_runner)? {
                let mut shell = build_runner.bcx.gctx.shell();
                writeln!(shell.out(), "{}", inventory.to_json_string())?;
            }
        }

        let execution_registered = build_runner.bcx.unit_to_index.len() as u64;
        let execution_clock = build_runner.bcx.gctx.invocation_instant();
        if let Some(logger) = build_runner.bcx.logger {
            logger.log(LogMessage::ExecutionEnabled {
                version: EXECUTION_VERSION,
            });
            logger.log(LogMessage::CompilerObservationsEnabled {
                version: crate::util::log_message::COMPILER_OBSERVATION_VERSION,
                rusage_requested: build_runner.bcx.gctx.cli_unstable().mem_stats,
            });
        }

        let progress =
            Progress::with_style("Building", ProgressStyle::Ratio, build_runner.bcx.gctx);
        let state = DrainState {
            root_cancelled: false,
            plan_running: String::new(),
            compiler_finalized: false,
            #[cfg(any(target_os = "linux", target_os = "macos"))]
            workload_script: None,
            execution: ExecutionSummary::default(),
            // Trust: DC-12a, the units this queue runs.
            ran: super::build_receipt::Ledger::default(),
            // Trust: compile timing and lifecycle denominators stay compile-only.
            total_units: self.queued_units.len(),
            queue: self.queue,
            tests,
            #[cfg(any(target_os = "linux", target_os = "macos"))]
            verification,
            #[cfg(any(target_os = "linux", target_os = "macos"))]
            native_inputs: build_runner.native_inputs(),
            // 100 here is somewhat arbitrary. It is a few screenfulls of
            // output, and hopefully at most a few megabytes of memory for
            // typical messages. If you change this, please update the test
            // caching_large_output, too.
            messages: Arc::new(Queue::new(100)),
            diag_dedupe: DiagDedupe::new(build_runner.bcx.gctx),
            warning_count: HashMap::default(),
            active: HashMap::default(),
            compiled: HashSet::default(),
            documented: HashSet::default(),
            scraped: HashSet::default(),
            counts: self.counts,
            progress,
            next_id: 0,
            timings: self.timings,
            index_to_unit: build_runner
                .bcx
                .unit_to_index
                .iter()
                .map(|(unit, &index)| (index, unit.clone()))
                .collect(),
            tokens: Vec::new(),
            retained_tokens: Default::default(),
            #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
            bootstrap_full: build_runner.bcx.gctx.original_bootstrap_full().cloned(),
            token_requests: 0,
            token_source_failed: false,
            starved_since: None,
            pool: build_runner.bcx.jobs() as usize,
            pending_queue: Vec::new(),
            print: DiagnosticPrinter::new(
                build_runner.bcx.gctx,
                &build_runner.bcx.rustc().workspace_wrapper,
            ),
            finished: 0,
            per_package_future_incompat_reports: Vec::new(),
        };

        // Create a helper thread for acquiring jobserver tokens
        let messages = state.messages.clone();
        let helper = build_runner
            .jobserver
            .client()
            .clone()
            .into_helper_thread(move |token| {
                messages.push(Message::Token(token));
            })
            .context("failed to create helper thread for jobserver management")?;

        // Create a helper thread to manage the diagnostics for rustfix if
        // necessary.
        let messages = state.messages.clone();
        // It is important that this uses `push` instead of `push_bounded` for
        // now. If someone wants to fix this to be bounded, the `drop`
        // implementation needs to be changed to avoid possible deadlocks.
        let _diagnostic_server = build_runner
            .bcx
            .build_config
            .rustfix_diagnostic_server
            .borrow_mut()
            .take()
            .map(move |srv| srv.start(move |msg| messages.push(Message::FixDiagnostic(msg))));

        // Trust: bind the same policy used by compile_with_exec before emitting
        // a terminal JSON success record, including after --keep-going.
        let warning_handling = build_runner.bcx.gctx.warning_handling()?;
        #[cfg(any(target_os = "linux", target_os = "macos"))]
        let verification_signals = state.verification_signals();
        let input_work_logger = build_runner.bcx.logger;
        let input_work_ids = Arc::clone(&build_runner.bcx.input_work_capture_ids);
        let (mut result, execution, mut test_run) = thread::scope(|scope| {
            // Trust: this guard lives inside the thread scope, so unwinding
            // cancels owned test groups before the scope waits for workers.
            let mut cancel = CancelTestWorkers::new(test_signals.as_deref());
            #[cfg(any(target_os = "linux", target_os = "macos"))]
            let mut cancel_verification = CancelTestWorkers::new(verification_signals.as_deref());
            let result = state.drain_the_queue(build_runner, scope, &helper, warning_handling);
            cancel.disarm();
            #[cfg(any(target_os = "linux", target_os = "macos"))]
            cancel_verification.disarm();
            result
        });
        // The actual scope has now joined every test worker, including a
        // sender whose TestFinished message arrived before its final drops.
        // Only this boundary can retire the original native harness phase.
        #[cfg(any(target_os = "linux", target_os = "macos"))]
        if let Some(runtime) = &build_runner.resource_runtime
            && let Err(error) = runtime.finish_workload_harnesses()
        {
            let message = format!("failed to retire original native harness phase: {error:#}");
            if let Some(run) = test_run.as_mut() {
                run.reporting_error
                    .get_or_insert_with(|| anyhow::anyhow!(message.clone()));
            }
            if result.is_ok() {
                result = Err(anyhow::anyhow!(message));
            }
        }
        if let Some(signals) = test_signals {
            match Arc::try_unwrap(signals) {
                Ok(signals) => {
                    if let Err(error) = signals.finish()
                        && let Some(run) = test_run.as_mut()
                    {
                        run.interruption.get_or_insert_with(|| error.to_string());
                    }
                }
                Err(_) => {
                    if let Some(run) = test_run.as_mut() {
                        run.reporting_error.get_or_insert_with(|| {
                            internal("test cancellation scope still owned after worker join")
                        });
                    }
                }
            }
        }
        build_runner.compilation.test_execution = test_run;
        #[cfg(any(target_os = "linux", target_os = "macos"))]
        if let Some(signals) = verification_signals {
            let finish = Arc::try_unwrap(signals)
                .map_err(|_| internal("verification cancellation owner retained after actual join"))
                .and_then(|scope| scope.finish().map_err(Into::into));
            if let Err(error) = finish {
                if let Some(run) = build_runner.compilation.qualification.as_mut() {
                    run.reporting_failure
                        .get_or_insert_with(|| format!("{error:#}"));
                }
                if result.is_ok() {
                    result = Err(error);
                }
            }
        }
        // Trust: scope return has joined the actual workers. Metadata-ready
        // events, unwinding or dropping an unfinished queue cannot synthesize
        // terminal completion records. Registered but unscheduled units include
        // graph filtering as well as dependencies never reached after failure.
        if !retained && let Some(logger) = input_work_logger {
            let not_executed = execution_registered
                .checked_sub(execution.scheduled)
                .ok_or_else(|| internal("more execution jobs scheduled than registered units"))?;
            logger.log(LogMessage::ExecutionGraphFinished {
                elapsed: execution
                    .compiler_finished
                    .unwrap_or_else(|| execution_clock.elapsed())
                    .as_secs_f64(),
                outcome: execution.outcome(),
                scheduled: execution.scheduled,
                completed: execution.completed,
                not_executed,
            });
        }
        // Trust: workers enqueue input work before their FIFO Finish message.
        // A successful drain processes those messages, and scope return joins
        // every worker. Only this coordinator endpoint can close accounting;
        // a failed/cancelled queue must not claim its forwarded rows complete.
        if !retained
            && result.is_ok()
            && let Some(logger) = input_work_logger
        {
            logger.log(crate::util::log_message::LogMessage::InputWorkFinalized {
                captures: input_work_ids.load(std::sync::atomic::Ordering::Relaxed),
            });
        }
        result
    }
}

impl<'gctx> DrainState<'gctx> {
    fn original_bootstrap(&self) -> bool {
        #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
        {
            self.bootstrap_full.is_some()
        }
        #[cfg(not(all(target_os = "macos", target_arch = "aarch64")))]
        {
            false
        }
    }
    fn retire_ready_tokens(&mut self) -> io::Result<()> {
        if self.original_bootstrap() {
            self.retained_tokens.retire_joined()
        } else {
            self.retained_tokens.retire();
            Ok(())
        }
    }
    fn compiler_actions_active(&self) -> usize {
        #[cfg(any(target_os = "linux", target_os = "macos"))]
        {
            self.active.len() + self.verification_active()
        }
        #[cfg(not(any(target_os = "linux", target_os = "macos")))]
        {
            self.active.len()
        }
    }
    fn observe_root_cancellation(&mut self, gctx: &GlobalContext) -> bool {
        self.poll_retained_cancellation();
        if gctx.poll_root_cancellation() {
            self.root_cancelled = true;
        }
        // Trust: a test plan's bound that ran out, or a signal, stops the
        // run as a root stop does, and the plan's outcome says which.
        self.observe_plan_stop(gctx);
        if self
            .tests
            .as_ref()
            .is_some_and(|tests| tests.signals.interrupted() && tests.reporter.error.is_none())
        {
            self.root_cancelled = true;
        }
        if self.root_cancelled {
            #[cfg(any(target_os = "linux", target_os = "macos"))]
            if let Some(state) = self.verification.as_mut() {
                state.stopped = true;
                state.signals.cancel();
            }
            if let Some(tests) = &self.tests {
                // Trust: stop admission and cancel owned test children before
                // acknowledging the root controller's stop request.
                tests.signals.cancel();
            }
            // Trust: this sticky scheduler gate is effective before A is sent.
            // WouldBlock leaves the one-byte acknowledgement for a later poll.
            gctx.acknowledge_root_stopped();
        }
        self.root_cancelled
    }

    /// Trust: reads the invocation's plan clock and its signal
    /// (`ops::cargo_test::plan_clock`). The first of them to stop the run
    /// is recorded with what was running, for the exit status and the
    /// closing record (`plan_outcome::stop`), and everything the run
    /// started is killed: the clock's custody ends every compiler-side
    /// child, the test scope every test executable.
    fn observe_plan_stop(&mut self, gctx: &GlobalContext) {
        use crate::ops::cargo_test::{plan_clock, plan_outcome};
        let Some(clock) = plan_clock::armed() else {
            return;
        };
        if plan_outcome::stopped().is_some() {
            // The invocation is stopped: a queue that starts after the stop
            // (a later phase, the plan's own after a phase) admits nothing.
            self.root_cancelled = true;
            self.end_plan_children(clock);
            return;
        }
        let now = Instant::now();
        let running = self
            .tests
            .as_ref()
            .map(|tests| tests.running())
            .unwrap_or_default();
        // The invocation's handlers are the clock's; a queue without tests
        // (a `[[tool]]` build) reads the same signal.
        let signal = clock
            .custody()
            .and_then(|custody| custody.signalled())
            .or_else(|| {
                self.tests
                    .as_ref()
                    .and_then(|tests| tests.signals.signalled())
            });
        // A run held at a barrier: read it, with whether the run has
        // anything left to do but wait there.
        let barrier = clock.barrier().and_then(|barrier| {
            let idle = self.tests.is_some() && self.active_count() == 0 && !self.pending_compile();
            let held = !barrier.released();
            let stop = barrier.poll(now, idle);
            if held && barrier.released() {
                let _ = gctx.shell().status(
                    "Released",
                    format!(
                        "the run's test executables: the barrier says `run` (waited {} s for \
                         it with nothing else to do)",
                        barrier.waited().as_secs()
                    ),
                );
            }
            stop
        });
        let (outcome, why) = if let Some(signal) = signal {
            // Each worker stops its own child at the signal and may have
            // reported back by now, so what ran is what the last look saw. A
            // signal that came before this queue's first look (while the plan
            // was selected, or a phase before it ended) has no last look:
            // what runs is what this look sees.
            let seen = if self.plan_running.is_empty() {
                clock.describe(now, &running)
            } else {
                self.plan_running.clone()
            };
            (
                plan_outcome::Outcome::Interrupted,
                format!("signal {signal} stopped the run; {seen}"),
            )
        } else if let Some(stop) = barrier {
            stop
        } else if let Some(why) = clock.expired(now, &running) {
            (plan_outcome::Outcome::OutOfTime, why)
        } else {
            let seen = clock.describe(now, &running);
            drop(running);
            self.plan_running = seen;
            return;
        };
        drop(running);
        if plan_outcome::stop(outcome, why.clone()) {
            let _ = gctx.shell().error(format!(
                "Targo stopped this test plan run: {why}; every compiler, build script and \
                 test executable still running is killed, with its descendants"
            ));
        }
        self.root_cancelled = true;
        self.end_plan_children(clock);
    }

    /// Trust: ends every compiler-side child of a stopped plan run.
    fn end_plan_children(&self, clock: &crate::ops::cargo_test::plan_clock::Clock) {
        if let Some(custody) = clock.custody() {
            custody.cancel();
        }
    }

    fn spawn_work_if_possible<'s>(
        &mut self,
        build_runner: &mut BuildRunner<'_, '_>,
        jobserver_helper: &HelperThread,
        scope: &'s Scope<'s, '_>,
        compiler_workers: &mut Vec<thread::ScopedJoinHandle<'s, ()>>,
    ) -> CargoResult<()> {
        let retained = self
            .tests
            .as_ref()
            .is_some_and(|tests| tests.options.retained);
        // Discover ready actions without prefetching global native credits.
        // Legacy scheduling retains its existing asynchronous token helper.
        while !self.observe_root_cancellation(build_runner.bcx.gctx)
            && let Some((node, work, priority)) = self.queue.dequeue()
        {
            if self.compiler_finalized && matches!(&node, QueueNode::Compile(_)) {
                continue;
            }
            if let QueueWork::Test(action) = &work
                && !self.test_action_ready(build_runner, action)
            {
                continue;
            }
            let rank = |work: &QueueWork, priority| test_admission::Rank {
                priority,
                test: match work {
                    QueueWork::Compile(_) => None,
                    #[cfg(any(target_os = "linux", target_os = "macos"))]
                    QueueWork::Verification(_) => None,
                    QueueWork::Test(action) => Some(action.index),
                },
            };
            let new = rank(&work, priority);
            let index = self.pending_queue.partition_point(|(_, queued, p)| {
                test_admission::stays_ahead(rank(queued, *p), new)
            });
            self.pending_queue.insert(index, (node, work, priority));
        }

        // Retired or stopped actions remain in the observed population but
        // cannot occupy admission or keep a native retry loop alive forever.
        self.retire_unschedulable();
        if !build_runner.native_resources() && !retained && !self.original_bootstrap() {
            self.request_wanted_tokens(jobserver_helper);
        }
        while !self.pending_queue.is_empty() {
            if self.observe_root_cancellation(build_runner.bcx.gctx) {
                break;
            }
            // A reporting or fail-fast transition can happen during this
            // dispatch pass. Retire queued test actions before attempting
            // either local or global admission for a process we will not run.
            self.retire_unschedulable();
            // A legacy jobserver's credits are the tokens in hand plus the
            // implicit one; native dispatch acquires its own below.
            let free =
                (!build_runner.native_resources() && !retained && !self.original_bootstrap())
                    .then(|| (self.tokens.len() + 1).saturating_sub(self.occupancy().held()));
            let Choice::Dispatch(index) =
                test_admission::choose(&self.occupancy(), &self.demands(), free)
            else {
                break;
            };
            #[cfg(any(target_os = "linux", target_os = "macos"))]
            if self.workload_script.is_none()
                && self.workload_inputs().is_some()
                && let (QueueNode::Compile(unit), QueueWork::Compile(job), _) =
                    &self.pending_queue[index]
                && unit.mode.is_run_custom_build()
                && !job.freshness().is_fresh()
            {
                // Park before ANY more queue work. Finish messages are not
                // retirement: the coordinator joins current actual workers
                // before the original script image/phase can be registered.
                build_runner
                    .resource_runtime
                    .as_ref()
                    .context("native workload script has no original runtime")?
                    .park_workload()?;
                self.workload_script = Some(workload_script::Script::waiting(unit.clone()));
                break;
            }
            // Native roots pair a local capacity credit with the actual host
            // lease at dispatch. A host refusal immediately returns the local
            // token; neither kind of action gets another implicit owner.
            let mut local_token = None;
            #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
            let mut bootstrap_permit = None;
            #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
            if let Some(full) = self.bootstrap_full.as_ref()
                && !matches!(&self.pending_queue[index].1, QueueWork::Compile(job) if job.freshness().is_fresh())
            {
                if let Some(primary) = full.try_implicit()? {
                    // Return/join an earlier supplementary acquisition before
                    // reusing this SAME Root-wide implicit borrower.
                    self.retained_tokens.retire_joined()?;
                    bootstrap_permit = Some(primary);
                } else {
                    let Some(credit) = self
                        .retained_tokens
                        .try_acquire(build_runner.jobserver.client())?
                    else {
                        break;
                    };
                    bootstrap_permit = Some(full.supplementary(credit)?);
                }
            }
            if retained && !build_runner.native_resources() && !self.original_bootstrap() {
                if self.active_count() == 0 {
                    // Reusing the original implicit credit no longer needs an
                    // earlier supplementary request. Return it before dispatch.
                    self.retained_tokens.retire();
                } else {
                    local_token = self
                        .retained_tokens
                        .try_acquire(build_runner.jobserver.client())?;
                    if local_token.is_none() {
                        break;
                    }
                }
            }
            #[cfg(any(target_os = "linux", target_os = "macos"))]
            let mut resources = None;
            #[cfg(any(target_os = "linux", target_os = "macos"))]
            if let Some(runtime) = &build_runner.resource_runtime {
                let external_serial = match &self.pending_queue[index] {
                    (QueueNode::Compile(unit), QueueWork::Compile(job), _)
                        if !job.freshness().is_fresh() =>
                    {
                        Some(unit.mode.is_run_custom_build())
                    }
                    (QueueNode::Test(_), QueueWork::Test(_), _) => Some(true),
                    #[cfg(any(target_os = "linux", target_os = "macos"))]
                    (QueueNode::Verification(_), QueueWork::Verification(_), _) => Some(false),
                    _ => None,
                };
                if let Some(external_serial) = external_serial {
                    if self.active_count() != 0 {
                        local_token = if retained {
                            self.retained_tokens
                                .try_acquire(build_runner.jobserver.client())?
                        } else {
                            build_runner.jobserver.client().try_acquire()?
                        };
                        if local_token.is_none() {
                            break;
                        }
                    } else if retained {
                        self.retained_tokens.retire();
                    }
                    resources = runtime.try_root(external_serial)?;
                    if resources.is_none() {
                        drop(local_token);
                        break;
                    }
                    if self.observe_root_cancellation(build_runner.bcx.gctx) {
                        break;
                    }
                }
            }
            let (node, work, _) = self.pending_queue.remove(index);
            match (node, work) {
                (QueueNode::Compile(unit), QueueWork::Compile(job)) => {
                    #[cfg(any(target_os = "linux", target_os = "macos"))]
                    if let Some(script) = self.workload_script.as_mut() {
                        script.dispatched(&unit)?;
                    }
                    *self.counts.get_mut(&unit.pkg.package_id()).unwrap() -= 1;
                    Self::note_unit_dispatched(build_runner, &unit, job.freshness())?;
                    self.note_working_on(
                        build_runner.bcx.gctx,
                        build_runner.bcx.ws.root(),
                        &unit,
                        job.freshness(),
                    )?;
                    self.run(
                        &unit,
                        job,
                        build_runner,
                        scope,
                        compiler_workers,
                        local_token,
                        #[cfg(any(target_os = "linux", target_os = "macos"))]
                        resources,
                        #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
                        bootstrap_permit,
                    );
                }
                (QueueNode::Test(index), QueueWork::Test(action)) => {
                    assert_eq!(index, action.index);
                    if !self.tests.as_ref().expect("test state").stopped {
                        self.run_test_action(
                            action,
                            build_runner,
                            scope,
                            local_token,
                            #[cfg(any(target_os = "linux", target_os = "macos"))]
                            resources,
                        );
                    }
                }
                #[cfg(any(target_os = "linux", target_os = "macos"))]
                (QueueNode::Verification(index), QueueWork::Verification(action)) => {
                    anyhow::ensure!(index == action.index, "verification node/work mismatch");
                    self.run_verification(
                        action,
                        build_runner,
                        scope,
                        compiler_workers,
                        local_token,
                        resources,
                    )?;
                }
                _ => unreachable!("queue node and work kind differ"),
            }
        }
        Ok(())
    }

    /// Trust: what admission sees of the running work.
    fn occupancy(&self) -> Occupancy {
        let tests = self.tests.as_ref();
        Occupancy {
            compiling: self.compiler_actions_active(),
            testing: tests.map_or(0, |tests| tests.active.len()),
            test_credits: tests.map_or(0, TestState::credits),
            exclusive: tests.is_some_and(TestState::exclusive_running),
            test_limit: tests.map_or(0, |tests| tests.options.limit),
            compiler_finalized: self.compiler_finalized,
            pool: self.pool,
            test_memory: tests.map_or(0, TestState::memory),
            memory_limit: tests.and_then(|tests| tests.options.memory_limit),
        }
    }

    /// Trust: what each pending entry asks of admission, in queue order.
    fn demands(&self) -> Vec<Demand> {
        self.pending_queue
            .iter()
            .map(|(node, work, _)| {
                #[cfg(any(target_os = "linux", target_os = "macos"))]
                if self
                    .workload_script
                    .as_ref()
                    .is_some_and(|script| !script.permits(node))
                {
                    return Demand::Parked;
                }
                match work {
                    QueueWork::Compile(_) => Demand::Compile,
                    #[cfg(any(target_os = "linux", target_os = "macos"))]
                    QueueWork::Verification(_) if !self.compiler_finalized => Demand::Parked,
                    #[cfg(any(target_os = "linux", target_os = "macos"))]
                    QueueWork::Verification(_) => Demand::Verification,
                    QueueWork::Test(_)
                        if self
                            .tests
                            .as_ref()
                            .is_some_and(|tests| !tests.can_dispatch()) =>
                    {
                        Demand::Parked
                    }
                    QueueWork::Test(_)
                        if !self.compiler_finalized
                            && self
                                .tests
                                .as_ref()
                                .is_some_and(|tests| tests.options.workload.is_some()) =>
                    {
                        Demand::Parked
                    }
                    QueueWork::Test(action) => Demand::Test {
                        weight: action.weight,
                        exclusive: action.exclusive,
                        memory: action.memory,
                    },
                }
            })
            .collect()
    }

    fn retire_unschedulable(&mut self) {
        let tests_stopped = self.tests.as_ref().is_some_and(|tests| tests.stopped);
        let compiler_finalized = self.compiler_finalized;
        self.pending_queue.retain(|(node, _, _)| match node {
            QueueNode::Compile(_) => !compiler_finalized,
            #[cfg(any(target_os = "linux", target_os = "macos"))]
            QueueNode::Verification(_) => self
                .verification
                .as_ref()
                .is_some_and(|state| !state.stopped),
            QueueNode::Test(_) => !tests_stopped,
        });
    }

    /// Trust: the credits running and admissible work could use if every
    /// one were granted. Tokens beyond them are released on an idle wait.
    fn wanted_credits(&self) -> usize {
        test_admission::wanted(&self.occupancy(), &self.demands())
    }

    /// Trust: ask the jobserver helper for the tokens admissible work is
    /// still missing, beyond the implicit one. A weighted test needs all of
    /// its credits at once, so requests must cover its whole weight, and a
    /// token an idle wait released is asked for again.
    fn request_wanted_tokens(&mut self, jobserver_helper: &HelperThread) {
        if self.token_source_failed {
            return;
        }
        let needed = self.wanted_credits().saturating_sub(1);
        while self.tokens.len() + self.token_requests < needed {
            jobserver_helper.request_token();
            self.token_requests += 1;
        }
    }

    fn handle_event(
        &mut self,
        build_runner: &mut BuildRunner<'_, '_>,
        event: Message,
    ) -> Result<(), ErrorToHandle> {
        let warning_handling = build_runner.bcx.gctx.warning_handling()?;
        match event {
            #[cfg(any(target_os = "linux", target_os = "macos"))]
            Message::VerificationFinished(completion) => self.finish_verification(completion)?,
            Message::OriginalCommand(observed) => observed.notify()?,
            Message::WorkloadMaterialized(id, observed) => {
                let unit = self
                    .active
                    .get(&id)
                    .context("materialization after original unit removal")?;
                if build_runner
                    .workload_materializations
                    .insert(unit.clone(), observed)
                    .is_some()
                {
                    return Err(anyhow::anyhow!(
                        "original workload unit materialization observed twice"
                    )
                    .into());
                }
            }
            Message::InputWork(message) => {
                if let Some(logger) = build_runner.bcx.logger {
                    logger.log(message);
                }
            }
            Message::RecheckFreshness { id, force, reply } => {
                let unit = self.active[&id].clone();
                let result = super::fingerprint::recheck_after_lock(build_runner, &unit, force);
                // Trust: DC-12a. The recheck under the lock found the unit
                // fresh: this build used it and did not build it. (A build that
                // waited for another's lease plans again before dispatch, so
                // such a unit is usually dispatched fresh and never rechecked;
                // tests/build_receipt.rs holds the receipt to that outcome.)
                if matches!(result, Ok(true)) {
                    self.ran.found_fresh(unit);
                }
                // A failed check goes back to the worker and follows the same
                // Finish/error path as a failed compiler invocation.
                reply
                    .send(result)
                    .map_err(|_| internal("build worker closed the freshness reply"))?;
            }
            Message::Run(id, cmd) => {
                build_runner
                    .bcx
                    .gctx
                    .shell()
                    .verbose(|c| c.status("Running", &cmd))?;
                self.timings
                    .unit_start(build_runner, id, self.active[&id].clone());
            }
            Message::Stdout(out) => {
                writeln!(build_runner.bcx.gctx.shell().out(), "{}", out)?;
            }
            Message::Stderr(err) => {
                let mut shell = build_runner.bcx.gctx.shell();
                shell.print_ansi_stderr(err.as_bytes())?;
                shell.err().write_all(b"\n")?;
            }
            Message::Diagnostic {
                id,
                level,
                diag,
                lint,
                fixable,
            } => {
                let emitted = self.diag_dedupe.emit_diag(&diag)?;
                if level == "warning" {
                    self.bump_warning_count(id, lint, emitted, fixable);
                }
                if level == "error" {
                    let count = self.warning_count.entry(id).or_default();
                    // If there is an error, the `cargo fix` message should not show
                    count.disallow_fixable();
                    // If there is an error, the default summary should be shown
                    count.supplanted_by_errors = true;
                }
            }
            Message::Warning { id, warning } => {
                build_runner.bcx.gctx.shell().warn(warning)?;
                let lint = false;
                let emitted = true;
                let fixable = false;
                self.bump_warning_count(id, lint, emitted, fixable);
            }
            Message::WarningCount {
                id,
                lint,
                emitted,
                fixable,
            } => {
                self.bump_warning_count(id, lint, emitted, fixable);
            }
            Message::FixDiagnostic(msg) => {
                self.print.print(&msg)?;
            }
            Message::Finish(id, artifact, mut result) => {
                let mut denied_warnings_for_unit = false;
                let unit = match artifact {
                    // If `id` has completely finished we remove it
                    // from the `active` map ...
                    Artifact::All => {
                        trace!("end: {:?}", id);
                        self.finished += 1;
                        let unit = self.active.remove(&id).unwrap();
                        // An error could add an entry for a `Unit`
                        // with 0 warnings but having fixable
                        // warnings be disallowed
                        let count = self
                            .warning_count
                            .get(&id)
                            .filter(|count| 0 < count.total)
                            .cloned();
                        if let Some(count) = count {
                            let denied_warnings =
                                warning_handling == WarningHandling::Deny && 0 < count.lints;
                            denied_warnings_for_unit = denied_warnings;
                            self.report_warning_count(
                                build_runner,
                                &unit,
                                &count,
                                &build_runner.bcx.rustc().workspace_wrapper,
                                denied_warnings,
                            );
                            let stop_on_warnings = denied_warnings
                                && !build_runner.bcx.build_config.keep_going
                                && !count.supplanted_by_errors;
                            if stop_on_warnings {
                                result = Err(anyhow::format_err!(
                                    "warnings are denied by `build.warnings` configuration"
                                ))
                            }
                        }
                        unit
                    }
                    // ... otherwise if it hasn't finished we leave it
                    // in there as we'll get another `Finish` later on.
                    Artifact::Metadata => {
                        trace!("end (meta): {:?}", id);
                        self.active[&id].clone()
                    }
                };
                debug!("end ({:?}): {:?}", unit, result);
                let tolerated = build_runner.bcx.unit_can_fail_for_docscraping(&unit);
                let outcome = execution_unit_outcome(
                    result.as_ref().map(|_| ()),
                    tolerated,
                    denied_warnings_for_unit,
                );
                // Trust: even fallible completion bookkeeping must leave the
                // actual terminal job observed. Preserve its failure and keep
                // draining peers; a metadata-ready event is never terminal.
                let handled = (|| -> Result<(), ErrorToHandle> {
                    match result {
                        Ok(()) => self.finish(id, &unit, artifact, build_runner)?,
                        Err(_) if tolerated => {
                            build_runner
                                .failed_scrape_units
                                .lock()
                                .unwrap()
                                .insert(build_runner.files().metadata(&unit).unit_id());
                            self.queue
                                .finish(&QueueNode::Compile(unit.clone()), &artifact);
                        }
                        Err(error) => {
                            let show_warnings = true;
                            self.emit_log_messages(&unit, build_runner, show_warnings)?;
                            self.back_compat_notice(build_runner, &unit)?;
                            return Err(ErrorToHandle {
                                error,
                                print_always: true,
                            });
                        }
                    }
                    Ok(())
                })();
                if artifact == Artifact::All {
                    let outcome = match &handled {
                        Err(error) => execution_unit_outcome(
                            Err(&error.error),
                            false,
                            denied_warnings_for_unit,
                        ),
                        Ok(()) => outcome,
                    };
                    self.execution.failed |= matches!(
                        outcome,
                        ExecutionUnitOutcome::Failed | ExecutionUnitOutcome::Cancelled
                    );
                    if matches!(
                        outcome,
                        ExecutionUnitOutcome::Failed | ExecutionUnitOutcome::Cancelled
                    ) {
                        self.test_prerequisite_failed(&unit);
                    }
                    self.execution.completed += 1;
                    if let Some(logger) = build_runner.bcx.logger {
                        logger.log(LogMessage::UnitOutcome {
                            index: build_runner.bcx.unit_to_index[&unit],
                            elapsed: build_runner
                                .bcx
                                .gctx
                                .invocation_instant()
                                .elapsed()
                                .as_secs_f64(),
                            outcome,
                        });
                    }
                }
                handled?;
            }
            Message::TestFinished {
                index,
                result,
                elapsed,
                workload,
            } => {
                self.finish_test_action_by_index(build_runner, index, result, elapsed, workload);
            }
            Message::FutureIncompatReport(id, items) => {
                let unit = &self.active[&id];
                let package_id = unit.pkg.package_id();
                let is_local = unit.is_local();
                self.per_package_future_incompat_reports
                    .push(FutureIncompatReportPackage {
                        package_id,
                        is_local,
                        items,
                    });
            }
            Message::UnusedExterns(id, unused_externs) => {
                let unit = &self.active[&id];
                build_runner
                    .unused_dep_state
                    .record_unused_externs_for_unit(unit, unused_externs);
            }
            Message::Token(acquired_token) => {
                self.token_requests = self.token_requests.saturating_sub(1);
                // Trust: a failed acquisition is not retried; requesting again
                // under keep-going would repeat the failure without end.
                self.token_source_failed |= acquired_token.is_err();
                let token = acquired_token.context("failed to acquire jobserver token")?;
                self.tokens.push(token);
                self.starved_since = None;
            }
            Message::SectionTiming(id, section) => {
                self.timings.unit_section_timing(build_runner, id, &section);
            }
            Message::PeakMemory(id, bytes) => {
                self.timings.unit_peak_memory(build_runner, id, bytes);
            }
            Message::CpuTimes(id, times) => {
                self.timings.unit_cpu_times(build_runner, id, times);
            }
        }

        Ok(())
    }

    // This will also tick the progress bar as appropriate
    fn wait_for_events(&mut self, gctx: &GlobalContext, retry_admission: bool) -> Vec<Message> {
        // Drain all events at once to avoid displaying the progress bar
        // unnecessarily. If there's no events we actually block waiting for
        // an event, but we keep a "heartbeat" going to allow `record_cpu`
        // to run above to calculate CPU usage over time. To do this we
        // listen for a message with a timeout, and on timeout we run the
        // previous parts of the loop again.
        let mut events = self.messages.try_pop_all();
        if events.is_empty() {
            loop {
                let was_cancelled = self.root_cancelled;
                if self.observe_root_cancellation(gctx) && !was_cancelled {
                    // Trust: wake the outer loop once for the stop transition.
                    // Already-stopped quiet jobs keep the ordinary paced wait.
                    break;
                }
                self.tick_progress();
                // Trust: release tokens nothing can use, but keep those a
                // weighted test is accumulating; it takes all at once.
                let wanted = self.wanted_credits();
                self.tokens.truncate(wanted.saturating_sub(1));
                match self.messages.pop(Duration::from_millis(500)) {
                    Some(message) => {
                        events.push(message);
                        break;
                    }
                    None if retry_admission => break,
                    None => continue,
                }
            }
        }
        events
    }

    /// This is the "main" loop, where Cargo does all work to run the
    /// compiler.
    ///
    /// This returns a tuple of `Result` to prevent the use of `?` on
    /// `Result` types because it is important for the loop to
    /// carefully handle errors.
    fn drain_the_queue<'s>(
        mut self,
        build_runner: &mut BuildRunner<'_, '_>,
        scope: &'s Scope<'s, '_>,
        jobserver_helper: &HelperThread,
        warning_handling: WarningHandling,
    ) -> (
        Result<(), anyhow::Error>,
        ExecutionSummary,
        Option<crate::ops::cargo_test::graph::TestGraphRun>,
    ) {
        trace!("queue: {:#?}", self.queue);
        // Trust: while this queue drains it reads a test plan's clock itself
        // (`observe_plan_stop`); the clock's watcher ends a stopped run only
        // when no queue drains.
        let _draining = crate::ops::cargo_test::plan_clock::armed().map(|clock| clock.draining());

        // Iteratively execute the entire dependency graph. Each turn of the
        // loop starts out by scheduling as much work as possible (up to the
        // maximum number of parallel jobs we have tokens for). A local queue
        // is maintained separately from the main dependency queue as one
        // dequeue may actually dequeue quite a bit of work (e.g., 10 binaries
        // in one package).
        //
        // After a job has finished we update our internal state if it was
        // successful and otherwise wait for pending work to finish if it failed
        // and then immediately return (or keep going, if requested by the build
        // config).
        let mut errors = ErrorsDuringDrain { count: 0 };
        // Trust: FinishOnDrop publishes All before JobState releases its
        // remaining lock-manager references. Keep actual handles so compiler
        // lease retirement observes worker return, not merely that message.
        let mut compiler_workers = Vec::new();
        // CAUTION! Do not use `?` or break out of the loop early. Every error
        // must be handled in such a way that the loop is still allowed to
        // drain event messages.
        loop {
            self.observe_root_cancellation(build_runner.bcx.gctx);
            // Trust: fatal original-credit errors stop admission and drain
            // actual workers instead of waiting forever on the empty proxy.
            #[cfg(any(target_os = "linux", target_os = "macos"))]
            if !self.root_cancelled
                && let Err(error) = build_runner.check_fixed_gnu()
            {
                self.root_cancelled = true;
                self.handle_error(&mut build_runner.bcx.gctx.shell(), &mut errors, error);
            }
            if !self.root_cancelled
                && (errors.count == 0 || build_runner.bcx.build_config.keep_going)
            {
                if let Err(e) = self.spawn_work_if_possible(
                    build_runner,
                    jobserver_helper,
                    scope,
                    &mut compiler_workers,
                ) {
                    self.handle_error(&mut build_runner.bcx.gctx.shell(), &mut errors, e);
                }
            }

            // A stopped frontier cannot consume an outstanding ready-only
            // request. Return any raced credit before active peers drain, so
            // their nested same-pool work retains forward progress.
            if self.root_cancelled
                || (errors.count != 0 && !build_runner.bcx.build_config.keep_going)
            {
                if let Err(error) = self.retire_ready_tokens() {
                    self.root_cancelled = true;
                    self.handle_error(&mut build_runner.bcx.gctx.shell(), &mut errors, error);
                }
            } else {
                let stopped = self.tests.as_ref().is_some_and(|tests| tests.stopped);
                let pending_compiler = self.pending_compile();
                if self.original_bootstrap() {
                    if stopped
                        && !pending_compiler
                        && let Err(error) = self.retire_ready_tokens()
                    {
                        self.root_cancelled = true;
                        self.handle_error(&mut build_runner.bcx.gctx.shell(), &mut errors, error);
                    }
                } else {
                    self.retained_tokens
                        .retire_stopped_tests(stopped, pending_compiler);
                }
            }

            #[cfg(any(target_os = "linux", target_os = "macos"))]
            if self.workload_script.is_some() && self.active.is_empty() {
                let admitting = !self.root_cancelled
                    && (errors.count == 0 || build_runner.bcx.build_config.keep_going);
                match self.advance_workload_script(build_runner, &mut compiler_workers, admitting) {
                    Ok(true) => continue,
                    Ok(false) => {}
                    Err(error) => {
                        self.root_cancelled = true;
                        self.retained_tokens.retire();
                        self.handle_error(&mut build_runner.bcx.gctx.shell(), &mut errors, error);
                    }
                }
            }

            // Tests never produce prerequisites for compilation. Once no
            // compiler is active and no ready compiler remains (or admission
            // has stopped after failure/cancellation), no future compiler can
            // make progress. Finalize and retire its leases before waiting on
            // a test that may itself start a same-target nested build.
            let compile_admission_stopped = self.root_cancelled
                || (errors.count != 0 && !build_runner.bcx.build_config.keep_going);
            if !self.compiler_finalized
                && self.active.is_empty()
                && (compile_admission_stopped || !self.pending_compile())
            {
                // Settle the original pipe's actual waiter before the proof
                // hold. No acquired/outstanding supplementary credit survives.
                if let Err(error) = self.retire_ready_tokens() {
                    self.root_cancelled = true;
                    self.handle_error(&mut build_runner.bcx.gctx.shell(), &mut errors, error);
                }
                self.finalize_compiler(
                    build_runner,
                    warning_handling,
                    &mut errors,
                    &mut compiler_workers,
                );
                let compile_succeeded =
                    errors.count == 0 && !self.execution.failed && !self.root_cancelled;
                if self
                    .tests
                    .as_ref()
                    .is_some_and(|tests| tests.options.retained)
                {
                    debug_assert!(
                        self.tokens.is_empty(),
                        "retained admission never prefetches jobserver credits"
                    );
                }
                match self.qualify_retained_tests(build_runner, compile_succeeded) {
                    Ok(true) => continue,
                    Ok(false) => {}
                    Err(error) => {
                        self.handle_error(&mut build_runner.bcx.gctx.shell(), &mut errors, error)
                    }
                }
                if errors.count == 0
                    && !self.root_cancelled
                    && self
                        .tests
                        .as_ref()
                        .is_some_and(|tests| tests.options.workload.is_some())
                {
                    // Workload nodes are parked until all actual compiler
                    // workers joined and output bookkeeping finished.
                    continue;
                }
            }

            // If after all that we're not actually running anything then we're
            // done!
            let admitting = !self.root_cancelled
                && (errors.count == 0 || build_runner.bcx.build_config.keep_going);
            // Trust: tests held at a test plan's barrier are released by a
            // file, which no queue event announces: keep the paced look.
            let held_at_barrier = self.tests.is_some()
                && crate::ops::cargo_test::plan_clock::armed()
                    .is_some_and(|clock| !clock.tests_may_start());
            let retry_admission = (build_runner.native_resources()
                || self.original_bootstrap()
                || held_at_barrier
                || self
                    .tests
                    .as_ref()
                    .is_some_and(|tests| tests.options.retained))
                && !self.pending_queue.is_empty()
                && admitting;
            // Trust: with nothing running, admissible work that still wants
            // credits is a weighted test whose requested tokens are on the
            // way; the wait below receives them.
            let awaiting_tokens = !build_runner.native_resources()
                && !self.original_bootstrap()
                && !self
                    .tests
                    .as_ref()
                    .is_some_and(|tests| tests.options.retained)
                && admitting
                && !self.token_source_failed
                && self.wanted_credits() > self.occupancy().held();
            if self.active_count() == 0 && !retry_admission && !awaiting_tokens {
                break;
            }
            // Trust: with nothing running, every token of a pool Targo made
            // is free within moments. Credits that stop arriving were lost (a
            // client exited or was killed while holding them, as rustc's
            // parallel frontend sometimes does); waiting longer would hang.
            let starving = self.active_count() == 0 && awaiting_tokens;
            if starving {
                let since = *self.starved_since.get_or_insert_with(Instant::now);
                if since.elapsed() >= TOKEN_STALL {
                    self.token_source_failed = true;
                    // With nothing running, the next test in dispatch order
                    // is the one short of credits; Targo holds its tokens and
                    // the implicit one.
                    let in_hand = self.tokens.len() + 1;
                    let head =
                        self.pending_queue
                            .iter()
                            .rev()
                            .find_map(|(_, work, _)| match work {
                                QueueWork::Test(action) => Some(action),
                                QueueWork::Compile(_) => None,
                                #[cfg(any(target_os = "linux", target_os = "macos"))]
                                QueueWork::Verification(_) => None,
                            });
                    let needs = match head {
                        Some(action) => format!(
                            "test target `{}` of `{}` needs {} jobserver credits",
                            action.unit.target.name(),
                            action.unit.pkg.name(),
                            action.weight
                        ),
                        None => "a pending test needs more jobserver credits".to_owned(),
                    };
                    self.handle_error(
                        &mut build_runner.bcx.gctx.shell(),
                        &mut errors,
                        anyhow::anyhow!(
                            "{needs}, but with nothing running for {}s Targo holds only \
                             {in_hand}: the pool's other tokens were lost, as when a client exits \
                             or is killed while holding them; the tests still pending did not run",
                            TOKEN_STALL.as_secs()
                        ),
                    );
                    continue;
                }
            } else {
                self.starved_since = None;
            }

            // And finally, before we block waiting for the next event, drop any
            // excess tokens we may have accidentally acquired. Due to how our
            // jobserver interface is architected we may acquire a token that we
            // don't actually use, and if this happens just relinquish it back
            // to the jobserver itself.
            // Trust: retain the ordinary paced wait while polling an original
            // GNU funding failure even when no local token event can arrive.
            #[cfg(any(target_os = "linux", target_os = "macos"))]
            let fixed_gnu = build_runner.has_fixed_gnu();
            #[cfg(not(any(target_os = "linux", target_os = "macos")))]
            let fixed_gnu = false;
            for event in self.wait_for_events(
                build_runner.bcx.gctx,
                retry_admission || starving || fixed_gnu,
            ) {
                if let Err(event_err) = self.handle_event(build_runner, event) {
                    self.handle_error(&mut build_runner.bcx.gctx.shell(), &mut errors, event_err);
                }
            }
        }
        #[cfg(any(target_os = "linux", target_os = "macos"))]
        self.finish_verification_graph(build_runner);
        let tests = self.finish_test_graph(build_runner);

        // Trust: cancellation is a non-success after actual scoped work drains,
        // even when every completed unit was successful or --keep-going was set.
        self.observe_root_cancellation(build_runner.bcx.gctx);
        // Trust: a test plan's own stop (a bound that ran out, a signal)
        // after the build ended is the test run's interruption, not a failed
        // build. The run is handed back, so that every failure it saw and
        // every harness Targo stopped is reported by its target with its
        // reason (`graph::consume`), and the invocation then ends as the
        // stop says. A stop while compiler work remained has no such run.
        let plan_stop = crate::ops::cargo_test::plan_outcome::stopped().is_some()
            && tests.as_ref().is_some_and(|run| run.interruption.is_some())
            && !self.compile_work_remaining();
        if self.root_cancelled && errors.count == 0 && !plan_stop {
            self.handle_error(
                &mut build_runner.bcx.gctx.shell(),
                &mut errors,
                anyhow::anyhow!(
                    "build cancelled after active work drained: {}",
                    build_runner.bcx.gctx.root_cancellation_reason()
                ),
            );
        }

        if let Some(error) = errors.to_error() {
            // Any errors up to this point have already been printed via the
            // `display_error` inside `handle_error`.
            (
                Err(anyhow::Error::new(AlreadyPrintedError::new(error))),
                self.execution,
                tests,
            )
        } else {
            debug_assert!(self.compiler_finalized);
            debug_assert!(!self.compile_work_remaining());
            (Ok(()), self.execution, tests)
        }
    }

    fn pending_compile(&self) -> bool {
        self.pending_queue.iter().any(|(node, _, _)| {
            if matches!(node, QueueNode::Compile(_)) {
                return true;
            }
            false
        })
    }

    fn compile_work_remaining(&self) -> bool {
        !self.active.is_empty()
            || self.pending_compile()
            || self.counts.values().any(|count| *count != 0)
    }

    /// Trust: all compiler writers are joined and finalized once. Tests retain
    /// the same jobserver and owned processes while compilation leases retire.
    fn finalize_compiler<'s>(
        &mut self,
        build_runner: &mut BuildRunner<'_, '_>,
        warning_handling: WarningHandling,
        errors: &mut ErrorsDuringDrain,
        compiler_workers: &mut Vec<thread::ScopedJoinHandle<'s, ()>>,
    ) {
        assert!(!self.compiler_finalized);
        assert!(self.active.is_empty());
        #[cfg(any(target_os = "linux", target_os = "macos"))]
        if self
            .tests
            .as_ref()
            .is_some_and(|tests| tests.options.workload.is_some())
            && let Some(runtime) = &build_runner.resource_runtime
            && let Err(error) = runtime.park_workload()
        {
            self.handle_error(&mut build_runner.bcx.gctx.shell(), errors, error);
        }
        self.compiler_finalized = true;
        for _ in 0..workload_script::join_current_workers(compiler_workers) {
            self.handle_error(
                &mut build_runner.bcx.gctx.shell(),
                errors,
                internal("compiler worker panicked before releasing its ownership"),
            );
        }
        self.progress.clear();

        let mut global_stats = GlobalDiagnosticStats::new();
        drop(unused_dependencies::lint_build_results(
            build_runner,
            &mut global_stats,
        ));
        errors.count += global_stats.error_count();
        build_runner.compilation.lint_warning_count += global_stats.lint_warning_count();
        if errors.count == 0
            && let Err(error) = compilation_warning_policy(
                warning_handling,
                build_runner.compilation.lint_warning_count,
            )
        {
            // Preserve the canonical cause before failed retirement. Otherwise
            // --keep-going can leave only the observation of denied warnings,
            // return Ok from this drain, and mask it with an Aborted-state
            // error from BuildRunner's successful-finalization fallback.
            self.handle_error(&mut build_runner.bcx.gctx.shell(), errors, error);
        }

        let profile_name = build_runner.bcx.build_config.requested_profile;
        // NOTE: this may be a bit inaccurate, since this may not display the
        // profile for what was actually built. Profile overrides can change
        // these settings, and in some cases different targets are built with
        // different profiles. To be accurate, it would need to collect a
        // list of Units built, and maybe display a list of the different
        // profiles used. However, to keep it simple and compatible with old
        // behavior, we just display what the base profile is.
        let profile = build_runner.bcx.profiles.base_profile();
        let mut opt_type = String::from(if profile.opt_level.as_str() == "0" {
            "unoptimized"
        } else {
            "optimized"
        });
        if profile.debuginfo.is_turned_on() {
            opt_type += " + debuginfo";
        }

        let time_elapsed = util::elapsed(build_runner.bcx.gctx.invocation_instant().elapsed());
        if let Err(e) = self
            .timings
            .finished(build_runner, &errors.to_error())
            .context("failed to render timing report")
        {
            self.handle_error(&mut build_runner.bcx.gctx.shell(), errors, e);
        }

        // Trust: establish the queue-drain invariant before publishing the
        // terminal machine record. Upstream asserts it afterwards, so a
        // scheduler bug could emit `build-finished { success: true }` and only
        // then return an internal error for work that was never run.
        if errors.count == 0 && !self.root_cancelled && self.compile_work_remaining() {
            debug!("queue: {:#?}", self.queue);
            self.handle_error(
                &mut build_runner.bcx.gctx.shell(),
                errors,
                internal("finished with compilation jobs still left in the queue"),
            );
        }
        // Trust: a request that arrived during final bookkeeping still cannot
        // publish terminal success. This is independent of artifact existence.
        self.observe_root_cancellation(build_runner.bcx.gctx);
        if self.root_cancelled && errors.count == 0 {
            self.handle_error(
                &mut build_runner.bcx.gctx.shell(),
                errors,
                anyhow::anyhow!(
                    "build cancelled after active work drained: {}",
                    build_runner.bcx.gctx.root_cancellation_reason()
                ),
            );
        }
        if errors.count == 0 {
            future_incompat::save_and_display_report(
                build_runner.bcx,
                &self.per_package_future_incompat_reports,
            );
        }
        let compile_succeeded = errors.count == 0
            && !self.root_cancelled
            && !self.execution.failed
            && (warning_handling != WarningHandling::Deny
                || build_runner.compilation.lint_warning_count == 0);
        let workload = self
            .tests
            .as_ref()
            .is_some_and(|tests| tests.options.workload.is_some());
        #[cfg(any(target_os = "linux", target_os = "macos"))]
        let native = build_runner.native_inputs().is_some();
        #[cfg(not(any(target_os = "linux", target_os = "macos")))]
        let native = false;
        // Trust: DC-12a. The runner keeps the build's receipt from what this
        // queue ran as it retires the compile leases.
        build_runner.units_ran = Some(std::mem::take(&mut self.ran));
        let finalized = if workload || native {
            build_runner.finish_compilation_with_workload_leases(compile_succeeded)
        } else {
            build_runner
                .finish_compilation_and_release_leases(compile_succeeded)
                .map(|()| None)
        };
        let mut workload_leases = match finalized {
            Ok(leases) => leases,
            Err(error) => {
                self.handle_error(&mut build_runner.bcx.gctx.shell(), errors, error);
                // A finalizer failure must not retain leases indefinitely while
                // an already-running test waits for a nested build. This fallback
                // retires only owned leases and never publishes unbuilt outputs.
                if let Err(error) = build_runner.finish_compilation_and_release_leases(false) {
                    self.handle_error(&mut build_runner.bcx.gctx.shell(), errors, error);
                }
                None
            }
        };
        #[cfg(any(target_os = "linux", target_os = "macos"))]
        if native {
            build_runner.retain_native_finalized_leases(workload_leases.clone());
        }
        // Finalizer writes and lease retirement may fail. A terminal success
        // belongs after that result, while the stdout record itself needs no
        // artifact lease and cannot race a compiler writer from this queue.
        self.observe_root_cancellation(build_runner.bcx.gctx);
        if self.root_cancelled && errors.count == 0 {
            self.handle_error(
                &mut build_runner.bcx.gctx.shell(),
                errors,
                anyhow::anyhow!(
                    "build cancelled after compiler lease retirement: {}",
                    build_runner.bcx.gctx.root_cancellation_reason()
                ),
            );
        }
        if build_runner.bcx.build_config.emit_json() {
            let mut shell = build_runner.bcx.gctx.shell();
            let msg = machine_message::BuildFinished {
                success: compile_succeeded && !self.root_cancelled && errors.count == 0,
            }
            .to_json_string();
            if let Err(error) = writeln!(shell.out(), "{}", msg) {
                self.handle_error(&mut shell, errors, error);
            }
        }
        if errors.count == 0 && compile_succeeded {
            let profile_link = build_runner.bcx.gctx.shell().err_hyperlink(
                "https://doc.rust-lang.org/cargo/reference/profiles.html#default-profiles",
            );
            let message = format!(
                "{profile_link}`{profile_name}` profile [{opt_type}]{profile_link:#} target(s) in {time_elapsed}",
            );
            let _ = build_runner.bcx.gctx.shell().status("Finished", message);
        }
        self.execution.root_cancelled = self.root_cancelled;
        self.execution.failed |= errors.count != 0
            || (warning_handling == WarningHandling::Deny
                && build_runner.compilation.lint_warning_count != 0);
        if self
            .tests
            .as_ref()
            .is_some_and(|tests| tests.options.retained)
            && let Some(logger) = build_runner.bcx.logger
        {
            let registered = build_runner.bcx.unit_to_index.len() as u64;
            if let Some(not_executed) = registered.checked_sub(self.execution.scheduled) {
                logger.log(LogMessage::ExecutionGraphFinished {
                    elapsed: build_runner
                        .bcx
                        .gctx
                        .invocation_instant()
                        .elapsed()
                        .as_secs_f64(),
                    outcome: self.execution.outcome(),
                    scheduled: self.execution.scheduled,
                    completed: self.execution.completed,
                    not_executed,
                });
                if compile_succeeded && errors.count == 0 {
                    logger.log(LogMessage::InputWorkFinalized {
                        captures: build_runner
                            .bcx
                            .input_work_capture_ids
                            .load(std::sync::atomic::Ordering::Relaxed),
                    });
                }
            } else {
                self.handle_error(
                    &mut build_runner.bcx.gctx.shell(),
                    errors,
                    internal("more execution jobs scheduled than registered units"),
                );
            }
        }
        let observer = self
            .tests
            .as_ref()
            .and_then(|tests| tests.options.workload.as_ref())
            .map(|workload| workload.observer.clone());
        if let Some(observer) = observer {
            let compiler_succeeded = compile_succeeded && errors.count == 0 && !self.root_cancelled;
            if compiler_succeeded {
                let inputs = self
                    .tests
                    .as_ref()
                    .expect("workload state")
                    .options
                    .workload
                    .as_ref()
                    .expect("workload options")
                    .inputs
                    .clone();
                let captured = workload_leases
                    .take()
                    .context("native workload has no original compile/output lease capsule")
                    .and_then(|leases| {
                        crate::ops::cargo_test::workload::OwnedOutputs::capture(
                            inputs,
                            &build_runner.compilation,
                            leases,
                            &build_runner.workload_materializations,
                        )
                    });
                match captured {
                    Ok(outputs) => {
                        self.tests.as_mut().expect("workload state").outputs = Some(outputs)
                    }
                    Err(error) => {
                        self.handle_error(&mut build_runner.bcx.gctx.shell(), errors, error)
                    }
                }
            }
            if let Err(error) = test_action::observe_report(|| {
                observer.compiler_retired(
                    &build_runner.compilation,
                    compiler_succeeded,
                    self.tests.as_ref().and_then(|tests| tests.outputs.as_ref()),
                )
            }) {
                self.handle_error(&mut build_runner.bcx.gctx.shell(), errors, error);
            }
            #[cfg(any(target_os = "linux", target_os = "macos"))]
            if compiler_succeeded && errors.count == 0 {
                let entered =
                    build_runner
                        .resource_runtime
                        .as_ref()
                        .context("native workload has no original retained runtime")
                        .and_then(|runtime| {
                            runtime.enter_workload_harnesses(
                        self.tests.as_ref().and_then(|tests| tests.outputs.as_ref())
                            .context("native workload has no original compiled output population")?
                    )
                        });
                if let Err(error) = entered {
                    self.handle_error(&mut build_runner.bcx.gctx.shell(), errors, error);
                }
            }
        }
        if (!compile_succeeded || errors.count != 0)
            && let Some(tests) = self.tests.as_mut()
        {
            tests.stopped = true;
        }
        #[cfg(any(target_os = "linux", target_os = "macos"))]
        if let Some(state) = self.verification.as_mut() {
            let succeeded = compile_succeeded && errors.count == 0 && !self.root_cancelled;
            if let Err(error) = state.compiler_retired(&build_runner.compilation, succeeded) {
                self.handle_error(&mut build_runner.bcx.gctx.shell(), errors, error);
            }
        }
        self.execution.compiler_finished =
            Some(build_runner.bcx.gctx.invocation_instant().elapsed());
    }

    fn handle_error(
        &mut self,
        shell: &mut Shell,
        err_state: &mut ErrorsDuringDrain,
        new_err: impl Into<ErrorToHandle>,
    ) {
        let new_err = new_err.into();
        if new_err.print_always || err_state.count == 0 {
            crate::display_error(&new_err.error, shell);
            if err_state.count == 0 && self.active_count() != 0 {
                self.progress.indicate_error();
                let _ = shell.warn("build failed, waiting for other jobs to finish...");
            }
            err_state.count += 1;
        } else {
            tracing::warn!("{:?}", new_err.error);
        }
    }

    // This also records CPU usage and marks concurrency; we roughly want to do
    // this as often as we spin on the events receiver (at least every 500ms or
    // so).
    fn tick_progress(&mut self) {
        if self.compiler_finalized {
            return;
        }
        // Record some timing information if `--timings` is enabled, and
        // this'll end up being a noop if we're not recording this
        // information.
        self.timings.record_cpu();

        let active_names = self
            .active
            .values()
            .map(|u| self.name_for_progress(u))
            .collect::<Vec<_>>();
        let _ = self.progress.tick_now(
            self.finished,
            self.total_units,
            &format!(": {}", active_names.join(", ")),
        );
    }

    fn name_for_progress(&self, unit: &Unit) -> String {
        let pkg_name = unit.pkg.name();
        let target_name = unit.target.name();
        match unit.mode {
            CompileMode::Doc { .. } => format!("{}(doc)", pkg_name),
            CompileMode::RunCustomBuild => format!("{}(build)", pkg_name),
            CompileMode::Test | CompileMode::Check { test: true } => match unit.target.kind() {
                TargetKind::Lib(_) => format!("{}(test)", target_name),
                TargetKind::CustomBuild => panic!("cannot test build script"),
                TargetKind::Bin => format!("{}(bin test)", target_name),
                TargetKind::Test => format!("{}(test)", target_name),
                TargetKind::Bench => format!("{}(bench)", target_name),
                TargetKind::ExampleBin | TargetKind::ExampleLib(_) => {
                    format!("{}(example test)", target_name)
                }
            },
            _ => match unit.target.kind() {
                TargetKind::Lib(_) => pkg_name.to_string(),
                TargetKind::CustomBuild => format!("{}(build.rs)", pkg_name),
                TargetKind::Bin => format!("{}(bin)", target_name),
                TargetKind::Test => format!("{}(test)", target_name),
                TargetKind::Bench => format!("{}(bench)", target_name),
                TargetKind::ExampleBin | TargetKind::ExampleLib(_) => {
                    format!("{}(example)", target_name)
                }
            },
        }
    }

    /// Executes a job.
    ///
    /// Fresh jobs block until finished (which should be very fast!), Dirty
    /// jobs will spawn a thread in the background and return immediately.
    fn run<'s>(
        &mut self,
        unit: &Unit,
        job: Job,
        build_runner: &BuildRunner<'_, '_>,
        scope: &'s Scope<'s, '_>,
        compiler_workers: &mut Vec<thread::ScopedJoinHandle<'s, ()>>,
        local_token: Option<Acquired>,
        #[cfg(any(target_os = "linux", target_os = "macos"))] resources: Option<
            Arc<super::resource_runtime::RootContext>,
        >,
        #[cfg(all(target_os = "macos", target_arch = "aarch64"))] bootstrap_permit: Option<
            crate::context::bootstrap_full::QueuePermit,
        >,
    ) {
        let id = JobId(self.next_id);
        self.next_id = self.next_id.checked_add(1).unwrap();

        debug!("start {}: {:?}", id, unit);

        assert!(self.active.insert(id, unit.clone()).is_none());
        self.execution.scheduled += 1;
        if let Some(logger) = build_runner.bcx.logger {
            logger.log(LogMessage::UnitScheduled {
                index: build_runner.bcx.unit_to_index[unit],
                elapsed: build_runner
                    .bcx
                    .gctx
                    .invocation_instant()
                    .elapsed()
                    .as_secs_f64(),
                fresh: job.freshness().is_fresh(),
            });
        }

        let messages = self.messages.clone();
        let is_fresh = job.freshness().is_fresh();
        // Trust: DC-12a. A dirty job may still turn fresh under its lock, which
        // `Message::RecheckFreshness` then records.
        self.ran.dispatched(unit.clone(), is_fresh);
        let record_workload_output =
            build_runner.records_workload_output() && !unit.mode.is_run_custom_build();
        let rmeta_required = build_runner.rmeta_required(unit);
        let lock_manager = build_runner.lock_manager.clone();
        let warning_handling = build_runner.bcx.gctx.warning_handling().unwrap_or_default();

        let doit = move |diag_dedupe| {
            // This local credit and JobState's host credit span the entire
            // execution, including its child wait and final bookkeeping.
            let _local_token = local_token;
            let state = JobState::new(
                id,
                messages,
                diag_dedupe,
                rmeta_required,
                lock_manager,
                warning_handling,
                is_fresh,
                record_workload_output,
                #[cfg(any(target_os = "linux", target_os = "macos"))]
                resources,
            );
            #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
            let state = state.with_bootstrap_permit(bootstrap_permit);
            state.run_to_finish(job);
        };

        match is_fresh {
            true => {
                // Running a fresh job on the same thread is often much faster than spawning a new
                // thread to run the job.
                doit(Some(&self.diag_dedupe));
            }
            false => {
                compiler_workers.push(scope.spawn(move || doit(None)));
            }
        }
    }

    fn emit_log_messages(
        &self,
        unit: &Unit,
        build_runner: &mut BuildRunner<'_, '_>,
        show_warnings: bool,
    ) -> CargoResult<()> {
        let outputs = build_runner.build_script_outputs.lock().unwrap();
        let Some(metadata_vec) = build_runner.find_build_script_metadatas(unit) else {
            return Ok(());
        };
        let bcx = &mut build_runner.bcx;
        for metadata in metadata_vec {
            if let Some(output) = outputs.get(metadata) {
                if !output.log_messages.is_empty()
                    && (show_warnings
                        || output
                            .log_messages
                            .iter()
                            .any(|(severity, _)| *severity == Severity::Error))
                {
                    let msg_with_package =
                        |msg: &str| format!("{}@{}: {}", unit.pkg.name(), unit.pkg.version(), msg);

                    for (severity, message) in output.log_messages.iter() {
                        match severity {
                            Severity::Error => {
                                bcx.gctx.shell().error(msg_with_package(message))?;
                            }
                            Severity::Warning => {
                                bcx.gctx.shell().warn(msg_with_package(message))?;
                            }
                        }
                    }
                }
            }
        }

        Ok(())
    }

    fn bump_warning_count(&mut self, id: JobId, lint: bool, emitted: bool, fixable: bool) {
        let count = self.warning_count.entry(id).or_default();
        count.total += 1;
        if lint {
            let unit = self.active.get(&id).unwrap();
            // If this is an upstream dep but we *do* want warnings, make sure that they
            // don't fail compilation.
            if unit.is_local() {
                count.lints += 1;
            }
        }
        if !emitted {
            count.duplicates += 1;
        // Don't add to fixable if it's already been emitted
        } else if fixable {
            // Do not add anything to the fixable warning count if
            // is `NotAllowed` since that indicates there was an
            // error while building this `Unit`
            if count.fixable_allowed() {
                count.fixable = match count.fixable {
                    FixableWarnings::NotAllowed => FixableWarnings::NotAllowed,
                    FixableWarnings::Zero => FixableWarnings::Positive(1),
                    FixableWarnings::Positive(fixable) => FixableWarnings::Positive(fixable + 1),
                };
            }
        }
    }

    /// Displays a final report of the warnings emitted by a particular job.
    fn report_warning_count(
        &mut self,
        runner: &mut BuildRunner<'_, '_>,
        unit: &Unit,
        count: &WarningCount,
        rustc_workspace_wrapper: &Option<PathBuf>,
        denied_warnings: bool,
    ) {
        let gctx = runner.bcx.gctx;
        runner.compilation.lint_warning_count += count.lints;
        let mut message = descriptive_pkg_name(&unit.pkg.name(), &unit.target, &unit.mode);
        message.push_str(" generated ");
        match count.total {
            1 => message.push_str("1 warning"),
            n => {
                let _ = write!(message, "{} warnings", n);
            }
        };
        match count.duplicates {
            0 => {}
            1 => message.push_str(" (1 duplicate)"),
            n => {
                let _ = write!(message, " ({} duplicates)", n);
            }
        }
        // Only show the `cargo fix` message if its a local `Unit`
        if unit.is_local() {
            // Do not show this if there are any errors or no fixable warnings
            if let FixableWarnings::Positive(fixable) = count.fixable {
                // `cargo fix` doesn't have an option for custom builds
                if !unit.target.is_custom_build() {
                    // Trust: keep the suggested fixer on the frontend/driver
                    // that emitted the diagnostics. `tippy-driver` is the
                    // branded Trust linter; `clippy-driver` remains the
                    // inherited compatibility path, and suggesting the wrong
                    // one prints a command that applies different fixes.
                    let (command, is_lint_wrapper) = fix_command_for_wrapper(
                        rustc_workspace_wrapper,
                        crate::is_targo_invocation(),
                    );

                    let mut args =
                        format!("{} -p {}", unit.target.description_named(), unit.pkg.name());
                    if unit.mode.is_rustc_test()
                        && !(unit.target.is_test() || unit.target.is_bench())
                    {
                        args.push_str(" --tests");
                    }
                    let mut suggestions = format!("{} suggestion", fixable);
                    if fixable > 1 {
                        suggestions.push_str("s")
                    }

                    #[expect(clippy::disallowed_methods, reason = "consistency with clippy")]
                    let encoded_args = is_lint_wrapper
                        .then(|| env::var_os(TIPPY_ENCODED_ARGS_ENV))
                        .flatten();
                    #[expect(clippy::disallowed_methods, reason = "consistency with clippy")]
                    let legacy_args = (is_lint_wrapper && encoded_args.is_none())
                        .then(|| env::var_os(CLIPPY_ARGS_ENV))
                        .flatten();
                    if let Err(error) = append_fix_suggestion(
                        &mut message,
                        command,
                        &args,
                        &suggestions,
                        is_lint_wrapper,
                        encoded_args.as_deref(),
                        legacy_args.as_deref(),
                    ) {
                        // Trust: a malformed authoritative channel makes the
                        // fix command unavailable. Emitting the base command with
                        // its lint arguments silently dropped could apply a
                        // different set of fixes, so leave the warning count
                        // without a `(run ...)` suggestion.
                        debug!(%error, "omitting fix suggestion with malformed Tippy arguments");
                    }
                }
            }
        }
        // Errors are ignored here because it is tricky to handle them
        // correctly, and they aren't important.
        let _ = if denied_warnings {
            gctx.shell().error(message)
        } else {
            gctx.shell().warn(message)
        };
    }

    fn finish(
        &mut self,
        id: JobId,
        unit: &Unit,
        artifact: Artifact,
        build_runner: &mut BuildRunner<'_, '_>,
    ) -> CargoResult<()> {
        if unit.mode.is_run_custom_build() {
            self.emit_log_messages(
                unit,
                build_runner,
                unit.show_warnings(build_runner.bcx.gctx),
            )?;
        }
        let unblocked = self
            .queue
            .finish(&QueueNode::Compile(unit.clone()), &artifact)
            .into_iter()
            .filter_map(QueueNode::as_compile)
            .collect();
        // Trust: DC-12b. The compile of `unit` has ended: note the
        // incremental folders it wrote, which only the compiler names, for
        // the build's receipt. The queue's dispatch already asked whether this
        // is targo, so asking again cannot panic.
        if artifact == Artifact::All
            && let Some(since) = self.ran.compiling_since(unit)
            && crate::is_targo_invocation()
            && let Some(dir) = build_runner.profile_incremental_dir(unit)
            && let Some(folders) =
                super::incremental_trim::written_by(&dir, &unit.target.crate_name(), since)
        {
            self.ran.wrote(unit.clone(), folders);
        }
        match artifact {
            Artifact::All => self.timings.unit_finished(build_runner, id, unblocked),
            Artifact::Metadata => self
                .timings
                .unit_rmeta_finished(build_runner, id, unblocked),
        }
        Ok(())
    }

    // Trust: keep this bounded event independent of package-level progress state.
    fn note_unit_dispatched(
        runner: &BuildRunner<'_, '_>,
        unit: &Unit,
        fresh: &Freshness,
    ) -> CargoResult<()> {
        if !crate::is_targo_invocation() || !runner.bcx.build_config.emit_json() {
            return Ok(());
        }
        let identity = super::trust_declared_unit_identity_sha256(runner, unit)?;
        let message = machine_message::CompilationUnitDispatched {
            schema: machine_message::TRUST_UNIT_DISPATCH_SCHEMA_V1,
            trust_unit_identity_sha256: &identity,
            trust_compile_mode: super::exact_unit_compile_mode(unit.mode),
            trust_compile_kind: super::exact_unit_compile_kind(unit.kind),
            fresh: matches!(fresh, Fresh),
            dirty_reason: match fresh {
                Fresh => None,
                Dirty(reason) => Some(reason.dispatch_cause()),
            },
        };
        writeln!(
            runner.bcx.gctx.shell().out(),
            "{}",
            message.to_json_string()
        )?;
        Ok(())
    }

    // This isn't super trivial because we don't want to print loads and
    // loads of information to the console, but we also want to produce a
    // faithful representation of what's happening. This is somewhat nuanced
    // as a package can start compiling *very* early on because of custom
    // build commands and such.
    //
    // In general, we try to print "Compiling" for the first nontrivial task
    // run for a package, regardless of when that is. We then don't print
    // out any more information for a package after we've printed it once.
    fn note_working_on(
        &mut self,
        gctx: &GlobalContext,
        ws_root: &Path,
        unit: &Unit,
        fresh: &Freshness,
    ) -> CargoResult<()> {
        if (self.compiled.contains(&unit.pkg.package_id())
            && !unit.mode.is_doc()
            && !unit.mode.is_doc_scrape())
            || (self.documented.contains(&unit.pkg.package_id()) && unit.mode.is_doc())
            || (self.scraped.contains(&unit.pkg.package_id()) && unit.mode.is_doc_scrape())
        {
            return Ok(());
        }

        match fresh {
            // Any dirty stage which runs at least one command gets printed as
            // being a compiled package.
            Dirty(dirty_reason) => {
                if !dirty_reason.is_fresh_build() {
                    gctx.shell().verbose(|shell| {
                        dirty_reason.present_to(shell, unit, ws_root, &self.index_to_unit)
                    })?;
                }

                if unit.mode.is_doc() {
                    self.documented.insert(unit.pkg.package_id());
                    gctx.shell().status("Documenting", &unit.pkg)?;
                } else if unit.mode.is_doc_test() {
                    // Skip doc test.
                } else if unit.mode.is_doc_scrape() {
                    self.scraped.insert(unit.pkg.package_id());
                    gctx.shell().status("Scraping", &unit.pkg)?;
                } else {
                    self.compiled.insert(unit.pkg.package_id());
                    if unit.mode.is_check() {
                        gctx.shell().status("Checking", &unit.pkg)?;
                    } else {
                        gctx.shell().status("Compiling", &unit.pkg)?;
                    }
                }
            }
            Fresh => {
                // If doc test are last, only print "Fresh" if nothing has been printed.
                if self.counts[&unit.pkg.package_id()] == 0
                    && !(unit.mode.is_doc_test() && self.compiled.contains(&unit.pkg.package_id()))
                {
                    self.compiled.insert(unit.pkg.package_id());
                    gctx.shell().verbose(|c| c.status("Fresh", &unit.pkg))?;
                }
            }
        }
        Ok(())
    }

    fn back_compat_notice(
        &self,
        build_runner: &BuildRunner<'_, '_>,
        unit: &Unit,
    ) -> CargoResult<()> {
        if unit.pkg.name() != "diesel"
            || unit.pkg.version() >= &Version::new(1, 4, 8)
            || build_runner.bcx.ws.resolve_behavior() == ResolveBehavior::V1
            || !unit.pkg.package_id().source_id().is_registry()
            || !unit.features.is_empty()
        {
            return Ok(());
        }
        if !build_runner
            .bcx
            .unit_graph
            .keys()
            .any(|unit| unit.pkg.name() == "diesel" && !unit.features.is_empty())
        {
            return Ok(());
        }
        build_runner.bcx.gctx.shell().note(
            "\
This error may be due to an interaction between diesel and Cargo's new
feature resolver. Try updating to diesel 1.4.8 to fix this error.
",
        )?;
        Ok(())
    }
}

// Trust: from here to the end of the file is Trust-authored. Upstream prints a
// single hard-coded `cargo fix` hint; the branded toolchain has four possible
// fixers and the correct one depends on which driver produced the diagnostics,
// which is only knowable from the workspace wrapper's identity. Whole-name
// matching (not `file_stem`) is deliberate: `tippy-driver.backup` must not
// inherit `tippy-driver`'s meaning.

fn fix_command_for_wrapper(
    rustc_workspace_wrapper: &Option<PathBuf>,
    targo_invocation: bool,
) -> (&'static str, bool) {
    fix_command_for_wrapper_with_windows_semantics(
        rustc_workspace_wrapper,
        targo_invocation,
        cfg!(windows),
    )
}

fn fix_command_for_wrapper_with_windows_semantics(
    rustc_workspace_wrapper: &Option<PathBuf>,
    targo_invocation: bool,
    windows_semantics: bool,
) -> (&'static str, bool) {
    let matches = |expected: &str| {
        rustc_workspace_wrapper.as_deref().is_some_and(|path| {
            crate::util::tippy_arg_protocol::executable_path_matches_with_windows_semantics(
                path,
                expected,
                windows_semantics,
            )
        })
    };
    if matches("tippy-driver") {
        ("targo tippy --fix", true)
    } else if matches("clippy-driver") {
        ("cargo clippy --fix", true)
    } else if targo_invocation {
        ("targo fix", false)
    } else {
        ("cargo fix", false)
    }
}

fn append_fix_suggestion(
    message: &mut String,
    command: &str,
    args: &str,
    suggestions: &str,
    is_lint_wrapper: bool,
    encoded_args: Option<&std::ffi::OsStr>,
    legacy_args: Option<&std::ffi::OsStr>,
) -> Result<(), String> {
    let lint_args = if is_lint_wrapper {
        suggested_args_suffix(encoded_args, legacy_args)?
    } else {
        String::new()
    };
    let _ = write!(
        message,
        " (run `{command} --{args}{lint_args}` to apply {suggestions})",
    );
    Ok(())
}

#[cfg(test)]
mod trust_tests {
    use super::{
        ExecutionGraphOutcome, ExecutionSummary, ExecutionUnitOutcome, append_fix_suggestion,
        compilation_warning_policy, execution_unit_outcome, fix_command_for_wrapper,
        fix_command_for_wrapper_with_windows_semantics,
    };
    use std::ffi::OsStr;
    use std::path::PathBuf;

    #[test]
    fn compiler_warning_policy_preserves_denial_after_keep_going() {
        use crate::context::WarningHandling;

        for handling in [
            WarningHandling::Allow,
            WarningHandling::Warn,
            WarningHandling::Deny,
        ] {
            assert!(compilation_warning_policy(handling, 0).is_ok());
        }
        for handling in [WarningHandling::Allow, WarningHandling::Warn] {
            assert!(compilation_warning_policy(handling, 3).is_ok());
        }
        // A successfully completed worker may still contribute denied lint
        // warnings when dispatch continues. That final policy failure must
        // retain its actual cause rather than become successful retirement.
        let error = compilation_warning_policy(WarningHandling::Deny, 3).unwrap_err();
        assert_eq!(
            error.to_string(),
            "warnings are denied by `build.warnings` configuration"
        );
    }

    #[test]
    fn execution_outcomes_preserve_policy_failures_and_typed_cancellation() {
        assert_eq!(
            execution_unit_outcome(Ok(()), false, false),
            ExecutionUnitOutcome::Succeeded
        );
        assert_eq!(
            execution_unit_outcome(Ok(()), false, true),
            ExecutionUnitOutcome::Failed
        );
        let error = anyhow::anyhow!("compiler rejected the program");
        assert_eq!(
            execution_unit_outcome(Err(&error), false, false),
            ExecutionUnitOutcome::Failed
        );
        assert_eq!(
            execution_unit_outcome(Err(&error), true, false),
            ExecutionUnitOutcome::ToleratedFailure
        );
        assert_eq!(
            execution_unit_outcome(Err(&error), true, true),
            ExecutionUnitOutcome::Failed
        );
        let interrupted = anyhow::Error::new(std::io::Error::new(
            std::io::ErrorKind::Interrupted,
            "owned worker cancelled",
        ))
        .context("compiler worker");
        assert_eq!(
            execution_unit_outcome(Err(&interrupted), false, false),
            ExecutionUnitOutcome::Cancelled
        );
        assert_eq!(
            execution_unit_outcome(Err(&interrupted), true, false),
            ExecutionUnitOutcome::Cancelled
        );
        let mentioned = anyhow::anyhow!("the user wrote `cancelled` in a compile error");
        assert_eq!(
            execution_unit_outcome(Err(&mentioned), false, false),
            ExecutionUnitOutcome::Failed
        );
    }

    #[test]
    fn execution_graph_success_requires_observed_terminals_and_policy_acceptance() {
        let mut summary = ExecutionSummary {
            scheduled: 3,
            completed: 2,
            ..Default::default()
        };
        assert_eq!(summary.outcome(), ExecutionGraphOutcome::Failed);
        summary.completed = 3;
        assert_eq!(summary.outcome(), ExecutionGraphOutcome::Succeeded);
        summary.failed = true;
        assert_eq!(summary.outcome(), ExecutionGraphOutcome::Failed);
        summary.root_cancelled = true;
        assert_eq!(summary.outcome(), ExecutionGraphOutcome::Cancelled);
        // A root stop changes the graph's outcome, not a completed worker's.
        assert_eq!(
            execution_unit_outcome(Ok(()), false, false),
            ExecutionUnitOutcome::Succeeded
        );
    }

    #[test]
    fn fixer_guidance_tracks_branded_frontend_and_lint_driver() {
        assert_eq!(fix_command_for_wrapper(&None, false), ("cargo fix", false));
        assert_eq!(fix_command_for_wrapper(&None, true), ("targo fix", false));
        assert_eq!(
            fix_command_for_wrapper(&Some(PathBuf::from("clippy-driver")), true),
            ("cargo clippy --fix", true)
        );
        assert_eq!(
            fix_command_for_wrapper(&Some(PathBuf::from("tippy-driver")), true),
            ("targo tippy --fix", true)
        );
        assert_eq!(
            fix_command_for_wrapper_with_windows_semantics(
                &Some(PathBuf::from("TIPPY-DRIVER.EXE")),
                true,
                true,
            ),
            ("targo tippy --fix", true)
        );
        assert_eq!(
            fix_command_for_wrapper_with_windows_semantics(
                &Some(PathBuf::from("CLIPPY-DRIVER.EXE")),
                true,
                true,
            ),
            ("cargo clippy --fix", true)
        );
        assert_eq!(
            fix_command_for_wrapper_with_windows_semantics(
                &Some(PathBuf::from("tippy-driver.backup")),
                true,
                false,
            ),
            ("targo fix", false)
        );
        assert_eq!(
            fix_command_for_wrapper_with_windows_semantics(
                &Some(PathBuf::from("clippy-driver.com")),
                true,
                true,
            ),
            ("targo fix", false)
        );
    }

    #[test]
    fn malformed_canonical_args_omit_the_entire_fix_suggestion() {
        let mut message = "demo generated 1 warning".to_string();
        let original = message.clone();
        let error = append_fix_suggestion(
            &mut message,
            "targo tippy --fix",
            "lib -p demo",
            "1 suggestion",
            true,
            Some(OsStr::new("tippy-args-v1;9:a")),
            Some(OsStr::new("-Wlegacy__CLIPPY_HACKERY__")),
        );

        assert!(error.is_err());
        assert_eq!(
            message, original,
            "malformed canonical args left a misleading fix command"
        );
        assert!(!message.contains("(run `"));
    }

    #[test]
    fn non_lint_fix_suggestion_does_not_depend_on_tippy_channels() {
        let mut message = "demo generated 1 warning".to_string();
        append_fix_suggestion(
            &mut message,
            "targo fix",
            "lib -p demo",
            "1 suggestion",
            false,
            Some(OsStr::new("malformed-authoritative-channel")),
            None,
        )
        .expect("non-lint suggestions do not consume Tippy transport");

        assert!(message.contains("(run `targo fix --lib -p demo` to apply 1 suggestion)"));
    }
}

impl ErrorsDuringDrain {
    fn to_error(&self) -> Option<anyhow::Error> {
        match self.count {
            0 => None,
            1 => Some(format_err!("1 job failed")),
            n => Some(format_err!("{} jobs failed", n)),
        }
    }
}
