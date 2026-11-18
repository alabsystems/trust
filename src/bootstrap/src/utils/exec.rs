//! Command Execution Module
//!
//! Provides a structured interface for executing and managing commands during bootstrap,
//! with support for controlled failure handling and output management.
//!
//! This module defines the [`ExecutionContext`] type, which encapsulates global configuration
//! relevant to command execution in the bootstrap process. This includes settings such as
//! dry-run mode, verbosity level, and failure behavior.

use std::backtrace::{Backtrace, BacktraceStatus};
use std::collections::HashMap;
use std::ffi::{OsStr, OsString};
use std::fmt::{Debug, Formatter};
use std::fs::File;
use std::hash::Hash;
use std::io::{self, BufWriter, Read, Write};
use std::panic::Location;
use std::path::{Path, PathBuf};
use std::process::{
    Child, ChildStderr, ChildStdout, Command, CommandArgs, CommandEnvs, ExitStatus, Output, Stdio,
};
#[cfg(any(target_os = "macos", target_os = "linux"))]
use std::sync::OnceLock;
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};

use build_helper::drop_bomb::DropBomb;
#[cfg(any(target_os = "macos", target_os = "linux"))]
use build_helper::trust_repo_lock::management::{
    ScopeDispatch, ScopedChild, ScopedReader, WeakScopeDispatch,
};

use crate::core::config::DryRun;
use crate::utils::helpers::{self, t};

// Trust: a permanent restriction, installed by the actual in-process owner.
// A weak sentinel cannot retain/reconstruct the original lease after closure.
// Expired/sealed installation refuses; it never restores standalone dispatch.
#[cfg(any(target_os = "macos", target_os = "linux"))]
static PROTECTED_SCOPE: OnceLock<WeakScopeDispatch> = OnceLock::new();

#[cfg(any(target_os = "macos", target_os = "linux"))]
pub fn install_protected_scope(scope: ScopeDispatch) -> io::Result<()> {
    scope.check_current()?;
    PROTECTED_SCOPE
        .set(scope.downgrade())
        .map_err(|_| io::Error::other("Bootstrap protected scope already installed"))?;
    scope.check_current()
}

#[cfg(any(target_os = "macos", target_os = "linux"))]
pub(crate) fn protected_scope() -> io::Result<Option<ScopeDispatch>> {
    PROTECTED_SCOPE.get().map(WeakScopeDispatch::upgrade).transpose()
}

/// What should be done when the command fails.
#[derive(Debug, Copy, Clone)]
pub(crate) enum BehaviorOnFailure {
    /// Immediately stop bootstrap.
    Exit,
    /// Delay failure until the end of bootstrap invocation.
    DelayFail,
    /// Ignore the failure, the command can fail in an expected way.
    Ignore,
}

/// How should the output of a specific stream of the command (stdout/stderr) be handled
/// (whether it should be captured or printed).
#[derive(Debug, Copy, Clone)]
pub(crate) enum OutputMode {
    /// Prints the stream by inheriting it from the bootstrap process.
    Print,
    /// Captures the stream into memory.
    Capture,
}

impl OutputMode {
    pub(crate) fn captures(&self) -> bool {
        match self {
            OutputMode::Print => false,
            OutputMode::Capture => true,
        }
    }

    pub(crate) fn stdio(&self) -> Stdio {
        match self {
            OutputMode::Print => Stdio::inherit(),
            OutputMode::Capture => Stdio::piped(),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, Default)]
pub(crate) struct CommandFingerprint {
    program: OsString,
    args: Vec<OsString>,
    envs: Vec<(OsString, Option<OsString>)>,
    cwd: Option<PathBuf>,
    // Trust: a raw command cache entry cannot impersonate a protected query.
    metadata_scheduler: bool,
    compiletest_transport: bool,
}

impl CommandFingerprint {
    #[cfg(feature = "tracing")]
    pub(crate) fn program_name(&self) -> String {
        Path::new(&self.program)
            .file_name()
            .map(|p| p.to_string_lossy().to_string())
            .unwrap_or_else(|| "<unknown command>".to_string())
    }

    /// Helper method to format both Command and BootstrapCommand as a short execution line,
    /// without all the other details (e.g. environment variables).
    pub(crate) fn format_short_cmd(&self) -> String {
        use std::fmt::Write;

        let mut cmd = self.program.to_string_lossy().to_string();
        for arg in &self.args {
            let arg = arg.to_string_lossy();
            if arg.contains(' ') {
                write!(cmd, " '{arg}'").unwrap();
            } else {
                write!(cmd, " {arg}").unwrap();
            }
        }
        if let Some(cwd) = &self.cwd {
            write!(cmd, " [workdir={}]", cwd.to_string_lossy()).unwrap();
        }
        cmd
    }
}

#[derive(Default, Clone)]
pub(crate) struct CommandProfile {
    pub(crate) traces: Vec<ExecutionTrace>,
}

#[derive(Default)]
pub(crate) struct CommandProfiler {
    stats: Mutex<HashMap<CommandFingerprint, CommandProfile>>,
}

impl CommandProfiler {
    pub(crate) fn record_execution(&self, key: CommandFingerprint, start_time: Instant) {
        let mut stats = self.stats.lock().unwrap();
        let entry = stats.entry(key).or_default();
        entry.traces.push(ExecutionTrace::Executed { duration: start_time.elapsed() });
    }

    pub(crate) fn record_cache_hit(&self, key: CommandFingerprint) {
        let mut stats = self.stats.lock().unwrap();
        let entry = stats.entry(key).or_default();
        entry.traces.push(ExecutionTrace::CacheHit);
    }

    /// Report summary of executed commands file at the specified `path`.
    pub(crate) fn report_summary(&self, path: &Path, start_time: Instant) {
        let file = t!(File::create(path));

        let mut writer = BufWriter::new(file);
        let stats = self.stats.lock().unwrap();

        let mut entries: Vec<_> = stats
            .iter()
            .map(|(key, profile)| {
                let max_duration = profile
                    .traces
                    .iter()
                    .filter_map(|trace| match trace {
                        ExecutionTrace::Executed { duration, .. } => Some(*duration),
                        _ => None,
                    })
                    .max();

                (key, profile, max_duration)
            })
            .collect();

        entries.sort_by_key(|e| std::cmp::Reverse(e.2));

        let total_bootstrap_duration = start_time.elapsed();

        let total_fingerprints = entries.len();
        let mut total_cache_hits = 0;
        let mut total_execution_duration = Duration::ZERO;
        let mut total_saved_duration = Duration::ZERO;

        for (key, profile, max_duration) in &entries {
            writeln!(writer, "Command: {:?}", key.format_short_cmd()).unwrap();

            let mut hits = 0;
            let mut runs = 0;
            let mut command_total_duration = Duration::ZERO;

            for trace in &profile.traces {
                match trace {
                    ExecutionTrace::CacheHit => {
                        hits += 1;
                    }
                    ExecutionTrace::Executed { duration, .. } => {
                        runs += 1;
                        command_total_duration += *duration;
                    }
                }
            }

            total_cache_hits += hits;
            total_execution_duration += command_total_duration;
            // This makes sense only in our current setup, where:
            // - If caching is enabled, we record the timing for the initial execution,
            //   and all subsequent runs will be cache hits.
            // - If caching is disabled or unused, there will be no cache hits,
            //   and we'll record timings for all executions.
            total_saved_duration += command_total_duration * hits as u32;

            let command_vs_bootstrap = if total_bootstrap_duration > Duration::ZERO {
                100.0 * command_total_duration.as_secs_f64()
                    / total_bootstrap_duration.as_secs_f64()
            } else {
                0.0
            };

            let duration_str = match max_duration {
                Some(d) => format!("{d:.2?}"),
                None => "-".into(),
            };

            writeln!(
                writer,
                "Summary: {runs} run(s), {hits} hit(s), max_duration={duration_str} total_duration: {command_total_duration:.2?} ({command_vs_bootstrap:.2?}% of total)\n"
            )
            .unwrap();
        }

        let overhead_time = total_bootstrap_duration
            .checked_sub(total_execution_duration)
            .unwrap_or(Duration::ZERO);

        writeln!(writer, "\n=== Aggregated Summary ===").unwrap();
        writeln!(writer, "Total unique commands (fingerprints): {total_fingerprints}").unwrap();
        writeln!(writer, "Total time spent in command executions: {total_execution_duration:.2?}")
            .unwrap();
        writeln!(writer, "Total bootstrap time: {total_bootstrap_duration:.2?}").unwrap();
        writeln!(writer, "Time spent outside command executions: {overhead_time:.2?}").unwrap();
        writeln!(writer, "Total cache hits: {total_cache_hits}").unwrap();
        writeln!(writer, "Estimated time saved due to cache hits: {total_saved_duration:.2?}")
            .unwrap();
    }
}

#[derive(Clone)]
pub(crate) enum ExecutionTrace {
    CacheHit,
    Executed { duration: Duration },
}

/// Wrapper around `std::process::Command`.
///
/// By default, the command will exit bootstrap if it fails.
/// If you want to allow failures, use [allow_failure].
/// If you want to delay failures until the end of bootstrap, use [delay_failure].
///
/// By default, the command will print its stdout/stderr to stdout/stderr of bootstrap ([OutputMode::Print]).
/// If you want to handle the output programmatically, use [BootstrapCommand::run_capture].
///
/// Bootstrap will print a debug log to stdout if the command fails and failure is not allowed.
///
/// By default, command executions are cached based on their workdir, program, arguments, and environment variables.
/// This avoids re-running identical commands unnecessarily, unless caching is explicitly disabled.
///
/// [allow_failure]: BootstrapCommand::allow_failure
/// [delay_failure]: BootstrapCommand::delay_failure
pub(crate) struct BootstrapCommand {
    command: Command,
    // Trust: std::Command does not expose env_clear or stdin. Preserve their
    // actual wrapper provenance before an in-process Full command is routed.
    original_inputs: OriginalCommandInputs,
    pub(crate) failure_behavior: BehaviorOnFailure,
    // Run the command even during dry run
    pub(crate) run_in_dry_run: bool,
    // This field makes sure that each command is executed (or disarmed) before it is dropped,
    // to avoid forgetting to execute a command.
    drop_bomb: DropBomb,
    should_cache: bool,
    // Trust: compiler-metadata constructors explicitly select this transport.
    metadata_scheduler: bool,
    compiletest_transport: bool,
}

#[derive(Clone, Copy)]
pub(crate) struct OriginalCommandInputs {
    pub(crate) environment_cleared: Option<bool>,
    pub(crate) inherited_stdin: bool,
}

impl<'a> BootstrapCommand {
    #[track_caller]
    pub(crate) fn new<S: AsRef<OsStr>>(program: S) -> Self {
        let mut command: Self = Command::new(program).into();
        command.original_inputs =
            OriginalCommandInputs { environment_cleared: Some(false), inherited_stdin: true };
        command
    }
    pub(crate) fn arg<S: AsRef<OsStr>>(&mut self, arg: S) -> &mut Self {
        self.command.arg(arg.as_ref());
        self
    }

    // Trust: this is transport selection, never CPU/proof admission. Dispatch
    // requires the real native capture and retains the exclusive borrower.
    pub(crate) fn metadata_scheduler(&mut self) {
        self.metadata_scheduler = true;
    }

    /// The SDK constructor's known compiler query uses the original borrower,
    /// with explicit time/output limits rather than the ordinary cached wait.
    #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
    pub(crate) fn bounded_metadata_output(
        &mut self,
        deadline: Instant,
        bytes: u64,
    ) -> io::Result<Output> {
        self.drop_bomb.defuse();
        if !self.metadata_scheduler || self.should_cache {
            return Err(io::Error::other("bounded query requires uncached metadata transport"));
        }
        super::metadata_scheduler::bounded_output(&mut self.command, deadline, bytes)
    }

    /// Only the maintained Compiletest constructor selects this original
    /// transport. Protected launches keep their existing registered borrower.
    pub(crate) fn compiletest_transport(&mut self) {
        self.compiletest_transport = true;
    }

    /// Cache the command. If it will be executed multiple times with the exact same arguments
    /// and environment variables in the same bootstrap invocation, the previous result will be
    /// loaded from memory.
    pub(crate) fn cached(&mut self) -> &mut Self {
        self.should_cache = true;
        self
    }

    pub(crate) fn args<I, S>(&mut self, args: I) -> &mut Self
    where
        I: IntoIterator<Item = S>,
        S: AsRef<OsStr>,
    {
        self.command.args(args);
        self
    }

    pub(crate) fn env<K, V>(&mut self, key: K, val: V) -> &mut Self
    where
        K: AsRef<OsStr>,
        V: AsRef<OsStr>,
    {
        self.command.env(key, val);
        self
    }

    pub(crate) fn get_envs(&self) -> CommandEnvs<'_> {
        self.command.get_envs()
    }

    pub(crate) fn get_args(&self) -> CommandArgs<'_> {
        self.command.get_args()
    }

    // Trust: controls inspect the actual selected executable, including argv0.
    #[cfg(test)]
    pub(crate) fn get_program(&self) -> &OsStr {
        self.command.get_program()
    }

    pub(crate) fn env_remove<K: AsRef<OsStr>>(&mut self, key: K) -> &mut Self {
        self.command.env_remove(key);
        self
    }

    /// A held native metadata image supplies its complete loader environment.
    pub(crate) fn env_clear(&mut self) -> &mut Self {
        self.command.env_clear();
        self.original_inputs.environment_cleared = Some(true);
        self
    }

    pub(crate) fn current_dir<P: AsRef<Path>>(&mut self, dir: P) -> &mut Self {
        self.command.current_dir(dir);
        self
    }

    // Trust: inspect forwarded Cargo configuration relative to Cargo's real cwd.
    pub(crate) fn get_current_dir(&self) -> Option<&Path> {
        self.command.get_current_dir()
    }

    pub(crate) fn stdin(&mut self, stdin: std::process::Stdio) -> &mut Self {
        self.command.stdin(stdin);
        // Stdio is opaque. Never infer null/inherit/pipe from Debug or an FD.
        self.original_inputs.inherited_stdin = false;
        self
    }

    #[must_use]
    pub(crate) fn delay_failure(self) -> Self {
        Self { failure_behavior: BehaviorOnFailure::DelayFail, ..self }
    }

    pub(crate) fn fail_fast(self) -> Self {
        Self { failure_behavior: BehaviorOnFailure::Exit, ..self }
    }

    #[must_use]
    pub(crate) fn allow_failure(self) -> Self {
        Self { failure_behavior: BehaviorOnFailure::Ignore, ..self }
    }

    pub(crate) fn run_in_dry_run(&mut self) -> &mut Self {
        self.run_in_dry_run = true;
        self
    }

    /// Run the command, while printing stdout and stderr.
    /// Returns true if the command has succeeded.
    #[track_caller]
    pub(crate) fn run(&mut self, exec_ctx: impl AsRef<ExecutionContext>) -> bool {
        exec_ctx.as_ref().run(self, OutputMode::Print, OutputMode::Print).is_success()
    }

    /// Run the command, while capturing and returning all its output.
    #[track_caller]
    pub(crate) fn run_capture(&mut self, exec_ctx: impl AsRef<ExecutionContext>) -> CommandOutput {
        exec_ctx.as_ref().run(self, OutputMode::Capture, OutputMode::Capture)
    }

    /// Run the command, while capturing and returning stdout, and printing stderr.
    #[track_caller]
    pub(crate) fn run_capture_stdout(
        &mut self,
        exec_ctx: impl AsRef<ExecutionContext>,
    ) -> CommandOutput {
        exec_ctx.as_ref().run(self, OutputMode::Capture, OutputMode::Print)
    }

    #[track_caller]
    pub fn start(&mut self, exec_ctx: impl AsRef<ExecutionContext>) -> DeferredCommand<'_> {
        exec_ctx.as_ref().start(self, OutputMode::Print, OutputMode::Print)
    }

    /// Spawn the command in background, while capturing and returning all its output.
    #[track_caller]
    // Trust: exec's protected tests call it, so it is dead only outside them.
    #[cfg_attr(
        not(all(test, any(target_os = "macos", target_os = "linux"))),
        expect(dead_code, reason = "general-purpose, currently unused")
    )]
    pub(crate) fn start_capture(
        &'a mut self,
        exec_ctx: impl AsRef<ExecutionContext>,
    ) -> DeferredCommand<'a> {
        exec_ctx.as_ref().start(self, OutputMode::Capture, OutputMode::Capture)
    }

    /// Spawn the command in background, while capturing and returning stdout, and printing stderr.
    #[track_caller]
    pub(crate) fn start_capture_stdout(
        &'a mut self,
        exec_ctx: impl AsRef<ExecutionContext>,
    ) -> DeferredCommand<'a> {
        exec_ctx.as_ref().start(self, OutputMode::Capture, OutputMode::Print)
    }

    /// Spawn the command in background, while capturing and returning stdout, and printing stderr.
    /// Returns None in dry-mode
    #[track_caller]
    pub(crate) fn stream_capture_stdout(
        &'a mut self,
        exec_ctx: impl AsRef<ExecutionContext>,
    ) -> Option<StreamingCommand> {
        exec_ctx.as_ref().stream(self, OutputMode::Capture, OutputMode::Print)
    }

    /// Mark the command as being executed, disarming the drop bomb.
    /// If this method is not called before the command is dropped, its drop will panic.
    pub(crate) fn mark_as_executed(&mut self) {
        self.drop_bomb.defuse();
    }

    /// Returns the source code location where this command was created.
    pub(crate) fn get_created_location(&self) -> std::panic::Location<'static> {
        self.drop_bomb.get_created_location()
    }

    pub(crate) fn fingerprint(&self) -> CommandFingerprint {
        let command = &self.command;
        CommandFingerprint {
            program: command.get_program().into(),
            args: command.get_args().map(OsStr::to_os_string).collect(),
            envs: command
                .get_envs()
                .map(|(k, v)| (k.to_os_string(), v.map(|val| val.to_os_string())))
                .collect(),
            cwd: command.get_current_dir().map(Path::to_path_buf),
            metadata_scheduler: self.metadata_scheduler,
            compiletest_transport: self.compiletest_transport,
        }
    }
}

impl Debug for BootstrapCommand {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self.command)?;
        write!(f, " (failure_mode={:?})", self.failure_behavior)
    }
}

impl From<Command> for BootstrapCommand {
    #[track_caller]
    fn from(command: Command) -> Self {
        let program = command.get_program().to_owned();
        Self {
            should_cache: false,
            metadata_scheduler: false,
            compiletest_transport: false,
            original_inputs: OriginalCommandInputs {
                environment_cleared: None,
                inherited_stdin: false,
            },
            command,
            failure_behavior: BehaviorOnFailure::Exit,
            run_in_dry_run: false,
            drop_bomb: DropBomb::arm(program),
        }
    }
}

/// Represents the current status of `BootstrapCommand`.
#[derive(Clone, PartialEq)]
enum CommandStatus {
    /// The command has started and finished with some status.
    Finished(ExitStatus),
    /// The actual child exited, but execution ownership is still unresolved.
    ResourceUnresolved(ExitStatus),
    /// It was not even possible to start the command or wait for it to finish.
    DidNotStartOrFinish,
}

/// Create a new BootstrapCommand. This is a helper function to make command creation
/// shorter than `BootstrapCommand::new`.
#[track_caller]
#[must_use]
pub(crate) fn command<S: AsRef<OsStr>>(program: S) -> BootstrapCommand {
    BootstrapCommand::new(program)
}

/// A trusted SDK tool's read-only compiler/planner metadata command. Darwin's
/// CoreFoundation can add this process-local text-encoding cache after launch;
/// it is not an input to the tool's version/print query. Declare its removal on
/// this command, leaving ordinary source/codegen commands and every other
/// explicit/inherited input unchanged. Scheduling remains the caller's choice.
pub(crate) fn tool_metadata_command<S: AsRef<OsStr>>(program: S) -> BootstrapCommand {
    let mut command = command(program);
    if cfg!(target_os = "macos") {
        command.env_remove("__CF_USER_TEXT_ENCODING");
    }
    command
}

/// Represents the output of an executed process.
#[derive(Clone, PartialEq)]
pub(crate) struct CommandOutput {
    status: CommandStatus,
    stdout: Option<Vec<u8>>,
    stderr: Option<Vec<u8>>,
}

impl CommandOutput {
    #[must_use]
    pub(crate) fn not_finished(stdout: OutputMode, stderr: OutputMode) -> Self {
        Self {
            status: CommandStatus::DidNotStartOrFinish,
            stdout: match stdout {
                OutputMode::Print => None,
                OutputMode::Capture => Some(vec![]),
            },
            stderr: match stderr {
                OutputMode::Print => None,
                OutputMode::Capture => Some(vec![]),
            },
        }
    }

    #[must_use]
    pub(crate) fn from_output(output: Output, stdout: OutputMode, stderr: OutputMode) -> Self {
        Self {
            status: CommandStatus::Finished(output.status),
            stdout: match stdout {
                OutputMode::Print => None,
                OutputMode::Capture => Some(output.stdout),
            },
            stderr: match stderr {
                OutputMode::Print => None,
                OutputMode::Capture => Some(output.stderr),
            },
        }
    }

    fn resource_unresolved(output: Output, stdout: OutputMode, stderr: OutputMode) -> Self {
        let status = output.status;
        let mut actual = Self::from_output(output, stdout, stderr);
        actual.status = CommandStatus::ResourceUnresolved(status);
        actual
    }

    #[must_use]
    pub(crate) fn is_success(&self) -> bool {
        match self.status {
            CommandStatus::Finished(status) => status.success(),
            CommandStatus::DidNotStartOrFinish | CommandStatus::ResourceUnresolved(_) => false,
        }
    }

    #[must_use]
    pub(crate) fn is_failure(&self) -> bool {
        !self.is_success()
    }

    pub(crate) fn status(&self) -> Option<ExitStatus> {
        match self.status {
            CommandStatus::Finished(status) => Some(status),
            CommandStatus::DidNotStartOrFinish | CommandStatus::ResourceUnresolved(_) => None,
        }
    }

    /// Child-exit DATA only. ResourceUnresolved never earns logical completion,
    /// command-cache reuse, a fresh GNU borrower or a scope/release capability.
    pub(crate) fn observed_child_status(&self) -> Option<ExitStatus> {
        match self.status {
            CommandStatus::Finished(status) | CommandStatus::ResourceUnresolved(status) => {
                Some(status)
            }
            CommandStatus::DidNotStartOrFinish => None,
        }
    }

    #[must_use]
    pub(crate) fn stdout(&self) -> String {
        String::from_utf8(
            self.stdout.clone().expect("Accessing stdout of a command that did not capture stdout"),
        )
        .expect("Cannot parse process stdout as UTF-8")
    }

    #[must_use]
    pub fn stdout_if_present(&self) -> Option<String> {
        self.stdout.as_ref().and_then(|s| String::from_utf8(s.clone()).ok())
    }

    pub fn stderr_if_present(&self) -> Option<String> {
        self.stderr.as_ref().and_then(|s| String::from_utf8(s.clone()).ok())
    }

    /// Trust: what the command printed, as bytes, when its stdout was captured. A git
    /// path need not be UTF-8 (`utils::trust_source_identity`).
    #[must_use]
    pub fn stdout_bytes_if_present(&self) -> Option<&[u8]> {
        self.stdout.as_deref()
    }

    #[must_use]
    pub(crate) fn stdout_if_ok(&self) -> Option<String> {
        if self.is_success() { Some(self.stdout()) } else { None }
    }

    #[must_use]
    pub(crate) fn stderr(&self) -> String {
        String::from_utf8(
            self.stderr.clone().expect("Accessing stderr of a command that did not capture stderr"),
        )
        .expect("Cannot parse process stderr as UTF-8")
    }
}

impl Default for CommandOutput {
    fn default() -> Self {
        Self {
            status: CommandStatus::Finished(ExitStatus::default()),
            stdout: Some(vec![]),
            stderr: Some(vec![]),
        }
    }
}

#[derive(Clone, Default)]
pub(crate) struct ExecutionContext {
    dry_run: DryRun,
    pub(crate) verbosity: u8,
    fail_fast: bool,
    delayed_failures: Arc<Mutex<Vec<String>>>,
    command_cache: Arc<CommandCache>,
    profiler: Arc<CommandProfiler>,
}

#[derive(Default)]
pub(crate) struct CommandCache {
    cache: Mutex<HashMap<CommandFingerprint, CommandOutput>>,
}

enum CommandState<'a> {
    Cached(CommandOutput),
    Deferred {
        process: Option<Result<CommandProcess, std::io::Error>>,
        command: &'a mut BootstrapCommand,
        stdout: OutputMode,
        stderr: OutputMode,
        executed_at: &'a Location<'a>,
        fingerprint: CommandFingerprint,
        start_time: Instant,
        #[cfg(feature = "tracing")]
        _span_guard: tracing::span::EnteredSpan,
    },
}

// Trust: metadata is completely waited while the implicit borrower is held;
// its deferred result can contain output, never an unguarded live child.
enum CommandProcess {
    Spawned(Child),
    Metadata(std::io::Result<Output>),
    // Trust: protected starts eagerly join the actual child/readers before
    // returning. Concurrent deferred starts cannot borrow implicit execution
    // twice or deadlock the original thread. This contains DATA only.
    #[cfg(any(target_os = "macos", target_os = "linux"))]
    Protected(std::io::Result<UnresolvedOutput>),
}

pub(crate) struct UnresolvedOutput {
    pub(crate) output: Output,
    pub(crate) reason: String,
}

#[cfg(any(target_os = "macos", target_os = "linux"))]
impl UnresolvedOutput {
    pub(crate) fn after_join(
        output: Output,
        producer: super::metadata_scheduler::ProducerBorrow,
        joined: io::Result<build_helper::trust_repo_lock::management::JoinedChild>,
    ) -> Self {
        Self { output, reason: producer.unresolved_join(joined) }
    }
}

enum ObservedCommand {
    Finished(Output),
    #[cfg(any(target_os = "macos", target_os = "linux"))]
    Unresolved(UnresolvedOutput),
}

impl CommandProcess {
    fn wait_with_output(self) -> std::io::Result<ObservedCommand> {
        match self {
            Self::Spawned(child) => child.wait_with_output().map(ObservedCommand::Finished),
            Self::Metadata(output) => output.map(ObservedCommand::Finished),
            #[cfg(any(target_os = "macos", target_os = "linux"))]
            Self::Protected(output) => output.map(ObservedCommand::Unresolved),
        }
    }
}

pub(crate) struct StreamingCommand {
    child: StreamingChild,
    pub(crate) stdout: Option<CommandReader>,
    // Trust: exec's protected tests read it, so it is dead only outside them.
    #[cfg_attr(
        not(all(test, any(target_os = "macos", target_os = "linux"))),
        expect(dead_code, reason = "symmetric with `stdout`")
    )]
    pub(crate) stderr: Option<CommandReader>,
    fingerprint: CommandFingerprint,
    start_time: Instant,
    #[cfg(feature = "tracing")]
    _span_guard: tracing::span::EnteredSpan,
}

enum StreamingChild {
    Ordinary(Child),
    // Trust: the synchronous library already finished all actual work. Its
    // regular status is DATA; this owner is neither a Child nor retirement.
    #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
    Original(crate::engine::CompletedCommand),
    #[cfg(any(target_os = "macos", target_os = "linux"))]
    Compiletest(super::metadata_scheduler::StreamingBorrow),
    #[cfg(any(target_os = "macos", target_os = "linux"))]
    Protected {
        child: ScopedChild,
        producer: super::metadata_scheduler::ProducerBorrow,
    },
}

// Trust: the actual protected reader has no raw-FD/clone/export operation.
pub(crate) enum CommandReader {
    Stdout(ChildStdout),
    Stderr(ChildStderr),
    #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
    Original(crate::engine::CompletedReader),
    #[cfg(any(target_os = "macos", target_os = "linux"))]
    Protected(ScopedReader),
}
impl Read for CommandReader {
    fn read(&mut self, bytes: &mut [u8]) -> io::Result<usize> {
        match self {
            Self::Stdout(reader) => reader.read(bytes),
            Self::Stderr(reader) => reader.read(bytes),
            #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
            Self::Original(reader) => reader.read(bytes),
            #[cfg(any(target_os = "macos", target_os = "linux"))]
            Self::Protected(reader) => reader.read(bytes),
        }
    }
}

#[cfg(any(target_os = "macos", target_os = "linux"))]
fn protected_output(
    command: &mut Command,
    scope: &ScopeDispatch,
    stdout: bool,
    stderr: bool,
    metadata: bool,
) -> io::Result<UnresolvedOutput> {
    if metadata {
        return super::metadata_scheduler::protected_output(command, scope, stdout, stderr);
    }
    let registration = scope.register_launch()?;
    // Final environment/stdio has already been selected. Re-export the SAME
    // original GNU after command processing; this borrows no fresh resources.
    let producer =
        super::metadata_scheduler::prepare_producer(command, &registration, scope.deadline())?;
    let (output, joined) = registration.spawn(command)?.wait_with_output_observed()?;
    Ok(UnresolvedOutput::after_join(output, producer, joined))
}

#[must_use]
pub(crate) struct DeferredCommand<'a> {
    state: CommandState<'a>,
}

impl CommandCache {
    pub(crate) fn get(&self, key: &CommandFingerprint) -> Option<CommandOutput> {
        self.cache.lock().unwrap().get(key).cloned()
    }

    pub(crate) fn insert(&self, key: CommandFingerprint, output: CommandOutput) {
        self.cache.lock().unwrap().insert(key, output);
    }
}

impl ExecutionContext {
    pub(crate) fn new(verbosity: u8, fail_fast: bool) -> Self {
        Self { verbosity, fail_fast, ..Default::default() }
    }

    pub(crate) fn dry_run(&self) -> bool {
        match self.dry_run {
            DryRun::Disabled => false,
            DryRun::SelfCheck | DryRun::UserSelected => true,
        }
    }

    pub(crate) fn profiler(&self) -> &CommandProfiler {
        &self.profiler
    }

    pub(crate) fn get_dry_run(&self) -> &DryRun {
        &self.dry_run
    }

    pub(crate) fn do_if_verbose(&self, f: impl Fn()) {
        if self.is_verbose() {
            f()
        }
    }

    pub(crate) fn is_verbose(&self) -> bool {
        self.verbosity > 0
    }

    pub(crate) fn set_dry_run(&mut self, value: DryRun) {
        self.dry_run = value;
    }

    pub(crate) fn set_verbosity(&mut self, value: u8) {
        self.verbosity = value;
    }

    pub(crate) fn add_to_delay_failure(&self, message: String) {
        self.delayed_failures.lock().unwrap().push(message);
    }

    // Trust: a workflow cannot publish success before delayed failures are reported.
    pub(crate) fn has_delayed_failures(&self) -> bool {
        !self.delayed_failures.lock().unwrap().is_empty()
    }

    pub(crate) fn report_failures_and_exit(&self) {
        let failures = self.delayed_failures.lock().unwrap();
        if failures.is_empty() {
            return;
        }
        eprintln!("\n{} command(s) did not execute successfully:\n", failures.len());
        for failure in &*failures {
            eprintln!("  - {failure}");
        }
        helpers::exit_process(1);
    }

    /// Execute a command and return its output.
    /// Note: Ideally, you should use one of the BootstrapCommand::run* functions to
    /// execute commands. They internally call this method.
    #[track_caller]
    pub(crate) fn start<'a>(
        &self,
        command: &'a mut BootstrapCommand,
        stdout: OutputMode,
        stderr: OutputMode,
    ) -> DeferredCommand<'a> {
        #[cfg(any(target_os = "macos", target_os = "linux"))]
        let protected = protected_scope();
        let fingerprint = command.fingerprint();

        #[cfg(any(target_os = "macos", target_os = "linux"))]
        let dispatch_valid = protected.is_ok() && !super::metadata_scheduler::hosted_graph_active();
        #[cfg(not(any(target_os = "macos", target_os = "linux")))]
        let dispatch_valid = true;

        if let Some(cached_output) =
            dispatch_valid.then(|| self.command_cache.get(&fingerprint)).flatten()
        {
            command.mark_as_executed();
            self.do_if_verbose(|| println!("Cache hit: {command:?}"));
            self.profiler.record_cache_hit(fingerprint);
            return DeferredCommand { state: CommandState::Cached(cached_output) };
        }

        #[cfg(feature = "tracing")]
        let span_guard = crate::utils::tracing::trace_cmd(command);

        let created_at = command.get_created_location();
        let executed_at = std::panic::Location::caller();

        if dispatch_valid && self.dry_run() && !command.run_in_dry_run {
            return DeferredCommand {
                state: CommandState::Deferred {
                    process: None,
                    command,
                    stdout,
                    stderr,
                    executed_at,
                    fingerprint,
                    start_time: Instant::now(),
                    #[cfg(feature = "tracing")]
                    _span_guard: span_guard,
                },
            };
        }

        self.do_if_verbose(|| {
            println!("running: {command:?} (created at {created_at}, executed at {executed_at})")
        });

        #[cfg(any(target_os = "macos", target_os = "linux"))]
        let original_inputs = command.original_inputs;
        let cmd = &mut command.command;
        cmd.stdout(stdout.stdio());
        cmd.stderr(stderr.stdio());

        let start_time = Instant::now();

        #[cfg(any(target_os = "macos", target_os = "linux"))]
        let child = match protected {
            Err(error) => Err(error),
            Ok(_) if super::metadata_scheduler::hosted_graph_active() => {
                Ok(CommandProcess::Metadata(super::metadata_scheduler::projected_output(
                    cmd,
                    stdout.captures(),
                    stderr.captures(),
                    original_inputs,
                )))
            }
            Ok(Some(scope)) => Ok(CommandProcess::Protected(protected_output(
                cmd,
                &scope,
                stdout.captures(),
                stderr.captures(),
                command.metadata_scheduler,
            ))),
            Ok(None) if command.metadata_scheduler => Ok(CommandProcess::Metadata(
                super::metadata_scheduler::output(cmd, stdout.captures(), stderr.captures()),
            )),
            Ok(None) => cmd.spawn().map(CommandProcess::Spawned),
        };
        #[cfg(not(any(target_os = "macos", target_os = "linux")))]
        let child = if command.metadata_scheduler {
            Ok(CommandProcess::Metadata(super::metadata_scheduler::output(
                cmd,
                stdout.captures(),
                stderr.captures(),
            )))
        } else {
            cmd.spawn().map(CommandProcess::Spawned)
        };

        DeferredCommand {
            state: CommandState::Deferred {
                process: Some(child),
                command,
                stdout,
                stderr,
                executed_at,
                fingerprint,
                start_time,
                #[cfg(feature = "tracing")]
                _span_guard: span_guard,
            },
        }
    }

    /// Execute a command and return its output.
    /// Note: Ideally, you should use one of the BootstrapCommand::run* functions to
    /// execute commands. They internally call this method.
    #[track_caller]
    pub(crate) fn run(
        &self,
        command: &mut BootstrapCommand,
        stdout: OutputMode,
        stderr: OutputMode,
    ) -> CommandOutput {
        self.start(command, stdout, stderr).wait_for_output(self)
    }

    fn fail(&self, message: &str) -> ! {
        println!("{message}");

        if !self.is_verbose() {
            println!("Command has failed. Rerun with -v to see more details.");
        }
        helpers::exit_process(1);
    }

    /// Spawns the command with configured stdout and stderr handling.
    ///
    /// Returns None if in dry-run mode or Panics if the command fails to spawn.
    pub(crate) fn stream(
        &self,
        command: &mut BootstrapCommand,
        stdout: OutputMode,
        stderr: OutputMode,
    ) -> Option<StreamingCommand> {
        // Trust: hosted commands cannot escape as asynchronous raw children.
        // The actual advanced Full owner may instead complete its command
        // synchronously and retain the SAME guards behind immutable readers.
        command.mark_as_executed();
        #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
        if super::metadata_scheduler::hosted_graph_active() {
            #[cfg(feature = "tracing")]
            let span_guard = crate::utils::tracing::trace_cmd(command);
            let fingerprint = command.fingerprint();
            let start_time = Instant::now();
            let completed = super::metadata_scheduler::host_graph::projected_stream(
                &command.command,
                stdout.captures(),
                stderr.captures(),
                command.original_inputs,
            )
            .unwrap_or_else(|| Err(super::metadata_scheduler::host_graph::refuse_streaming()));
            let mut completed = completed.unwrap_or_else(|error| {
                panic!("original Bootstrap library streaming refused: {error}")
            });
            let stdout =
                stdout.captures().then(|| CommandReader::Original(completed.take_stdout()));
            let stderr =
                stderr.captures().then(|| CommandReader::Original(completed.take_stderr()));
            return Some(StreamingCommand {
                child: StreamingChild::Original(completed),
                stdout,
                stderr,
                fingerprint,
                start_time,
                #[cfg(feature = "tracing")]
                _span_guard: span_guard,
            });
        }
        #[cfg(any(target_os = "macos", target_os = "linux"))]
        let protected = protected_scope()
            .unwrap_or_else(|error| panic!("Bootstrap protected streaming refused: {error}"));
        assert!(!command.metadata_scheduler, "bootstrap metadata requires synchronous capture");
        if !command.run_in_dry_run && self.dry_run() {
            return None;
        }

        #[cfg(feature = "tracing")]
        let span_guard = crate::utils::tracing::trace_cmd(command);

        let start_time = Instant::now();
        let fingerprint = command.fingerprint();
        let cmd = &mut command.command;
        cmd.stdout(stdout.stdio());
        cmd.stderr(stderr.stdio());
        #[cfg(any(target_os = "macos", target_os = "linux"))]
        let child = if let Some(scope) = protected {
            (|| {
                let registration = scope.register_launch()?;
                let producer = super::metadata_scheduler::prepare_producer(
                    cmd,
                    &registration,
                    scope.deadline(),
                )?;
                let child = registration.spawn(cmd)?;
                Ok(StreamingChild::Protected { child, producer })
            })()
        } else if command.compiletest_transport {
            super::metadata_scheduler::stream_original(cmd).map(StreamingChild::Compiletest)
        } else {
            cmd.spawn().map(StreamingChild::Ordinary)
        };
        #[cfg(not(any(target_os = "macos", target_os = "linux")))]
        let child = cmd.spawn().map(StreamingChild::Ordinary);
        let (child, stdout, stderr) = match child {
            Ok(StreamingChild::Ordinary(mut child)) => {
                let stdout = child.stdout.take().map(CommandReader::Stdout);
                let stderr = child.stderr.take().map(CommandReader::Stderr);
                (StreamingChild::Ordinary(child), stdout, stderr)
            }
            #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
            Ok(StreamingChild::Original(mut completed)) => {
                let stdout =
                    stdout.captures().then(|| CommandReader::Original(completed.take_stdout()));
                let stderr =
                    stderr.captures().then(|| CommandReader::Original(completed.take_stderr()));
                (StreamingChild::Original(completed), stdout, stderr)
            }
            #[cfg(any(target_os = "macos", target_os = "linux"))]
            Ok(StreamingChild::Compiletest(mut child)) => {
                let stdout = child.take_stdout().map(CommandReader::Stdout);
                let stderr = child.take_stderr().map(CommandReader::Stderr);
                (StreamingChild::Compiletest(child), stdout, stderr)
            }
            #[cfg(any(target_os = "macos", target_os = "linux"))]
            Ok(StreamingChild::Protected { mut child, producer }) => {
                let stdout = child.take_stdout().map(CommandReader::Protected);
                let stderr = child.take_stderr().map(CommandReader::Protected);
                (StreamingChild::Protected { child, producer }, stdout, stderr)
            }
            Err(e) => panic!("failed to execute command: {cmd:?}\nERROR: {e}"),
        };
        Some(StreamingCommand {
            child,
            stdout,
            stderr,
            fingerprint,
            start_time,
            #[cfg(feature = "tracing")]
            _span_guard: span_guard,
        })
    }
}

impl AsRef<ExecutionContext> for ExecutionContext {
    fn as_ref(&self) -> &ExecutionContext {
        self
    }
}

impl StreamingCommand {
    pub(crate) fn wait(
        self,
        exec_ctx: impl AsRef<ExecutionContext>,
    ) -> Result<ExitStatus, std::io::Error> {
        let exec_ctx = exec_ctx.as_ref();
        let output = match self.child {
            StreamingChild::Ordinary(mut child) => child.wait(),
            #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
            StreamingChild::Original(completed) => completed.wait(),
            #[cfg(any(target_os = "macos", target_os = "linux"))]
            StreamingChild::Compiletest(child) => child.wait(),
            #[cfg(any(target_os = "macos", target_os = "linux"))]
            StreamingChild::Protected { mut child, producer } => (|| {
                let status = child.wait()?;
                let reason = producer.unresolved_join(child.joined());
                Err(io::Error::other(format!("actual child {status}; {reason}")))
            })(),
        };
        exec_ctx.profiler().record_execution(self.fingerprint, self.start_time);
        output
    }
}

impl<'a> DeferredCommand<'a> {
    pub(crate) fn wait_for_output(self, exec_ctx: impl AsRef<ExecutionContext>) -> CommandOutput {
        match self.state {
            CommandState::Cached(output) => output,
            CommandState::Deferred {
                process,
                command,
                stdout,
                stderr,
                executed_at,
                fingerprint,
                start_time,
                #[cfg(feature = "tracing")]
                _span_guard,
            } => {
                let exec_ctx = exec_ctx.as_ref();

                let output =
                    Self::finish_process(process, command, stdout, stderr, executed_at, exec_ctx);

                #[cfg(feature = "tracing")]
                drop(_span_guard);

                if (!exec_ctx.dry_run() || command.run_in_dry_run)
                    && output.observed_child_status().is_some()
                {
                    if command.should_cache && output.status().is_some() {
                        exec_ctx.command_cache.insert(fingerprint.clone(), output.clone());
                    }
                    exec_ctx.profiler.record_execution(fingerprint, start_time);
                }

                output
            }
        }
    }

    // Only the deferred command itself consumes this private process state.
    fn finish_process(
        mut process: Option<Result<CommandProcess, std::io::Error>>,
        command: &mut BootstrapCommand,
        stdout: OutputMode,
        stderr: OutputMode,
        executed_at: &'a std::panic::Location<'a>,
        exec_ctx: &ExecutionContext,
    ) -> CommandOutput {
        use std::fmt::Write;

        command.mark_as_executed();

        let process = match process.take() {
            Some(p) => p,
            None => return CommandOutput::default(),
        };

        let created_at = command.get_created_location();

        #[allow(clippy::enum_variant_names)]
        enum FailureReason {
            FailedAtRuntime(ExitStatus),
            FailedToFinish(std::io::Error),
            FailedToStart(std::io::Error),
            ResourceUnresolved(String),
        }

        let (output, fail_reason) = match process {
            Ok(child) => match child.wait_with_output() {
                Ok(ObservedCommand::Finished(output)) if output.status.success() => {
                    // Successful execution
                    (CommandOutput::from_output(output, stdout, stderr), None)
                }
                Ok(ObservedCommand::Finished(output)) => {
                    // Command started, but then it failed
                    let status = output.status;
                    (
                        CommandOutput::from_output(output, stdout, stderr),
                        Some(FailureReason::FailedAtRuntime(status)),
                    )
                }
                #[cfg(any(target_os = "macos", target_os = "linux"))]
                Ok(ObservedCommand::Unresolved(actual)) => (
                    CommandOutput::resource_unresolved(actual.output, stdout, stderr),
                    Some(FailureReason::ResourceUnresolved(actual.reason)),
                ),
                Err(e) => {
                    // Failed to wait for output
                    (
                        CommandOutput::not_finished(stdout, stderr),
                        Some(FailureReason::FailedToFinish(e)),
                    )
                }
            },
            Err(e) => {
                // Failed to spawn the command
                (CommandOutput::not_finished(stdout, stderr), Some(FailureReason::FailedToStart(e)))
            }
        };

        if let Some(fail_reason) = fail_reason {
            let mut error_message = String::new();
            let command_str = if exec_ctx.is_verbose() {
                format!("{command:?}")
            } else {
                command.fingerprint().format_short_cmd()
            };
            let action = match fail_reason {
                FailureReason::FailedAtRuntime(e) => {
                    format!("failed with exit code {}", e.code().unwrap_or(1))
                }
                FailureReason::FailedToFinish(e) => {
                    format!("failed to finish: {e:?}")
                }
                FailureReason::FailedToStart(e) => {
                    format!("failed to start: {e:?}")
                }
                FailureReason::ResourceUnresolved(reason) => format!(
                    "child exited {:?}, but execution ownership is unresolved: {reason}",
                    output.observed_child_status()
                ),
            };
            writeln!(
                error_message,
                r#"Command `{command_str}` {action}
Created at: {created_at}
Executed at: {executed_at}"#,
            )
            .unwrap();
            if stdout.captures() {
                let text = String::from_utf8_lossy(output.stdout.as_deref().unwrap_or_default());
                writeln!(error_message, "\n--- STDOUT vvv\n{}", text.trim()).unwrap();
            }
            if stderr.captures() {
                let text = String::from_utf8_lossy(output.stderr.as_deref().unwrap_or_default());
                writeln!(error_message, "\n--- STDERR vvv\n{}", text.trim()).unwrap();
            }
            let backtrace = if exec_ctx.verbosity > 1 {
                Backtrace::force_capture()
            } else if matches!(command.failure_behavior, BehaviorOnFailure::Ignore) {
                Backtrace::disabled()
            } else {
                Backtrace::capture()
            };
            if matches!(backtrace.status(), BacktraceStatus::Captured) {
                writeln!(error_message, "\n--- BACKTRACE vvv\n{backtrace}").unwrap();
            }

            match command.failure_behavior {
                BehaviorOnFailure::DelayFail => {
                    if exec_ctx.fail_fast {
                        exec_ctx.fail(&error_message);
                    }
                    exec_ctx.add_to_delay_failure(error_message);
                }
                BehaviorOnFailure::Exit => {
                    exec_ctx.fail(&error_message);
                }
                BehaviorOnFailure::Ignore => {
                    // If failures are allowed, either the error has been printed already
                    // (OutputMode::Print) or the user used a capture output mode and wants to
                    // handle the error output on their own.
                }
            }
        }

        output
    }
}

#[cfg(all(test, any(target_os = "macos", target_os = "linux")))]
// Trust: out-of-line unit tests, as tidy's `unit_tests` check requires: the file sits
// under exec/tests/ so the module keeps its `protected_tests` path.
#[path = "exec/tests/protected_tests.rs"]
mod protected_tests;

mod thread_scope;
pub(crate) use thread_scope::scoped_threads;

/// Until a raw subprocess has an original native executor/retirement owner,
/// installed protected mode must refuse it. Absent installation preserves the
/// standalone path; expired/sealed installation never becomes that fallback.
pub(crate) fn require_standalone_process(operation: &str) -> io::Result<()> {
    #[cfg(any(target_os = "macos", target_os = "linux"))]
    if protected_scope()?.is_some() {
        return Err(io::Error::new(
            io::ErrorKind::Unsupported,
            format!("protected Bootstrap has no native process owner for {operation}"),
        ));
    }
    #[cfg(not(any(target_os = "macos", target_os = "linux")))]
    let _ = operation;
    Ok(())
}

#[cfg(all(test, any(target_os = "macos", target_os = "linux")))]
// Trust: out-of-line unit tests, as tidy's `unit_tests` check requires: the file sits
// under exec/tests/ so the module keeps its `untracked_tests` path.
#[path = "exec/tests/untracked_tests.rs"]
mod untracked_tests;

#[cfg(test)]
#[path = "exec/tests/tool_metadata_tests.rs"]
mod tool_metadata_tests;

#[cfg(all(test, target_os = "macos", target_arch = "aarch64"))]
#[path = "exec/tests/full_command_tests.rs"]
mod full_command_tests;
