use crate::process_error::ProcessError;
use crate::read2::{Read2Action, read2_interruptible};

use anyhow::{Context, Result, anyhow, bail};
use jobserver_utils::Jobserver;
use shell_escape::escape;
use tempfile::NamedTempFile;

use std::collections::BTreeMap;
use std::env;
use std::ffi::{OsStr, OsString};
use std::fmt;
use std::io::{self, Write};
use std::iter::once;
#[cfg(unix)]
use std::os::fd::{AsRawFd as _, OwnedFd};
use std::path::Path;
use std::process::{Child, Command, ExitStatus, Output};
use std::sync::Arc;
use std::sync::OnceLock;
use std::time::{Duration, Instant};

// Trust: opt-in raw failure evidence shares this module's lifecycle owner.
mod capture;
// Trust: retained lifecycle for synchronous compiler queries.
mod owned_output;
pub use capture::{
    CaptureCompletionCause, CaptureOwnerObservation, CaptureStreamEnd, CapturedProcess,
};

/// Trust: finite buffering policy for untrusted child stdout and stderr.
///
/// Upstream reads a child's output until the pipe closes, which is fine when
/// the child is trusted and fatal when it is not: a compiler, proc macro, or
/// build script can emit an unbounded newline-free stream and exhaust the
/// parent's memory before any consumer inspects a single line.
///
/// The ordinary Cargo streaming API remains unbounded for compatibility. A
/// caller handling authenticated or otherwise adversarial output can opt into
/// this policy with [`ProcessBuilder::exec_with_streaming_limits`]. Each stream
/// gets an independent aggregate budget; `max_line_bytes` also bounds the
/// unterminated partial line retained while waiting for a newline.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct StreamingOutputLimits {
    max_line_bytes: usize,
    max_stream_bytes: usize,
    timeout: Option<Duration>,
    child_exit_cleanup: bool,
    // Trust: see `with_long_lines_cut`.
    cut_long_lines: bool,
}

impl StreamingOutputLimits {
    /// `max_line_bytes` bounds one complete line, and the unterminated tail
    /// held while waiting for a newline. It is applied exactly as given.
    ///
    /// `max_stream_bytes` is NOT always the bound enforced. Below
    /// `MAX_AUTHENTICATED_TRANSPORT_FLOOR_BYTES` (512 MiB) it is a deliberately
    /// tight probe budget and is applied verbatim; at or above it the request
    /// is transport-class, and the bound actually enforced is
    /// `scaled_stream_ceiling` of it and this machine's memory — larger, and
    /// machine-dependent. A rejection always names the figure that was
    /// applied, never the one requested.
    pub const fn new(max_line_bytes: usize, max_stream_bytes: usize) -> Self {
        Self {
            max_line_bytes,
            max_stream_bytes,
            timeout: None,
            child_exit_cleanup: false,
            cut_long_lines: false,
        }
    }

    /// Trust: a line longer than `max_line_bytes` does not stop the read. It
    /// reaches its callback once, as [`long_line_mark`] followed by the line's
    /// first bytes, `max_line_bytes` in all; the rest of the line is dropped.
    /// Every byte read still counts against the aggregate budget, which is
    /// the bound on what the child may write, and memory held stays bounded
    /// by the line limit as before.
    ///
    /// For output whose reader takes meaning from short lines only (libtest's
    /// `test <name> ... ok` and `test result:`): a failing test may print a
    /// message of any length, and stopping the harness there loses the
    /// results of every test it ran. The mark comes first so that no cut line
    /// begins as the child began it: a reader matching line prefixes cannot
    /// take a cut line for a short one.
    pub const fn with_long_lines_cut(mut self) -> Self {
        self.cut_long_lines = true;
        self
    }

    /// Adds a finite elapsed-time budget for spawning, reading, and waiting
    /// for the child. The timeout uses a monotonic clock.
    pub const fn with_timeout(mut self, timeout: Duration) -> Self {
        self.timeout = Some(timeout);
        self
    }

    /// Trust: stop this child's isolated group when its leader exits, without
    /// waiting for descendants to close inherited output pipes. The leader is
    /// observed without reaping and stays owned through the final group signal.
    /// Only one such signal lease may be active in a process: nested or
    /// concurrent opt-in calls refuse immediately rather than wait or deadlock.
    pub const fn with_child_exit_cleanup(mut self) -> Self {
        self.child_exit_cleanup = true;
        self
    }

    /// Actual resolved per-line output bound.
    pub const fn line_bytes(self) -> usize {
        self.max_line_bytes
    }
    /// Actual resolved aggregate bound per output stream.
    pub const fn stream_bytes(self) -> usize {
        self.max_stream_bytes
    }
    /// Target runtime budget; hosted owners start it at actual target GO.
    pub const fn runtime_timeout(self) -> Option<Duration> {
        self.timeout
    }

    fn validate(self) -> Result<()> {
        if self.child_exit_cleanup && !cfg!(any(target_os = "linux", target_os = "macos")) {
            bail!("streaming child-exit cleanup is supported only on Linux and macOS");
        }
        #[cfg(any(target_os = "linux", target_os = "macos"))]
        if self.child_exit_cleanup {
            ensure_streaming_wait_ownership()?;
        }
        if self.max_line_bytes == 0 {
            bail!("streaming output line limit must be greater than zero");
        }
        if self.cut_long_lines && self.max_line_bytes <= long_line_mark(self.max_line_bytes).len() {
            bail!(
                "streaming output line limit of {} bytes leaves no room for a cut line's mark",
                self.max_line_bytes
            );
        }
        if self.max_stream_bytes == 0 {
            bail!("streaming output aggregate limit must be greater than zero");
        }
        if self.timeout == Some(Duration::ZERO) {
            bail!("streaming process timeout must be greater than zero");
        }
        Ok(())
    }

    /// Trust: the limits actually enforced on this machine.
    ///
    /// Resolution happens ONCE per exec, before any output is read, so that
    /// the aggregate comparison and the rejection message that reports it can
    /// never name different numbers.
    fn resolved(self) -> Self {
        Self {
            max_stream_bytes: scaled_stream_ceiling(
                self.max_stream_bytes,
                effective_physical_memory_bytes(),
            ),
            ..self
        }
    }
}

/// Trust: the FLOOR of the machine-scaled aggregate stream budget, and the
/// threshold at or above which a caller's request is read as an authenticated
/// TRANSPORT budget rather than a deliberately tight probe budget.
///
/// ONE RULE, TWO SITES — mirror any change. The same rule already exists in
/// `targo-trust/src/input_limits.rs` as
/// `MAX_AUTHENTICATED_CARGO_TRANSPORT_BYTES` (this floor),
/// `scaled_transport_ceiling` (the arithmetic below) and
/// `max_authenticated_cargo_transport_bytes` (that rule applied to
/// `trust_router::effective_physical_memory_bytes`), where it bounds the proof
/// driver's own retained transport. It is duplicated here rather than shared
/// because `cargo-util` belongs to the vendored Cargo workspace
/// (`src/tools/targo`), which is disjoint from the Trust workspace, and
/// because `trust-router` — where the memory reader lives — depends on
/// `trust-budget`, a crate carrying the native `ensures` grammar and therefore
/// buildable only by the Trust toolchain. `cargo-util` is compiled by stock
/// rustc during bootstrap, so that edge cannot be taken.
const MAX_AUTHENTICATED_TRANSPORT_FLOOR_BYTES: usize = 512 * 1024 * 1024;

/// The aggregate stream budget actually applied, given what the caller asked
/// for and this machine's effective memory.
///
/// A request BELOW the transport floor is a deliberately tight bound — the
/// verified rustdoc `-Vv` identity probe's 64 KiB, a test's 4096 — asserting a
/// property of a specific child rather than guarding memory. Scaling it would
/// delete the property, so it is applied verbatim.
///
/// A request at or above the floor is the transport-class budget. What that
/// budget bounds depends on the caller's `capture_output`, and BOTH modes are
/// live in this tree:
///
///   * `capture_output: true` — build scripts, `compiler/custom_build.rs:816`,
///     and the rustdoc identity probe. Completed lines are retained in the
///     returned `Output` (see the `try_reserve_exact` guard further down this
///     file), so the aggregate bounds THIS process's memory.
///   * `capture_output: false` — every rustc and rustdoc compile, via
///     `exec_with_targo_streaming_policy` at `compiler/mod.rs:208` and
///     `mod.rs:6942`. Nothing is retained here but the unterminated tail,
///     which `max_line_bytes` already bounds. The aggregate instead bounds the
///     VOLUME one child may put through the parent: the reading and scanning
///     this process does on its behalf, and the evidence handed onward to a
///     consumer that keeps its own, independently scaled, retention bound
///     (`targo-trust/src/pipeline/transport.rs:1074`). This is the mode the
///     `ay` failures below were in, so on that path the number below governs
///     throughput, not memory.
///
/// In neither mode is it a flood DETECTOR: it cannot tell a proof payload from
/// a diagnostic repeated ten thousand times, and it fires identically on both.
/// Sizing it is therefore a question about the machine — what a box can hold,
/// and how much work it may be asked to do for one unit — which is why it is
/// `max(memory / 8, requested)` and not a constant. With the caller sitting
/// exactly on the floor this is `scaled_transport_ceiling` in
/// `targo-trust/src/input_limits.rs`, byte for byte.
///
/// A flat 512 MiB was a measurement of nothing. Measured 2026-09-09 on a
/// 128 GiB box: `targo trust check --allow-l0-gaps --workspace --all-targets
/// --all-features` over `ay` reached 337 units and failed two of them with
/// "streaming stderr exceeds the 536870912-byte aggregate safety limit" —
/// refusing evidence the machine could have held thirty-two times over.
fn scaled_stream_ceiling(requested_bytes: usize, effective_memory_bytes: u64) -> usize {
    if requested_bytes < MAX_AUTHENTICATED_TRANSPORT_FLOOR_BYTES {
        return requested_bytes;
    }
    let scaled = usize::try_from(effective_memory_bytes / 8).unwrap_or(usize::MAX);
    requested_bytes.max(scaled)
}

/// This machine's effective memory in bytes, or `0` when it cannot be read —
/// in which case [`scaled_stream_ceiling`] degrades to its floor, which is the
/// behaviour that existed before it.
///
/// Read once per process: the ceiling is resolved on every streamed child, and
/// a `sysctl` or `/sys` read per spawn would sit on the build's hot path.
fn effective_physical_memory_bytes() -> u64 {
    static EFFECTIVE_MEMORY_BYTES: OnceLock<u64> = OnceLock::new();
    *EFFECTIVE_MEMORY_BYTES.get_or_init(total_physical_memory_bytes)
}

#[cfg(target_os = "macos")]
fn total_physical_memory_bytes() -> u64 {
    let mut size: u64 = 0;
    let mut len = std::mem::size_of::<u64>();
    let name = c"hw.memsize";
    // SAFETY: `name` is a valid null-terminated C string; `size` and `len` are
    // owned stack locals under exclusive mutable access whose layouts match the
    // `u64` and `size_t` that `sysctlbyname` writes. The new-value pointer is
    // null with a zero length, the documented read-only usage.
    let ret = unsafe {
        libc::sysctlbyname(
            name.as_ptr(),
            std::ptr::addr_of_mut!(size).cast::<libc::c_void>(),
            &raw mut len,
            std::ptr::null_mut(),
            0,
        )
    };
    if ret == 0 { size } else { 0 }
}

#[cfg(target_os = "linux")]
fn total_physical_memory_bytes() -> u64 {
    // SAFETY: `_SC_PHYS_PAGES` and `_SC_PAGE_SIZE` are read-only `sysconf`
    // queries taking no pointer parameters; both return -1 on failure, which is
    // handled below.
    let pages = unsafe { libc::sysconf(libc::_SC_PHYS_PAGES) };
    let page_size = unsafe { libc::sysconf(libc::_SC_PAGE_SIZE) };
    if pages <= 0 || page_size <= 0 {
        return 0;
    }
    let Some(host_bytes) = (pages as u64).checked_mul(page_size as u64) else {
        return 0;
    };
    match linux_cgroup_memory_cap_bytes() {
        Some(cap) => host_bytes.min(cap),
        None => host_bytes,
    }
}

/// Best-effort cgroup cap for the host figure above, and a KNOWN and NARROWED
/// divergence from `trust_router::effective_physical_memory_bytes`, which walks
/// `/proc/self/cgroup` and `/proc/self/mountinfo` to the mount root before
/// reading the authority it finds there. That walk is several hundred lines of
/// Linux-specific code and is not duplicated here; this reader looks only at
/// the root of `/sys/fs/cgroup`, so a nested slice whose limit lives deeper is
/// missed and the host figure stands.
///
/// Where the two readers DO see the same authority they now agree, including
/// when it will not be read — see [`linux_cgroup_memory_authority`]. Silently
/// preferring the host total inside a constrained domain is the one divergence
/// that could push this ceiling ABOVE what the machine can honour, so it is the
/// one that is closed rather than disclosed.
#[cfg(target_os = "linux")]
fn linux_cgroup_memory_cap_bytes() -> Option<u64> {
    [
        "/sys/fs/cgroup/memory.max",
        "/sys/fs/cgroup/memory/memory.limit_in_bytes",
    ]
    .into_iter()
    .find_map(|path| linux_cgroup_memory_authority(std::fs::read_to_string(path)))
}

/// What one cgroup memory-authority file says, in the three ways that matter to
/// a caller that will cap the host figure with the result.
///
///   * Absent (`NotFound`) — `None`: no authority here, so the next path is
///     tried and, failing that, the host figure stands. A machine with no
///     cgroupfs is unconstrained, not unreadable.
///   * Present but unreadable, or present and unintelligible — `Some(0)`, which
///     collapses effective memory to zero and the ceiling to its floor. A
///     domain that will not say how constrained it is does not thereby license
///     the host total. This mirrors `apply_linux_memory_limit`'s `Err(_) => 0`
///     in `trust-router/src/memory_jobserver.rs:1848`, the fail-closed half of
///     the rule this file duplicates; it can only ever restore the flat 512 MiB
///     that preceded the scaling, never anything tighter.
///   * A limit — `Some(bytes)`, capping the host figure.
#[cfg(any(target_os = "linux", test))]
fn linux_cgroup_memory_authority(read: io::Result<String>) -> Option<u64> {
    match read {
        Ok(text) => match parse_linux_cgroup_memory_limit(&text) {
            CgroupMemoryLimit::Bytes(bytes) => Some(bytes),
            CgroupMemoryLimit::Unconstrained => None,
            CgroupMemoryLimit::Unintelligible => Some(0),
        },
        Err(error) if error.kind() == io::ErrorKind::NotFound => None,
        Err(_) => Some(0),
    }
}

/// One line of a cgroup memory-limit file, read three ways because the caller
/// must treat them three ways: an unconstrained authority keeps the host figure
/// while an unintelligible one must not.
#[cfg(any(target_os = "linux", test))]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum CgroupMemoryLimit {
    /// A real bound, in bytes.
    Bytes(u64),
    /// Explicitly no limit: cgroup v2 spells this as the literal `max`, v1 as a
    /// saturated page count near `i64::MAX` that must not be mistaken for four
    /// exbibytes of RAM.
    Unconstrained,
    /// A file that exists and says something else, `0` included: no process is
    /// running under a zero-byte memory limit.
    Unintelligible,
}

#[cfg(any(target_os = "linux", test))]
fn parse_linux_cgroup_memory_limit(text: &str) -> CgroupMemoryLimit {
    const UNLIMITED_SENTINEL_FLOOR: u64 = 1 << 62;
    let value = text.trim();
    if value == "max" {
        return CgroupMemoryLimit::Unconstrained;
    }
    match value.parse::<u64>() {
        Ok(bytes) if bytes >= UNLIMITED_SENTINEL_FLOOR => CgroupMemoryLimit::Unconstrained,
        Ok(bytes) if bytes > 0 => CgroupMemoryLimit::Bytes(bytes),
        Ok(_) | Err(_) => CgroupMemoryLimit::Unintelligible,
    }
}

/// Every other platform, Windows included: `0`, so the ceiling stays at its
/// floor and a large Windows box keeps the flat 512 MiB this rule was written
/// to replace.
///
/// Deliberately NOT fixed here. `trust_router::effective_physical_memory_bytes`
/// — the other half of ONE RULE, TWO SITES — has exactly the same platform
/// coverage, and a `GlobalMemoryStatusEx` reader that nobody on this tree can
/// compile or run would replace one guess with another while making the two
/// halves disagree about a platform neither has measured. Fix both together, on
/// a machine that can run the result.
#[cfg(not(any(target_os = "macos", target_os = "linux")))]
fn total_physical_memory_bytes() -> u64 {
    0
}

/// Metrics gathered while running a process
///
/// Returned by [`ProcessBuilder::exec_with_streaming`] whether or not it succeeded.
#[derive(Clone, Copy, Debug, Default)]
pub struct ExecStats {
    /// Peak resident set size of the process, in bytes.
    pub peak_rss: Option<u64>,
    /// CPU booked by the owning wait for the child and descendants it waited for.
    /// None means unavailable, including paths that already reaped without accounting.
    pub cpu_times: Option<CpuTimes>,
}

/// Separate components from one owning kernel wait, never a live-process sample.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CpuTimes {
    /// User mode CPU, including waited descendants, converted to a duration.
    pub user: Duration,
    /// Kernel mode CPU from the same wait.
    pub system: Duration,
}

/// A builder object for an external process, similar to [`std::process::Command`].
#[derive(Clone)]
pub struct ProcessBuilder {
    /// The program to execute.
    program: OsString,
    /// Best-effort replacement for arg0
    arg0: Option<OsString>,
    /// A list of arguments to pass to the program.
    args: Vec<OsString>,
    /// Any environment variables that should be set for the program.
    env: BTreeMap<String, Option<OsString>>,
    /// Trust: immutable source for inherited variables on confined actions.
    environment_snapshot: Option<crate::EnvironmentInputs>,
    /// The directory to run the program from.
    cwd: Option<OsString>,
    /// A list of wrappers that wrap the original program when calling
    /// [`ProcessBuilder::wrapped`]. The last one is the outermost one.
    wrappers: Vec<OsString>,
    /// Trust: enforced by the OS before the selected executable starts.
    action_sandbox: Option<crate::ActionSandbox>,
    /// Trust: cancellation belongs to this execution group, not all callers.
    execution_cancel: Option<Arc<std::sync::atomic::AtomicBool>>,
    /// A scoped owned execution route; never a scalar admission grant.
    executor: Option<Arc<dyn crate::ProcessExecutor>>,
    /// The `make` jobserver. See the [jobserver crate] for
    /// more information.
    ///
    /// [jobserver crate]: https://docs.rs/jobserver/
    jobserver: Option<Jobserver>,
    /// `true` to include environment variable in display.
    display_env_vars: bool,
    /// `true` to retry with an argfile if hitting "command line too big" error.
    /// See [`ProcessBuilder::retry_with_argfile`] for more information.
    retry_with_argfile: bool,
    /// Data to write to stdin.
    stdin: Option<Vec<u8>>,
    /// Descriptors whose `FD_CLOEXEC` bit is cleared only in this command's
    /// post-fork child. The parent and unrelated children retain CLOEXEC.
    #[cfg(unix)]
    inherited_fds: Vec<Arc<OwnedFd>>,
    /// CLOEXEC descriptors retained through fork so they can back a
    /// builder-scoped capability, but never inherited across exec.
    #[cfg(unix)]
    exec_guard_fds: Vec<Arc<OwnedFd>>,
    stdout: Option<Stdio>,
    stderr: Option<Stdio>,
}

fn private_resource_environment(key: &str) -> bool {
    matches!(
        key,
        "TRUST_CPU_HANDOFF"
            | "CARGO_JOBSERVER_HANDOFF"
            | "ATERM_RESOURCE_JOB_V3"
            | "TRUST_FIXED_CLAIM_HANDOFF_V1"
            | "TRUST_FIXED_ADMISSION_FD_V1"
    )
}

impl fmt::Debug for ProcessBuilder {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let environment: BTreeMap<_, _> = self
            .env
            .iter()
            .map(|(key, value)| {
                let value = value.as_ref().map(|value| {
                    if private_resource_environment(key) {
                        OsStr::new("<redacted>")
                    } else {
                        value.as_os_str()
                    }
                });
                (key, value)
            })
            .collect();
        f.debug_struct("ProcessBuilder")
            .field("program", &self.program)
            .field("arg0", &self.arg0)
            .field("args", &self.args)
            .field("env", &environment)
            .field("cwd", &self.cwd)
            .field("wrappers", &self.wrappers)
            .field("display_env_vars", &self.display_env_vars)
            .finish_non_exhaustive()
    }
}

impl fmt::Display for ProcessBuilder {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "`")?;

        if self.display_env_vars {
            for (key, val) in self.env.iter() {
                if let Some(val) = val {
                    let val = if private_resource_environment(key) {
                        escape(OsStr::new("<redacted>").to_string_lossy())
                    } else {
                        escape(val.to_string_lossy())
                    };
                    if cfg!(windows) {
                        write!(f, "set {}={}&& ", key, val)?;
                    } else {
                        write!(f, "{}={} ", key, val)?;
                    }
                }
            }
        }

        write!(f, "{}", self.get_program().to_string_lossy())?;

        for arg in self.get_args() {
            write!(f, " {}", escape(arg.to_string_lossy()))?;
        }

        write!(f, "`")
    }
}

impl ProcessBuilder {
    /// Creates a new [`ProcessBuilder`] with the given executable path.
    pub fn new<T: AsRef<OsStr>>(cmd: T) -> ProcessBuilder {
        ProcessBuilder {
            program: cmd.as_ref().to_os_string(),
            arg0: None,
            args: Vec::new(),
            cwd: None,
            env: BTreeMap::new(),
            environment_snapshot: None,
            wrappers: Vec::new(),
            action_sandbox: None,
            execution_cancel: None,
            executor: None,
            jobserver: None,
            display_env_vars: false,
            retry_with_argfile: false,
            stdin: None,
            #[cfg(unix)]
            inherited_fds: Vec::new(),
            #[cfg(unix)]
            exec_guard_fds: Vec::new(),
            stdout: None,
            stderr: None,
        }
    }

    /// Trust: attach a kernel-enforced action allowlist. Unsupported platforms
    /// fail here; callers must never silently retry an action unconfined.
    pub fn action_sandbox(&mut self, sandbox: crate::ActionSandbox) -> Result<&mut Self> {
        sandbox.require_supported()?;
        #[cfg(unix)]
        if !self.inherited_fds.is_empty() {
            bail!("confined action cannot inherit undeclared file descriptors");
        }
        self.action_sandbox = Some(sandbox);
        Ok(self)
    }

    /// Trust: pass a CLOEXEC descriptor to this process only.
    ///
    /// Upstream has no way to give exactly one child a descriptor: clearing
    /// CLOEXEC in the parent hands it to every subsequent child as well. A
    /// capability that authenticates one specific handoff has to be narrower
    /// than that, so the bit is cleared after fork and before exec, only for
    /// commands cloned from this builder.
    #[cfg(unix)]
    pub fn inherit_fd_for_exec(&mut self, fd: Arc<OwnedFd>) -> io::Result<&mut ProcessBuilder> {
        if self.action_sandbox.is_some() {
            return Err(io::Error::new(
                io::ErrorKind::PermissionDenied,
                "confined action cannot inherit undeclared file descriptors",
            ));
        }
        let raw_fd = fd.as_raw_fd();
        if raw_fd < 3 {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "inherited process descriptor must not alias stdin/stdout/stderr",
            ));
        }
        let flags = unsafe { libc::fcntl(raw_fd, libc::F_GETFD) };
        if flags < 0 {
            return Err(io::Error::last_os_error());
        }
        if flags & libc::FD_CLOEXEC == 0 {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "inherited process descriptor must be CLOEXEC in the parent",
            ));
        }
        if self
            .inherited_fds
            .iter()
            .chain(&self.exec_guard_fds)
            .any(|existing| existing.as_raw_fd() == raw_fd)
        {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "process descriptor was registered more than once",
            ));
        }
        self.inherited_fds.push(fd);
        Ok(self)
    }

    /// Trust: discard explicit exec inheritance at an authenticated launch
    /// boundary before installing the selected owned scheduling transport.
    /// Private exec guards remain retained and CLOEXEC; this does not expose
    /// their descriptors or turn them into child capabilities.
    #[cfg(unix)]
    pub fn clear_exec_inheritance(&mut self) -> &mut Self {
        self.inherited_fds.clear();
        self
    }

    /// Trust: keep a CLOEXEC descriptor live until this command crosses exec.
    ///
    /// Unlike [`Self::inherit_fd_for_exec`], this never clears CLOEXEC. It is
    /// useful for retaining the peer of a child-only socket capability without
    /// exposing that authoritative endpoint to the child image.
    #[cfg(unix)]
    pub fn hold_fd_through_exec(&mut self, fd: Arc<OwnedFd>) -> io::Result<&mut ProcessBuilder> {
        let raw_fd = fd.as_raw_fd();
        if raw_fd < 3 {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "exec guard descriptor must not alias stdin/stdout/stderr",
            ));
        }
        let flags = unsafe { libc::fcntl(raw_fd, libc::F_GETFD) };
        if flags < 0 {
            return Err(io::Error::last_os_error());
        }
        if flags & libc::FD_CLOEXEC == 0 {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "exec guard descriptor must be CLOEXEC",
            ));
        }
        if self
            .exec_guard_fds
            .iter()
            .chain(&self.inherited_fds)
            .any(|existing| existing.as_raw_fd() == raw_fd)
        {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "process descriptor was registered more than once",
            ));
        }
        self.exec_guard_fds.push(fd);
        Ok(self)
    }

    /// (chainable) Sets the executable for the process.
    pub fn program<T: AsRef<OsStr>>(&mut self, program: T) -> &mut ProcessBuilder {
        self.program = program.as_ref().to_os_string();
        self
    }

    /// (chainable) Overrides `arg0` for this program.
    pub fn arg0<T: AsRef<OsStr>>(&mut self, arg: T) -> &mut ProcessBuilder {
        self.arg0 = Some(arg.as_ref().to_os_string());
        self
    }

    /// (chainable) Adds `arg` to the args list.
    pub fn arg<T: AsRef<OsStr>>(&mut self, arg: T) -> &mut ProcessBuilder {
        self.args.push(arg.as_ref().to_os_string());
        self
    }

    /// (chainable) Adds multiple `args` to the args list.
    pub fn args<T: AsRef<OsStr>>(&mut self, args: &[T]) -> &mut ProcessBuilder {
        self.args
            .extend(args.iter().map(|t| t.as_ref().to_os_string()));
        self
    }

    /// (chainable) Replaces the args list with the given `args`.
    pub fn args_replace<T: AsRef<OsStr>>(&mut self, args: &[T]) -> &mut ProcessBuilder {
        if let Some(program) = self.wrappers.pop() {
            // User intend to replace all args, so we
            // - use the outermost wrapper as the main program, and
            // - cleanup other inner wrappers.
            self.program = program;
            self.wrappers = Vec::new();
        }
        self.args = args.iter().map(|t| t.as_ref().to_os_string()).collect();
        self
    }

    /// (chainable) Sets the current working directory of the process.
    pub fn cwd<T: AsRef<OsStr>>(&mut self, path: T) -> &mut ProcessBuilder {
        self.cwd = Some(path.as_ref().to_os_string());
        self
    }

    /// (chainable) Sets an environment variable for the process.
    pub fn env<T: AsRef<OsStr>>(&mut self, key: &str, val: T) -> &mut ProcessBuilder {
        self.env
            .insert(key.to_string(), Some(val.as_ref().to_os_string()));
        self
    }

    /// (chainable) Unsets an environment variable for the process.
    pub fn env_remove(&mut self, key: &str) -> &mut ProcessBuilder {
        self.env.insert(key.to_string(), None);
        self
    }

    /// Trust: clears an explicit set/unset operation for an environment
    /// variable.
    ///
    /// This differs from [`ProcessBuilder::env_remove`]: the child resumes
    /// inheriting the variable instead of receiving an unset operation. It is
    /// useful when replacing every case variant of a variable on platforms
    /// whose environment namespace is case-insensitive.
    pub fn env_clear_override(&mut self, key: &str) -> &mut ProcessBuilder {
        self.env.remove(key);
        self
    }

    /// (chainable) Configure the process's stdout handle
    ///
    /// Only applies when used with [`Self::status`] and [`Self::exec`]
    pub fn stdout<T: Into<Stdio>>(&mut self, cfg: T) -> &mut ProcessBuilder {
        self.stdout = Some(cfg.into());
        self
    }

    /// (chainable) Configure the process's stderr handle
    ///
    /// Only applies when used with [`Self::status`] and [`Self::exec`]
    pub fn stderr<T: Into<Stdio>>(&mut self, cfg: T) -> &mut ProcessBuilder {
        self.stderr = Some(cfg.into());
        self
    }

    /// Gets the executable name.
    pub fn get_program(&self) -> &OsString {
        self.wrappers.last().unwrap_or(&self.program)
    }

    /// Gets the program arg0.
    pub fn get_arg0(&self) -> Option<&OsStr> {
        self.arg0.as_deref()
    }

    /// Gets the program arguments.
    pub fn get_args(&self) -> impl Iterator<Item = &OsString> {
        self.wrappers
            .iter()
            .rev()
            .chain(once(&self.program))
            .chain(self.args.iter())
            .skip(1) // Skip the main `program
    }

    /// Gets the current working directory for the process.
    pub fn get_cwd(&self) -> Option<&Path> {
        self.cwd.as_ref().map(Path::new)
    }

    /// Gets an environment variable as the process will see it (will inherit from environment
    /// unless explicitly unset).
    pub fn get_env(&self, var: &str) -> Option<OsString> {
        self.env
            .get(var)
            .cloned()
            .or_else(|| {
                Some(match &self.environment_snapshot {
                    Some(snapshot) => snapshot.get(OsStr::new(var)),
                    None => env::var_os(var),
                })
            })
            .and_then(|s| s)
    }

    /// Trust: replace ambient inheritance with a captured environment. Explicit
    /// additions/removals and the jobserver overlay still apply afterwards.
    /// Later process-global environment changes cannot change this command.
    pub fn environment_snapshot(&mut self, snapshot: crate::EnvironmentInputs) -> &mut Self {
        self.environment_snapshot = Some(snapshot);
        self
    }

    /// Trust: whether a caller already selected a complete environment.
    /// A scoped default must not overwrite an explicit captured question.
    pub fn has_environment_snapshot(&self) -> bool {
        self.environment_snapshot.is_some()
    }

    /// Gets all environment variables explicitly set or unset for the process (not inherited
    /// vars).
    pub fn get_envs(&self) -> &BTreeMap<String, Option<OsString>> {
        &self.env
    }

    /// Trust: returns the complete environment this builder will present to
    /// its child, including the jobserver overlay applied at spawn time.
    ///
    /// Unlike [`Self::get_envs`], this materializes inherited variables.
    /// Authenticating a child's environment requires the environment it will
    /// actually see, and upstream's view omits everything inherited — which is
    /// most of it.
    #[cfg(unix)]
    pub fn get_effective_envs(&self) -> io::Result<BTreeMap<OsString, OsString>> {
        let mut effective = match &self.environment_snapshot {
            Some(snapshot) => snapshot.variables().clone(),
            None => {
                let mut inherited = BTreeMap::new();
                for (name, value) in env::vars_os() {
                    if inherited.insert(name, value).is_some() {
                        return Err(io::Error::new(
                            io::ErrorKind::InvalidData,
                            "process environment contains a duplicate variable name",
                        ));
                    }
                }
                inherited
            }
        };
        for (name, value) in &self.env {
            match value {
                Some(value) => {
                    effective.insert(name.into(), value.clone());
                }
                None => {
                    effective.remove(OsStr::new(name));
                }
            }
        }
        if let Some(jobserver) = &self.jobserver {
            // Trust: `Client::configure` is the authoritative source for the
            // spawn-time jobserver environment. Apply its overlay after the
            // builder's explicit environment, matching `build_command`, or this
            // view disagrees with the child's in exactly the variables that
            // grant it resources.
            let mut probe = Command::new("__cargo_effective_env_probe__");
            jobserver.configure(&mut probe);
            for (name, value) in probe.get_envs() {
                match value {
                    Some(value) => {
                        effective.insert(name.to_os_string(), value.to_os_string());
                    }
                    None => {
                        effective.remove(name);
                    }
                }
            }
        } else {
            // Trust: an unaware spawn cannot accidentally retain an ambient
            // recovery endpoint when no scheduler was explicitly selected.
            effective.remove(OsStr::new(jobserver_utils::DESCENDANT_HANDOFF_ENV));
        }
        Ok(effective)
    }

    /// Sets the `make` jobserver. See the [jobserver crate][jobserver_docs] for
    /// more information.
    ///
    /// [jobserver_docs]: https://docs.rs/jobserver/latest/jobserver/
    pub fn inherit_jobserver(&mut self, jobserver: &Jobserver) -> &mut Self {
        self.jobserver = Some(jobserver.clone());
        self
    }

    /// Trust: borrow the actually attached scheduler for native ownership
    /// checks. Environment strings cannot substitute for these held originals.
    pub fn get_jobserver(&self) -> Option<&Jobserver> {
        self.jobserver.as_ref()
    }

    /// Whether resource transport is supplied by an owned scheduler.
    pub fn has_jobserver(&self) -> bool {
        self.jobserver.is_some()
    }

    pub fn has_action_sandbox(&self) -> bool {
        self.action_sandbox.is_some()
    }

    /// Trust: remove inherited jobserver authority from a command that will be
    /// launched by a platform-specific authenticated executor instead of
    /// [`Command`].
    ///
    /// The normal spawn path arranges both the environment and descriptor
    /// inheritance inside `jobserver::Client::configure`. An authenticated
    /// executor that deliberately closes every non-stdio descriptor must not
    /// leave a `CARGO_MAKEFLAGS` capability string naming descriptors it did
    /// not transfer. Test binaries do not need build-scheduler authority.
    pub fn clear_jobserver(&mut self) -> &mut Self {
        self.jobserver = None;
        self.env_remove(jobserver_utils::DESCENDANT_HANDOFF_ENV);
        self
    }

    /// Enables environment variable display.
    pub fn display_env_vars(&mut self) -> &mut Self {
        self.display_env_vars = true;
        self
    }

    /// Enables retrying with an argfile if hitting "command line too big" error
    ///
    /// This is primarily for the `@path` arg of rustc and rustdoc, which treat
    /// each line as an command-line argument, so `LF` and `CRLF` bytes are not
    /// valid as an argument for argfile at this moment.
    /// For example, `RUSTDOCFLAGS="--crate-version foo\nbar" cargo doc` is
    /// valid when invoking from command-line but not from argfile.
    ///
    /// To sum up, the limitations of the argfile are:
    ///
    /// - Must be valid UTF-8 encoded.
    /// - Must not contain any newlines in each argument.
    ///
    /// Ref:
    ///
    /// - <https://doc.rust-lang.org/rustdoc/command-line-arguments.html#path-load-command-line-flags-from-a-path>
    /// - <https://doc.rust-lang.org/rustc/command-line-arguments.html#path-load-command-line-flags-from-a-path>
    pub fn retry_with_argfile(&mut self, enabled: bool) -> &mut Self {
        self.retry_with_argfile = enabled;
        self
    }

    /// Bind this command to an already authorized execution owner. Any failure
    /// remains with that owner; there is no native spawn/argfile fallback.
    pub fn process_executor(&mut self, executor: Arc<dyn crate::ProcessExecutor>) -> &mut Self {
        self.executor = Some(executor);
        self
    }
    fn executor(&self) -> Option<Arc<dyn crate::ProcessExecutor>> {
        self.executor
            .clone()
            .or_else(crate::process_executor::default_executor)
    }

    /// Whether an explicit or scoped execution owner replaces local spawning.
    /// This reports routing data; it grants no custody or execution authority.
    pub fn has_process_executor(&self) -> bool {
        self.executor().is_some()
    }
    /// Effective stdout selection for a status-only execution owner.
    pub fn status_stdout(&self) -> std::process::Stdio {
        self.stdout
            .as_ref()
            .map_or_else(std::process::Stdio::inherit, Stdio::to_std)
    }
    /// Effective stderr selection for a status-only execution owner.
    pub fn status_stderr(&self) -> std::process::Stdio {
        self.stderr
            .as_ref()
            .map_or_else(std::process::Stdio::inherit, Stdio::to_std)
    }

    /// The existing execution group's cancellation flag, never global PID state.
    pub fn execution_cancellation(&self) -> Option<Arc<std::sync::atomic::AtomicBool>> {
        self.execution_cancel.clone()
    }

    /// Sets a value that will be written to stdin of the process on launch.
    pub fn stdin<T: Into<Vec<u8>>>(&mut self, stdin: T) -> &mut Self {
        self.stdin = Some(stdin.into());
        self
    }

    /// Trust: declared stdin bytes, or ambient inheritance when absent.
    pub fn get_stdin(&self) -> Option<&[u8]> {
        self.stdin.as_deref()
    }

    fn should_retry_with_argfile(&self, err: &io::Error) -> bool {
        self.retry_with_argfile && imp::command_line_too_big(err)
    }

    /// Like [`Command::status`] but with a better error message.
    pub fn status(&self) -> Result<ExitStatus> {
        self._status()
            .with_context(|| ProcessError::could_not_execute(self))
    }

    fn _status(&self) -> io::Result<ExitStatus> {
        if let Some(executor) = self.executor() {
            if self.action_sandbox.is_some() {
                return Err(io::Error::new(
                    io::ErrorKind::Unsupported,
                    "hosted executor cannot bypass a confined action",
                ));
            }
            return executor.status(self);
        }
        let (mut child, argfile) = self.spawn_native_status()?;
        let status = child.wait();
        if let Some(argfile) = argfile {
            close_tempfile_and_log_error(argfile);
        }
        status
    }

    fn spawn_native_status(&self) -> io::Result<(Child, Option<NamedTempFile>)> {
        if !debug_force_argfile(self.retry_with_argfile) {
            let mut cmd = self.build_command();
            if let Some(stdout) = &self.stdout {
                cmd.stdout(stdout.to_std());
            }
            if let Some(stderr) = &self.stderr {
                cmd.stderr(stderr.to_std());
            }
            match cmd.spawn() {
                Err(ref e) if self.should_retry_with_argfile(e) => {}
                Err(e) => return Err(e),
                Ok(child) => return Ok((child, None)),
            }
        }
        let (mut cmd, argfile) = self.build_command_with_argfile()?;
        if let Some(stdout) = &self.stdout {
            cmd.stdout(stdout.to_std());
        }
        if let Some(stderr) = &self.stderr {
            cmd.stderr(stderr.to_std());
        }
        Ok((cmd.spawn()?, Some(argfile)))
    }

    /// Runs the process, waiting for completion, and mapping non-success exit codes to an error.
    pub fn exec(&self) -> Result<()> {
        let exit = self.status()?;
        if exit.success() {
            Ok(())
        } else {
            Err(ProcessError::new(
                &format!("process didn't exit successfully: {}", self),
                Some(exit),
                None,
            )
            .into())
        }
    }

    /// Trust: preserve the actual backend's target status while finishing a
    /// retained scheduling owner after that target's wait. The caller retains
    /// its actual original group/signalling owner; PID-only cancellation is not
    /// a supported delivery route here. This method never forwards a signal or
    /// creates a group. Completion alone grants no retirement: the supplied
    /// owner must settle its actual guards.
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    pub fn exec_in_original_group_with_retirement(
        &self,
        retire: impl FnOnce() -> Result<()>,
    ) -> Result<()> {
        if self.executor().is_some() {
            return Err(crate::TargetExecutionError::unobserved(anyhow!(
                "retained scheduling retirement requires the original native target wait"
            ))
            .into());
        }
        // Keep the native parent alive through group cancellation without
        // moving the target out of its original outer owner's process group.
        let mut signals = StreamingSignals::install(true)
            .map_err(|error| crate::TargetExecutionError::unobserved(error.into()))?
            .expect("enabled native wait signal scope");
        if pending_streaming_signal() != 0 {
            let error = signals.restore().unwrap_err();
            return Err(crate::TargetExecutionError::unobserved(error.into()).into());
        }
        let (mut child, argfile) = self
            .spawn_native_status()
            .with_context(|| ProcessError::could_not_execute(self))
            .map_err(crate::TargetExecutionError::unobserved)?;
        let status = loop {
            // The original group owner delivers cancellation. This wait never
            // guesses whether a caught signal was PID- or group-directed and
            // never duplicates that delivery to the target.
            match child.try_wait() {
                Ok(Some(status)) => break status,
                Ok(None) => std::thread::sleep(Duration::from_millis(5)),
                Err(error) if error.kind() == io::ErrorKind::Interrupted => {}
                Err(error) => {
                    return Err(crate::TargetExecutionError::unobserved(
                        anyhow::Error::from(error).context(
                            "native target owning wait unavailable; no retirement continuation",
                        ),
                    )
                    .into());
                }
            }
        };
        if let Some(argfile) = argfile {
            close_tempfile_and_log_error(argfile);
        }
        let retirement = retire();
        let signal_mask = pending_streaming_signal();
        let restored = signals.restore();
        let signal_mask = signal_mask | pending_streaming_signal();
        let completion = match (retirement, restored) {
            (Err(error), Err(signal)) => {
                Err(error.context(format!("signal scope also failed: {signal}")))
            }
            (Err(error), Ok(())) => Err(error),
            (Ok(()), Err(error)) => Err(error.into()),
            (Ok(()), Ok(())) => Ok(()),
        };
        if let Err(error) = completion {
            return Err(crate::TargetExecutionError::new(status, error)
                .with_signal_mask(signal_mask)
                .into());
        }
        if status.success() {
            Ok(())
        } else {
            Err(ProcessError::new(
                &format!("process didn't exit successfully: {}", self),
                Some(status),
                None,
            )
            .into())
        }
    }

    /// Replaces the current process with the target process.
    ///
    /// On Unix, this executes the process using the Unix syscall `execvp`, which will block
    /// this process, and will only return if there is an error.
    ///
    /// On Windows this isn't technically possible. Instead we emulate it to the best of our
    /// ability. One aspect we fix here is that we specify a handler for the Ctrl-C handler.
    /// In doing so (and by effectively ignoring it) we should emulate proxying Ctrl-C
    /// handling to the application at hand, which will either terminate or handle it itself.
    /// According to Microsoft's documentation at
    /// <https://docs.microsoft.com/en-us/windows/console/ctrl-c-and-ctrl-break-signals>.
    /// the Ctrl-C signal is sent to all processes attached to a terminal, which should
    /// include our child process. If the child terminates then we'll reap them in Cargo
    /// pretty quickly, and if the child handles the signal then we won't terminate
    /// (and we shouldn't!) until the process itself later exits.
    pub fn exec_replace(&self) -> Result<()> {
        if self.executor().is_some() {
            bail!("owned hosted execution cannot replace the native root");
        }
        imp::exec_replace(self)
    }

    /// Runs the target while retaining this process as a transparent Linux
    /// supervisor.
    ///
    /// This is for callers that own in-process state which must outlive the
    /// launched program and therefore cannot use [`Self::exec_replace`].
    /// Common process-control and termination signals are forwarded through a
    /// pidfd, and this process exits with the child's exact numeric status or
    /// terminating signal. Only spawn or supervision setup failures return.
    ///
    /// On macOS (Trust T14c), signals are forwarded by numeric pid only while
    /// the child is known unreaped, and a signal whose default writes a crash
    /// report ends this process with one line and `128 + n` instead of being
    /// re-raised, so a crashed target never produces a second report.
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    pub fn exec_replace_supervised(&self) -> Result<()> {
        self.exec_replace_supervised_with_retirement(|| Ok(()))
    }

    /// Trust: finish an actual retained scheduling owner after the child's
    /// owning wait, before this supervisor recreates its exit status. A failed
    /// retirement cannot become the target's successful exit. Setup or wait
    /// failures never invoke this continuation.
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    pub fn exec_replace_supervised_with_retirement(
        &self,
        retire: impl FnOnce() -> Result<()>,
    ) -> Result<()> {
        if self.executor().is_some() {
            bail!("owned hosted execution cannot replace the native supervisor");
        }
        imp::exec_replace_supervised(self, retire)
    }

    /// Like [`Command::output`] but with a better error message.
    pub fn output(&self) -> Result<Output> {
        self._output()
            .with_context(|| ProcessError::could_not_execute(self))
    }

    fn _output(&self) -> io::Result<Output> {
        if let Some(executor) = self.executor() {
            if self.action_sandbox.is_some() {
                return Err(io::Error::new(
                    io::ErrorKind::Unsupported,
                    "hosted executor cannot bypass a confined action",
                ));
            }
            return executor.output(self);
        }
        if !debug_force_argfile(self.retry_with_argfile) {
            let mut cmd = self.build_command();
            match piped(&mut cmd, self.stdin.is_some()).spawn() {
                Err(ref e) if self.should_retry_with_argfile(e) => {}
                Err(e) => return Err(e),
                Ok(mut child) => {
                    if let Some(stdin) = &self.stdin {
                        child.stdin.take().unwrap().write_all(stdin)?;
                    }
                    return child.wait_with_output();
                }
            }
        }
        let (mut cmd, argfile) = self.build_command_with_argfile()?;
        let mut child = piped(&mut cmd, self.stdin.is_some()).spawn()?;
        if let Some(stdin) = &self.stdin {
            child.stdin.take().unwrap().write_all(stdin)?;
        }
        let output = child.wait_with_output();
        close_tempfile_and_log_error(argfile);
        output
    }

    /// Executes the process, returning the stdio output, or an error if non-zero exit status.
    pub fn exec_with_output(&self) -> Result<Output> {
        let output = self.output()?;
        if output.status.success() {
            Ok(output)
        } else {
            Err(ProcessError::new(
                &format!("process didn't exit successfully: {}", self),
                Some(output.status),
                Some(&output),
            )
            .into())
        }
    }

    /// Executes a command, passing each line of stdout and stderr to the supplied callbacks, which
    /// can mutate the string data.
    ///
    /// If any invocations of these function return an error, it will be propagated.
    ///
    /// If `capture_output` is true, then all the output will also be buffered
    /// and stored in the returned `Output` object. If it is false, no caching
    /// is done, and the callbacks are solely responsible for handling the
    /// output.
    ///
    /// The returned [`ExecStats`] are populated only when `capture_rusage` is
    /// set, and are returned even on failure (e.g. an OOM-killed process).
    pub fn exec_with_streaming(
        &self,
        on_stdout_line: &mut dyn FnMut(&str) -> Result<()>,
        on_stderr_line: &mut dyn FnMut(&str) -> Result<()>,
        capture_output: bool,
        capture_rusage: bool,
    ) -> (ExecStats, Result<Output>) {
        self.exec_with_streaming_impl(
            on_stdout_line,
            on_stderr_line,
            capture_output,
            None,
            capture_rusage,
            None,
        )
    }

    /// Bind this command to the execution group's local cancellation token.
    pub fn supervised_by(&mut self, scope: &StreamingProcessScope) -> &mut Self {
        self.execution_cancel = Some(Arc::clone(&scope.cancel));
        self
    }

    /// Trust: prepare lifecycle custody before a platform-authenticated launch.
    /// The launcher retains image validation and creates an isolated child group.
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    pub fn prepare_isolated_child(&self) -> io::Result<PreparedIsolatedChild> {
        PreparedIsolatedChild::prepare_with_cancel(self.execution_cancel.clone())
    }

    /// Trust: executes a command with finite per-line and per-stream output
    /// budgets, and does not outlive the output it has already rejected.
    ///
    /// Unlike [`ProcessBuilder::exec_with_streaming`], this creates an isolated
    /// child process group on Unix. A callback rejection, read failure, limit
    /// violation, or configured timeout stops both pipe readers immediately,
    /// terminates the group, and reaps the direct child before returning. This
    /// prevents an untrusted child (or a descendant holding one of its pipes
    /// open) from retaining Cargo's lifetime after its output has already been
    /// rejected.
    ///
    /// The per-stream figure in `limits` is a floor once it reaches 512 MiB:
    /// see `StreamingOutputLimits::new`. Above that threshold the bound
    /// enforced is this machine's, not the caller's.
    pub fn exec_with_streaming_limits(
        &self,
        on_stdout_line: &mut dyn FnMut(&str) -> Result<()>,
        on_stderr_line: &mut dyn FnMut(&str) -> Result<()>,
        capture_output: bool,
        limits: StreamingOutputLimits,
    ) -> Result<Output> {
        self.exec_with_streaming_limits_and_stats(
            on_stdout_line,
            on_stderr_line,
            capture_output,
            limits,
            false,
        )
        .1
    }

    /// Execute under the same finite output/lifecycle policy and retain actual
    /// accounting, including on failure. Unsupported or already consumed
    /// accounting is absent; it is never reconstructed from elapsed time.
    pub fn exec_with_streaming_limits_and_stats(
        &self,
        on_stdout_line: &mut dyn FnMut(&str) -> Result<()>,
        on_stderr_line: &mut dyn FnMut(&str) -> Result<()>,
        capture_output: bool,
        limits: StreamingOutputLimits,
        capture_rusage: bool,
    ) -> (ExecStats, Result<Output>) {
        if let Err(error) = limits.validate() {
            return (ExecStats::default(), Err(error));
        }
        self.exec_with_streaming_impl(
            on_stdout_line,
            on_stderr_line,
            capture_output,
            Some(limits),
            capture_rusage,
            None,
        )
    }

    /// Trust: collect exact bounded raw prefixes, including failure tails.
    ///
    /// Existing streaming APIs and their completed-line diagnostics are unchanged.
    /// Hosted execution refuses before delivery until its owner supports this
    /// evidence contract; it never retries through a local process.
    /// This first strict capture API requires child-exit cleanup (Linux/macOS).
    pub fn exec_with_capture(&self, limits: StreamingOutputLimits) -> CapturedProcess {
        self.exec_with_capture_and_stats(limits, false).1
    }

    /// Same original capture owner with optional original owning-wait stats.
    /// A capture failure does not discard observed bytes, status or accounting.
    pub fn exec_with_capture_and_stats(
        &self,
        limits: StreamingOutputLimits,
        capture_rusage: bool,
    ) -> (ExecStats, CapturedProcess) {
        let mut captured = CapturedProcess::default();
        let executor = self.executor();
        if executor
            .as_ref()
            .is_some_and(|owner| !owner.supports_structured_capture())
        {
            captured.failure = Some(anyhow!(
                "execution owner does not support structured capture"
            ));
            return (ExecStats::default(), captured);
        }
        if !limits.child_exit_cleanup {
            captured.failure = Some(anyhow!("structured capture requires child-exit cleanup"));
            return (ExecStats::default(), captured);
        }
        if let Err(error) = limits.validate() {
            captured.failure = Some(error);
            return (ExecStats::default(), captured);
        }
        if let Some(executor) = executor {
            if self.action_sandbox.is_some() {
                captured.failure = Some(anyhow!("hosted executor cannot bypass a confined action"));
                return (ExecStats::default(), captured);
            }
            // No local fallback or argument-file retry after selected-owner delivery.
            return executor.capture(self, limits.resolved(), capture_rusage);
        }
        let (stats, result) = self.exec_with_streaming_impl(
            &mut |_| Ok(()),
            &mut |_| Ok(()),
            false,
            Some(limits),
            capture_rusage,
            Some(&mut captured),
        );
        captured.failure = result.err();
        (stats, captured)
    }

    fn exec_with_streaming_impl(
        &self,
        on_stdout_line: &mut dyn FnMut(&str) -> Result<()>,
        on_stderr_line: &mut dyn FnMut(&str) -> Result<()>,
        capture_output: bool,
        limits: Option<StreamingOutputLimits>,
        capture_rusage: bool,
        mut captured: Option<&mut CapturedProcess>,
    ) -> (ExecStats, Result<Output>) {
        // Trust: apply the machine-scaled aggregate ceiling ONCE, before a byte
        // of output is read, so `limits.max_stream_bytes` below is both the
        // bound enforced and the number the rejection message names.
        let limits = limits.map(StreamingOutputLimits::resolved);
        if let Some(capture) = captured.as_deref_mut() {
            capture.limits = limits;
        }
        if let Some(executor) = self.executor() {
            if captured.is_some() {
                return (
                    ExecStats::default(),
                    Err(anyhow!(
                        "execution owner does not support structured capture"
                    )),
                );
            }
            if self.action_sandbox.is_some() {
                return (
                    ExecStats::default(),
                    Err(anyhow!("hosted executor cannot bypass a confined action")),
                );
            }
            return executor.streaming(
                self,
                on_stdout_line,
                on_stderr_line,
                capture_output,
                limits,
                capture_rusage,
            );
        }
        let deadline = limits
            .and_then(|limits| limits.timeout)
            .map(|timeout| {
                Instant::now().checked_add(timeout).ok_or_else(|| {
                    anyhow!(
                        "streaming process timeout cannot be represented by the monotonic clock"
                    )
                })
            })
            .transpose();
        let deadline = match deadline {
            Ok(deadline) => deadline,
            Err(error) => return (ExecStats::default(), Err(error)),
        };

        let mut signal_guard =
            match StreamingSignals::install(limits.is_some_and(|limits| limits.child_exit_cleanup))
            {
                Ok(guard) => guard,
                Err(error) => return (ExecStats::default(), Err(error.into())),
            };
        let mut stdout = Vec::new();
        let mut stderr = Vec::new();

        let mut callback_error = None;
        let mut stdout_pos = 0;
        let mut stderr_pos = 0;
        // Trust: whether the rest of a cut line is still arriving
        // (`StreamingOutputLimits::with_long_lines_cut`).
        let mut stdout_cut = false;
        let mut stderr_cut = false;
        let mut stdout_bytes = 0_usize;
        let mut stderr_bytes = 0_usize;

        let spawn = |mut cmd| {
            configure_streaming_child(&mut cmd, limits.is_some());
            if !debug_force_argfile(self.retry_with_argfile) {
                match piped(&mut cmd, false).spawn() {
                    Err(ref e) if self.should_retry_with_argfile(e) => {}
                    Err(e) => return Err(e),
                    Ok(child) => return Ok((child, None)),
                }
            }
            let (mut cmd, argfile) = self.build_command_with_argfile()?;
            configure_streaming_child(&mut cmd, limits.is_some());
            Ok((piped(&mut cmd, false).spawn()?, Some(argfile)))
        };

        let mut collected_stats = ExecStats::default();
        let wait_result = (|| {
            if signal_guard.is_some() && pending_streaming_signal() != 0 {
                bail!("streaming spawn interrupted before child launch");
            }
            if self
                .execution_cancel
                .as_ref()
                .is_some_and(|cancel| cancel.load(std::sync::atomic::Ordering::Acquire))
            {
                bail!("streaming execution group cancelled before child launch");
            }
            let cmd = self.build_command();
            let (mut child, argfile) = spawn(cmd)?;
            if let Some(capture) = captured.as_deref_mut() {
                capture.started = true;
            }
            let out = child.stdout.take().unwrap();
            let err = child.stderr.take().unwrap();
            let mut child_exit = StreamingChildExit::start(
                &mut child,
                limits.is_some_and(|limits| limits.child_exit_cleanup),
                self.execution_cancel.clone(),
                captured.as_deref_mut(),
            )?;
            let mut on_data = |is_out, data: &mut Vec<u8>, eof| {
                if callback_error.is_some() {
                    return Read2Action::Stop;
                }

                let pos = if is_out {
                    &mut stdout_pos
                } else {
                    &mut stderr_pos
                };
                let stream_bytes = if is_out {
                    &mut stdout_bytes
                } else {
                    &mut stderr_bytes
                };
                let stream_name = if is_out { "stdout" } else { "stderr" };

                let Some(new_bytes) = data.len().checked_sub(*pos) else {
                    callback_error = Some(anyhow!(
                        "internal streaming {stream_name} buffer position moved past its data"
                    ));
                    return Read2Action::Stop;
                };
                if let Some(capture) = captured.as_deref_mut() {
                    if let Err(error) = capture.retain(is_out, &data[*pos..]) {
                        callback_error = Some(error);
                        return Read2Action::Stop;
                    }
                    if eof && !limits.is_some_and(|limits| limits.child_exit_cleanup) {
                        capture.ended(is_out, CaptureStreamEnd::Eof);
                    }
                }
                if let Some(limits) = limits {
                    let Some(total) = stream_bytes.checked_add(new_bytes) else {
                        callback_error = Some(anyhow!(
                            "streaming {stream_name} byte count overflowed its aggregate safety limit"
                        ));
                        return Read2Action::Stop;
                    };
                    if total > limits.max_stream_bytes {
                        callback_error = Some(anyhow!(
                            "streaming {stream_name} exceeds the {}-byte aggregate safety limit",
                            limits.max_stream_bytes
                        ));
                        return Read2Action::Stop;
                    }
                    *stream_bytes = total;
                    // Trust: after the count, so a cut line's dropped bytes
                    // are charged like any others. The buffer changed, so
                    // the newline search below starts from its beginning.
                    if limits.cut_long_lines
                        && cut_long_lines(
                            data,
                            limits.max_line_bytes,
                            if is_out {
                                &mut stdout_cut
                            } else {
                                &mut stderr_cut
                            },
                        )
                    {
                        *pos = 0;
                    }
                }

                let idx = if eof {
                    data.len()
                } else {
                    match data[*pos..].iter().rposition(|b| *b == b'\n') {
                        Some(i) => *pos + i + 1,
                        None => {
                            *pos = data.len();
                            if let Some(limits) = limits
                                && data.len() > limits.max_line_bytes
                            {
                                callback_error = Some(anyhow!(
                                    "streaming {stream_name} line exceeds the {}-byte safety limit; \
                                     line prefix (up to {STREAMING_LINE_PREFIX_BYTES} bytes, ASCII-escaped): \"{}\"",
                                    limits.max_line_bytes,
                                    StreamingLinePrefix(data),
                                ));
                                return Read2Action::Stop;
                            }
                            return Read2Action::Continue;
                        }
                    }
                };

                let new_lines = &data[..idx];
                if let Some(limits) = limits
                    && let Some(line) = oversized_line(new_lines, limits.max_line_bytes)
                {
                    callback_error = Some(anyhow!(
                        "streaming {stream_name} line contains {} bytes, exceeding the {}-byte safety limit; \
                         line prefix (up to {STREAMING_LINE_PREFIX_BYTES} bytes, ASCII-escaped): \"{}\"",
                        line.len(),
                        limits.max_line_bytes,
                        StreamingLinePrefix(line),
                    ));
                    return Read2Action::Stop;
                }
                if let Some(limits) = limits
                    && data.len() - idx > limits.max_line_bytes
                {
                    callback_error = Some(anyhow!(
                        "streaming {stream_name} line exceeds the {}-byte safety limit; \
                         line prefix (up to {STREAMING_LINE_PREFIX_BYTES} bytes, ASCII-escaped): \"{}\"",
                        limits.max_line_bytes,
                        StreamingLinePrefix(&data[idx..]),
                    ));
                    return Read2Action::Stop;
                }

                for line in String::from_utf8_lossy(new_lines).lines() {
                    let callback_result = if is_out {
                        on_stdout_line(line)
                    } else {
                        on_stderr_line(line)
                    };
                    if let Err(e) = callback_result {
                        callback_error = Some(e);
                        return Read2Action::Stop;
                    }
                }

                if capture_output {
                    let dst = if is_out { &mut stdout } else { &mut stderr };
                    if limits.is_some()
                        && let Err(error) = dst.try_reserve_exact(new_lines.len())
                    {
                        callback_error = Some(anyhow!(
                            "could not retain bounded streaming {stream_name}: {error}"
                        ));
                        return Read2Action::Stop;
                    }
                    dst.extend(new_lines);
                }

                data.drain(..idx);
                // Trust: `stream_bytes` already includes every byte currently
                // in `data`, including an unterminated tail retained for the next
                // callback. Keep the cursor at the retained length after the
                // completed prefix is drained so that the next read counts
                // only newly appended bytes.
                *pos = data.len();
                Read2Action::Continue
            };
            let read_result = match child_exit.as_mut() {
                Some(owner) => owner.read(out, err, deadline, &mut on_data),
                None => read2_interruptible(out, err, deadline, &mut on_data),
            };
            drop(on_data);
            if let Some(capture) = captured.as_deref_mut() {
                capture.read_error = read_result
                    .as_ref()
                    .err()
                    .map(ToString::to_string)
                    .or_else(|| callback_error.as_ref().map(|error| format!("{error:#}")));
            }

            let status = if let Some(mut owner) = child_exit {
                // The observer is joined before finish can reap, including
                // callback rejection, pipe errors, timeout, and unwinding.
                owner.capture_rusage = capture_rusage;
                let waited = owner.finish(!matches!(&read_result, Ok(Read2Action::Continue)));
                collected_stats = owner.reaped_stats;
                if let Some(capture) = captured.as_deref_mut() {
                    capture.stdout_end = owner.stream_ends[0];
                    capture.stderr_end = owner.stream_ends[1];
                    capture.status = owner.reaped_status;
                    capture.cleanup_error = waited.as_ref().err().map(ToString::to_string);
                }
                match read_result {
                    Ok(_) => waited
                        .map(|status| (status, collected_stats))
                        .map_err(anyhow::Error::from),
                    Err(error) => waited
                        .map_err(anyhow::Error::from)
                        .and_then(|_| Err(error.into())),
                }
            } else {
                // Trust: even None carries the guard's borrow until dropped.
                // Release it before the ordinary branch borrows/reaps child.
                drop(child_exit);
                match read_result {
                Ok(Read2Action::Continue) => {
                    if capture_rusage && deadline.is_none() {
                        imp::wait_with_resource_usage(&mut child).map_err(anyhow::Error::from)
                    } else {
                        wait_for_streaming_child(&mut child, deadline, limits.is_some())
                            .map(|status| (status, ExecStats::default()))
                            .map_err(anyhow::Error::from)
                    }
                }
                Ok(Read2Action::Stop) => terminate_and_reap(&mut child, limits.is_some())
                    .map(|status| (status, ExecStats::default()))
                    .map_err(anyhow::Error::from)
                    .with_context(|| {
                        let rejection = callback_error
                            .as_ref()
                            .map(ToString::to_string)
                            .unwrap_or_else(|| "stream reader interruption".to_string());
                        format!("failed to terminate child after rejecting output: {rejection}")
                    }),
                Err(read_error) => terminate_and_reap(&mut child, limits.is_some())
                    .map(|status| {
                        if let Some(capture) = captured.as_deref_mut() {
                            capture.status = Some(status);
                        }
                        (status, ExecStats::default())
                    })
                    .map_err(anyhow::Error::from)
                    .with_context(|| {
                        format!(
                            "failed to terminate child after streaming read failed: {read_error}"
                        )
                    })
                    .and_then(|_| Err(read_error.into())),
                }
            };
            if let Some(capture) = captured.as_deref_mut() {
                if let Ok((status, _)) = &status {
                    capture.status = Some(*status);
                } else if capture.cleanup_error.is_none() {
                    // A read failure with a known reap is already represented
                    // separately. Otherwise final wait/cleanup was unavailable.
                    if capture.status.is_none() {
                        capture.cleanup_error =
                            status.as_ref().err().map(|error| format!("{error:#}"));
                    }
                }
            }
            if let Some(argfile) = argfile {
                close_tempfile_and_log_error(argfile);
            }
            status
        })();
        let wait_result = if captured.is_some() {
            wait_result
        } else {
            wait_result.with_context(|| ProcessError::could_not_execute(self))
        };

        if let Ok((_, stats)) = &wait_result {
            collected_stats = *stats;
        }
        // Restore only after child and observer ownership has been discharged.
        // A caught signal must never be converted into a successful result.
        let wait_result = match signal_guard.as_mut().map(StreamingSignals::restore) {
            Some(Err(signal_error)) => {
                if let Some(capture) = captured.as_deref_mut() {
                    let previous = capture.cleanup_error.take();
                    capture.cleanup_error = Some(match previous {
                        Some(previous) => format!("{previous}; signal restoration: {signal_error}"),
                        None => signal_error.to_string(),
                    });
                }
                Err(match wait_result {
                    Ok(_) => anyhow::Error::from(signal_error),
                    Err(error) => error.context(signal_error.to_string()),
                })
            }
            _ => wait_result,
        };
        let (status, stats) = match wait_result {
            Ok(captured) => captured,
            // The process may have failed to spawn.
            Err(e) => return (collected_stats, Err(e)),
        };

        let output = Output {
            status,
            stdout,
            stderr,
        };

        let result = {
            let to_print = if capture_output { Some(&output) } else { None };
            if let Some(e) = callback_error {
                let cx = ProcessError::new(
                    &format!("failed to parse process output: {}", self),
                    Some(output.status),
                    to_print,
                );
                Err(anyhow::Error::new(cx).context(e))
            } else if !output.status.success() {
                Err(anyhow::Error::new(ProcessError::new(
                    &format!("process didn't exit successfully: {}", self),
                    Some(output.status),
                    to_print,
                )))
            } else {
                Ok(())
            }
        };

        (stats, result.map(|()| output))
    }

    /// Builds the command with an `@<path>` argfile that contains all the
    /// arguments. This is primarily served for rustc/rustdoc command family.
    fn build_command_with_argfile(&self) -> io::Result<(Command, NamedTempFile)> {
        use std::io::Write as _;

        if self.action_sandbox.is_some() {
            return Err(io::Error::new(
                io::ErrorKind::Unsupported,
                "confined action cannot read an undeclared argument file",
            ));
        }

        let mut tmp = tempfile::Builder::new()
            .prefix("cargo-argfile.")
            .tempfile()?;

        let mut arg = OsString::from("@");
        arg.push(tmp.path());
        let mut cmd = self.build_command_without_args();
        cmd.arg(arg);
        tracing::debug!("created argfile at {} for {self}", tmp.path().display());

        let cap = self.get_args().map(|arg| arg.len() + 1).sum::<usize>();
        let mut buf = Vec::with_capacity(cap);
        for arg in &self.args {
            let arg = arg.to_str().ok_or_else(|| {
                io::Error::new(
                    io::ErrorKind::Other,
                    format!(
                        "argument for argfile contains invalid UTF-8 characters: `{}`",
                        arg.to_string_lossy()
                    ),
                )
            })?;
            if arg.contains('\n') {
                return Err(io::Error::new(
                    io::ErrorKind::Other,
                    format!("argument for argfile contains newlines: `{arg}`"),
                ));
            }
            writeln!(buf, "{arg}")?;
        }
        tmp.write_all(&mut buf)?;
        Ok((cmd, tmp))
    }

    /// Builds a command from `ProcessBuilder` for everything but not `args`.
    fn build_command_without_args(&self) -> Command {
        let mut command = {
            let mut iter = self.wrappers.iter().rev().chain(once(&self.program));
            let mut cmd = if let Some(sandbox) = &self.action_sandbox {
                let mut cmd = Command::new("/usr/bin/sandbox-exec");
                cmd.arg("-p").arg(sandbox.profile());
                cmd
            } else {
                Command::new(iter.next().expect("at least one `program` exists"))
            };
            cmd.args(iter);
            cmd
        };
        #[cfg(unix)]
        if let Some(arg0) = self.get_arg0() {
            use std::os::unix::process::CommandExt as _;
            command.arg0(arg0);
        }
        #[cfg(unix)]
        // Trust: the only moment a per-child descriptor can be granted is
        // between fork and exec — before it, the parent would be handing the
        // capability to every future child; after it, the child is already
        // running.
        if !self.inherited_fds.is_empty() || !self.exec_guard_fds.is_empty() {
            use std::os::unix::process::CommandExt as _;

            let inherited_fds = self.inherited_fds.clone();
            let exec_guard_fds = self.exec_guard_fds.clone();
            unsafe {
                command.pre_exec(move || {
                    // Trust: capturing the guard descriptors in the command
                    // keeps the parent-side capability endpoints live through fork. They
                    // retain CLOEXEC and therefore disappear from the child
                    // image. Do not otherwise touch them in the post-fork path.
                    let _ = &exec_guard_fds;
                    for fd in &inherited_fds {
                        let fd = fd.as_raw_fd();
                        let flags = libc::fcntl(fd, libc::F_GETFD);
                        if flags < 0 {
                            return Err(io::Error::last_os_error());
                        }
                        if libc::fcntl(fd, libc::F_SETFD, flags & !libc::FD_CLOEXEC) < 0 {
                            return Err(io::Error::last_os_error());
                        }
                    }
                    Ok(())
                });
            }
        }
        if let Some(cwd) = self.get_cwd() {
            command.current_dir(cwd);
        }
        if let Some(snapshot) = &self.environment_snapshot {
            command.env_clear().envs(snapshot.variables());
        }
        for (k, v) in &self.env {
            match *v {
                Some(ref v) => {
                    command.env(k, v);
                }
                None => {
                    command.env_remove(k);
                }
            }
        }
        if let Some(ref c) = self.jobserver {
            c.configure(&mut command);
        } else {
            command.env_remove(jobserver_utils::DESCENDANT_HANDOFF_ENV);
        }
        command
    }

    /// Converts `ProcessBuilder` into a `std::process::Command`, and handles
    /// the jobserver, if present.
    ///
    /// Note that this method doesn't take argfile fallback into account. The
    /// caller should handle it by themselves.
    pub fn build_command(&self) -> Command {
        let mut command = self.build_command_without_args();
        for arg in &self.args {
            command.arg(arg);
        }
        command
    }

    /// Wraps an existing command with the provided wrapper, if it is present and valid.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use cargo_util::ProcessBuilder;
    /// // Running this would execute `rustc`
    /// let cmd = ProcessBuilder::new("rustc");
    ///
    /// // Running this will execute `sccache rustc`
    /// let cmd = cmd.wrapped(Some("sccache"));
    /// ```
    pub fn wrapped(mut self, wrapper: Option<impl AsRef<OsStr>>) -> Self {
        if let Some(wrapper) = wrapper.as_ref() {
            let wrapper = wrapper.as_ref();
            if !wrapper.is_empty() {
                self.wrappers.push(wrapper.to_os_string());
            }
        }
        self
    }
}

// Trust: inspect only this fixed prefix when explaining a rejected line. Format
// bytes directly: UTF-8 decoding, JSON parsing, or copying the entire diagnostic
// would defeat the refusal's memory bound. ASCII escaping also prevents child
// control bytes, newlines, bidi text, or invalid UTF-8 from altering the error.
// Each input byte writes at most four printable ASCII bytes, with no allocation
// in this formatter. This context is diagnostic only and never reaches a line
// callback or acquires evidence authority.
const STREAMING_LINE_PREFIX_BYTES: usize = 256;

struct StreamingLinePrefix<'a>(&'a [u8]);

impl fmt::Display for StreamingLinePrefix<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for byte in &self.0[..self.0.len().min(STREAMING_LINE_PREFIX_BYTES)] {
            fmt::Display::fmt(&byte.escape_ascii(), f)?;
        }
        Ok(())
    }
}

/// Trust: what begins a line `StreamingOutputLimits::with_long_lines_cut`
/// cut. It ends with a space and begins with `[`, so the line it opens
/// matches no prefix the child wrote.
pub fn long_line_mark(max_line_bytes: usize) -> String {
    format!("[line cut: it is longer than {max_line_bytes} bytes] ")
}

// Trust: rewrites `data` (complete lines, then at most one unterminated
// tail) so that no line in it is longer than `max_line_bytes`. A longer line
// becomes the mark and the line's first bytes, `max_line_bytes` together. A
// longer unterminated tail is cut the same way and ended there; `dropping`
// then says the rest of that line, up to its newline, is still to come and
// is to be discarded. Returns whether `data` changed.
fn cut_long_lines(data: &mut Vec<u8>, max_line_bytes: usize, dropping: &mut bool) -> bool {
    if !*dropping && oversized_line(data, max_line_bytes).is_none() {
        return false;
    }
    let mark = long_line_mark(max_line_bytes);
    let keep = max_line_bytes - mark.len();
    let mut rest = &data[..];
    if *dropping {
        match rest.iter().position(|byte| *byte == b'\n') {
            Some(newline) => {
                rest = &rest[newline + 1..];
                *dropping = false;
            }
            None => {
                data.clear();
                return true;
            }
        }
    }
    let mut kept = Vec::new();
    while !rest.is_empty() {
        let newline = rest.iter().position(|byte| *byte == b'\n');
        let line = &rest[..newline.unwrap_or(rest.len())];
        if line.len() > max_line_bytes {
            kept.extend_from_slice(mark.as_bytes());
            kept.extend_from_slice(&line[..keep]);
            // An unterminated line is ended here; its rest is dropped as it comes.
            kept.push(b'\n');
            *dropping = newline.is_none();
        } else {
            kept.extend_from_slice(line);
            if newline.is_some() {
                kept.push(b'\n');
            }
        }
        rest = &rest[line.len() + usize::from(newline.is_some())..];
    }
    *data = kept;
    true
}

// Trust: retain the actual offending slice, rather than only its length, so
// diagnostics name its bounded prefix even when a read contains earlier lines.
fn oversized_line(bytes: &[u8], max_line_bytes: usize) -> Option<&[u8]> {
    let mut line_start = 0;
    for (index, byte) in bytes.iter().enumerate() {
        if *byte == b'\n' {
            let line_bytes = index - line_start;
            if line_bytes > max_line_bytes {
                return Some(&bytes[line_start..index]);
            }
            line_start = index + 1;
        }
    }
    let trailing_bytes = bytes.len() - line_start;
    (trailing_bytes > max_line_bytes).then_some(&bytes[line_start..])
}

/// Trust: an isolated process group is what makes a rejection enforceable — a
/// child that spawned descendants holding its pipes cannot otherwise be stopped
/// without also killing unrelated work.
fn configure_streaming_child(command: &mut Command, isolated_process_group: bool) {
    #[cfg(unix)]
    if isolated_process_group {
        use std::os::unix::process::CommandExt as _;
        command.process_group(0);
    }

    #[cfg(not(unix))]
    let _ = (command, isolated_process_group);
}

// Trust: one signal epoch shared with the original-group observer and native harnesses.
#[cfg(all(test, any(target_os = "linux", target_os = "macos")))]
use trust_resource_provenance::process::OWNED_GROUP_SIGNALS as STREAMING_SIGNALS;
#[cfg(unix)]
use trust_resource_provenance::process::{
    ChildSignalLease as StreamingSignals, pending_child_signal as pending_streaming_signal,
};
#[cfg(not(unix))]
struct StreamingSignals;
#[cfg(not(unix))]
impl StreamingSignals {
    fn install(enabled: bool) -> io::Result<Option<Self>> {
        if enabled {
            Err(io::Error::new(
                io::ErrorKind::Unsupported,
                "streaming signal cleanup is unsupported",
            ))
        } else {
            Ok(None)
        }
    }
    fn restore(&mut self) -> io::Result<()> {
        Ok(())
    }
}
#[cfg(not(unix))]
fn pending_streaming_signal() -> u32 {
    0
}

/// Trust: keeps one cancellation epoch alive across a group of native jobs.
/// Concurrent supervised children observe the same signal and retain their own
/// process-group custody. The final owner restores the original handlers.
pub struct StreamingProcessScope {
    signals: StreamingSignals,
    cancel: Arc<std::sync::atomic::AtomicBool>,
}

// Trust: authenticated launchers share cancellation and unreaped-child custody.
#[cfg(any(target_os = "linux", target_os = "macos"))]
mod isolated_child;
#[cfg(any(target_os = "linux", target_os = "macos"))]
pub use isolated_child::{OwnedIsolatedChild, PreparedIsolatedChild};

impl StreamingProcessScope {
    pub fn new() -> io::Result<Self> {
        Ok(Self {
            signals: StreamingSignals::install(true)?.expect("enabled signal scope"),
            cancel: Arc::new(std::sync::atomic::AtomicBool::new(false)),
        })
    }

    pub fn interrupted(&self) -> bool {
        pending_streaming_signal() != 0 || self.cancel.load(std::sync::atomic::Ordering::Acquire)
    }

    /// Trust: the number of a signal this process caught while the scope was
    /// open, if it caught one (the lowest, of several). `interrupted` is
    /// also true after `cancel`, which is the owner's own stop; a caller
    /// that reports why a run ended needs to know which of the two it was.
    pub fn signalled(&self) -> Option<u32> {
        // The pending signals are a mask with bit `n` set for signal `n`.
        let mask = pending_streaming_signal();
        (mask != 0).then(|| mask.trailing_zeros())
    }

    /// Cancel the owned supervised children without signalling unrelated PIDs.
    pub fn cancel(&self) {
        self.cancel
            .store(true, std::sync::atomic::Ordering::Release);
    }

    pub fn finish(mut self) -> io::Result<()> {
        self.signals.restore()
    }
}

// Trust: this guard is the sole reaper while the optional observer exists.
// The observer never calls wait/try_wait and reports loss of custody without
// signalling a numeric PID that might already have been reused.
struct StreamingChildExit<'a> {
    child: &'a mut Child,
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    cancel: Arc<std::sync::atomic::AtomicBool>,
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    wake: std::os::unix::net::UnixStream,
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    observer: Option<std::thread::JoinHandle<ChildExitObservation>>,
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    observed: Option<ChildExitObservation>,
    finished: bool,
    // Trust: keep capture observations even when finish returns a cleanup error.
    reaped_status: Option<ExitStatus>,
    reaped_stats: ExecStats,
    capture_rusage: bool,
    stream_ends: [CaptureStreamEnd; 2],
}

#[cfg(any(target_os = "linux", target_os = "macos"))]
use trust_resource_provenance::process::OwnedGroupExit as ChildExitObservation;

impl<'a> StreamingChildExit<'a> {
    fn start(
        child: &'a mut Child,
        enabled: bool,
        execution_cancel: Option<Arc<std::sync::atomic::AtomicBool>>,
        mut captured: Option<&mut CapturedProcess>,
    ) -> io::Result<Option<Self>> {
        if !enabled {
            return Ok(None);
        }
        #[cfg(any(target_os = "linux", target_os = "macos"))]
        {
            use std::sync::atomic::AtomicBool;
            let setup = (|| {
                let pid = libc::pid_t::try_from(child.id())
                    .map_err(|_| io::Error::other("streaming child PID does not fit pid_t"))?;
                let (wake, mut notify) = std::os::unix::net::UnixStream::pair()?;
                let cancel = Arc::new(AtomicBool::new(false));
                let observer_cancel = Arc::clone(&cancel);
                let observer = std::thread::Builder::new()
                    .name("targo-stream-child-exit".into())
                    .spawn(move || {
                        let result = observe_streaming_child_exit(
                            pid,
                            &observer_cancel,
                            execution_cancel.as_deref(),
                        );
                        // A failed write still closes the owned socket, waking
                        // poll with HUP. The result remains in the join handle.
                        let _ = notify.write_all(&[1]);
                        result
                    })?;
                Ok((cancel, wake, observer))
            })();
            // A spawn failure created no observer; this caller still owns the
            // unreaped Child. Do not leave it running on this error path.
            return match setup {
                Ok((cancel, wake, observer)) => Ok(Some(Self {
                    child,
                    cancel,
                    wake,
                    observer: Some(observer),
                    observed: None,
                    finished: false,
                    reaped_status: None,
                    reaped_stats: ExecStats::default(),
                    capture_rusage: false,
                    stream_ends: [CaptureStreamEnd::Incomplete; 2],
                })),
                Err(error) => {
                    let cleanup = terminate_and_reap_observed(
                        child,
                        true,
                        captured.as_deref_mut().map(|capture| &mut capture.status),
                    );
                    if let Some(capture) = captured.as_deref_mut() {
                        match cleanup {
                            Ok(status) => capture.status = Some(status),
                            Err(cleanup) => capture.cleanup_error = Some(cleanup.to_string()),
                        }
                    }
                    Err(error)
                }
            };
        }
        #[cfg(not(any(target_os = "linux", target_os = "macos")))]
        Err(io::Error::new(
            io::ErrorKind::Unsupported,
            "streaming child-exit cleanup is unsupported",
        ))
    }

    #[cfg(any(target_os = "linux", target_os = "macos"))]
    fn join_observer(&mut self) {
        if let Some(observer) = self.observer.take() {
            self.observed = Some(observer.join().unwrap_or_else(|_| ChildExitObservation {
                exited: false,
                error: Some(io::Error::other("streaming child-exit observer panicked")),
            }));
        }
    }

    fn finish(&mut self, cancel: bool) -> io::Result<ExitStatus> {
        #[cfg(any(target_os = "linux", target_os = "macos"))]
        {
            if cancel {
                self.cancel
                    .store(true, std::sync::atomic::Ordering::Release);
            }
            self.join_observer();
            self.finished = true;
            let observed = self
                .observed
                .take()
                .expect("observer joined once before reap");
            if !observed.exited {
                // In particular ECHILD must not become kill/wait on a recycled
                // number. The lost-custody error is the only available result.
                return Err(observed
                    .error
                    .unwrap_or_else(|| io::Error::other("child-exit custody was lost")));
            }
            let status = if self.capture_rusage {
                let (status, stats) = imp::wait_with_resource_usage(self.child)?;
                self.reaped_stats = stats;
                status
            } else {
                self.child.wait()?
            };
            self.reaped_status = Some(status);
            return observed.error.map_or(Ok(status), Err);
        }
        #[cfg(not(any(target_os = "linux", target_os = "macos")))]
        {
            let _ = cancel;
            Err(io::Error::new(
                io::ErrorKind::Unsupported,
                "streaming child-exit cleanup is unsupported",
            ))
        }
    }

    #[cfg(any(target_os = "linux", target_os = "macos"))]
    fn read(
        &mut self,
        mut out: std::process::ChildStdout,
        mut err: std::process::ChildStderr,
        deadline: Option<Instant>,
        data: &mut dyn FnMut(bool, &mut Vec<u8>, bool) -> Read2Action,
    ) -> io::Result<Read2Action> {
        use std::io::Read as _;
        for fd in [out.as_raw_fd(), err.as_raw_fd()] {
            // SAFETY: both descriptors are owned by the reader for this call.
            let flags = unsafe { libc::fcntl(fd, libc::F_GETFL) };
            if flags == -1
                || unsafe { libc::fcntl(fd, libc::F_SETFL, flags | libc::O_NONBLOCK) } == -1
            {
                return Err(io::Error::last_os_error());
            }
        }
        let mut buffers = [Vec::new(), Vec::new()];
        let mut done = [false; 2];
        let mut exited = false;
        let mut fds = [
            libc::pollfd {
                fd: out.as_raw_fd(),
                events: libc::POLLIN,
                revents: 0,
            },
            libc::pollfd {
                fd: err.as_raw_fd(),
                events: libc::POLLIN,
                revents: 0,
            },
            libc::pollfd {
                fd: self.wake.as_raw_fd(),
                events: libc::POLLIN,
                revents: 0,
            },
        ];
        loop {
            if exited && done.iter().all(|done| *done) {
                return Ok(Read2Action::Continue);
            }
            let timeout = if exited {
                0 // Drain already-written bytes; never await an escaped holder.
            } else if let Some(deadline) = deadline {
                let left = deadline
                    .checked_duration_since(Instant::now())
                    .ok_or_else(|| {
                        io::Error::new(
                            io::ErrorKind::TimedOut,
                            "streaming process exceeded its wall-clock timeout",
                        )
                    })?;
                left.as_millis()
                    .saturating_add(1)
                    .min(libc::c_int::MAX as u128) as libc::c_int
            } else {
                -1
            };
            // SAFETY: fds is a live three-element pollfd array.
            let count = unsafe { libc::poll(fds.as_mut_ptr(), fds.len() as libc::nfds_t, timeout) };
            if count < 0 {
                let error = io::Error::last_os_error();
                if error.kind() == io::ErrorKind::Interrupted {
                    continue;
                }
                return Err(error);
            }
            if fds[2].revents != 0 {
                self.join_observer();
                let observation = self
                    .observed
                    .as_ref()
                    .expect("observer joined on notification");
                if let Some(error) = &observation.error {
                    return Err(io::Error::new(error.kind(), error.to_string()));
                }
                exited = observation.exited;
                fds[2].fd = -1;
            }
            if count == 0 && !exited {
                return Err(io::Error::new(
                    io::ErrorKind::TimedOut,
                    "streaming process exceeded its wall-clock timeout",
                ));
            }
            for index in 0..2 {
                if done[index] || (fds[index].revents == 0 && !(exited && count == 0)) {
                    continue;
                }
                let mut chunk = [0_u8; 64 * 1024];
                let read = if index == 0 {
                    out.read(&mut chunk)
                } else {
                    err.read(&mut chunk)
                };
                match read {
                    Ok(0) => {
                        done[index] = true;
                        self.stream_ends[index] = CaptureStreamEnd::Eof;
                    }
                    Ok(size) => {
                        buffers[index]
                            .try_reserve_exact(size)
                            .map_err(io::Error::other)?;
                        buffers[index].extend_from_slice(&chunk[..size]);
                    }
                    Err(error) if error.kind() == io::ErrorKind::WouldBlock => {
                        if !exited {
                            continue;
                        }
                        done[index] = true;
                        self.stream_ends[index] = CaptureStreamEnd::LeaderExitDrained;
                    }
                    Err(error) if error.kind() == io::ErrorKind::Interrupted => continue,
                    Err(error) => return Err(error),
                }
                if done[index] {
                    fds[index].fd = -1;
                }
                if data(index == 0, &mut buffers[index], done[index]) == Read2Action::Stop {
                    return Ok(Read2Action::Stop);
                }
            }
        }
    }

    #[cfg(not(any(target_os = "linux", target_os = "macos")))]
    fn read(
        &mut self,
        _out: std::process::ChildStdout,
        _err: std::process::ChildStderr,
        _deadline: Option<Instant>,
        _data: &mut dyn FnMut(bool, &mut Vec<u8>, bool) -> Read2Action,
    ) -> io::Result<Read2Action> {
        Err(io::Error::new(
            io::ErrorKind::Unsupported,
            "streaming child-exit cleanup is unsupported",
        ))
    }
}

impl Drop for StreamingChildExit<'_> {
    fn drop(&mut self) {
        if !self.finished {
            let _ = self.finish(true);
        }
    }
}

#[cfg(any(target_os = "linux", target_os = "macos"))]
fn ensure_streaming_wait_ownership() -> io::Result<()> {
    let mut action: libc::sigaction = unsafe { std::mem::zeroed() };
    // SAFETY: this only reads the process disposition into an owned buffer.
    if unsafe { libc::sigaction(libc::SIGCHLD, std::ptr::null(), &mut action) } != 0 {
        return Err(io::Error::last_os_error());
    }
    if action.sa_sigaction != libc::SIG_DFL || action.sa_flags & libc::SA_NOCLDWAIT != 0 {
        return Err(io::Error::other(
            "child-exit cleanup requires default SIGCHLD handling and unreaped child ownership",
        ));
    }
    Ok(())
}

#[cfg(any(target_os = "linux", target_os = "macos"))]
fn observe_streaming_child_exit(
    pid: libc::pid_t,
    cancel: &std::sync::atomic::AtomicBool,
    execution_cancel: Option<&std::sync::atomic::AtomicBool>,
) -> ChildExitObservation {
    observe_streaming_child_exit_with_poll(pid, cancel, execution_cancel, || false)
}

// Trust: both streaming and native harness children share the exact original
// group observer. These wrappers retain Cargo's cancellation/signal epoch.
#[cfg(unix)]
fn unreaped_streaming_child_exit(pid: libc::pid_t) -> io::Result<bool> {
    // SAFETY: every caller retains the original direct child without reaping.
    unsafe { trust_resource_provenance::process::unreaped_child_exit(pid) }
}

#[cfg(any(target_os = "linux", target_os = "macos"))]
fn observe_streaming_child_exit_with_poll(
    pid: libc::pid_t,
    cancel: &std::sync::atomic::AtomicBool,
    execution_cancel: Option<&std::sync::atomic::AtomicBool>,
    mut poll_cancel: impl FnMut() -> bool,
) -> ChildExitObservation {
    // SAFETY: the streaming/isolated owner retains this original direct child
    // and its spawn-created process group until after the returned observation.
    unsafe {
        trust_resource_provenance::process::observe_owned_group_exit(pid, || {
            let polled = poll_cancel();
            polled
                || cancel.load(std::sync::atomic::Ordering::Acquire)
                || execution_cancel
                    .is_some_and(|cancel| cancel.load(std::sync::atomic::Ordering::Acquire))
                || pending_streaming_signal() != 0
        })
    }
}

#[cfg(unix)]
fn stop_streaming_group(pid: libc::pid_t) -> io::Result<()> {
    // SAFETY: each caller still owns the exclusively unreaped original leader.
    unsafe { trust_resource_provenance::process::stop_owned_group(pid) }
}

fn terminate_and_reap(child: &mut Child, isolated_process_group: bool) -> io::Result<ExitStatus> {
    terminate_and_reap_observed(child, isolated_process_group, None)
}

fn terminate_and_reap_observed(
    child: &mut Child,
    isolated_process_group: bool,
    reaped_status: Option<&mut Option<ExitStatus>>,
) -> io::Result<ExitStatus> {
    let mut termination_error = None;

    #[cfg(not(unix))]
    let _ = isolated_process_group;

    #[cfg(unix)]
    if isolated_process_group {
        let child_pid = libc::c_int::try_from(child.id()).map_err(|_| {
            io::Error::other(format!("child pid {} does not fit in c_int", child.id()))
        })?;
        // The bounded streaming path creates the child as its own process-group
        // leader, so a negative PID reaches descendants that inherited either
        // output pipe. The unreaped leader keeps this PID from being reused
        // during the signal operation.
        if unsafe { libc::kill(-child_pid, libc::SIGKILL) } == -1 {
            let error = io::Error::last_os_error();
            if error.raw_os_error() != Some(libc::ESRCH) {
                termination_error = Some(error);
            }
        }
    }

    if let Err(error) = child.kill()
        && error.kind() != io::ErrorKind::InvalidInput
        && error.raw_os_error() != Some(libc_esrch())
        && termination_error.is_none()
    {
        termination_error = Some(error);
    }

    let status = child.wait()?;
    if let Some(observed) = reaped_status {
        *observed = Some(status);
    }
    if let Some(error) = termination_error {
        return Err(error);
    }
    Ok(status)
}

fn wait_for_streaming_child(
    child: &mut Child,
    deadline: Option<Instant>,
    isolated_process_group: bool,
) -> io::Result<ExitStatus> {
    wait_for_streaming_child_with_exit_check(child, deadline, isolated_process_group, |_| {})
}

fn wait_for_streaming_child_with_exit_check(
    child: &mut Child,
    deadline: Option<Instant>,
    isolated_process_group: bool,
    mut exit_check: impl FnMut(u32),
) -> io::Result<ExitStatus> {
    let Some(deadline) = deadline else {
        return child.wait();
    };
    #[cfg(unix)]
    let pid = libc::pid_t::try_from(child.id())
        .map_err(|_| io::Error::other("streaming child PID does not fit pid_t"))?;

    loop {
        #[cfg(unix)]
        let exited = match unreaped_streaming_child_exit(pid) {
            Ok(exited) => exited,
            Err(error) if error.kind() == io::ErrorKind::Interrupted => continue,
            // Lost wait custody never authorizes a numeric signal or retry.
            Err(error) => return Err(error),
        };
        #[cfg(not(unix))]
        let exited = child.try_wait()?.is_some();
        if exited {
            exit_check(child.id());
            if Instant::now() < deadline {
                return child.wait();
            }
            let timeout = io::Error::new(
                io::ErrorKind::TimedOut,
                "streaming process exceeded its wall-clock timeout",
            );
            #[cfg(unix)]
            let cleanup = {
                // The exited leader remains unreaped through the group
                // signal. Do not signal the already-exited leader itself.
                let stopped = if isolated_process_group {
                    stop_streaming_group(pid)
                } else {
                    Ok(())
                };
                child.wait().and_then(|status| stopped.map(|()| status))
            };
            #[cfg(not(unix))]
            let cleanup = terminate_and_reap(child, isolated_process_group);
            return match cleanup {
                Ok(_) => Err(timeout),
                Err(cleanup) => Err(io::Error::other(format!(
                    "{timeout}; additionally failed to clean up timed-out process group: {cleanup}"
                ))),
            };
        }
        let Some(remaining) = deadline.checked_duration_since(Instant::now()) else {
            let timeout = io::Error::new(
                io::ErrorKind::TimedOut,
                "streaming process exceeded its wall-clock timeout",
            );
            return match terminate_and_reap(child, isolated_process_group) {
                Ok(_) => Err(timeout),
                Err(cleanup) => Err(io::Error::other(format!(
                    "{timeout}; additionally failed to terminate timed-out child: {cleanup}"
                ))),
            };
        };
        std::thread::sleep(remaining.min(Duration::from_millis(10)));
    }
}

#[cfg(unix)]
const fn libc_esrch() -> i32 {
    libc::ESRCH
}

#[cfg(not(unix))]
const fn libc_esrch() -> i32 {
    // Windows does not expose an errno-style ESRCH through Child::kill.
    i32::MIN
}

#[derive(Clone, Debug)]
pub enum Stdio {
    Piped,
    Inherit,
    Null,
}

impl Stdio {
    fn to_std(&self) -> std::process::Stdio {
        match self {
            Self::Piped => std::process::Stdio::piped(),
            Self::Inherit => std::process::Stdio::inherit(),
            Self::Null => std::process::Stdio::null(),
        }
    }
}

/// Forces the command to use `@path` argfile.
///
/// You should set `__CARGO_TEST_FORCE_ARGFILE` to enable this.
fn debug_force_argfile(retry_enabled: bool) -> bool {
    retry_enabled && env::var("__CARGO_TEST_FORCE_ARGFILE").is_ok()
}

/// Creates new pipes for stderr, stdout, and optionally stdin.
fn piped(cmd: &mut Command, pipe_stdin: bool) -> &mut Command {
    use std::process::Stdio;

    cmd.stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .stdin(if pipe_stdin {
            Stdio::piped()
        } else {
            Stdio::null()
        })
}

fn close_tempfile_and_log_error(file: NamedTempFile) {
    file.close().unwrap_or_else(|e| {
        tracing::warn!("failed to close temporary file: {e}");
    });
}

#[cfg(unix)]
mod imp {
    use super::{ProcessBuilder, ProcessError, close_tempfile_and_log_error, debug_force_argfile};
    #[cfg(target_os = "linux")]
    use anyhow::Context as _;
    use anyhow::Result;
    use std::io;
    #[cfg(target_os = "linux")]
    use std::mem::MaybeUninit;
    #[cfg(target_os = "linux")]
    use std::os::fd::{AsRawFd as _, FromRawFd as _, OwnedFd};
    use std::os::unix::process::{CommandExt, ExitStatusExt};
    use std::process::ExitStatus;
    #[cfg(target_os = "linux")]
    use std::process::{Child, Command};
    #[cfg(target_os = "linux")]
    use std::sync::atomic::{AtomicBool, AtomicI32, AtomicU32, Ordering};

    /// The signals a supervisor catches while its target runs. All but the
    /// keyboard ones are forwarded to the target (`forwarded_to_target`).
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    const SUPERVISED_SIGNALS: &[libc::c_int] = &[
        libc::SIGHUP,
        libc::SIGINT,
        libc::SIGQUIT,
        libc::SIGUSR1,
        libc::SIGUSR2,
        libc::SIGALRM,
        libc::SIGTERM,
    ];

    /// Trust (T14c): whether a caught signal is sent on to the target.
    ///
    /// SIGINT and SIGQUIT are not. They are keyboard signals: a terminal sends
    /// them to its whole foreground process group, and a job-control parent
    /// (a shell, aterm's release cutter) sends them to the group as well. The
    /// target runs in the supervisor's group, so it has its own copy already,
    /// and forwarding one made a single Ctrl-C arrive twice (which a program
    /// that escalates on a second interrupt reads as two). The supervisor
    /// keeps a handler for them, so it outlives the interrupt and ends the
    /// way its target does, exactly as `system(3)` ignores them while it
    /// waits. The one difference from an exec replacement: a SIGINT or SIGQUIT
    /// sent to the supervisor's pid alone does not reach the target; signal
    /// the group, or send SIGTERM, which is forwarded.
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    const fn forwarded_to_target(signal: libc::c_int) -> bool {
        signal != libc::SIGINT && signal != libc::SIGQUIT
    }
    #[cfg(target_os = "linux")]
    static SUPERVISED_EXEC_ACTIVE: AtomicBool = AtomicBool::new(false);
    #[cfg(target_os = "linux")]
    static SUPERVISED_CHILD_PIDFD: AtomicI32 = AtomicI32::new(-1);
    #[cfg(target_os = "linux")]
    static PENDING_SUPERVISED_SIGNALS: AtomicU32 = AtomicU32::new(0);

    #[cfg(target_os = "linux")]
    const fn supervised_signal_bit(signal: libc::c_int) -> u32 {
        if signal > 0 && signal < u32::BITS as libc::c_int {
            1_u32 << signal
        } else {
            0
        }
    }

    #[cfg(target_os = "linux")]
    unsafe extern "C" fn forward_supervised_exec_signal(signal: libc::c_int) {
        let bit = supervised_signal_bit(signal);
        if bit == 0 || !forwarded_to_target(signal) {
            return;
        }
        PENDING_SUPERVISED_SIGNALS.fetch_or(bit, Ordering::SeqCst);
        let pidfd = SUPERVISED_CHILD_PIDFD.load(Ordering::SeqCst);
        if pidfd >= 0 && PENDING_SUPERVISED_SIGNALS.fetch_and(!bit, Ordering::SeqCst) & bit != 0 {
            // SAFETY: the signal handler performs only lock-free atomics, raw
            // TLS errno access, and one raw system call; it restores errno
            // before returning. Once published, the descriptor remains open
            // through process exit (and is deliberately leaked on a returnable
            // error) so an already-running handler cannot observe fd reuse.
            unsafe {
                let saved_errno = *libc::__errno_location();
                libc::syscall(
                    libc::SYS_pidfd_send_signal,
                    pidfd,
                    signal,
                    std::ptr::null::<libc::siginfo_t>(),
                    0_u32,
                );
                *libc::__errno_location() = saved_errno;
            }
        }
    }

    #[cfg(target_os = "linux")]
    struct SupervisedSignalHandlers {
        previous: Vec<(libc::c_int, libc::sigaction)>,
        child_pidfd: Option<OwnedFd>,
        restored: bool,
    }

    #[cfg(target_os = "linux")]
    impl SupervisedSignalHandlers {
        fn install() -> io::Result<Self> {
            if SUPERVISED_EXEC_ACTIVE
                .compare_exchange(false, true, Ordering::SeqCst, Ordering::SeqCst)
                .is_err()
            {
                return Err(io::Error::other(
                    "a supervised exec replacement is already active",
                ));
            }
            SUPERVISED_CHILD_PIDFD.store(-1, Ordering::SeqCst);
            PENDING_SUPERVISED_SIGNALS.store(0, Ordering::SeqCst);

            let mut handlers = Self {
                previous: Vec::with_capacity(SUPERVISED_SIGNALS.len()),
                child_pidfd: None,
                restored: false,
            };
            for &signal in SUPERVISED_SIGNALS {
                // SAFETY: zero is a valid initial representation for sigaction;
                // sigemptyset initializes its mask before installation.
                let mut action: libc::sigaction = unsafe { std::mem::zeroed() };
                action.sa_sigaction = forward_supervised_exec_signal as *const () as usize;
                action.sa_flags = libc::SA_RESTART;
                // SAFETY: action owns a valid sigset_t output buffer.
                if unsafe { libc::sigemptyset(&mut action.sa_mask) } != 0 {
                    let error = io::Error::last_os_error();
                    handlers.restore_best_effort();
                    return Err(error);
                }
                let mut previous = MaybeUninit::<libc::sigaction>::uninit();
                // SAFETY: both pointers name correctly sized sigaction
                // structures for this process.
                if unsafe { libc::sigaction(signal, &action, previous.as_mut_ptr()) } != 0 {
                    let error = io::Error::last_os_error();
                    handlers.restore_best_effort();
                    return Err(error);
                }
                // SAFETY: successful sigaction initialized the old action.
                handlers
                    .previous
                    .push((signal, unsafe { previous.assume_init() }));
            }
            Ok(handlers)
        }

        fn publish_child(&mut self, pidfd: OwnedFd) {
            let descriptor = pidfd.as_raw_fd();
            self.child_pidfd = Some(pidfd);
            SUPERVISED_CHILD_PIDFD.store(descriptor, Ordering::SeqCst);
            let pending = PENDING_SUPERVISED_SIGNALS.swap(0, Ordering::SeqCst);
            for &signal in SUPERVISED_SIGNALS {
                if pending & supervised_signal_bit(signal) != 0 {
                    // SAFETY: pidfd remains owned by the caller throughout
                    // supervision, and pidfd_send_signal binds delivery to the
                    // captured child rather than a reusable numeric PID.
                    unsafe {
                        libc::syscall(
                            libc::SYS_pidfd_send_signal,
                            descriptor,
                            signal,
                            std::ptr::null::<libc::siginfo_t>(),
                            0_u32,
                        );
                    }
                }
            }
        }

        fn child_ignored_signals(&self) -> u32 {
            self.previous
                .iter()
                .filter(|(_, action)| action.sa_sigaction == libc::SIG_IGN)
                .fold(0, |signals, (signal, _)| {
                    signals | supervised_signal_bit(*signal)
                })
        }

        fn restore(&mut self) -> io::Result<()> {
            if self.restored {
                return Ok(());
            }
            let mut first_error = None;
            for (signal, action) in self.previous.iter().rev() {
                // SAFETY: action is the exact initialized disposition returned
                // by the matching successful sigaction installation.
                if unsafe { libc::sigaction(*signal, action, std::ptr::null_mut()) } != 0
                    && first_error.is_none()
                {
                    first_error = Some(io::Error::last_os_error());
                }
            }
            self.restored = true;
            SUPERVISED_CHILD_PIDFD.store(-1, Ordering::SeqCst);
            SUPERVISED_EXEC_ACTIVE.store(false, Ordering::SeqCst);
            if let Some(error) = first_error {
                Err(error)
            } else {
                Ok(())
            }
        }

        fn restore_best_effort(&mut self) {
            let _ = self.restore();
        }
    }

    #[cfg(target_os = "linux")]
    impl Drop for SupervisedSignalHandlers {
        fn drop(&mut self) {
            self.restore_best_effort();
            if let Some(pidfd) = self.child_pidfd.take() {
                // A signal handler which loaded this raw descriptor before
                // restoration may still be running on another thread. There
                // is no async-signal-safe join protocol here, so preserving the
                // process-bound pidfd until process exit is safer than closing
                // it into the descriptor-reuse race.
                std::mem::forget(pidfd);
            }
        }
    }

    #[cfg(target_os = "linux")]
    fn prepare_supervised_child(
        command: &mut Command,
        parent_pid: libc::pid_t,
        ignored_signals: u32,
    ) {
        // SAFETY: after fork the callback performs only async-signal-safe raw
        // syscalls, reads copied integers/static data, and constructs an
        // io::Error from thread-local errno if setup fails.
        unsafe {
            command.pre_exec(move || {
                // PR_SET_PDEATHSIG prevents an abrupt parent death, including
                // uncatchable SIGKILL, from orphaning the launched program.
                // Rechecking getppid after prctl closes the race in which the
                // parent died just before setup. SIGSTOP does not kill the
                // parent and is intentionally left to ordinary process-group
                // job control rather than claimed as a closed death gap.
                if libc::prctl(libc::PR_SET_PDEATHSIG, libc::SIGKILL) != 0 {
                    return Err(io::Error::last_os_error());
                }
                if libc::getppid() != parent_pid {
                    libc::_exit(128 + libc::SIGKILL);
                }
                for &signal in SUPERVISED_SIGNALS {
                    let mut action: libc::sigaction = std::mem::zeroed();
                    action.sa_sigaction = if ignored_signals & supervised_signal_bit(signal) != 0 {
                        libc::SIG_IGN
                    } else {
                        libc::SIG_DFL
                    };
                    if libc::sigemptyset(&mut action.sa_mask) != 0
                        || libc::sigaction(signal, &action, std::ptr::null_mut()) != 0
                    {
                        return Err(io::Error::last_os_error());
                    }
                }
                Ok(())
            });
        }
    }

    #[cfg(target_os = "linux")]
    fn open_child_pidfd(child: &Child) -> io::Result<OwnedFd> {
        let pid = libc::pid_t::try_from(child.id())
            .map_err(|_| io::Error::other("child pid does not fit Linux pid_t"))?;
        // SAFETY: pidfd_open takes the copied PID and zero flags. The returned
        // descriptor is checked before ownership is constructed.
        let descriptor = unsafe { libc::syscall(libc::SYS_pidfd_open, pid, 0_u32) };
        if descriptor < 0 {
            return Err(io::Error::last_os_error());
        }
        let descriptor = libc::c_int::try_from(descriptor)
            .map_err(|_| io::Error::other("pidfd descriptor does not fit c_int"))?;
        // SAFETY: successful pidfd_open returned one new owned descriptor.
        Ok(unsafe { OwnedFd::from_raw_fd(descriptor) })
    }

    #[cfg(target_os = "linux")]
    fn spawn_supervised(
        process_builder: &ProcessBuilder,
        parent_pid: libc::pid_t,
        ignored_signals: u32,
    ) -> io::Result<(Child, Option<tempfile::NamedTempFile>)> {
        if debug_force_argfile(process_builder.retry_with_argfile) {
            let (mut command, argfile) = process_builder.build_command_with_argfile()?;
            prepare_supervised_child(&mut command, parent_pid, ignored_signals);
            return command.spawn().map(|child| (child, Some(argfile)));
        }

        let mut command = process_builder.build_command();
        prepare_supervised_child(&mut command, parent_pid, ignored_signals);
        match command.spawn() {
            Ok(child) => Ok((child, None)),
            Err(error) if process_builder.should_retry_with_argfile(&error) => {
                let (mut command, argfile) = process_builder.build_command_with_argfile()?;
                prepare_supervised_child(&mut command, parent_pid, ignored_signals);
                command.spawn().map(|child| (child, Some(argfile)))
            }
            Err(error) => Err(error),
        }
    }

    #[cfg(target_os = "linux")]
    fn exit_like_supervised_child(status: ExitStatus) -> ! {
        // Trust (RL-64): nothing below drops an endpoint owner, and the signal
        // arm ends in a raised signal or `_exit`, which runs no exit handler:
        // remove this process's job-server folders here. The target has been
        // waited for and its scheduler retired, so nothing can still use them.
        jobserver_utils::remove_endpoint_directories();
        if let Some(code) = status.code() {
            std::process::exit(code);
        }
        if let Some(signal) = status.signal() {
            // SAFETY: this process is deliberately recreating exec-replacement
            // semantics. Defaulting, unblocking, and delivering the child's
            // terminating signal makes observers see the same wait status.
            unsafe {
                let mut action: libc::sigaction = std::mem::zeroed();
                action.sa_sigaction = libc::SIG_DFL;
                libc::sigemptyset(&mut action.sa_mask);
                libc::sigaction(signal, &action, std::ptr::null_mut());
                let mut mask: libc::sigset_t = std::mem::zeroed();
                libc::sigemptyset(&mut mask);
                libc::sigaddset(&mut mask, signal);
                libc::pthread_sigmask(libc::SIG_UNBLOCK, &mask, std::ptr::null_mut());
                libc::kill(libc::getpid(), signal);
                libc::_exit(128 + signal);
            }
        }
        std::process::exit(101);
    }

    pub fn exec_replace(process_builder: &ProcessBuilder) -> Result<()> {
        // Trust (RL-64): an exec that succeeds runs no exit handler and no
        // destructor, closes every job-server folder's descriptor and ends the
        // threads that served this process's endpoints, so the folders could
        // be neither used nor removed afterwards: remove them here. Targo
        // reaches this with its compiler-query endpoint parked in a static
        // (a `run` that owns no broker and gave its target no scheduler). An
        // exec that fails returns an error on which every caller ends the
        // process, which makes no further use of an endpoint.
        #[cfg(any(target_os = "linux", target_os = "macos"))]
        jobserver_utils::remove_endpoint_directories();
        let mut error;
        let mut file = None;
        if debug_force_argfile(process_builder.retry_with_argfile) {
            let (mut command, argfile) = process_builder.build_command_with_argfile()?;
            file = Some(argfile);
            error = command.exec()
        } else {
            let mut command = process_builder.build_command();
            error = command.exec();
            if process_builder.should_retry_with_argfile(&error) {
                let (mut command, argfile) = process_builder.build_command_with_argfile()?;
                file = Some(argfile);
                error = command.exec()
            }
        }
        if let Some(file) = file {
            close_tempfile_and_log_error(file);
        }

        Err(anyhow::Error::from(error).context(ProcessError::new(
            &format!("could not execute process {}", process_builder),
            None,
            None,
        )))
    }

    #[cfg(target_os = "linux")]
    pub fn exec_replace_supervised(
        process_builder: &ProcessBuilder,
        retire: impl FnOnce() -> Result<()>,
    ) -> Result<()> {
        let mut handlers = SupervisedSignalHandlers::install()
            .map_err(anyhow::Error::from)
            .context("failed to install supervised exec signal forwarding")?;
        let parent_pid = libc::pid_t::try_from(std::process::id())
            .map_err(|_| anyhow::anyhow!("supervisor pid does not fit Linux pid_t"))?;
        let ignored_signals = handlers.child_ignored_signals();
        let (mut child, argfile) = spawn_supervised(process_builder, parent_pid, ignored_signals)
            .map_err(|error| {
            anyhow::Error::from(error).context(ProcessError::new(
                &format!("could not execute process {}", process_builder),
                None,
                None,
            ))
        })?;
        let pidfd = match open_child_pidfd(&child) {
            Ok(pidfd) => pidfd,
            Err(error) => {
                let _ = child.kill();
                let _ = child.wait();
                return Err(anyhow::Error::from(error)
                    .context("failed to bind supervised exec replacement to a Linux pidfd"));
            }
        };
        handlers.publish_child(pidfd);
        let status = match child.wait() {
            Ok(status) => status,
            Err(error) => {
                let _ = child.kill();
                let _ = child.wait();
                let restore = handlers
                    .restore()
                    .context("failed to restore signal dispositions after wait failure");
                std::mem::forget(handlers);
                restore?;
                return Err(anyhow::Error::from(error).context(ProcessError::new(
                    &format!("could not wait for process {}", process_builder),
                    None,
                    None,
                )));
            }
        };
        if let Some(argfile) = argfile {
            close_tempfile_and_log_error(argfile);
        }
        // Keep the handlers and pidfd live through the non-returning status
        // recreation below. Restoring dispositions cannot synchronize with a
        // handler already running on the broker thread, while process exit
        // itself closes every descriptor without any reuse window.
        std::mem::forget(handlers);
        // Trust: process::exit does not run scheduling guard destructors.
        // The same explicit owner must settle actual credits first.
        if let Err(error) = retire() {
            return Err(crate::TargetExecutionError::new(status, error).into());
        }
        exit_like_supervised_child(status)
    }

    // Trust (T14c, DECISION_QUEUE T14-EXPORT-2): the macOS supervisor for a
    // `targo run` whose root owns the nested-unverified broker. macOS has no
    // pidfd, so a forwarded signal goes to the numeric pid, and only while the
    // child is known unreaped: the signal handler records the signal and wakes
    // a forwarding thread through a pipe (both async-signal-safe), the thread
    // sends under a lock, and the waiter takes that lock to retire the pid
    // after `waitid(WNOWAIT)` reports the exit and before reaping. A reaped
    // pid is therefore never signalled. macOS has no parent-death signal, so a
    // supervisor killed outright leaves its target running, as an exec
    // replacement's caller would see.
    /// The signals whose default action writes a crash report on macOS.
    #[cfg(target_os = "macos")]
    const CRASH_REPORT_SIGNALS: &[(libc::c_int, &str)] = &[
        (libc::SIGQUIT, "SIGQUIT"),
        (libc::SIGILL, "SIGILL"),
        (libc::SIGTRAP, "SIGTRAP"),
        (libc::SIGABRT, "SIGABRT"),
        (libc::SIGFPE, "SIGFPE"),
        (libc::SIGBUS, "SIGBUS"),
        (libc::SIGSEGV, "SIGSEGV"),
        (libc::SIGSYS, "SIGSYS"),
    ];

    #[cfg(target_os = "macos")]
    static MAC_SUPERVISED_ACTIVE: std::sync::atomic::AtomicBool =
        std::sync::atomic::AtomicBool::new(false);
    #[cfg(target_os = "macos")]
    static MAC_PENDING_SIGNALS: std::sync::atomic::AtomicU32 = std::sync::atomic::AtomicU32::new(0);
    #[cfg(target_os = "macos")]
    static MAC_WAKE_FD: std::sync::atomic::AtomicI32 = std::sync::atomic::AtomicI32::new(-1);
    /// The child's pid while it is unreaped; `None` once it is retired.
    #[cfg(target_os = "macos")]
    static MAC_SUPERVISED_CHILD: std::sync::Mutex<Option<libc::pid_t>> =
        std::sync::Mutex::new(None);

    #[cfg(target_os = "macos")]
    const fn mac_signal_bit(signal: libc::c_int) -> u32 {
        if signal > 0 && signal < u32::BITS as libc::c_int {
            1_u32 << signal
        } else {
            0
        }
    }

    #[cfg(target_os = "macos")]
    unsafe extern "C" fn record_supervised_signal(signal: libc::c_int) {
        let bit = mac_signal_bit(signal);
        if bit == 0 || !forwarded_to_target(signal) {
            return;
        }
        MAC_PENDING_SIGNALS.fetch_or(bit, std::sync::atomic::Ordering::SeqCst);
        let wake = MAC_WAKE_FD.load(std::sync::atomic::Ordering::SeqCst);
        if wake >= 0 {
            // SAFETY: only async-signal-safe calls (errno access and write(2)
            // of one byte); errno is restored before returning.
            unsafe {
                let saved = *libc::__error();
                let byte = 1_u8;
                libc::write(wake, (&byte as *const u8).cast(), 1);
                *libc::__error() = saved;
            }
        }
    }

    /// What the supervisor does once its child has ended.
    #[cfg(target_os = "macos")]
    #[derive(Debug, PartialEq, Eq)]
    pub(super) enum SupervisedExit {
        Code(i32),
        /// Re-raise the child's terminating signal.
        Signal(libc::c_int),
        /// Exit `128 + n` after one line, for a signal that writes a crash
        /// report.
        CrashSignal(i32, String),
    }

    #[cfg(target_os = "macos")]
    pub(super) fn supervised_exit(status: std::process::ExitStatus) -> SupervisedExit {
        use std::os::unix::process::ExitStatusExt as _;

        if let Some(code) = status.code() {
            return SupervisedExit::Code(code);
        }
        match status.signal() {
            Some(signal) => match CRASH_REPORT_SIGNALS.iter().find(|(s, _)| *s == signal) {
                Some((_, name)) => SupervisedExit::CrashSignal(
                    128 + signal,
                    format!(
                        "error: the target process was ended by {name}; exiting {} instead of raising it again",
                        128 + signal
                    ),
                ),
                None => SupervisedExit::Signal(signal),
            },
            None => SupervisedExit::Code(101),
        }
    }

    #[cfg(target_os = "macos")]
    fn exit_like_supervised_child(status: std::process::ExitStatus) -> ! {
        // Trust (RL-64): nothing below drops an endpoint owner, and the signal
        // arm ends in a raised signal or `_exit`, which runs no exit handler:
        // remove this process's job-server folders here. The target has been
        // waited for and its scheduler retired, so nothing can still use them.
        jobserver_utils::remove_endpoint_directories();
        match supervised_exit(status) {
            SupervisedExit::Code(code) => std::process::exit(code),
            #[expect(
                clippy::print_stderr,
                reason = "the exec supervisor has no Shell/logger context and must report the child crash to inherited stderr before exiting"
            )]
            SupervisedExit::CrashSignal(code, line) => {
                eprintln!("{line}");
                std::process::exit(code)
            }
            // SAFETY: recreate the exec-replacement wait status: default the
            // signal's disposition, unblock it, and deliver it to this thread.
            // `raise` is thread-directed, so the signal ends the process before
            // `_exit` runs; a process-directed `kill` may be delivered to
            // another thread after it, as macOS is free to do.
            SupervisedExit::Signal(signal) => unsafe {
                let mut action: libc::sigaction = std::mem::zeroed();
                action.sa_sigaction = libc::SIG_DFL;
                libc::sigemptyset(&mut action.sa_mask);
                libc::sigaction(signal, &action, std::ptr::null_mut());
                let mut mask: libc::sigset_t = std::mem::zeroed();
                libc::sigemptyset(&mut mask);
                libc::sigaddset(&mut mask, signal);
                libc::pthread_sigmask(libc::SIG_UNBLOCK, &mask, std::ptr::null_mut());
                libc::raise(signal);
                libc::_exit(128 + signal);
            },
        }
    }

    #[cfg(target_os = "macos")]
    fn install_mac_supervised_handlers() -> io::Result<u32> {
        use std::sync::atomic::Ordering;

        if MAC_SUPERVISED_ACTIVE
            .compare_exchange(false, true, Ordering::SeqCst, Ordering::SeqCst)
            .is_err()
        {
            return Err(io::Error::other(
                "a supervised exec replacement is already active",
            ));
        }
        let mut ignored = 0_u32;
        for &signal in SUPERVISED_SIGNALS {
            // SAFETY: zero is a valid initial sigaction; sigemptyset
            // initializes its mask before installation, and both pointers
            // name correctly sized sigaction structures.
            unsafe {
                let mut action: libc::sigaction = std::mem::zeroed();
                action.sa_sigaction = record_supervised_signal as *const () as usize;
                action.sa_flags = libc::SA_RESTART;
                if libc::sigemptyset(&mut action.sa_mask) != 0 {
                    return Err(io::Error::last_os_error());
                }
                let mut previous: libc::sigaction = std::mem::zeroed();
                if libc::sigaction(signal, &action, &mut previous) != 0 {
                    return Err(io::Error::last_os_error());
                }
                if previous.sa_sigaction == libc::SIG_IGN {
                    ignored |= mac_signal_bit(signal);
                }
            }
        }
        Ok(ignored)
    }

    #[cfg(target_os = "macos")]
    fn prepare_mac_supervised_child(command: &mut std::process::Command, ignored: u32) {
        // SAFETY: after fork the callback performs only sigemptyset/sigaction
        // on copied integers and static data.
        unsafe {
            command.pre_exec(move || {
                for &signal in SUPERVISED_SIGNALS {
                    let mut action: libc::sigaction = std::mem::zeroed();
                    action.sa_sigaction = if ignored & mac_signal_bit(signal) != 0 {
                        libc::SIG_IGN
                    } else {
                        libc::SIG_DFL
                    };
                    if libc::sigemptyset(&mut action.sa_mask) != 0
                        || libc::sigaction(signal, &action, std::ptr::null_mut()) != 0
                    {
                        return Err(io::Error::last_os_error());
                    }
                }
                Ok(())
            });
        }
    }

    #[cfg(target_os = "macos")]
    fn forward_mac_signals(wake_read: libc::c_int) {
        use std::sync::atomic::Ordering;

        let mut buffer = [0_u8; 64];
        loop {
            // SAFETY: `buffer` is writable for its length.
            let read = unsafe { libc::read(wake_read, buffer.as_mut_ptr().cast(), buffer.len()) };
            if read < 0 && io::Error::last_os_error().kind() == io::ErrorKind::Interrupted {
                continue;
            }
            if read <= 0 {
                return;
            }
            let child = MAC_SUPERVISED_CHILD
                .lock()
                .unwrap_or_else(|e| e.into_inner());
            let Some(pid) = *child else {
                continue;
            };
            let pending = MAC_PENDING_SIGNALS.swap(0, Ordering::SeqCst);
            for &signal in SUPERVISED_SIGNALS {
                if pending & mac_signal_bit(signal) != 0 {
                    // SAFETY: `pid` names this process's unreaped child: the
                    // waiter retires it under this lock before reaping.
                    unsafe {
                        libc::kill(pid, signal);
                    }
                }
            }
        }
    }

    #[cfg(target_os = "macos")]
    pub fn exec_replace_supervised(
        process_builder: &ProcessBuilder,
        retire: impl FnOnce() -> Result<()>,
    ) -> Result<()> {
        use anyhow::Context as _;
        use std::sync::atomic::Ordering;

        let ignored = install_mac_supervised_handlers()
            .context("failed to install supervised exec signal forwarding")?;
        let mut pipe = [-1 as libc::c_int; 2];
        // SAFETY: `pipe` is a two-element output array.
        if unsafe { libc::pipe(pipe.as_mut_ptr()) } != 0 {
            return Err(anyhow::Error::from(io::Error::last_os_error()))
                .context("failed to create the supervised exec wake pipe");
        }
        for descriptor in pipe {
            // SAFETY: `descriptor` was just returned by pipe(2).
            unsafe {
                libc::fcntl(descriptor, libc::F_SETFD, libc::FD_CLOEXEC);
            }
        }
        let [wake_read, wake_write] = pipe;
        MAC_WAKE_FD.store(wake_write, Ordering::SeqCst);
        std::thread::Builder::new()
            .name("targo-run-signal-forwarder".to_owned())
            .spawn(move || forward_mac_signals(wake_read))
            .context("failed to start the supervised exec signal forwarder")?;

        let spawned = if debug_force_argfile(process_builder.retry_with_argfile) {
            process_builder
                .build_command_with_argfile()
                .and_then(|(mut command, argfile)| {
                    prepare_mac_supervised_child(&mut command, ignored);
                    command.spawn().map(|child| (child, Some(argfile)))
                })
        } else {
            let mut command = process_builder.build_command();
            prepare_mac_supervised_child(&mut command, ignored);
            match command.spawn() {
                Ok(child) => Ok((child, None)),
                Err(error) if process_builder.should_retry_with_argfile(&error) => process_builder
                    .build_command_with_argfile()
                    .and_then(|(mut command, argfile)| {
                        prepare_mac_supervised_child(&mut command, ignored);
                        command.spawn().map(|child| (child, Some(argfile)))
                    }),
                Err(error) => Err(error),
            }
        };
        let (mut child, argfile) = spawned.map_err(|error| {
            anyhow::Error::from(error).context(ProcessError::new(
                &format!("could not execute process {}", process_builder),
                None,
                None,
            ))
        })?;
        let pid = libc::pid_t::try_from(child.id())
            .map_err(|_| anyhow::anyhow!("child pid does not fit pid_t"))?;
        *MAC_SUPERVISED_CHILD
            .lock()
            .unwrap_or_else(|e| e.into_inner()) = Some(pid);
        // Deliver any signal recorded before the child existed.
        let byte = 1_u8;
        // SAFETY: one-byte write to the pipe this function owns.
        unsafe {
            libc::write(wake_write, (&byte as *const u8).cast(), 1);
        }

        loop {
            // SAFETY: `info` is a zeroed output buffer; WNOWAIT leaves the
            // child unreaped, so its pid cannot be reused yet.
            let mut info: libc::siginfo_t = unsafe { std::mem::zeroed() };
            let result = unsafe {
                libc::waitid(
                    libc::P_PID,
                    pid as libc::id_t,
                    &mut info,
                    libc::WEXITED | libc::WNOWAIT,
                )
            };
            if result == 0 {
                break;
            }
            let error = io::Error::last_os_error();
            if error.kind() != io::ErrorKind::Interrupted {
                return Err(anyhow::Error::from(error).context(ProcessError::new(
                    &format!("could not wait for process {}", process_builder),
                    None,
                    None,
                )));
            }
        }
        // Retire the pid before reaping it: no signal is sent after this.
        *MAC_SUPERVISED_CHILD
            .lock()
            .unwrap_or_else(|e| e.into_inner()) = None;
        let status = child.wait().map_err(|error| {
            anyhow::Error::from(error).context(ProcessError::new(
                &format!("could not wait for process {}", process_builder),
                None,
                None,
            ))
        })?;
        if let Some(argfile) = argfile {
            close_tempfile_and_log_error(argfile);
        }
        // Trust: retain scheduling custody through the actual owning wait;
        // successful exit recreation cannot skip its explicit retirement.
        if let Err(error) = retire() {
            return Err(crate::TargetExecutionError::new(status, error).into());
        }
        exit_like_supervised_child(status)
    }

    pub fn command_line_too_big(err: &io::Error) -> bool {
        err.raw_os_error() == Some(libc::E2BIG)
    }

    /// Wait for this owned child, keeping its status, resident peak and CPU components.
    ///
    /// Use `wait4` to read `rusage.ru_maxrss` (the kernel's exact high-water mark),
    /// instead of the plain `waitpid` that [`std::process::Child::wait`] performs,
    /// which discards the `rusage`.
    #[cfg(not(any(target_os = "solaris", target_os = "illumos")))]
    pub fn wait_with_resource_usage(
        child: &mut std::process::Child,
    ) -> io::Result<(ExitStatus, super::ExecStats)> {
        let pid = child.id() as libc::pid_t;
        let mut status: libc::c_int = 0;
        // SAFETY: All rusage fields are safe to be initialized to zeroes (structs with i64 fields).
        let mut usage: libc::rusage = unsafe { std::mem::zeroed() };
        loop {
            // SAFETY: Pid is valid, usage and status are initialized.
            let ret = unsafe { libc::wait4(pid, &mut status, 0, &mut usage) };
            if ret == -1 {
                let err = io::Error::last_os_error();
                if err.kind() == io::ErrorKind::Interrupted {
                    tracing::debug!("Process `{pid}` was interrupted");
                    continue;
                }
                tracing::error!(
                    "Unexpected error while waiting for process `{pid}` to finish. {err}"
                );
                // ECHILD is lost owning custody, even when std cached an older
                // status. No second numeric-PID wait can establish accounting.
                return Err(err);
            }
            break;
        }
        // `ru_maxrss` is in kilobytes on Linux / FreeBSD and bytes on the Darwin family. Refs:
        // Linux: https://man7.org/linux/man-pages/man2/getrusage.2.html
        // Darwin: https://developer.apple.com/library/archive/documentation/System/Conceptual/ManPages_iPhoneOS/man2/getrusage.2.html
        // FreeBSD: https://man.freebsd.org/cgi/man.cgi?manpath=FreeBSD+14.0-RELEASE&query=getrusage&sektion=2
        let peak = if cfg!(target_os = "macos") {
            usage.ru_maxrss.max(0) as u64
        } else {
            (usage.ru_maxrss.max(0) as u64).saturating_mul(1024)
        };
        let span = |value: libc::timeval| {
            let seconds = u64::try_from(value.tv_sec).ok()?;
            let micros = u32::try_from(value.tv_usec)
                .ok()
                .filter(|v| *v < 1_000_000)?;
            Some(std::time::Duration::new(seconds, micros * 1000))
        };
        let cpu_times = (|| {
            Some(super::CpuTimes {
                user: span(usage.ru_utime)?,
                system: span(usage.ru_stime)?,
            })
        })();
        // We already reaped the child via `wait4`; `Child`'s `Drop` on Unix does
        // not wait, so simply dropping it here does not double-reap.
        Ok((
            ExitStatus::from_raw(status),
            super::ExecStats {
                peak_rss: Some(peak),
                cpu_times,
            },
        ))
    }

    /// Regular wait logic since Solaris/Illumos do not support `wait4`.
    #[cfg(any(target_os = "solaris", target_os = "illumos"))]
    pub fn wait_with_resource_usage(
        child: &mut std::process::Child,
    ) -> io::Result<(ExitStatus, super::ExecStats)> {
        child
            .wait()
            .map(|status| (status, super::ExecStats::default()))
    }
}

#[cfg(windows)]
mod imp {
    use super::{ProcessBuilder, ProcessError};
    use anyhow::Result;
    use std::io;
    use std::process::ExitStatus;
    use windows_sys::Win32::Foundation::{FALSE, TRUE};
    use windows_sys::Win32::System::Console::SetConsoleCtrlHandler;
    use windows_sys::core::BOOL;

    unsafe extern "system" fn ctrlc_handler(_: u32) -> BOOL {
        // Do nothing; let the child process handle it.
        TRUE
    }

    pub fn exec_replace(process_builder: &ProcessBuilder) -> Result<()> {
        unsafe {
            if SetConsoleCtrlHandler(Some(ctrlc_handler), TRUE) == FALSE {
                return Err(ProcessError::new("Could not set Ctrl-C handler.", None, None).into());
            }
        }

        // Just execute the process as normal.
        process_builder.exec()
    }

    pub fn command_line_too_big(err: &io::Error) -> bool {
        use windows_sys::Win32::Foundation::ERROR_FILENAME_EXCED_RANGE;
        err.raw_os_error() == Some(ERROR_FILENAME_EXCED_RANGE as i32)
    }

    pub fn wait_with_resource_usage(
        child: &mut std::process::Child,
    ) -> io::Result<(ExitStatus, super::ExecStats)> {
        use std::os::windows::io::AsRawHandle;
        use windows_sys::Win32::System::ProcessStatus::{
            GetProcessMemoryInfo, PROCESS_MEMORY_COUNTERS,
        };

        let status = child.wait()?;
        // SAFETY: All PROCESS_MEMORY_COUNTERS fields are safe to zero-initialize (plain integers).
        let mut counters: PROCESS_MEMORY_COUNTERS = unsafe { std::mem::zeroed() };
        counters.cb = std::mem::size_of::<PROCESS_MEMORY_COUNTERS>() as u32;
        // SAFETY: The handle is valid (owned by the not-yet-dropped `child`), `counters` is
        // initialized, and `cb` is set to its size as `GetProcessMemoryInfo` requires.
        if unsafe { GetProcessMemoryInfo(child.as_raw_handle() as _, &mut counters, counters.cb) }
            != 0
        {
            Ok((
                status,
                super::ExecStats {
                    peak_rss: Some(counters.PeakWorkingSetSize as u64),
                    ..super::ExecStats::default()
                },
            ))
        } else {
            Ok((status, super::ExecStats::default()))
        }
    }
}

// Trust: pins the bounded-streaming and descriptor-scoping behavior above.
// These spawn real children because the properties under test — a limit
// stopping an unbounded writer, a timeout reaping a wedged process group, a
// descriptor being absent from the child image — only exist at the process
// boundary.
#[cfg(test)]
mod tests {
    mod deadline_custody;
    #[test]
    fn resource_capabilities_are_redacted_without_changing_child_environment() {
        let mut process = ProcessBuilder::new("__metadata_only__");
        for key in [
            "TRUST_CPU_HANDOFF",
            "CARGO_JOBSERVER_HANDOFF",
            "ATERM_RESOURCE_JOB_V3",
        ] {
            process.env(key, "private-resource-sentinel");
        }
        process
            .env("VISIBLE_RESOURCE_LABEL", "ordinary-label")
            .display_env_vars();
        for rendered in [format!("{process}"), format!("{process:?}")] {
            assert!(!rendered.contains("private-resource-sentinel"));
            assert!(rendered.contains("ordinary-label"));
            assert!(rendered.contains("<redacted>"));
        }
        for key in [
            "TRUST_CPU_HANDOFF",
            "CARGO_JOBSERVER_HANDOFF",
            "ATERM_RESOURCE_JOB_V3",
        ] {
            assert_eq!(
                process.get_env(key).as_deref(),
                Some(std::ffi::OsStr::new("private-resource-sentinel"))
            );
        }
    }

    #[cfg(any(target_os = "linux", target_os = "macos"))]
    #[test]
    fn jobserver_handoff_overlay_matches_effective_and_spawn_environments() {
        let mut server = jobserver_utils::Jobserver::new(1).unwrap();
        server.enable_descendant_handoff().unwrap();
        let mut process = ProcessBuilder::new("__metadata_only__");
        process.env(
            jobserver_utils::DESCENDANT_HANDOFF_ENV,
            "untrusted-authored-endpoint",
        );
        process.inherit_jobserver(&server);
        let effective = process.get_effective_envs().unwrap();
        let actual = process.build_command();
        for key in ["CARGO_MAKEFLAGS", jobserver_utils::DESCENDANT_HANDOFF_ENV] {
            let key = std::ffi::OsStr::new(key);
            let configured = actual
                .get_envs()
                .find_map(|(name, value)| (name == key).then_some(value))
                .flatten();
            assert!(configured.is_some(), "selected pool supplied no {key:?}");
            assert_eq!(
                effective.get(key).map(|value| value.as_os_str()),
                configured
            );
        }
        assert_ne!(
            effective[std::ffi::OsStr::new(jobserver_utils::DESCENDANT_HANDOFF_ENV)],
            "untrusted-authored-endpoint"
        );
        assert_eq!(
            process.get_effective_envs().unwrap(),
            effective,
            "environment inspection changed the selected endpoint"
        );
        assert_eq!(
            server.client().available().unwrap(),
            1,
            "environment materialization consumed or minted a token"
        );
    }

    #[cfg(any(target_os = "linux", target_os = "macos"))]
    #[test]
    fn unselected_or_cleared_jobserver_never_exports_handoff() {
        let key = jobserver_utils::DESCENDANT_HANDOFF_ENV;
        let mut server = jobserver_utils::Jobserver::new(1).unwrap();
        server.enable_descendant_handoff().unwrap();
        for clear in [false, true] {
            let mut process = ProcessBuilder::new("__metadata_only__");
            process.env(key, "untrusted-authored-endpoint");
            if clear {
                process.inherit_jobserver(&server).clear_jobserver();
            }
            assert!(
                !process
                    .get_effective_envs()
                    .unwrap()
                    .contains_key(std::ffi::OsStr::new(key))
            );
            let command = process.build_command();
            assert!(
                command
                    .get_envs()
                    .any(|(name, value)| name == key && value.is_none())
            );
        }
        assert_eq!(server.client().available().unwrap(), 1);
    }

    use super::{
        CgroupMemoryLimit, MAX_AUTHENTICATED_TRANSPORT_FLOOR_BYTES, ProcessBuilder,
        STREAMING_LINE_PREFIX_BYTES, StreamingLinePrefix, StreamingOutputLimits, cut_long_lines,
        effective_physical_memory_bytes, linux_cgroup_memory_authority, long_line_mark,
        oversized_line, parse_linux_cgroup_memory_limit, scaled_stream_ceiling,
    };
    use anyhow::bail;
    use std::fs;
    use std::io::{self, Write as _};
    use std::process::{Command, Stdio};
    use std::thread;
    use std::time::{Duration, Instant};

    // Opt-in production calls serialize signal ownership by refusal. These
    // ordinary lifecycle cases must not compete when libtest runs in parallel.
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    pub(super) static CHILD_EXIT_TEST_LOCK: std::sync::Mutex<()> = std::sync::Mutex::new(());

    const GIB: u64 = 1024 * 1024 * 1024;
    /// `VERIFIED_TARGO_MAX_CHILD_LINE_BYTES` at `compiler/mod.rs:137`: the
    /// per-line ceiling passed for every verified rustc and rustdoc child, so
    /// the covering test below runs the production transport policy rather
    /// than a shape invented for it.
    const TRANSPORT_POLICY_LINE_BYTES: usize = 128 * 1024 * 1024;
    /// One line of the `transport-scale-stdout` flood, newline included.
    const TRANSPORT_SCALE_LINE_BYTES: usize = 64 * 1024;
    /// Lines per `write_all`, to keep the child's syscall count off the clock.
    const TRANSPORT_SCALE_CHUNK_LINES: usize = 64;
    /// Comfortably past the flat 512 MiB ceiling that refused honest evidence,
    /// and far under an eighth of the memory of any machine that would notice
    /// the difference. An exact multiple of the chunk above.
    const TRANSPORT_SCALE_STDOUT_BYTES: usize =
        MAX_AUTHENTICATED_TRANSPORT_FLOOR_BYTES + 32 * 1024 * 1024;
    const STREAMING_CHILD_ROLE: &str = "__CARGO_UTIL_STREAMING_CHILD_ROLE";
    pub(super) const STREAMING_CHILD_MARKER: &str = "__CARGO_UTIL_STREAMING_CHILD_MARKER";
    // Trust: recognizable producer context followed by hostile diagnostic bytes.
    const DIAGNOSTIC_PREFIX: &[u8] =
        b"{\"$message_type\":\"diagnostic\",\"message\":\"producer\\\"\x1b[31m\r\x00\xf0\x9f\xa6\x80";
    #[cfg(unix)]
    const INHERITED_FD_TEST_ENV: &str = "__CARGO_UTIL_INHERITED_FD_TEST";
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    const SUPERVISED_CHILD_ROLE: &str = "__CARGO_UTIL_SUPERVISED_CHILD_ROLE";

    /// Trust (T14c): the process a supervisor test runs. It replaces itself,
    /// supervised, with a shell that ends the way `role` says, or (for
    /// `count-sigint`) with this binary again as a target that counts the
    /// SIGINTs it receives.
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    #[test]
    fn supervised_child_helper() {
        let Ok(role) = std::env::var(SUPERVISED_CHILD_ROLE) else {
            return;
        };
        if role == "direct-cancel-target" {
            static CANCELED: std::sync::atomic::AtomicUsize =
                std::sync::atomic::AtomicUsize::new(0);
            extern "C" fn terminated(_: libc::c_int) {
                CANCELED.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
                // Same signal is blocked during its handler: a duplicated
                // delivery stays pending and is counted after this returns.
                unsafe {
                    libc::usleep(200_000);
                }
            }
            let root =
                std::path::PathBuf::from(std::env::var_os("__CARGO_UTIL_RETIRE_ROOT").unwrap());
            assert_ne!(
                unsafe { libc::signal(libc::SIGTERM, terminated as *const () as usize) },
                libc::SIG_ERR
            );
            fs::write(root.join("ready"), b"actual-target-ready").unwrap();
            let deadline = Instant::now() + Duration::from_secs(20);
            while CANCELED.load(std::sync::atomic::Ordering::SeqCst) == 0 {
                assert!(Instant::now() < deadline);
                thread::sleep(Duration::from_millis(1));
            }
            thread::sleep(Duration::from_millis(300));
            let count = CANCELED.load(std::sync::atomic::Ordering::SeqCst);
            fs::write(root.join("closed"), count.to_string()).unwrap();
            return;
        }
        if role == "direct-cancel-parent" {
            let root =
                std::path::PathBuf::from(std::env::var_os("__CARGO_UTIL_RETIRE_ROOT").unwrap());
            let error = ProcessBuilder::new(std::env::current_exe().unwrap())
                .args(&[
                    "--exact",
                    "process_builder::tests::supervised_child_helper",
                    "--nocapture",
                    "--test-threads=1",
                ])
                .env(SUPERVISED_CHILD_ROLE, "direct-cancel-target")
                .exec_in_original_group_with_retirement(|| {
                    anyhow::ensure!(
                        fs::read(root.join("closed"))? == b"1",
                        "original group SIGTERM was delivered more than once"
                    );
                    fs::write(root.join("retired"), b"after-owning-wait")?;
                    Ok(())
                })
                .unwrap_err();
            let observed = error.downcast_ref::<crate::TargetExecutionError>().unwrap();
            assert_eq!(observed.observed_status().unwrap().code(), Some(0));
            assert_ne!(observed.signal_mask() & (1_u32 << libc::SIGTERM), 0);
            println!(
                "ACTUAL-DIRECT-GROUP-SIGTERM-COUNT={}",
                String::from_utf8_lossy(&fs::read(root.join("closed")).unwrap())
            );
            assert_eq!(fs::read(root.join("closed")).unwrap(), b"1");
            println!("ACTUAL-DIRECT-CANCEL-RETAINED-TARGET0-AND-RETIREMENT");
            return;
        }
        if role == "retire-spawn-failed" {
            let mut called = false;
            ProcessBuilder::new("/__trust_missing_run_target__")
                .exec_replace_supervised_with_retirement(|| {
                    called = true;
                    Ok(())
                })
                .unwrap_err();
            assert!(
                !called,
                "spawn failure cannot manufacture an owning-wait continuation"
            );
            println!("ACTUAL-RETIREMENT-NOT-CALLED-ON-SPAWN-FAILURE");
            return;
        }
        if matches!(role.as_str(), "retire-exit" | "retire-refused") {
            let root =
                std::path::PathBuf::from(std::env::var_os("__CARGO_UTIL_RETIRE_ROOT").unwrap());
            let target_exit = std::env::var("__CARGO_UTIL_RETIRE_EXIT").unwrap();
            let script = match target_exit.as_str() {
                "0" => "printf target-settled > \"$1\"; exit 0",
                "3" => "printf target-settled > \"$1\"; exit 3",
                "signal" => "printf target-settled > \"$1\"; kill -TERM $$",
                other => panic!("unexpected actual target status {other}"),
            };
            let error = ProcessBuilder::new("/bin/sh")
                .args(&["-c", script, "retire-target"])
                .arg(root.join("target"))
                .exec_replace_supervised_with_retirement(|| {
                    assert_eq!(fs::read(root.join("target"))?, b"target-settled");
                    fs::write(root.join("retired"), b"after-owning-wait")?;
                    if role == "retire-refused" {
                        anyhow::bail!("actual retirement refused");
                    }
                    Ok(())
                })
                .unwrap_err();
            assert_eq!(
                role, "retire-refused",
                "successful retirement must recreate the observed child status"
            );
            assert!(error.to_string().contains("actual retirement refused"));
            let observed = error.downcast_ref::<crate::TargetExecutionError>().unwrap();
            if target_exit == "signal" {
                use std::os::unix::process::ExitStatusExt as _;
                assert_eq!(
                    observed.observed_status().unwrap().signal(),
                    Some(libc::SIGTERM)
                );
            } else {
                assert_eq!(
                    observed.observed_status().unwrap().code(),
                    Some(target_exit.parse().unwrap())
                );
            }
            assert!(
                observed
                    .completion_error()
                    .to_string()
                    .contains("actual retirement refused")
            );
            assert!(
                error.downcast_ref::<crate::ProcessError>().is_none(),
                "retirement failure cannot forward the target's exit code"
            );
            println!("ACTUAL-RETIREMENT-REFUSAL-AFTER-WAIT");
            return;
        }
        // Trust (RL-64): the caller still owns a job-server endpoint when the
        // supervisor ends the process, as `targo run` does, or when a true
        // exec replaces it, as a nested `targo run` does.
        if let Some(target) = role.strip_prefix("handoff-") {
            let mut owner = jobserver_utils::Jobserver::new(1).unwrap();
            owner.enable_descendant_handoff().unwrap();
            // The folder is in this role's private TMPDIR now, so a test that
            // finds none there afterwards saw this one removed. A failure
            // here ends the role 101, which no test of it expects.
            let made: Vec<_> = fs::read_dir(std::env::temp_dir())
                .unwrap()
                .map(|entry| entry.unwrap().file_name())
                .collect();
            assert!(
                matches!(made.as_slice(), [name] if name.to_string_lossy().starts_with("tjs-")),
                "expected one job-server folder in TMPDIR, found {made:?}"
            );
            if target == "exec" {
                let error = ProcessBuilder::new("/bin/sh")
                    .args(&["-c", "exit 3"])
                    .exec_replace()
                    .unwrap_err();
                drop(owner);
                panic!("exec returned: {error:#}");
            }
            let script = match target {
                "exit-3" => "exit 3",
                "sigint" => "kill -INT $$",
                other => panic!("unknown handoff role {other}"),
            };
            let error = ProcessBuilder::new("/bin/sh")
                .args(&["-c", script])
                .exec_replace_supervised()
                .unwrap_err();
            drop(owner);
            panic!("supervised exec returned: {error:#}");
        }
        match role.as_str() {
            "count-sigint" => {
                let error = ProcessBuilder::new(std::env::current_exe().unwrap())
                    .args(&[
                        "--exact",
                        "process_builder::tests::supervised_child_helper",
                        "--nocapture",
                        "--test-threads=1",
                    ])
                    .env(SUPERVISED_CHILD_ROLE, "count-sigint-target")
                    .exec_replace_supervised()
                    .unwrap_err();
                panic!("supervised exec returned: {error:#}");
            }
            "count-sigint-target" => count_sigint_target(),
            _ => {}
        }
        let script = match role.as_str() {
            "exit-3" => "exit 3",
            "sigint" => "kill -INT $$",
            "sleep" => "echo supervised-ready; exec /bin/sleep 30",
            other => panic!("unknown supervised role {other}"),
        };
        let error = ProcessBuilder::new("/bin/sh")
            .args(&["-c", script])
            .exec_replace_supervised()
            .unwrap_err();
        panic!("supervised exec returned: {error:#}");
    }

    #[cfg(any(target_os = "linux", target_os = "macos"))]
    #[test]
    fn supervised_retirement_follows_owning_wait_before_exit_and_cannot_fabricate_success() {
        let _signal_owner = CHILD_EXIT_TEST_LOCK.lock().unwrap();
        for refused in [false, true] {
            for target_exit in ["0", "3", "signal"] {
                let root = tempfile::tempdir().unwrap();
                let role = if refused {
                    "retire-refused"
                } else {
                    "retire-exit"
                };
                let output = Command::new(std::env::current_exe().unwrap())
                    .args([
                        "--exact",
                        "process_builder::tests::supervised_child_helper",
                        "--nocapture",
                        "--test-threads=1",
                    ])
                    .env(SUPERVISED_CHILD_ROLE, role)
                    .env("__CARGO_UTIL_RETIRE_ROOT", root.path())
                    .env("__CARGO_UTIL_RETIRE_EXIT", target_exit)
                    .output()
                    .unwrap();
                assert_eq!(
                    output.status.code(),
                    if refused {
                        Some(0)
                    } else {
                        target_exit.parse().ok()
                    },
                    "{output:?}"
                );
                if !refused && target_exit == "signal" {
                    use std::os::unix::process::ExitStatusExt as _;
                    assert_eq!(output.status.signal(), Some(libc::SIGTERM));
                }
                assert_eq!(
                    fs::read(root.path().join("target")).unwrap(),
                    b"target-settled"
                );
                assert_eq!(
                    fs::read(root.path().join("retired")).unwrap(),
                    b"after-owning-wait"
                );
                if refused {
                    assert!(
                        String::from_utf8_lossy(&output.stdout)
                            .contains("ACTUAL-RETIREMENT-REFUSAL-AFTER-WAIT")
                    );
                }
            }
        }
        // Signal ownership is process-wide: isolate even no-child failures.
        let output = Command::new(std::env::current_exe().unwrap())
            .args([
                "--exact",
                "process_builder::tests::supervised_child_helper",
                "--nocapture",
                "--test-threads=1",
            ])
            .env(SUPERVISED_CHILD_ROLE, "retire-spawn-failed")
            .output()
            .unwrap();
        assert!(output.status.success(), "{output:?}");
        assert!(
            String::from_utf8_lossy(&output.stdout)
                .contains("ACTUAL-RETIREMENT-NOT-CALLED-ON-SPAWN-FAILURE")
        );
    }

    #[cfg(any(target_os = "linux", target_os = "macos"))]
    #[test]
    fn direct_retirement_retains_actual_status_and_cannot_fabricate_a_successful_exit() {
        use std::os::unix::process::ExitStatusExt as _;
        for refused in [false, true] {
            for target_exit in ["0", "3", "signal"] {
                let root = tempfile::tempdir().unwrap();
                let script = match target_exit {
                    "0" => "printf settled > \"$1\"; exit 0",
                    "3" => "printf settled > \"$1\"; exit 3",
                    _ => "printf settled > \"$1\"; kill -TERM $$",
                };
                let result = ProcessBuilder::new("/bin/sh")
                    .args(&["-c", script, "actual-direct-target"])
                    .arg(root.path().join("target"))
                    .exec_in_original_group_with_retirement(|| {
                        assert_eq!(fs::read(root.path().join("target"))?, b"settled");
                        fs::write(root.path().join("retired"), b"after-owning-wait")?;
                        if refused {
                            anyhow::bail!("actual direct retirement refused");
                        }
                        Ok(())
                    });
                assert_eq!(
                    fs::read(root.path().join("retired")).unwrap(),
                    b"after-owning-wait"
                );
                if refused {
                    let error = result.unwrap_err();
                    let failure = error.downcast_ref::<crate::TargetExecutionError>().unwrap();
                    if target_exit == "signal" {
                        assert_eq!(
                            failure.observed_status().unwrap().signal(),
                            Some(libc::SIGTERM)
                        );
                    } else {
                        assert_eq!(
                            failure.observed_status().unwrap().code(),
                            Some(target_exit.parse().unwrap())
                        );
                    }
                    assert!(
                        failure
                            .completion_error()
                            .to_string()
                            .contains("actual direct retirement refused")
                    );
                    assert!(error.downcast_ref::<crate::ProcessError>().is_none());
                } else if target_exit == "0" {
                    result.unwrap();
                } else {
                    let error = result.unwrap_err();
                    let observed = error.downcast_ref::<crate::ProcessError>().unwrap();
                    if target_exit == "signal" {
                        assert_eq!(observed.signal, Some(libc::SIGTERM));
                    } else {
                        assert_eq!(observed.code, Some(3));
                    }
                }
            }
        }
        let mut called = false;
        ProcessBuilder::new("/__trust_missing_direct_target__")
            .exec_in_original_group_with_retirement(|| {
                called = true;
                Ok(())
            })
            .unwrap_err();
        assert!(!called);
    }

    #[cfg(any(target_os = "linux", target_os = "macos"))]
    #[test]
    fn direct_retirement_survives_original_group_cancel_and_withholds_target0_success() {
        use std::os::unix::process::CommandExt as _;
        let root = tempfile::tempdir().unwrap();
        let mut parent = supervised_command("direct-cancel-parent")
            .env("__CARGO_UTIL_RETIRE_ROOT", root.path())
            .process_group(0)
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .unwrap();
        let deadline = Instant::now() + Duration::from_secs(20);
        while !root.path().join("ready").exists() {
            assert!(
                parent.try_wait().unwrap().is_none(),
                "actual parent exited before readiness"
            );
            assert!(Instant::now() < deadline);
            thread::sleep(Duration::from_millis(1));
        }
        let pid = libc::pid_t::try_from(parent.id()).unwrap();
        assert_eq!(unsafe { libc::killpg(pid, libc::SIGTERM) }, 0);
        let output = parent.wait_with_output().unwrap();
        assert!(output.status.success(), "{output:?}");
        assert_eq!(
            fs::read(root.path().join("retired")).unwrap(),
            b"after-owning-wait"
        );
        assert!(
            String::from_utf8_lossy(&output.stdout)
                .contains("ACTUAL-DIRECT-CANCEL-RETAINED-TARGET0-AND-RETIREMENT")
        );
    }

    /// The `count-sigint` target: count SIGINTs for a while, then print the
    /// count and exit 0. The handler holds SIGINT blocked for a moment (the
    /// kernel blocks it while its handler runs), so a second copy arriving
    /// meanwhile waits as pending and is counted rather than merged into the
    /// first.
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    fn count_sigint_target() -> ! {
        use std::sync::atomic::{AtomicUsize, Ordering};

        static SIGINTS: AtomicUsize = AtomicUsize::new(0);
        extern "C" fn count(_: libc::c_int) {
            SIGINTS.fetch_add(1, Ordering::SeqCst);
            // SAFETY: usleep is async-signal-safe.
            unsafe {
                libc::usleep(200_000);
            }
        }
        // SAFETY: a zeroed sigaction with an initialized mask and a plain
        // `extern "C"` handler.
        unsafe {
            let mut action: libc::sigaction = std::mem::zeroed();
            action.sa_sigaction = count as *const () as usize;
            action.sa_flags = libc::SA_RESTART;
            libc::sigemptyset(&mut action.sa_mask);
            assert_eq!(
                libc::sigaction(libc::SIGINT, &action, std::ptr::null_mut()),
                0
            );
        }
        println!("supervised-ready");
        io::stdout().flush().unwrap();
        thread::sleep(Duration::from_millis(1500));
        println!("sigint-count={}", SIGINTS.load(Ordering::SeqCst));
        io::stdout().flush().unwrap();
        std::process::exit(0)
    }

    #[cfg(any(target_os = "linux", target_os = "macos"))]
    fn supervised_command(role: &str) -> Command {
        let mut command = Command::new(std::env::current_exe().unwrap());
        command
            .args([
                "--exact",
                "process_builder::tests::supervised_child_helper",
                "--nocapture",
                "--test-threads=1",
            ])
            .env(SUPERVISED_CHILD_ROLE, role);
        command
    }

    #[cfg(target_os = "macos")]
    #[test]
    fn the_macos_supervisor_mirrors_exit_codes_and_forwards_terminating_signals() {
        use std::io::BufRead as _;
        use std::os::unix::process::ExitStatusExt as _;

        let status = supervised_command("exit-3")
            .stdout(Stdio::null())
            .status()
            .unwrap();
        assert_eq!(status.code(), Some(3), "{status:?}");

        let status = supervised_command("sigint")
            .stdout(Stdio::null())
            .status()
            .unwrap();
        assert_eq!(status.signal(), Some(libc::SIGINT), "{status:?}");

        // SIGTERM sent to the supervisor reaches its target, and the
        // supervisor then ends the way the target did.
        let mut supervisor = supervised_command("sleep")
            .stdout(Stdio::piped())
            .spawn()
            .unwrap();
        let mut stdout = io::BufReader::new(supervisor.stdout.take().unwrap());
        let mut line = String::new();
        while !line.contains("supervised-ready") {
            line.clear();
            assert_ne!(
                stdout.read_line(&mut line).unwrap(),
                0,
                "the target never started"
            );
        }
        let pid = libc::pid_t::try_from(supervisor.id()).unwrap();
        // SAFETY: `pid` is this test's own unreaped child.
        assert_eq!(unsafe { libc::kill(pid, libc::SIGTERM) }, 0);
        let status = supervisor.wait().unwrap();
        assert_eq!(status.signal(), Some(libc::SIGTERM), "{status:?}");
    }

    /// Trust (RL-64): the supervisor ends its process with an endpoint owner
    /// still on its caller's stack. Both ways out remove that owner's
    /// job-server folder: an exit code goes through exit(3), and a mirrored
    /// signal, which runs no exit handler, relies on the explicit removal in
    /// `exit_like_supervised_child`.
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    #[test]
    fn a_supervised_exit_leaves_no_job_server_folder() {
        use std::os::unix::process::ExitStatusExt as _;

        for (role, code, signal) in [
            ("handoff-exit-3", Some(3), None),
            ("handoff-sigint", None, Some(libc::SIGINT)),
        ] {
            let (status, left) = handoff_role_status_and_leftovers(role);
            assert_eq!(
                (status.code(), status.signal()),
                (code, signal),
                "{role}: {status:?}"
            );
            assert!(left.is_empty(), "{role} left {left:?}");
        }
    }

    /// Trust (RL-64): a true exec runs no exit handler and no destructor, and
    /// the image that replaces this one holds neither the folder's descriptor
    /// nor the thread that served its socket. A `targo run` that owns no
    /// broker and gave its target no scheduler ends this way (a nested one, or
    /// one under the `cargo` name) with its compiler-query endpoint parked in
    /// a static, so `imp::exec_replace` removes the folder before it execs.
    /// Exit 3 is the shell's: the exec happened.
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    #[test]
    fn an_exec_replacement_leaves_no_job_server_folder() {
        let (status, left) = handoff_role_status_and_leftovers("handoff-exec");
        assert_eq!(status.code(), Some(3), "{status:?}");
        assert!(left.is_empty(), "handoff-exec left {left:?}");
    }

    /// Trust (RL-64): run the helper as `role`, which makes one job-server
    /// folder in its TMPDIR, and say how it ended and what it left there.
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    fn handoff_role_status_and_leftovers(
        role: &str,
    ) -> (std::process::ExitStatus, Vec<std::ffi::OsString>) {
        // A private TMPDIR short enough to hold the socket's address, so
        // the folder is made in it and not in the shared `/tmp`.
        let tmp = tempfile::Builder::new()
            .prefix("cu-tjs-")
            .tempdir_in("/tmp")
            .unwrap();
        let status = supervised_command(role)
            .env("TMPDIR", tmp.path())
            .stdout(Stdio::null())
            .status()
            .unwrap();
        let left = fs::read_dir(tmp.path())
            .unwrap()
            .map(|entry| entry.unwrap().file_name())
            .collect();
        (status, left)
    }

    /// A Ctrl-C reaches the whole foreground process group, the supervisor
    /// and its target alike. The target gets it exactly once: the supervisor
    /// does not forward a keyboard signal its target already has, and it
    /// outlives the interrupt to mirror the target's exit (here 0).
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    #[test]
    fn a_group_interrupt_reaches_the_target_once() {
        use std::io::BufRead as _;
        use std::os::unix::process::CommandExt as _;

        let mut supervisor = supervised_command("count-sigint")
            .process_group(0)
            .stdout(Stdio::piped())
            .spawn()
            .unwrap();
        let mut stdout = io::BufReader::new(supervisor.stdout.take().unwrap());
        let mut line = String::new();
        while !line.contains("supervised-ready") {
            line.clear();
            assert_ne!(
                stdout.read_line(&mut line).unwrap(),
                0,
                "the target never started"
            );
        }
        let group = libc::pid_t::try_from(supervisor.id()).unwrap();
        // SAFETY: `group` is the process group this test just created for its
        // own child, which holds the supervisor and its target only.
        assert_eq!(unsafe { libc::killpg(group, libc::SIGINT) }, 0);
        let mut count = None;
        line.clear();
        while stdout.read_line(&mut line).unwrap() != 0 {
            if let Some(value) = line.trim().strip_prefix("sigint-count=") {
                count = Some(value.parse::<usize>().unwrap());
            }
            line.clear();
        }
        let status = supervisor.wait().unwrap();
        assert_eq!(count, Some(1), "one Ctrl-C must reach the target once");
        assert_eq!(status.code(), Some(0), "{status:?}");
    }

    /// A signal whose default writes a crash report is not raised again: the
    /// supervisor exits `128 + n` after one line, so a crashed target never
    /// produces a second report (for targo). Decided on synthetic statuses,
    /// so no test process crashes.
    #[cfg(target_os = "macos")]
    #[test]
    fn a_crash_report_signal_becomes_an_exit_code_and_one_line() {
        use super::imp::{SupervisedExit, supervised_exit};
        use std::os::unix::process::ExitStatusExt as _;
        use std::process::ExitStatus;

        match supervised_exit(ExitStatus::from_raw(libc::SIGSEGV)) {
            SupervisedExit::CrashSignal(139, line) => {
                assert!(line.contains("SIGSEGV") && line.contains("139"), "{line}");
                assert!(!line.contains('\n'), "{line}");
            }
            other => panic!("SIGSEGV must not be raised again: {other:?}"),
        }
        for signal in [libc::SIGABRT, libc::SIGBUS, libc::SIGILL, libc::SIGQUIT] {
            assert!(matches!(
                supervised_exit(ExitStatus::from_raw(signal)),
                SupervisedExit::CrashSignal(code, _) if code == 128 + signal
            ));
        }
        assert_eq!(
            supervised_exit(ExitStatus::from_raw(libc::SIGTERM)),
            SupervisedExit::Signal(libc::SIGTERM)
        );
        assert_eq!(
            supervised_exit(ExitStatus::from_raw(3 << 8)),
            SupervisedExit::Code(3)
        );
    }

    pub(super) fn streaming_child_command(role: &str) -> ProcessBuilder {
        let mut cmd = ProcessBuilder::new(std::env::current_exe().unwrap());
        cmd.args(&[
            "--exact",
            "process_builder::tests::streaming_child_helper",
            "--nocapture",
            // Trust: libtest's single-threaded status prefix otherwise joins
            // the first payload line and changes the protocol being tested.
            "--quiet",
        ])
        .env(STREAMING_CHILD_ROLE, role);
        cmd
    }

    #[test]
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    fn owning_wait_never_replaces_echild_with_a_cached_standard_child_status() {
        let _serial = CHILD_EXIT_TEST_LOCK
            .lock()
            .unwrap_or_else(|error| error.into_inner());
        let mut child = std::process::Command::new("/bin/sh")
            .env_clear()
            .args(["-c", "exit 7"])
            .spawn()
            .unwrap();
        // A real completed wait leaves std's cached status but no kernel child.
        // It must not satisfy a later owning accounting wait after ECHILD.
        assert_eq!(child.wait().unwrap().code(), Some(7));
        let error = super::imp::wait_with_resource_usage(&mut child).unwrap_err();
        assert_eq!(error.raw_os_error(), Some(libc::ECHILD));
    }

    #[test]
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    fn owning_wait_keeps_cpu_on_failure_and_missing_accounting_stays_unknown() {
        let _serial = CHILD_EXIT_TEST_LOCK
            .lock()
            .unwrap_or_else(|error| error.into_inner());
        for (requested, deadline, owned) in [
            (true, false, false),
            (false, false, false),
            (true, true, true),
            (true, true, false),
        ] {
            let command = streaming_child_command("accounting-body-failed");
            let mut stdout = Vec::new();
            let mut stderr = Vec::new();
            let mut out = |line: &str| {
                stdout.push(line.to_owned());
                Ok(())
            };
            let mut err = |line: &str| {
                stderr.push(line.to_owned());
                Ok(())
            };
            let (stats, result) = if deadline {
                let limits = small_streaming_limits().with_timeout(Duration::from_secs(60));
                let limits = if owned {
                    limits.with_child_exit_cleanup()
                } else {
                    limits
                };
                command.exec_with_streaming_limits_and_stats(
                    &mut out, &mut err, true, limits, requested,
                )
            } else {
                command.exec_with_streaming(&mut out, &mut err, true, requested)
            };
            assert!(stdout.iter().any(|line| line.contains("accounting-body")));
            assert!(stderr.iter().any(|line| line.contains("accounting-stderr")));
            let error = result.unwrap_err();
            assert_eq!(
                error.downcast_ref::<crate::ProcessError>().unwrap().code,
                Some(7)
            );
            if requested && (!deadline || owned) {
                let times = stats
                    .cpu_times
                    .expect("same owning wait must retain both CPU components");
                assert!(times.user > Duration::ZERO, "{stats:?}");
                assert!(stats.peak_rss.is_some_and(|bytes| bytes > 0), "{stats:?}");
            } else {
                assert!(
                    stats.cpu_times.is_none(),
                    "missing accounting is not measured zero"
                );
            }
        }
    }

    fn small_streaming_limits() -> StreamingOutputLimits {
        StreamingOutputLimits::new(1024, 16 * 1024)
    }

    fn assert_fast_failure(started: Instant) {
        assert!(
            started.elapsed() < Duration::from_secs(5),
            "bounded streaming rejection did not terminate the child promptly: {:?}",
            started.elapsed()
        );
    }

    #[test]
    fn streaming_child_helper() {
        let Ok(role) = std::env::var(STREAMING_CHILD_ROLE) else {
            return;
        };
        match role.as_str() {
            "accounting-body-failed" => {
                let mut memory = vec![0u8; 16 * 1024 * 1024];
                for (index, byte) in memory.iter_mut().enumerate() {
                    *byte = index as u8;
                }
                std::hint::black_box(&memory);
                println!("accounting-body");
                eprintln!("accounting-stderr");
                std::process::exit(7);
            }
            #[cfg(unix)]
            "capture-split" => {
                use std::io::Read as _;
                let mut acknowledgement = std::os::unix::net::UnixStream::connect(
                    std::env::var_os(STREAMING_CHILD_MARKER).unwrap(),
                )
                .unwrap();
                io::stdout()
                    .write_all(b"prefix-first\npartial\0\xff")
                    .unwrap();
                io::stdout().flush().unwrap();
                acknowledgement.read_exact(&mut [0]).unwrap();
                io::stdout().write_all(b"-finished\nlast\0\xfe").unwrap();
                io::stdout().flush().unwrap();
                std::process::exit(0);
            }
            "capture-success" | "capture-failure" | "capture-timeout" | "capture-signal" => {
                io::stdout().write_all(b"raw\0\xff-final-tail").unwrap();
                io::stdout().flush().unwrap();
                io::stderr().write_all(b"stderr-evidence-tail\0").unwrap();
                io::stderr().flush().unwrap();
                match role.as_str() {
                    "capture-timeout" => loop {
                        thread::park();
                    },
                    #[cfg(unix)]
                    "capture-signal" => {
                        // SAFETY: the fixture terminates only itself, no crash report.
                        assert_eq!(unsafe { libc::kill(libc::getpid(), libc::SIGKILL) }, 0);
                        // Signal delivery can follow a successful kill return.
                        // Preserve the exact evidence stream until termination.
                        loop {
                            thread::park();
                        }
                    }
                    "capture-failure" => std::process::exit(7),
                    _ => std::process::exit(0),
                }
            }
            "framed-lines" => {
                println!("first-payload-line");
                println!("second-payload-line");
            }
            #[cfg(unix)]
            "inherited-fd-open" | "inherited-fd-closed" => {
                let fd = std::env::var(INHERITED_FD_TEST_ENV)
                    .unwrap()
                    .parse::<libc::c_int>()
                    .unwrap();
                let flags = unsafe { libc::fcntl(fd, libc::F_GETFD) };
                if role == "inherited-fd-open" {
                    assert!(flags >= 0, "selected child did not inherit its descriptor");
                } else {
                    assert_eq!(
                        flags, -1,
                        "an unrelated child inherited a builder-scoped descriptor"
                    );
                }
            }
            "oversized-stdout" => {
                let mut stdout = io::stdout().lock();
                stdout.write_all(&vec![b'o'; 1025]).unwrap();
                stdout.flush().unwrap();
                loop {
                    thread::park_timeout(Duration::from_secs(60));
                }
            }
            "oversized-stderr" => {
                let mut stderr = io::stderr().lock();
                stderr.write_all(&vec![b'e'; 1025]).unwrap();
                stderr.flush().unwrap();
                loop {
                    thread::park_timeout(Duration::from_secs(60));
                }
            }
            // Trust: exercise complete, retained-tail, EOF and split-read
            // refusals through the actual process reader and callback boundary.
            "oversized-diagnostic-complete"
            | "oversized-diagnostic-tail"
            | "oversized-diagnostic-eof"
            | "oversized-diagnostic-split" => {
                let mut stderr = io::stderr().lock();
                stderr.write_all(b"earlier-line\n").unwrap();
                let mut line = vec![b'x'; 1025];
                line[..DIAGNOSTIC_PREFIX.len()].copy_from_slice(DIAGNOSTIC_PREFIX);
                line[STREAMING_LINE_PREFIX_BYTES..STREAMING_LINE_PREFIX_BYTES + 14]
                    .copy_from_slice(b"PRIVATE-SUFFIX");
                if role == "oversized-diagnostic-split" {
                    stderr.write_all(&line[..1024]).unwrap();
                    stderr.flush().unwrap();
                    thread::sleep(Duration::from_millis(100));
                    stderr.write_all(&line[1024..]).unwrap();
                } else {
                    stderr.write_all(&line).unwrap();
                }
                if role == "oversized-diagnostic-complete" {
                    stderr.write_all(b"\nlater-summary\n").unwrap();
                }
                stderr.flush().unwrap();
                if role != "oversized-diagnostic-eof" {
                    loop {
                        thread::park_timeout(Duration::from_secs(60));
                    }
                }
            }
            // Trust: lines longer than the limit among short ones, on a
            // stream the test harness itself does not write: a complete one,
            // one that arrives in three writes, and one the stream ends in.
            "long-lines" => {
                let mut stderr = io::stderr().lock();
                stderr.write_all(b"before\n").unwrap();
                stderr
                    .write_all(&[b"test a ... ok".as_slice(), &vec![b'x'; 3000]].concat())
                    .unwrap();
                stderr.write_all(b"\nbetween\n").unwrap();
                for part in [b'p', b'q', b'r'] {
                    stderr.write_all(&vec![part; 900]).unwrap();
                    stderr.flush().unwrap();
                    thread::sleep(Duration::from_millis(100));
                }
                stderr.write_all(b"\nafter\n").unwrap();
                stderr.write_all(&vec![b'y'; 5000]).unwrap();
                stderr.flush().unwrap();
            }
            "aggregate-stdout" => {
                let mut stdout = io::stdout().lock();
                for _ in 0..4096 {
                    stdout.write_all(b"bounded-line\n").unwrap();
                }
                stdout.flush().unwrap();
                loop {
                    thread::park_timeout(Duration::from_secs(60));
                }
            }
            "burst-later-rejection" => {
                let mut stderr = io::stderr().lock();
                stderr.write_all(b"first\nreject-later\ntrailing").unwrap();
                stderr.flush().unwrap();
                loop {
                    thread::park_timeout(Duration::from_secs(60));
                }
            }
            "split-partial" => {
                let mut stderr = io::stderr().lock();
                stderr.write_all(b"complete\npartial").unwrap();
                stderr.flush().unwrap();
                thread::sleep(Duration::from_millis(500));
                stderr.write_all(b"more\n").unwrap();
                stderr.flush().unwrap();
                loop {
                    thread::park_timeout(Duration::from_secs(60));
                }
            }
            "transport-scale-stdout" => {
                let mut line = vec![b'x'; TRANSPORT_SCALE_LINE_BYTES];
                line[TRANSPORT_SCALE_LINE_BYTES - 1] = b'\n';
                let mut chunk =
                    Vec::with_capacity(TRANSPORT_SCALE_CHUNK_LINES * TRANSPORT_SCALE_LINE_BYTES);
                for _ in 0..TRANSPORT_SCALE_CHUNK_LINES {
                    chunk.extend_from_slice(&line);
                }
                let mut stdout = io::stdout().lock();
                let mut written = 0;
                while written < TRANSPORT_SCALE_STDOUT_BYTES {
                    stdout.write_all(&chunk).unwrap();
                    written += chunk.len();
                }
                stdout.flush().unwrap();
                // Unlike every other role, this one must EXIT: the parent is
                // asserting that a stream this size is read to completion.
            }
            "silent-hang" => loop {
                thread::park_timeout(Duration::from_secs(60));
            },
            "closed-pipes-hang" => {
                #[cfg(unix)]
                unsafe {
                    libc::close(libc::STDOUT_FILENO);
                    libc::close(libc::STDERR_FILENO);
                }
                loop {
                    thread::park_timeout(Duration::from_secs(60));
                }
            }
            "timeout-parent" => {
                #[cfg(unix)]
                {
                    let marker = std::env::var_os(STREAMING_CHILD_MARKER).unwrap();
                    Command::new(std::env::current_exe().unwrap())
                        .args([
                            "--exact",
                            "process_builder::tests::streaming_child_helper",
                            "--nocapture",
                        ])
                        .env(STREAMING_CHILD_ROLE, "timeout-descendant")
                        .env(STREAMING_CHILD_MARKER, marker)
                        .stdout(Stdio::inherit())
                        .stderr(Stdio::inherit())
                        .spawn()
                        .unwrap();
                }
                loop {
                    thread::park_timeout(Duration::from_secs(60));
                }
            }
            "exit-with-inherited-pipes" => {
                let marker = std::env::var_os(STREAMING_CHILD_MARKER).unwrap();
                let ready = std::path::Path::new(&marker).with_extension("ready");
                // A silent pipe holder avoids a second libtest process writing
                // its own progress prefixes into the final unterminated tail.
                Command::new("/bin/sh")
                    .args([
                        "-c",
                        "printf ready > \"$2\"; /bin/sleep 0.25; printf survived > \"$1\"; /bin/sleep 60",
                        "held-pipe",
                    ])
                    .arg(marker)
                    .arg(&ready)
                    .stdout(Stdio::inherit())
                    .stderr(Stdio::inherit())
                    .spawn()
                    .unwrap();
                let started = Instant::now();
                while !ready.exists() {
                    assert!(
                        started.elapsed() < Duration::from_secs(2),
                        "pipe holder did not start"
                    );
                    thread::sleep(Duration::from_millis(1));
                }
                // These bytes are buffered before exit and must survive the
                // observer's group cleanup even with a live pipe holder.
                print!("leader-final-line\nleader-final-tail");
                io::stdout().flush().unwrap();
                eprintln!("leader-final-stderr");
                std::process::exit(0);
            }
            "timeout-descendant" => {
                thread::sleep(Duration::from_secs(2));
                fs::write(
                    std::env::var_os(STREAMING_CHILD_MARKER).unwrap(),
                    "survived",
                )
                .unwrap();
                loop {
                    thread::park_timeout(Duration::from_secs(60));
                }
            }
            "callback-parent" => {
                #[cfg(unix)]
                {
                    let marker = std::env::var_os(STREAMING_CHILD_MARKER).unwrap();
                    Command::new(std::env::current_exe().unwrap())
                        .args([
                            "--exact",
                            "process_builder::tests::streaming_child_helper",
                            "--nocapture",
                        ])
                        .env(STREAMING_CHILD_ROLE, "callback-descendant")
                        .env(STREAMING_CHILD_MARKER, marker)
                        .stdout(Stdio::inherit())
                        .stderr(Stdio::inherit())
                        .spawn()
                        .unwrap();
                }
                println!("reject-now");
                io::stdout().flush().unwrap();
                loop {
                    thread::park_timeout(Duration::from_secs(60));
                }
            }
            "callback-descendant" => {
                thread::sleep(Duration::from_millis(750));
                fs::write(
                    std::env::var_os(STREAMING_CHILD_MARKER).unwrap(),
                    "survived",
                )
                .unwrap();
                loop {
                    thread::park_timeout(Duration::from_secs(60));
                }
            }
            role => panic!("unknown streaming child role `{role}`"),
        }
    }

    // Trust: exercise the real reader and fixture under the libtest mode that
    // writes a status prefix immediately before calling the child test body.
    #[test]
    fn streaming_fixture_preserves_first_line_in_single_thread_mode() {
        let mut cmd = streaming_child_command("framed-lines");
        cmd.env("RUST_TEST_THREADS", "1");
        let mut lines = Vec::new();
        let output = cmd
            .exec_with_streaming_limits(
                &mut |line| {
                    lines.push(line.to_owned());
                    Ok(())
                },
                &mut |_| Ok(()),
                true,
                small_streaming_limits(),
            )
            .unwrap();
        for payload in ["first-payload-line", "second-payload-line"] {
            assert_eq!(lines.iter().filter(|line| *line == payload).count(), 1);
        }
        assert_eq!(
            lines,
            String::from_utf8(output.stdout)
                .unwrap()
                .lines()
                .map(str::to_owned)
                .collect::<Vec<_>>()
        );
    }

    #[test]
    fn bounded_streaming_rejects_oversized_newline_free_stdout() {
        let cmd = streaming_child_command("oversized-stdout");
        let started = Instant::now();
        let error = cmd
            .exec_with_streaming_limits(
                &mut |_| Ok(()),
                &mut |_| Ok(()),
                false,
                small_streaming_limits(),
            )
            .unwrap_err();
        assert_fast_failure(started);
        let error = format!("{error:#}");
        assert!(
            error.contains("streaming stdout line exceeds the 1024-byte safety limit"),
            "{error}"
        );
    }

    #[cfg(any(target_os = "linux", target_os = "macos"))]
    #[test]
    fn child_exit_cleanup_drains_final_bytes_and_stops_inherited_pipe_holders() {
        let _test_lease = CHILD_EXIT_TEST_LOCK
            .lock()
            .unwrap_or_else(|error| error.into_inner());
        let temp = tempfile::tempdir().unwrap();
        let marker = temp.path().join("descendant-survived");
        let mut cmd = streaming_child_command("exit-with-inherited-pipes");
        cmd.env(STREAMING_CHILD_MARKER, &marker);
        let mut stdout = Vec::new();
        let mut stderr = Vec::new();
        let started = Instant::now();
        let output = cmd
            .exec_with_streaming_limits(
                &mut |line| {
                    stdout.push(line.to_owned());
                    Ok(())
                },
                &mut |line| {
                    stderr.push(line.to_owned());
                    Ok(())
                },
                false,
                small_streaming_limits()
                    .with_child_exit_cleanup()
                    .with_timeout(Duration::from_secs(5)),
            )
            .unwrap();
        assert!(output.status.success());
        assert_fast_failure(started);
        assert!(
            stdout
                .iter()
                .any(|line| line.ends_with("leader-final-line")),
            "{stdout:?}"
        );
        assert!(
            stdout.iter().any(|line| line == "leader-final-tail"),
            "{stdout:?}"
        );
        assert!(
            stderr.iter().any(|line| line == "leader-final-stderr"),
            "{stderr:?}"
        );
        thread::sleep(Duration::from_secs(1));
        assert!(
            !marker.exists(),
            "an inherited pipe holder survived leader exit"
        );
    }

    #[cfg(any(target_os = "linux", target_os = "macos"))]
    #[test]
    fn child_exit_cleanup_preserves_newline_free_line_bounds() {
        let _test_lease = CHILD_EXIT_TEST_LOCK
            .lock()
            .unwrap_or_else(|error| error.into_inner());
        for role in ["oversized-stdout", "oversized-stderr"] {
            let cmd = streaming_child_command(role);
            let started = Instant::now();
            let error = cmd
                .exec_with_streaming_limits(
                    &mut |_| Ok(()),
                    &mut |_| Ok(()),
                    false,
                    small_streaming_limits()
                        .with_child_exit_cleanup()
                        .with_timeout(Duration::from_secs(5)),
                )
                .unwrap_err();
            assert_fast_failure(started);
            assert!(format!("{error:#}").contains("line exceeds"), "{error:#}");
        }
    }

    #[cfg(any(target_os = "linux", target_os = "macos"))]
    #[test]
    fn child_exit_cleanup_cancels_on_callback_rejection_and_panic() {
        let _test_lease = CHILD_EXIT_TEST_LOCK
            .lock()
            .unwrap_or_else(|error| error.into_inner());
        for panic in [false, true] {
            let temp = tempfile::tempdir().unwrap();
            let marker = temp.path().join("descendant-survived");
            let mut cmd = streaming_child_command("callback-parent");
            cmd.env(STREAMING_CHILD_MARKER, &marker);
            let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                cmd.exec_with_streaming_limits(
                    &mut |line| {
                        if line.ends_with("reject-now") {
                            if panic {
                                panic!("deliberate callback panic");
                            }
                            bail!("deliberate callback rejection");
                        }
                        Ok(())
                    },
                    &mut |_| Ok(()),
                    false,
                    small_streaming_limits()
                        .with_child_exit_cleanup()
                        .with_timeout(Duration::from_secs(5)),
                )
            }));
            if panic {
                assert!(result.is_err());
            } else {
                let error = result.unwrap().unwrap_err();
                assert!(format!("{error:#}").contains("deliberate callback rejection"));
            }
            thread::sleep(Duration::from_secs(1));
            assert!(
                !marker.exists(),
                "a pipe holder survived callback cancellation"
            );
        }
    }

    #[cfg(any(target_os = "linux", target_os = "macos"))]
    #[test]
    fn child_exit_cleanup_timeout_still_applies_after_pipes_close() {
        let _test_lease = CHILD_EXIT_TEST_LOCK
            .lock()
            .unwrap_or_else(|error| error.into_inner());
        let cmd = streaming_child_command("closed-pipes-hang");
        let started = Instant::now();
        let (stats, result) = cmd.exec_with_streaming_limits_and_stats(
            &mut |_| Ok(()),
            &mut |_| Ok(()),
            false,
            small_streaming_limits()
                .with_child_exit_cleanup()
                .with_timeout(Duration::from_millis(100)),
            true,
        );
        let error = result.unwrap_err();
        assert_fast_failure(started);
        assert!(format!("{error:#}").contains("timeout"), "{error:#}");
        assert!(
            stats.cpu_times.is_some(),
            "a canceled child was actually reaped: {stats:?}"
        );
    }

    #[cfg(any(target_os = "linux", target_os = "macos"))]
    #[test]
    fn child_exit_cleanup_handles_signals_and_restores_handlers() {
        let _test_lease = CHILD_EXIT_TEST_LOCK
            .lock()
            .unwrap_or_else(|error| error.into_inner());
        for signal in super::STREAMING_SIGNALS {
            let mut prior: libc::sigaction = unsafe { std::mem::zeroed() };
            assert_eq!(
                unsafe { libc::sigaction(signal, std::ptr::null(), &mut prior) },
                0
            );
            let temp = tempfile::tempdir().unwrap();
            let marker = temp.path().join("descendant-survived");
            let mut cmd = streaming_child_command("callback-parent");
            cmd.env(STREAMING_CHILD_MARKER, &marker);
            let mut raised = false;
            let error = cmd
                .exec_with_streaming_limits(
                    &mut |line| {
                        if line.ends_with("reject-now") && !raised {
                            let mut current: libc::sigaction = unsafe { std::mem::zeroed() };
                            assert_eq!(
                                unsafe { libc::sigaction(signal, std::ptr::null(), &mut current) },
                                0
                            );
                            // Check before raising so a missing installation is a
                            // normal assertion failure, not a killed test harness.
                            assert_eq!(
                                current.sa_sigaction,
                                super::StreamingSignals::handler_address()
                            );
                            raised = true;
                            assert_eq!(unsafe { libc::raise(signal) }, 0);
                        }
                        Ok(())
                    },
                    &mut |_| Ok(()),
                    false,
                    small_streaming_limits()
                        .with_child_exit_cleanup()
                        .with_timeout(Duration::from_secs(5)),
                )
                .unwrap_err();
            assert!(raised);
            assert!(
                format!("{error:#}").contains("interrupted by signal"),
                "{error:#}"
            );
            let mut restored: libc::sigaction = unsafe { std::mem::zeroed() };
            assert_eq!(
                unsafe { libc::sigaction(signal, std::ptr::null(), &mut restored) },
                0
            );
            assert_eq!(restored.sa_sigaction, prior.sa_sigaction);
            assert_eq!(restored.sa_flags, prior.sa_flags);
            thread::sleep(Duration::from_secs(1));
            assert!(
                !marker.exists(),
                "an isolated descendant survived signal {signal}"
            );
        }
    }

    #[cfg(any(target_os = "linux", target_os = "macos"))]
    #[test]
    fn child_exit_cleanup_shares_signal_custody_and_isolates_cancellation() {
        let _test_lease = CHILD_EXIT_TEST_LOCK
            .lock()
            .unwrap_or_else(|error| error.into_inner());
        let mut before: libc::sigaction = unsafe { std::mem::zeroed() };
        assert_eq!(
            unsafe { libc::sigaction(libc::SIGTERM, std::ptr::null(), &mut before) },
            0
        );
        let first = super::StreamingProcessScope::new().unwrap();
        let second = super::StreamingProcessScope::new().unwrap();
        first.cancel();
        assert!(first.interrupted());
        assert!(!second.interrupted());
        let mut cancelled = streaming_child_command("framed-lines");
        cancelled.supervised_by(&first);
        assert!(
            cancelled
                .exec_with_streaming_limits(
                    &mut |_| Ok(()),
                    &mut |_| Ok(()),
                    false,
                    small_streaming_limits().with_child_exit_cleanup()
                )
                .is_err()
        );
        let mut surviving = streaming_child_command("framed-lines");
        surviving.supervised_by(&second);
        thread::spawn(move || {
            surviving.exec_with_streaming_limits(
                &mut |_| Ok(()),
                &mut |_| Ok(()),
                false,
                small_streaming_limits().with_child_exit_cleanup(),
            )
        })
        .join()
        .unwrap()
        .unwrap();
        drop(first);
        let mut during: libc::sigaction = unsafe { std::mem::zeroed() };
        assert_eq!(
            unsafe { libc::sigaction(libc::SIGTERM, std::ptr::null(), &mut during) },
            0
        );
        assert_eq!(
            during.sa_sigaction,
            super::StreamingSignals::handler_address()
        );
        second.finish().unwrap();
        let mut after: libc::sigaction = unsafe { std::mem::zeroed() };
        assert_eq!(
            unsafe { libc::sigaction(libc::SIGTERM, std::ptr::null(), &mut after) },
            0
        );
        assert_eq!(before.sa_sigaction, after.sa_sigaction);
        assert_eq!(before.sa_flags, after.sa_flags);
    }

    #[cfg(any(target_os = "linux", target_os = "macos"))]
    #[test]
    fn child_exit_cleanup_never_accepts_a_late_termination_signal() {
        let _test_lease = CHILD_EXIT_TEST_LOCK
            .lock()
            .unwrap_or_else(|error| error.into_inner());
        let temp = tempfile::tempdir().unwrap();
        let marker = temp.path().join("descendant-survived");
        let mut cmd = streaming_child_command("exit-with-inherited-pipes");
        cmd.env(STREAMING_CHILD_MARKER, &marker);
        let mut raised = false;
        let error = cmd
            .exec_with_streaming_limits(
                &mut |line| {
                    if line.ends_with("leader-final-line") && !raised {
                        let mut action: libc::sigaction = unsafe { std::mem::zeroed() };
                        assert_eq!(
                            unsafe {
                                libc::sigaction(libc::SIGTERM, std::ptr::null(), &mut action)
                            },
                            0
                        );
                        assert_eq!(
                            action.sa_sigaction,
                            super::StreamingSignals::handler_address()
                        );
                        raised = true;
                        assert_eq!(unsafe { libc::raise(libc::SIGTERM) }, 0);
                    }
                    Ok(())
                },
                &mut |_| Ok(()),
                false,
                small_streaming_limits()
                    .with_child_exit_cleanup()
                    .with_timeout(Duration::from_secs(5)),
            )
            .unwrap_err();
        assert!(raised);
        assert!(
            format!("{error:#}").contains("interrupted by signal"),
            "{error:#}"
        );
        thread::sleep(Duration::from_secs(1));
        assert!(!marker.exists());
    }

    #[test]
    fn bounded_streaming_rejects_oversized_newline_free_stderr() {
        let cmd = streaming_child_command("oversized-stderr");
        let started = Instant::now();
        let error = cmd
            .exec_with_streaming_limits(
                &mut |_| Ok(()),
                &mut |_| Ok(()),
                false,
                small_streaming_limits(),
            )
            .unwrap_err();
        assert_fast_failure(started);
        let error = format!("{error:#}");
        assert!(
            error.contains("streaming stderr line exceeds the 1024-byte safety limit"),
            "{error}"
        );
    }

    // Trust: the actual refusal formatter is byte-oriented, including escaped
    // quotes/backslashes, terminal control bytes, invalid UTF-8 and Unicode.
    #[test]
    fn streaming_line_prefix_escapes_untrusted_bytes_as_printable_ascii() {
        let bytes = b"\x00\t\n\r\x1b\x7f\"'\\{}\xc3\xa9\xff\xe2\x80\xae";
        let prefix = StreamingLinePrefix(bytes).to_string();
        assert_eq!(
            prefix,
            r#"\x00\t\n\r\x1b\x7f\"\'\\{}\xc3\xa9\xff\xe2\x80\xae"#,
        );
        assert!(prefix.bytes().all(|byte| byte.is_ascii_graphic()));
    }

    #[test]
    fn streaming_line_prefix_bounds_reads_and_writes_at_a_unicode_boundary() {
        use std::fmt::Write as _;

        // The fixed input bound cuts a Unicode character between its bytes.
        // Changing every following byte must have no effect on the context.
        let mut line = vec![b'x'; STREAMING_LINE_PREFIX_BYTES - 1];
        line.extend_from_slice("é".as_bytes());
        line.resize(2 * 1024 * 1024, 0xff);
        let prefix = StreamingLinePrefix(&line).to_string();
        assert_eq!(prefix, format!("{}\\xc3", "x".repeat(255)));
        line[STREAMING_LINE_PREFIX_BYTES..].fill(b'y');
        assert_eq!(StreamingLinePrefix(&line).to_string(), prefix);
        assert_eq!(StreamingLinePrefix(&[]).to_string(), "");

        // A fixed sink refuses any output beyond the worst-case 4:1 expansion.
        // The production formatter allocates nothing, regardless of line size.
        struct BoundedSink(usize);
        impl std::fmt::Write for BoundedSink {
            fn write_str(&mut self, value: &str) -> std::fmt::Result {
                self.0 += value.len();
                assert!(self.0 <= 4 * STREAMING_LINE_PREFIX_BYTES);
                assert!(value.bytes().all(|byte| byte.is_ascii_graphic()));
                Ok(())
            }
        }
        line.fill(0xff);
        let mut sink = BoundedSink(0);
        write!(&mut sink, "{}", StreamingLinePrefix(&line)).unwrap();
        assert_eq!(sink.0, 4 * STREAMING_LINE_PREFIX_BYTES);
    }

    #[test]
    fn a_long_line_is_cut_to_the_limit_behind_its_mark() {
        let mark = long_line_mark(40);
        let keep = 40 - mark.len();
        let cut = |line: &[u8]| [mark.as_bytes(), &line[..keep]].concat();
        // Whole lines, a long one among them, and a short tail left alone.
        let mut dropping = false;
        let long = b"test a ... ok and then far more than forty bytes of it";
        let mut data = [b"short\n".as_slice(), long, b"\nlast\ntail"].concat();
        assert!(cut_long_lines(&mut data, 40, &mut dropping));
        assert_eq!(
            data,
            [b"short\n".as_slice(), &cut(long), b"\nlast\ntail"].concat()
        );
        assert!(!dropping);
        assert_eq!(oversized_line(&data, 40), None);
        // Nothing to cut: untouched, and said so.
        assert!(!cut_long_lines(&mut data, 40, &mut dropping));
        // A long tail is ended where it is cut; what follows of that line is
        // dropped, over as many reads as it takes, and the next line is kept.
        let mut data = vec![b'z'; 41];
        assert!(cut_long_lines(&mut data, 40, &mut dropping));
        assert_eq!(data, [cut(&[b'z'; 41]).as_slice(), b"\n"].concat());
        assert!(dropping);
        let mut data = b"zzzz".to_vec();
        assert!(cut_long_lines(&mut data, 40, &mut dropping));
        assert!(data.is_empty() && dropping);
        let mut data = b"zz\nnext\n".to_vec();
        assert!(cut_long_lines(&mut data, 40, &mut dropping));
        assert_eq!(data, b"next\n");
        assert!(!dropping);
        // Exactly the limit is not long (CR counts, the newline does not).
        let mut data = [vec![b'k'; 40], b"\n".to_vec()].concat();
        assert!(!cut_long_lines(&mut data, 40, &mut dropping));
        // No cut line begins as the child began it.
        assert!(mark.starts_with('[') && mark.ends_with(' '));
    }

    #[test]
    fn bounded_streaming_cuts_long_lines_and_keeps_reading() {
        let limits = small_streaming_limits().with_long_lines_cut();
        let mark = long_line_mark(1024);
        let keep = 1024 - mark.len();
        let mut lines = Vec::new();
        streaming_child_command("long-lines")
            .exec_with_streaming_limits(
                &mut |_| Ok(()),
                &mut |line| {
                    lines.push(line.to_owned());
                    Ok(())
                },
                false,
                limits,
            )
            .unwrap();
        let first = format!("test a ... ok{}", "x".repeat(3000));
        let second = format!("{}{}{}", "p".repeat(900), "q".repeat(900), "r".repeat(900));
        assert_eq!(
            lines,
            [
                "before".to_owned(),
                format!("{mark}{}", &first[..keep]),
                "between".to_owned(),
                format!("{mark}{}", &second[..keep]),
                "after".to_owned(),
                format!("{mark}{}", "y".repeat(keep)),
            ]
        );
        assert!(lines.iter().all(|line| line.len() <= 1024));
        // Without the mode the same child is stopped at its first long line.
        let error = streaming_child_command("long-lines")
            .exec_with_streaming_limits(
                &mut |_| Ok(()),
                &mut |_| Ok(()),
                false,
                small_streaming_limits(),
            )
            .unwrap_err();
        assert!(
            format!("{error:#}").contains("1024-byte safety limit"),
            "{error:#}"
        );
        // The dropped bytes are still the child's output: the aggregate
        // budget counts them and stops a child that writes past it.
        let error = streaming_child_command("long-lines")
            .exec_with_streaming_limits(
                &mut |_| Ok(()),
                &mut |_| Ok(()),
                false,
                StreamingOutputLimits::new(1024, 8 * 1024).with_long_lines_cut(),
            )
            .unwrap_err();
        assert!(
            format!("{error:#}")
                .contains("streaming stderr exceeds the 8192-byte aggregate safety limit"),
            "{error:#}"
        );
        // A limit with no room for the mark is refused before any child runs.
        let error = streaming_child_command("long-lines")
            .exec_with_streaming_limits(
                &mut |_| Ok(()),
                &mut |_| Ok(()),
                false,
                StreamingOutputLimits::new(8, 1024).with_long_lines_cut(),
            )
            .unwrap_err();
        assert!(
            format!("{error:#}").contains("leaves no room for a cut line's mark"),
            "{error:#}"
        );
    }

    #[test]
    fn oversized_line_identifies_the_offending_line_without_changing_the_cap() {
        let bytes = b"short\nsecond\nproducer-too-long\nlast";
        let line = oversized_line(bytes, 6).unwrap();
        assert_eq!(line, b"producer-too-long");
        assert_eq!(line.as_ptr(), bytes[13..].as_ptr());
        assert_eq!(oversized_line(b"123456\n123456", 6), None);
        assert_eq!(oversized_line(b"123456\n1234567", 6), Some(&b"1234567"[..]));
        // Existing byte semantics count CR but not the terminating LF.
        assert_eq!(oversized_line(b"123456\r\n", 6), Some(&b"123456\r"[..]));
    }

    #[test]
    fn bounded_streaming_reports_only_the_rejected_diagnostic_prefix() {
        for role in [
            "oversized-diagnostic-complete",
            "oversized-diagnostic-tail",
            "oversized-diagnostic-eof",
            "oversized-diagnostic-split",
        ] {
            let cmd = streaming_child_command(role);
            let started = Instant::now();
            let mut visited = Vec::new();
            let error = cmd
                .exec_with_streaming_limits(
                    &mut |_| Ok(()),
                    &mut |line| {
                        visited.push(line.to_owned());
                        Ok(())
                    },
                    false,
                    small_streaming_limits(),
                )
                .unwrap_err();
            assert_fast_failure(started);
            // Neither a rejected report nor its following summary can become
            // evidence, even when the child exits successfully at EOF.
            assert!(
                visited.iter().all(|line| line == "earlier-line"),
                "{visited:?}"
            );
            let error = format!("{error:#}");
            assert!(error.contains("1024-byte safety limit"), "{role}: {error}");
            assert!(
                error.contains("line prefix (up to 256 bytes, ASCII-escaped)"),
                "{error}"
            );
            assert!(
                error.contains(&StreamingLinePrefix(DIAGNOSTIC_PREFIX).to_string()),
                "{error}"
            );
            assert!(!error.contains("PRIVATE-SUFFIX"), "{error}");
            assert!(!error.contains('\u{1b}'), "{error}");
            assert!(!error.contains('\r'), "{error}");
            assert!(!error.contains('\0'), "{error}");
        }
    }

    #[test]
    fn bounded_streaming_rejects_aggregate_output() {
        let cmd = streaming_child_command("aggregate-stdout");
        let started = Instant::now();
        let error = cmd
            .exec_with_streaming_limits(
                &mut |_| Ok(()),
                &mut |_| Ok(()),
                true,
                StreamingOutputLimits::new(1024, 4096),
            )
            .unwrap_err();
        assert_fast_failure(started);
        let error = format!("{error:#}");
        assert!(
            error.contains("streaming stdout exceeds the 4096-byte aggregate safety limit"),
            "{error}"
        );
    }

    /// The failure this scaling was written for, end to end and through the
    /// real streaming path: a child that emits more than the old flat 512 MiB
    /// and less than this machine's share of its own memory must be READ, not
    /// refused. Deleting the one line in `exec_with_streaming_impl` that
    /// resolves the ceiling turns this test red — and nothing else in this
    /// module notices, because every other test of the rule calls the pure
    /// function directly.
    ///
    /// The ceiling is recomputed here from the prose rule (an eighth of memory,
    /// never below the floor) rather than from `scaled_stream_ceiling`, so a
    /// wrong rule cannot agree with itself. On a machine too small to tell the
    /// rule from the constant the same stream must be refused, naming the
    /// figure actually applied; that branch is the pre-existing behaviour.
    #[test]
    fn a_transport_stream_over_the_old_flat_ceiling_is_bounded_by_this_machine() {
        let ceiling = (effective_physical_memory_bytes() / 8)
            .max(MAX_AUTHENTICATED_TRANSPORT_FLOOR_BYTES as u64);
        let cmd = streaming_child_command("transport-scale-stdout");
        let mut flood_bytes = 0_usize;
        let started = Instant::now();
        let result = cmd.exec_with_streaming_limits(
            &mut |line| {
                // The child is a test binary: its harness writes a few short
                // lines of its own around the flood. Count only the flood.
                if line.len() + 1 == TRANSPORT_SCALE_LINE_BYTES {
                    flood_bytes += TRANSPORT_SCALE_LINE_BYTES;
                }
                Ok(())
            },
            &mut |_| Ok(()),
            false,
            StreamingOutputLimits::new(
                TRANSPORT_POLICY_LINE_BYTES,
                MAX_AUTHENTICATED_TRANSPORT_FLOOR_BYTES,
            ),
        );
        if ceiling >= TRANSPORT_SCALE_STDOUT_BYTES as u64 {
            let output = result.unwrap_or_else(|error| {
                panic!(
                    "{TRANSPORT_SCALE_STDOUT_BYTES} bytes of stdout refused on a machine whose \
                     ceiling is {ceiling}: {error:#}"
                )
            });
            assert!(output.status.success(), "{:?}", output.status);
            assert_eq!(flood_bytes, TRANSPORT_SCALE_STDOUT_BYTES);
            // `capture_output: false` — the mode every rustc compile runs in.
            // Nothing was retained, which is why the aggregate this test moves
            // is a volume bound and not a memory bound on that path.
            assert!(
                output.stdout.is_empty(),
                "an uncaptured stream was retained"
            );
        } else {
            let error = format!("{:#}", result.unwrap_err());
            assert!(
                error.contains(&format!(
                    "streaming stdout exceeds the {ceiling}-byte aggregate safety limit"
                )),
                "{error}"
            );
            assert!(
                started.elapsed() < Duration::from_secs(60),
                "rejection did not terminate the child promptly: {:?}",
                started.elapsed()
            );
        }
    }

    #[test]
    fn the_stream_ceiling_is_an_eighth_of_memory_and_never_below_the_floor() {
        // A machine too small to matter, or one whose memory cannot be read at
        // all, gets the floor: exactly the flat bound this rule replaced.
        assert_eq!(
            scaled_stream_ceiling(MAX_AUTHENTICATED_TRANSPORT_FLOOR_BYTES, 0),
            MAX_AUTHENTICATED_TRANSPORT_FLOOR_BYTES
        );
        assert_eq!(
            scaled_stream_ceiling(MAX_AUTHENTICATED_TRANSPORT_FLOOR_BYTES, 2 * GIB),
            MAX_AUTHENTICATED_TRANSPORT_FLOOR_BYTES
        );
        // A large machine gets an eighth of what it actually has. Spelled out
        // in bytes: the 128 GiB box whose 337-unit run failed at 536870912 now
        // stops at 17179869184, thirty-two times as far.
        assert_eq!(
            scaled_stream_ceiling(MAX_AUTHENTICATED_TRANSPORT_FLOOR_BYTES, 16 * GIB),
            2_147_483_648
        );
        assert_eq!(
            scaled_stream_ceiling(MAX_AUTHENTICATED_TRANSPORT_FLOOR_BYTES, 137_438_953_472),
            17_179_869_184
        );
        // Arithmetic at the top of the range saturates rather than wrapping,
        // written as `input_limits.rs:54` (`transport_ceiling_tests`) writes
        // it, so the two copies of the rule are checked against each other
        // rather than each against itself.
        assert_eq!(
            scaled_stream_ceiling(MAX_AUTHENTICATED_TRANSPORT_FLOOR_BYTES, u64::MAX),
            usize::MAX.min((u64::MAX / 8) as usize)
        );
    }

    #[test]
    fn a_deliberately_tight_stream_budget_is_applied_verbatim() {
        // Below the floor the caller is asserting a property of one child, not
        // guarding memory. The verified rustdoc `-Vv` identity probe's 64 KiB
        // budget and this module's own 16 KiB/4096/1024-byte cases must hold on
        // a machine of any size.
        assert_eq!(scaled_stream_ceiling(64 * 1024, 128 * GIB), 64 * 1024);
        assert_eq!(scaled_stream_ceiling(16 * 1024, 128 * GIB), 16 * 1024);
        assert_eq!(scaled_stream_ceiling(4096, 128 * GIB), 4096);
        assert_eq!(scaled_stream_ceiling(1024, 128 * GIB), 1024);
        assert_eq!(scaled_stream_ceiling(4096, 0), 4096);
        // At or above the floor the caller's own figure still wins whenever it
        // is the larger of the two.
        assert_eq!(
            scaled_stream_ceiling(4 * GIB as usize, 2 * GIB),
            4 * GIB as usize
        );
    }

    #[test]
    fn resolving_limits_fixes_the_number_the_rejection_message_names() {
        // The 4096-byte aggregate case above resolves to itself, which is why
        // its message still says 4096 on this 128 GiB machine.
        let small = StreamingOutputLimits::new(1024, 4096);
        assert_eq!(small.resolved(), small);
        assert_eq!(
            small_streaming_limits().resolved(),
            small_streaming_limits()
        );

        let transport =
            StreamingOutputLimits::new(128 * 1024 * 1024, MAX_AUTHENTICATED_TRANSPORT_FLOOR_BYTES)
                .resolved();
        assert_eq!(transport.max_line_bytes, 128 * 1024 * 1024);
        assert!(transport.max_stream_bytes >= MAX_AUTHENTICATED_TRANSPORT_FLOOR_BYTES);
        // The figure a rejection would name on THIS machine, derived from the
        // prose rule rather than by calling the function that implements it.
        let memory = effective_physical_memory_bytes();
        let expected = if memory / 8 > MAX_AUTHENTICATED_TRANSPORT_FLOOR_BYTES as u64 {
            usize::try_from(memory / 8).expect("an eighth of addressable memory is addressable")
        } else {
            MAX_AUTHENTICATED_TRANSPORT_FLOOR_BYTES
        };
        assert_eq!(transport.max_stream_bytes, expected);
        // Resolution is idempotent, so a limit cannot drift by being resolved
        // more than once, and the timeout is carried through untouched.
        assert_eq!(transport.resolved(), transport);
        let timed = small_streaming_limits().with_timeout(Duration::from_millis(200));
        assert_eq!(timed.resolved().timeout, Some(Duration::from_millis(200)));
    }

    #[cfg(any(target_os = "macos", target_os = "linux"))]
    #[test]
    fn the_machine_memory_reader_reads_this_machine() {
        assert!(
            effective_physical_memory_bytes() > 0,
            "the scaled ceiling silently degrades to its floor when memory cannot be read"
        );
    }

    #[test]
    fn a_cgroup_memory_limit_is_taken_only_when_it_is_a_real_bound() {
        use CgroupMemoryLimit::{Bytes, Unconstrained, Unintelligible};
        assert_eq!(
            parse_linux_cgroup_memory_limit("  4294967296  "),
            Bytes(4 * GIB)
        );
        assert_eq!(parse_linux_cgroup_memory_limit("max\n"), Unconstrained);
        // cgroup v1's "unlimited" is a saturated page count, not 8 EiB of RAM.
        assert_eq!(
            parse_linux_cgroup_memory_limit("9223372036854771712\n"),
            Unconstrained
        );
        assert_eq!(parse_linux_cgroup_memory_limit("0\n"), Unintelligible);
        assert_eq!(
            parse_linux_cgroup_memory_limit("not-a-number"),
            Unintelligible
        );
        assert_eq!(parse_linux_cgroup_memory_limit(""), Unintelligible);
    }

    #[test]
    fn an_unreadable_cgroup_authority_fails_closed_the_way_trust_router_does() {
        // Absent: no authority, so the host figure stands. This is a machine
        // without cgroups, not a machine hiding its limits.
        assert_eq!(
            linux_cgroup_memory_authority(Err(io::Error::from(io::ErrorKind::NotFound))),
            None
        );
        // Present and unreadable, or present and unintelligible: `Some(0)`
        // collapses the ceiling to its floor rather than assuming the host
        // total inside a domain that will not say how large it is. Before this,
        // both of these silently returned the host figure — the fail-OPEN drift
        // that `trust-router/src/memory_jobserver.rs:1848` does not have.
        assert_eq!(
            linux_cgroup_memory_authority(Err(io::Error::from(io::ErrorKind::PermissionDenied))),
            Some(0)
        );
        assert_eq!(
            linux_cgroup_memory_authority(Ok("not-a-number".to_string())),
            Some(0)
        );
        // Unconstrained authorities keep the host figure.
        assert_eq!(linux_cgroup_memory_authority(Ok("max\n".to_string())), None);
        assert_eq!(
            linux_cgroup_memory_authority(Ok("9223372036854771712\n".to_string())),
            None
        );
        // A real limit caps it.
        assert_eq!(
            linux_cgroup_memory_authority(Ok("4294967296\n".to_string())),
            Some(4 * GIB)
        );
        // And a capped machine is still scaled by what it was capped TO: 4 GiB
        // of container is an eighth of 4 GiB, which is below the floor.
        assert_eq!(
            scaled_stream_ceiling(MAX_AUTHENTICATED_TRANSPORT_FLOOR_BYTES, 4 * GIB),
            MAX_AUTHENTICATED_TRANSPORT_FLOOR_BYTES
        );
    }

    #[test]
    fn bounded_streaming_times_out_a_silent_hung_child() {
        let cmd = streaming_child_command("silent-hang");
        let started = Instant::now();
        let error = cmd
            .exec_with_streaming_limits(
                &mut |_| Ok(()),
                &mut |_| Ok(()),
                false,
                small_streaming_limits().with_timeout(Duration::from_millis(200)),
            )
            .unwrap_err();
        assert_fast_failure(started);
        let error = format!("{error:#}");
        assert!(error.contains("wall-clock timeout"), "{error}");
    }

    #[cfg(unix)]
    #[test]
    fn bounded_streaming_times_out_after_a_child_closes_its_pipes() {
        let cmd = streaming_child_command("closed-pipes-hang");
        let started = Instant::now();
        let error = cmd
            .exec_with_streaming_limits(
                &mut |_| Ok(()),
                &mut |_| Ok(()),
                false,
                small_streaming_limits().with_timeout(Duration::from_millis(200)),
            )
            .unwrap_err();
        assert_fast_failure(started);
        let error = format!("{error:#}");
        assert!(error.contains("wall-clock timeout"), "{error}");
    }

    #[cfg(unix)]
    #[test]
    fn bounded_streaming_timeout_kills_the_child_process_group() {
        let temp = tempfile::tempdir().unwrap();
        let marker = temp.path().join("timeout-descendant-survived");
        let mut cmd = streaming_child_command("timeout-parent");
        cmd.env(STREAMING_CHILD_MARKER, &marker);
        let started = Instant::now();
        let error = cmd
            .exec_with_streaming_limits(
                &mut |_| Ok(()),
                &mut |_| Ok(()),
                false,
                small_streaming_limits().with_timeout(Duration::from_millis(200)),
            )
            .unwrap_err();
        assert_fast_failure(started);
        let error = format!("{error:#}");
        assert!(error.contains("wall-clock timeout"), "{error}");

        thread::sleep(Duration::from_millis(2200));
        assert!(
            !marker.exists(),
            "a descendant survived the timed-out child's isolated process group"
        );
    }

    #[test]
    fn bounded_streaming_rejects_a_later_complete_line_from_one_read() {
        let cmd = streaming_child_command("burst-later-rejection");
        let started = Instant::now();
        let mut visited = Vec::new();
        let error = cmd
            .exec_with_streaming_limits(
                &mut |_| Ok(()),
                &mut |line| {
                    visited.push(line.to_owned());
                    if line == "reject-later" {
                        bail!("deliberate later-line rejection");
                    }
                    Ok(())
                },
                false,
                small_streaming_limits(),
            )
            .unwrap_err();
        assert_fast_failure(started);
        assert_eq!(visited, ["first", "reject-later"]);
        let error = format!("{error:#}");
        assert!(error.contains("deliberate later-line rejection"), "{error}");
    }

    #[test]
    fn retained_partial_line_bytes_are_not_counted_twice() {
        let cmd = streaming_child_command("split-partial");
        let started = Instant::now();
        let mut visited = Vec::new();
        let error = cmd
            .exec_with_streaming_limits(
                &mut |_| Ok(()),
                &mut |line| {
                    visited.push(line.to_owned());
                    if line == "partialmore" {
                        bail!("deliberate joined-line rejection");
                    }
                    Ok(())
                },
                false,
                StreamingOutputLimits::new(1024, 21),
            )
            .unwrap_err();
        assert_fast_failure(started);
        assert_eq!(visited, ["complete", "partialmore"]);
        let error = format!("{error:#}");
        assert!(
            error.contains("deliberate joined-line rejection"),
            "{error}"
        );
        assert!(!error.contains("aggregate safety limit"), "{error}");
    }

    #[test]
    fn callback_rejection_kills_hanging_child_process_group() {
        let temp = tempfile::tempdir().unwrap();
        let marker = temp.path().join("descendant-survived");
        let mut cmd = streaming_child_command("callback-parent");
        cmd.env(STREAMING_CHILD_MARKER, &marker);
        let started = Instant::now();
        let error = cmd
            .exec_with_streaming_limits(
                &mut |line| {
                    if line == "reject-now" {
                        bail!("deliberate callback rejection");
                    }
                    Ok(())
                },
                &mut |_| Ok(()),
                false,
                small_streaming_limits(),
            )
            .unwrap_err();
        assert_fast_failure(started);
        let error = format!("{error:#}");
        assert!(error.contains("deliberate callback rejection"), "{error}");

        #[cfg(unix)]
        {
            thread::sleep(Duration::from_secs(1));
            assert!(
                !marker.exists(),
                "a descendant holding the child's output pipes survived callback rejection"
            );
        }
    }

    #[cfg(unix)]
    #[test]
    fn inherited_fd_is_scoped_to_the_selected_process_builder() {
        use std::os::fd::{AsRawFd as _, OwnedFd};
        use std::os::unix::net::UnixStream;
        use std::sync::Arc;

        let (_peer, inherited) = UnixStream::pair().unwrap();
        let inherited: OwnedFd = inherited.into();
        let inherited = Arc::new(inherited);
        let fd = inherited.as_raw_fd();
        let flags = unsafe { libc::fcntl(fd, libc::F_GETFD) };
        assert!(flags >= 0);
        assert_ne!(flags & libc::FD_CLOEXEC, 0);

        let mut selected = streaming_child_command("inherited-fd-open");
        selected
            .env(INHERITED_FD_TEST_ENV, fd.to_string())
            .inherit_fd_for_exec(Arc::clone(&inherited))
            .unwrap();
        selected.exec().unwrap();

        let mut unrelated = streaming_child_command("inherited-fd-closed");
        unrelated.env(INHERITED_FD_TEST_ENV, fd.to_string());
        unrelated.exec().unwrap();

        let parent_flags = unsafe { libc::fcntl(fd, libc::F_GETFD) };
        assert!(parent_flags >= 0);
        assert_ne!(parent_flags & libc::FD_CLOEXEC, 0);
    }

    #[test]
    fn argfile_build_succeeds() {
        let mut cmd = ProcessBuilder::new("echo");
        cmd.args(["foo", "bar"].as_slice());
        let (cmd, argfile) = cmd.build_command_with_argfile().unwrap();

        assert_eq!(cmd.get_program(), "echo");
        let cmd_args: Vec<_> = cmd.get_args().map(|s| s.to_str().unwrap()).collect();
        assert_eq!(cmd_args.len(), 1);
        assert!(cmd_args[0].starts_with("@"));
        assert!(cmd_args[0].contains("cargo-argfile."));

        let buf = fs::read_to_string(argfile.path()).unwrap();
        assert_eq!(buf, "foo\nbar\n");
    }

    #[test]
    fn argfile_build_fails_if_arg_contains_newline() {
        let mut cmd = ProcessBuilder::new("echo");
        cmd.arg("foo\n");
        let err = cmd.build_command_with_argfile().unwrap_err();
        assert_eq!(
            err.to_string(),
            "argument for argfile contains newlines: `foo\n`"
        );
    }

    #[test]
    fn argfile_build_fails_if_arg_contains_invalid_utf8() {
        let mut cmd = ProcessBuilder::new("echo");

        #[cfg(windows)]
        let invalid_arg = {
            use std::os::windows::prelude::*;
            std::ffi::OsString::from_wide(&[0x0066, 0x006f, 0xD800, 0x006f])
        };

        #[cfg(unix)]
        let invalid_arg = {
            use std::os::unix::ffi::OsStrExt;
            std::ffi::OsStr::from_bytes(&[0x66, 0x6f, 0x80, 0x6f]).to_os_string()
        };

        cmd.arg(invalid_arg);
        let err = cmd.build_command_with_argfile().unwrap_err();
        assert_eq!(
            err.to_string(),
            "argument for argfile contains invalid UTF-8 characters: `fo�o`"
        );
    }
}
