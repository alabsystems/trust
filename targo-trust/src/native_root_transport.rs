//! One native custodian CLI owner for finite metadata/resolver input and the
//! explicitly negotiated interactive/accounted workload stream.
//! This owns the outer process and original streams, never resource admission.
use std::io::{Read as _, Seek as _, Write as _};
use std::os::fd::{AsRawFd as _, OwnedFd};
use std::os::unix::net::UnixStream;
use std::os::unix::process::ExitStatusExt as _;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::sync::Arc;
use std::time::{Duration, Instant};

use serde::Deserialize;
use serde_json::{Value, json};
use sha2::{Digest as _, Sha256};
use trust_qualification::{Refusal, Result, pair};
use trust_resource_controller::CompletionCause;
use trust_resource_controller::accounting::{CpuTimes, Observation, Scope};
use trust_resource_provenance::{PinnedHelper, Store};
const TOTAL: Duration = Duration::from_secs(900);
const STATUS_MAX: usize = 64 * 1024;
pub(crate) fn hex(bytes: &[u8]) -> String {
    const DIGITS: &[u8; 16] = b"0123456789abcdef";
    let mut output = String::with_capacity(bytes.len().saturating_mul(2));
    for byte in bytes {
        output.push(char::from(DIGITS[(byte >> 4) as usize]));
        output.push(char::from(DIGITS[(byte & 15) as usize]));
    }
    output
}
pub(crate) struct RootSpec<'a> {
    pub program: &'a Path,
    pub cwd: &'a Path,
    pub entry: &'a str,
    pub environment: &'a [(&'a str, &'a std::ffi::OsStr)],
    pub input: &'a [u8],
    pub max_output: usize,
    pub max_stderr: usize,
    pub job: &'a str,
}
pub(crate) struct RootCapture {
    pub output: std::result::Result<Output, String>,
    pub statuses: std::result::Result<Vec<u8>, String>,
    pub image_valid: bool,
    pub observation: Value,
    pub _pin: Arc<PinnedHelper>,
    pub conversation_output: Option<crate::bounded_process::PartialCapture>,
    pub exit_observation: Option<std::process::ExitStatus>,
}
pub(crate) fn capture(spec: RootSpec<'_>, host_store: &Option<PathBuf>) -> Result<RootCapture> {
    capture_mode(spec, host_store, None)
}

/// Interactive support only. Numeric requests and observations grant nothing;
/// the actual host must admit its original cooperative workload/SDK/CPU/memory.
pub(crate) struct Interactive {
    pub input: std::fs::File,
    pub deadline: Instant,
    pub root_timeout_ms: u64,
    pub conversation: crate::bounded_process::Conversation,
    pub protocol: InteractiveProtocol,
}
#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) enum InteractiveProtocol {
    Workload,
    PairedQualification,
}
pub(crate) fn capture_interactive(
    spec: RootSpec<'_>,
    host_store: &Option<PathBuf>,
    interactive: Interactive,
) -> Result<RootCapture> {
    match interactive.protocol {
        InteractiveProtocol::Workload => {
            validate_workload_launch(&spec, interactive.root_timeout_ms, interactive.deadline)?
        }
        InteractiveProtocol::PairedQualification => {
            validate_paired_launch(&spec, interactive.root_timeout_ms, interactive.deadline)?
        }
    }
    capture_mode(spec, host_store, Some(interactive))
}
fn validate_workload_launch(spec: &RootSpec<'_>, timeout_ms: u64, deadline: Instant) -> Result<()> {
    if spec.entry != trust_resource_controller::workload::WORKLOAD_STARTUP_ARGUMENT
        || timeout_ms == 0
        || timeout_ms > trust_resource_controller::workload::budget::MAX_ROOT_TIMEOUT_MS
        || deadline <= Instant::now()
    {
        return Err(Refusal("invalid original finite interactive workload launch".into()));
    }
    let invocation = trust_resource_controller::workload::WorkloadInvocation::decode(spec.input)?;
    validate_invocation_environment(spec, &invocation)
}
fn validate_paired_launch(spec: &RootSpec<'_>, timeout_ms: u64, deadline: Instant) -> Result<()> {
    use trust_resource_controller::paired_qualification::{self as paired, PairedInvocation};
    if spec.entry != paired::PAIRED_STARTUP_ARGUMENT || deadline <= Instant::now() {
        return Err(Refusal("invalid original paired qualification launch".into()));
    }
    let invocation = PairedInvocation::decode(spec.input)?;
    if timeout_ms
        != paired::budget::Budget::new(
            invocation.consumer.repetitions,
            invocation.consumer.timeout_ns,
        )?
        .root_timeout_ms
    {
        return Err(Refusal(
            "paired launch omitted its complete original finite plan budget".into(),
        ));
    }
    validate_invocation_environment(spec, &invocation.consumer)
}
fn validate_invocation_environment(
    spec: &RootSpec<'_>,
    invocation: &trust_resource_controller::workload::WorkloadInvocation,
) -> Result<()> {
    use std::ffi::OsStr;
    use std::path::Component;
    if invocation.program.path != spec.program.as_os_str().as_encoded_bytes()
        || invocation.cwd != spec.cwd.as_os_str().as_encoded_bytes()
    {
        return Err(Refusal(
            "interactive launch differs from its original submitted invocation".into(),
        ));
    }
    let environment =
        spec.environment.iter().copied().collect::<std::collections::BTreeMap<_, _>>();
    let compiler = spec
        .program
        .parent()
        .ok_or_else(|| Refusal("workload program has no actual bin parent".into()))?
        .join("trustc");
    let home = environment.get("CARGO_HOME").map(Path::new);
    if environment.len() != 4
        || spec.environment.len() != 4
        || environment.get("CARGO").copied() != Some(spec.program.as_os_str())
        || environment.get("RUSTC").copied() != Some(compiler.as_os_str())
        || environment.get("CARGO_CACHE_RUSTC_INFO").copied() != Some(OsStr::new("0"))
        || environment
            .get("CARGO_HOME")
            .is_none_or(|home| home.as_encoded_bytes() != invocation.cargo_home)
        || !home.is_some_and(|path| {
            path.is_absolute()
                && path
                    .components()
                    .all(|part| !matches!(part, Component::CurDir | Component::ParentDir))
        })
    {
        return Err(Refusal(
            "interactive workload requires its exact original SDK/compiler/home/cache environment"
                .into(),
        ));
    }
    Ok(())
}
fn capture_mode(
    spec: RootSpec<'_>,
    host_store: &Option<PathBuf>,
    interactive: Option<Interactive>,
) -> Result<RootCapture> {
    let paired = interactive
        .as_ref()
        .is_some_and(|mode| mode.protocol == InteractiveProtocol::PairedQualification);
    // Finite metadata/resolver and oldv1 semantics remain closed. The new
    // paired route offers an EXPECTATION from its independent original pin;
    // only the actual GUI-enrolled backend can compare and admit it.
    if host_store.is_some() && !paired {
        return Err(Refusal("private native root admission requires an original-store root CLI boundary; helper pinning alone cannot select it and account fallback is forbidden".into()));
    }
    for name in ["ATERM_RESOURCE_JOB_V3", "TRUST_CPU_HANDOFF", "TRUST_CPU_IMPLICIT_FD"] {
        if std::env::var_os(name).is_some() {
            return Err(Refusal(format!(
                "paired native root cannot replace original {name}; ancestor borrowing is unsupported"
            )));
        }
    }
    let until = interactive.as_ref().map_or_else(|| Instant::now() + TOTAL, |mode| mode.deadline);
    let accounted = interactive.is_some();
    let root_timeout_ms = interactive.as_ref().map_or(600_000, |mode| mode.root_timeout_ms);
    let store = match host_store {
        Some(path) if paired => Store::open_at(path)?,
        _ => Store::open_account()?,
    };
    let host = store.connect_ancestor((Instant::now() + Duration::from_secs(20)).min(until))?;
    let pin = Arc::new(host.into_helper((Instant::now() + Duration::from_secs(20)).min(until))?);
    let store_expectation = if paired {
        Some(pin.duplicate_original_store((Instant::now() + Duration::from_secs(20)).min(until))?)
    } else {
        None
    };
    let host_image = pair::file_identity(pin.helper_path())?;
    let (input, conversation) = match interactive {
        Some(mode) => (mode.input, Some(mode.conversation)),
        None => {
            let mut input = tempfile::tempfile()?;
            input.write_all(spec.input)?;
            input.flush()?;
            input.rewind()?;
            (input, None)
        }
    };
    let supplied_sha = format!("{:x}", Sha256::digest(spec.input));
    let cancellation = conversation.as_ref().map(|mode| mode.cancellation_flag());
    let (mut status, writer) = UnixStream::pair()?;
    let writer = Arc::new(OwnedFd::from(writer));
    let session = std::env::var("ATERM_PARENT_SESSION_ID")
        .or_else(|_| std::env::var("ATERM_SESSION_ID"))
        .map_err(|_| {
            Refusal("native root requires explicit current aterm session locator".into())
        })?;
    if session.len() > 64
        || !session.strip_prefix("s-").is_some_and(|sid| {
            !sid.is_empty() && sid.bytes().all(|c| c.is_ascii_digit() || (b'a'..=b'f').contains(&c))
        })
    {
        return Err(Refusal("native root session locator is not canonical".into()));
    }
    let mut command = Command::new(pin.helper_path());
    command.args(["resource-run", "--session"]).arg(format!("@{session}"));
    if let Some(socket) = std::env::var_os("ATERM_CONTROL_SOCK") {
        command.arg("--sock").arg(socket);
    }
    command.arg("--job").arg(spec.job);
    if accounted {
        command.arg("--accounted");
    }
    if let Some(original) = &store_expectation {
        command.arg(trust_resource_controller::paired_qualification::host::ORIGINAL_STORE_EXPECTATION_ARGUMENT)
            .arg(original.as_raw_fd().to_string());
    }
    command
        .args([
            "--cpu-units",
            if accounted { "7" } else { "1" },
            "--memory-bytes",
            if accounted { "15032385536" } else { "2147483648" },
            "--timeout-ms",
        ])
        .arg(root_timeout_ms.to_string())
        .arg("--status-fd")
        .arg(writer.as_raw_fd().to_string())
        .arg("--")
        .arg(spec.program)
        .arg(spec.entry)
        .env_clear()
        .env("LANG", "C")
        .env("LC_ALL", "C")
        .current_dir(spec.cwd);
    for (name, value) in spec.environment {
        command.env(name, value);
    }
    let actual_cli_argv: Vec<_> = std::iter::once(command.get_program())
        .chain(command.get_args())
        .map(|s| hex(s.as_encoded_bytes()))
        .collect();
    let mut inherited = vec![writer.as_raw_fd()];
    if let Some(original) = &store_expectation {
        inherited.push(original.as_raw_fd());
    }
    trust_resource_controller::client::inherit_descriptions(&mut command, &inherited)?;
    let status_reader = std::thread::spawn(move || {
        let mut bytes = Vec::new();
        let mut block = [0; 4096];
        let result = (|| -> std::io::Result<()> {
            loop {
                if cancellation
                    .as_ref()
                    .is_some_and(|flag| flag.load(std::sync::atomic::Ordering::Acquire))
                {
                    return Err(std::io::Error::other(
                        "original interactive capture cancelled; status prefix remains incomplete",
                    ));
                }
                if Instant::now() >= until {
                    return Err(std::io::ErrorKind::TimedOut.into());
                }
                let remaining =
                    until.saturating_duration_since(Instant::now()).max(Duration::from_millis(1));
                status.set_read_timeout(Some(if cancellation.is_some() {
                    remaining.min(Duration::from_millis(50))
                } else {
                    remaining
                }))?;
                match status.read(&mut block) {
                    Ok(0) => return Ok(()),
                    Ok(n) => {
                        let retained = n.min(STATUS_MAX.saturating_sub(bytes.len()));
                        bytes.extend_from_slice(&block[..retained]);
                        if retained < n {
                            return Err(std::io::Error::other(
                                "native root status exceeds64KiB; actual prefix retained",
                            ));
                        }
                    }
                    Err(e) if e.kind() == std::io::ErrorKind::Interrupted => continue,
                    Err(e)
                        if cancellation.is_some()
                            && matches!(
                                e.kind(),
                                std::io::ErrorKind::WouldBlock | std::io::ErrorKind::TimedOut
                            ) =>
                    {
                        continue;
                    }
                    Err(e) => return Err(e),
                }
            }
        })();
        (bytes, result.map_err(|e| e.to_string()))
    });
    let check =
        |child: &std::process::Child, deadline: Instant| -> std::result::Result<(), String> {
            pin.validate_child(child, deadline)
                .map(|_| ())
                .map_err(|e| format!("native custodian CLI image mismatch: {e}"))
        };
    let output = match conversation {
        Some(mode) => crate::bounded_process::output_with_checked_conversation(
            &mut command,
            input,
            spec.job,
            [spec.max_output, spec.max_stderr],
            until,
            &check,
            mode,
        ),
        None => crate::bounded_process::output_with_checked_input_file_limits(
            &mut command,
            input,
            spec.job,
            [spec.max_output, spec.max_stderr],
            until,
            &check,
        ),
    };
    drop(command);
    drop(writer);
    let (status_prefix, status_result) = status_reader
        .join()
        .unwrap_or_else(|_| (Vec::new(), Err("native status reader failed".into())));
    let statuses = match status_result {
        Ok(()) => Ok(status_prefix.clone()),
        Err(error) => Err(error),
    };
    let mut observation = json!({"scope":"actual outer CLI capture; root admission/retirement only from original authenticated host lifecycle; Git preparation outside root admission",
        "custodian_image_observation":host_image,"submitted_frame_sha256":supplied_sha,"actual_cli_argv_hex":actual_cli_argv,
        "actual_entry_program":spec.program,"actual_entry_argv":[spec.entry],"root_cwd":spec.cwd,"stdout_max_bytes":spec.max_output,"stderr_max_bytes":spec.max_stderr,
        "submitted_environment":spec.environment.iter().map(|(k,v)|(k,hex(v.as_encoded_bytes()))).collect::<Vec<_>>(),
        "root_status_stream_hex":hex(&status_prefix)});
    if let Err(e) = &statuses {
        observation["status_capture_error"] = json!(e);
    }
    if let Err(e) = &output.validation {
        observation["native_cli_image_refusal"] = json!(e);
    }
    if let Some(partial) = &output.failed_output {
        observation["failed_capture_prefixes"] = json!({"stdout_hex":hex(&partial.bytes[0]),"stderr_hex":hex(&partial.bytes[1]),
        "stdout_eof":partial.eof[0],"stderr_eof":partial.eof[1],"bytes_seen":partial.bytes_seen,"read_errors":partial.read_errors,
        "scope":"actual read prefixes only; no fabricated exit or retirement"});
    }
    if let Ok(captured) = &output.captured {
        observation[if accounted { "entry_stdout_prefix_hex" } else { "entry_stdout_hex" }] =
            json!(hex(&captured.stdout));
        observation["entry_stderr_hex"] = json!(hex(&captured.stderr));
        observation["native_cli_exit"] = json!(captured.status.code());
        observation["native_cli_signal"] = json!(captured.status.signal());
    } else if let Err(e) = &output.captured {
        observation["capture_error"] = json!(e);
    }
    if let Some(streams) = &output.conversation_output {
        observation["interactive_stream_observation"] = json!({"bytes_seen":streams.bytes_seen,"physical_eof":streams.eof,
            "stdout_prefix_bytes":streams.bytes[0].len(),"stderr_prefix_bytes":streams.bytes[1].len(),"scope":"original outer CLI reads; complete protocol bytes belong to the same original streaming sink"});
    }
    observation["root_protocol"] = json!(if paired {
        "interactive-accounted-paired-qualification-v1"
    } else if accounted {
        "interactive-accounted-workload-v1"
    } else {
        "finite-metadata-or-resolver-v1"
    });
    if let Some(exit) = output.exit_observation {
        observation["actual_owning_wait_exit"] = json!({"exit":exit.code(),"signal":exit.signal(),"scope":"original outer CLI only; no hosted root/member/cohort retirement inferred"});
    }
    let mut image_valid = output.validation.is_ok();
    if let Err(e) = pin.validate(until) {
        image_valid = false;
        observation["final_native_cli_image_refusal"] = json!(e.to_string());
    }
    Ok(RootCapture {
        output: output.captured,
        statuses,
        image_valid,
        observation,
        _pin: pin,
        conversation_output: output.conversation_output,
        exit_observation: output.exit_observation,
    })
}
enum Present<T> {
    Missing,
    Value(T),
}
impl<T> Default for Present<T> {
    fn default() -> Self {
        Self::Missing
    }
}
impl<'de, T: Deserialize<'de>> Deserialize<'de> for Present<T> {
    fn deserialize<D: serde::Deserializer<'de>>(d: D) -> std::result::Result<Self, D::Error> {
        T::deserialize(d).map(Self::Value)
    }
}
impl<T> Present<T> {
    fn missing(&self) -> bool {
        matches!(self, Self::Missing)
    }
    fn value(self) -> Result<T> {
        match self {
            Self::Value(value) => Ok(value),
            Self::Missing => Err(Refusal("native root status missing a required field".into())),
        }
    }
}
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct RootOutcome {
    #[serde(default)]
    exit: Present<i32>,
    #[serde(default)]
    signal: Present<i32>,
}
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct RootStatus {
    version: u64,
    session: String,
    attempt: String,
    event: String,
    #[serde(default)]
    pid: Present<u32>,
    #[serde(default)]
    birth: Present<u64>,
    #[serde(default)]
    monotonic_ns: Present<u64>,
    #[serde(default)]
    unix_ns: Present<u64>,
    #[serde(default)]
    outcome: Present<RootOutcome>,
    #[serde(default)]
    cause: Present<String>,
    #[serde(default)]
    runtime_ns: Present<u64>,
    #[serde(default)]
    reason: Present<String>,
    #[serde(default)]
    accounting: Present<RootAccounting>,
}
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct RootCpuTimes {
    user_ns: u64,
    system_ns: u64,
}
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct RootAccounting {
    scope: String,
    #[serde(default)]
    cpu_times: Present<Option<RootCpuTimes>>,
    #[serde(default)]
    peak_rss_bytes: Present<Option<u64>>,
}
impl RootAccounting {
    fn checked(self) -> Result<Observation> {
        if self.scope != "child-and-waited-descendants-v1" {
            return Err(Refusal("native root accounting scope unsupported".into()));
        }
        Ok(Observation {
            scope: Scope::ChildAndWaitedDescendantsV1,
            cpu_times: self
                .cpu_times
                .value()?
                .map(|cpu| CpuTimes { user_ns: cpu.user_ns, system_ns: cpu.system_ns }),
            peak_rss_bytes: self.peak_rss_bytes.value()?,
        })
    }
}
pub(crate) struct RootEnd {
    pub(crate) normal: bool,
    pub(crate) outcome: trust_qualification::dependencies::ResolverOutcome,
    pub(crate) pid: u32,
    pub(crate) birth: u64,
    pub(crate) session: String,
    pub(crate) attempt: String,
    /// Actual target GO-to-kernel-exit interval; excludes later drain.
    pub(crate) runtime_ns: u64,
    pub(crate) cause: CompletionCause,
    /// Independently optional same-wait data, never whole-workload CPU.
    pub(crate) accounting: Option<Observation>,
}
pub(crate) fn validate_statuses(bytes: &[u8], exit: &std::process::ExitStatus) -> Result<RootEnd> {
    validate_statuses_with_accounting(bytes, exit, false)
}
/// Only the explicit --accounted workload route may use this reader. Missing
/// capability/legacy terminal is a refusal, never a legacy-route retry.
pub(crate) fn validate_accounted_statuses(
    bytes: &[u8],
    exit: &std::process::ExitStatus,
) -> Result<RootEnd> {
    validate_statuses_with_accounting(bytes, exit, true)
}
fn validate_statuses_with_accounting(
    bytes: &[u8],
    exit: &std::process::ExitStatus,
    accounted: bool,
) -> Result<RootEnd> {
    if bytes.is_empty() || bytes.len() > STATUS_MAX || !bytes.ends_with(b"\n") {
        return Err(Refusal("native root lifecycle is missing, excessive or truncated".into()));
    }
    let mut binding = None;
    let mut queued = false;
    let mut started = false;
    let mut terminal = false;
    let mut normal = false;
    let mut root_outcome = None;
    let mut actual_start = None;
    let mut completion = None;
    for line in bytes[..bytes.len() - 1].split(|b| *b == b'\n') {
        let frame: RootStatus = serde_json::from_slice(line)
            .map_err(|error| Refusal(format!("invalid native root lifecycle: {error}")))?;
        if terminal
            || frame.version != 3
            || frame.session.len() > 64
            || !frame.session.strip_prefix("s-").is_some_and(|sid| {
                !sid.is_empty()
                    && sid.bytes().all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
            })
            || frame.attempt.len() != 32
            || frame.attempt.bytes().all(|byte| byte == b'0')
            || !frame.attempt.bytes().all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
        {
            return Err(Refusal("native root lifecycle binding/version/ordering refused".into()));
        }
        let current = (frame.session.clone(), frame.attempt.clone());
        if binding.as_ref().is_some_and(|old| old != &current) {
            return Err(Refusal("native root lifecycle changed attempts".into()));
        }
        binding = Some(current);
        let launch_empty = frame.pid.missing()
            && frame.birth.missing()
            && frame.monotonic_ns.missing()
            && frame.unix_ns.missing();
        let finish_empty = frame.outcome.missing()
            && frame.cause.missing()
            && frame.runtime_ns.missing()
            && frame.accounting.missing();
        match frame.event.as_str() {
            "queued"
                if !queued
                    && !started
                    && launch_empty
                    && finish_empty
                    && frame.reason.missing() =>
            {
                queued = true
            }
            "started" if queued && !started && finish_empty && frame.reason.missing() => {
                let pid = frame.pid.value()?;
                let birth = frame.birth.value()?;
                if pid <= 1
                    || birth == 0
                    || frame.monotonic_ns.value()? == 0
                    || frame.unix_ns.value()? == 0
                {
                    return Err(Refusal("native root has invalid actual birth/GO clocks".into()));
                }
                started = true;
                actual_start = Some((pid, birth));
            }
            "finished" if started && launch_empty && frame.reason.missing() => {
                let outcome = frame.outcome.value()?;
                let cause = frame.cause.value()?;
                let runtime_ns = frame.runtime_ns.value()?;
                let accounting = if accounted {
                    Some(frame.accounting.value()?.checked()?)
                } else if frame.accounting.missing() {
                    None
                } else {
                    return Err(Refusal(
                        "legacy native root route cannot accept accounted terminal".into(),
                    ));
                };
                let code = match (outcome.exit, outcome.signal) {
                    (Present::Value(code), Present::Missing) if (0..=255).contains(&code) => {
                        root_outcome =
                            Some(trust_qualification::dependencies::ResolverOutcome::Exit(code));
                        code
                    }
                    (Present::Missing, Present::Value(signal)) if (1..=127).contains(&signal) => {
                        root_outcome = Some(
                            trust_qualification::dependencies::ResolverOutcome::Signal(signal),
                        );
                        128 + signal
                    }
                    _ => return Err(Refusal("native root outcome is ambiguous".into())),
                };
                if exit.code() != Some(code) {
                    return Err(Refusal("actual native CLI exit contradicts root outcome".into()));
                }
                if !matches!(cause.as_str(), "exited" | "timeout" | "cancelled" | "resource_limit")
                {
                    return Err(Refusal("unknown native root completion cause".into()));
                }
                normal = code == 0 && cause == "exited";
                let cause = match cause.as_str() {
                    "exited" => CompletionCause::Exited,
                    "timeout" => CompletionCause::Timeout,
                    "cancelled" => CompletionCause::Cancelled,
                    "resource_limit" => CompletionCause::ResourceLimit,
                    _ => unreachable!("validated cause"),
                };
                completion = Some((runtime_ns, cause, accounting));
                terminal = true;
            }
            "refused" if !started && launch_empty && finish_empty => {
                return Err(Refusal(format!(
                    "native metadata root refused: {}",
                    frame.reason.value()?
                )));
            }
            "transport_unknown" if launch_empty && finish_empty => {
                return Err(Refusal(format!(
                    "native metadata root delivery unknown; never retry: {}",
                    frame.reason.value()?
                )));
            }
            _ => {
                return Err(Refusal(
                    "native root lifecycle has missing, duplicate or contradictory phases".into(),
                ));
            }
        }
    }
    if !terminal {
        return Err(Refusal("native metadata root has no actual retirement receipt".into()));
    }
    let (pid, birth) =
        actual_start.ok_or_else(|| Refusal("native root start unavailable".into()))?;
    let (session, attempt) =
        binding.ok_or_else(|| Refusal("native root binding unavailable".into()))?;
    let (runtime_ns, cause, accounting) = completion
        .ok_or_else(|| Refusal("native root completion observation unavailable".into()))?;
    Ok(RootEnd {
        normal,
        outcome: root_outcome.ok_or_else(|| Refusal("native root outcome unavailable".into()))?,
        pid,
        birth,
        session,
        attempt,
        runtime_ns,
        cause,
        accounting,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn private_root_selection_refuses_before_filesystem_discovery_or_cli_delivery() {
        let spec = RootSpec {
            program: Path::new("/absent-sdk/bin/targo"),
            cwd: Path::new("/absent-source"),
            entry: "--resource-resolver-v1",
            environment: &[],
            input: b"not a request",
            max_output: 1024,
            max_stderr: 1024,
            job: "pre-delivery-refusal",
        };
        let refusal = capture(spec, &Some(PathBuf::from("/must-not-open-this-private-store")))
            .err()
            .expect("helper path alone must never select private root admission");
        assert!(refusal.0.contains("original-store root CLI boundary"));
        assert!(refusal.0.contains("account fallback is forbidden"));
    }

    #[test]
    fn interactive_mode_requires_exact_original_workload_invocation_and_closed_environment() {
        use std::ffi::OsStr;

        use trust_resource_controller::workload::{
            InputFile, WORKLOAD_STARTUP_ARGUMENT, WorkloadInvocation,
        };
        let input = |path: &str| InputFile { path: path.as_bytes().to_vec(), sha256: [2; 32] };
        // Data-shape/equality controls only; no original native owner, SDK,
        // output capsule, process grant or host readiness is constructed.
        let mut invocation = WorkloadInvocation {
            invocation: [1; 16],
            observed_host_store: None,
            root: b"/sdk".to_vec(),
            program: input("/sdk/bin/targo"),
            compiler: input("/sdk/bin/trustc"),
            cwd: b"/source".to_vec(),
            cargo_home: b"/cargo".to_vec(),
            output_root: b"/output".to_vec(),
            refutation_step: input("/fixtures/step.rs"),
            refutation_loop: input("/fixtures/loop.rs"),
            trust_spec_source: input("/fixtures/spec.rs"),
            repetitions: 1,
            timeout_ns: 1_000_000_000,
        };
        let bytes = invocation.encode().unwrap();
        let environment = [
            ("CARGO", OsStr::new("/sdk/bin/targo")),
            ("RUSTC", OsStr::new("/sdk/bin/trustc")),
            ("CARGO_HOME", OsStr::new("/cargo")),
            ("CARGO_CACHE_RUSTC_INFO", OsStr::new("0")),
        ];
        fn spec<'a>(environment: &'a [(&'a str, &'a OsStr)], input: &'a [u8]) -> RootSpec<'a> {
            RootSpec {
                program: Path::new("/sdk/bin/targo"),
                cwd: Path::new("/source"),
                entry: WORKLOAD_STARTUP_ARGUMENT,
                environment,
                input,
                max_output: 1024,
                max_stderr: 1024,
                job: "data-only",
            }
        }
        let until = Instant::now() + Duration::from_secs(10);
        assert!(validate_workload_launch(&spec(&environment, &bytes), 15_000, until).is_ok());
        for (index, value) in
            [(0, "/foreign/targo"), (1, "/foreign/trustc"), (2, "relative"), (3, "1")]
        {
            let mut changed = environment;
            changed[index].1 = OsStr::new(value);
            assert!(validate_workload_launch(&spec(&changed, &bytes), 15_000, until).is_err());
        }
        let mut duplicate = environment.to_vec();
        duplicate.push(environment[0]);
        assert!(validate_workload_launch(&spec(&duplicate, &bytes), 15_000, until).is_err());
        assert!(validate_workload_launch(&spec(&environment, &bytes), u64::MAX, until).is_err());
        let mut wrong = spec(&environment, &bytes);
        wrong.entry = "--resource-resolver-v1";
        assert!(validate_workload_launch(&wrong, 15_000, until).is_err());
        invocation.cwd = b"/different-source".to_vec();
        assert!(
            validate_workload_launch(
                &spec(&environment, &invocation.encode().unwrap()),
                15_000,
                until
            )
            .is_err()
        );
    }

    #[test]
    fn paired_mode_requires_complete60_own_budget_and_original_environment_without_v1_retry() {
        use std::ffi::OsStr;

        use trust_resource_controller::paired_qualification::{
            self as paired, AySubject, PairedInvocation,
        };
        use trust_resource_controller::workload::{InputFile, WorkloadInvocation};
        let file = |path: &str| InputFile { path: path.as_bytes().to_vec(), sha256: [2; 32] };
        // Equality fixtures only. They do not construct an original host,
        // CPU/SDK owner, output capsule or an authenticated startup.
        let plan = PairedInvocation {
            consumer: WorkloadInvocation {
                invocation: [1; 16],
                observed_host_store: None,
                root: b"/sdk".to_vec(),
                program: file("/sdk/bin/targo"),
                compiler: file("/sdk/bin/trustc"),
                cwd: b"/consumer".to_vec(),
                cargo_home: b"/cargo".to_vec(),
                output_root: b"/output".to_vec(),
                refutation_step: file("/fixtures/step.rs"),
                refutation_loop: file("/fixtures/loop.rs"),
                trust_spec_source: file("/fixtures/spec.rs"),
                repetitions: 1,
                timeout_ns: 1_000_000_000,
            },
            ay: AySubject {
                root: b"/ay".to_vec(),
                workspace_manifest: file("/ay/Cargo.toml"),
                crate_manifest: file("/ay/crates/ay-proof-common/Cargo.toml"),
                lockfile: file("/ay/Cargo.lock"),
                cargo_config: file("/ay/.cargo/config.toml"),
                toolchain_config: file("/ay/rust-toolchain.toml"),
                source_commit: [3; 20],
                crate_tree: [4; 20],
            },
        };
        let environment = [
            ("CARGO", OsStr::new("/sdk/bin/targo")),
            ("RUSTC", OsStr::new("/sdk/bin/trustc")),
            ("CARGO_HOME", OsStr::new("/cargo")),
            ("CARGO_CACHE_RUSTC_INFO", OsStr::new("0")),
        ];
        let bytes = plan.encode().unwrap();
        let mut spec = RootSpec {
            program: Path::new("/sdk/bin/targo"),
            cwd: Path::new("/consumer"),
            entry: paired::PAIRED_STARTUP_ARGUMENT,
            environment: &environment,
            input: &bytes,
            max_output: 1024,
            max_stderr: 1024,
            job: "paired-profile-data-control",
        };
        let until = Instant::now() + Duration::from_secs(1);
        let budget = paired::budget::Budget::new(1, plan.consumer.timeout_ns).unwrap();
        validate_paired_launch(&spec, budget.root_timeout_ms, until).unwrap();
        assert!(validate_workload_launch(&spec, budget.root_timeout_ms, until).is_err());
        assert!(
            validate_paired_launch(
                &spec,
                trust_resource_controller::workload::budget::Budget::new(
                    1,
                    plan.consumer.timeout_ns
                )
                .unwrap()
                .root_timeout_ms,
                until
            )
            .is_err()
        );
        let old = plan.consumer.encode().unwrap();
        spec.input = &old;
        assert!(validate_paired_launch(&spec, budget.root_timeout_ms, until).is_err());
        spec.input = &bytes;
        spec.entry = trust_resource_controller::workload::WORKLOAD_STARTUP_ARGUMENT;
        assert!(validate_paired_launch(&spec, budget.root_timeout_ms, until).is_err());
        spec.entry = paired::PAIRED_STARTUP_ARGUMENT;
        spec.cwd = Path::new("/ay");
        assert!(validate_paired_launch(&spec, budget.root_timeout_ms, until).is_err());
        spec.cwd = Path::new("/consumer");
        let mut wrong = environment;
        wrong[1].1 = OsStr::new("/different/bin/trustc");
        spec.environment = &wrong;
        assert!(validate_paired_launch(&spec, budget.root_timeout_ms, until).is_err());
    }

    fn accounted_transcript(cpu: &str, rss: &str, exit: i32, cause: &str) -> String {
        let prefix = r#""version":3,"session":"s-ab","attempt":"01010101010101010101010101010101""#;
        format!(
            "{{{prefix},\"event\":\"queued\"}}\n{{{prefix},\"event\":\"started\",\"pid\":42,\"birth\":123,\"monotonic_ns\":1,\"unix_ns\":2}}\n{{{prefix},\"event\":\"finished\",\"outcome\":{{\"exit\":{exit}}},\"cause\":\"{cause}\",\"runtime_ns\":0,\"accounting\":{{\"scope\":\"child-and-waited-descendants-v1\",\"cpu_times\":{cpu},\"peak_rss_bytes\":{rss}}}}}\n"
        )
    }
    #[test]
    fn accounted_root_requires_explicit_fields_and_preserves_observed_zero_versus_unknown() {
        let zero = accounted_transcript(r#"{"user_ns":0,"system_ns":0}"#, "0", 0, "exited");
        let exit = std::process::ExitStatus::from_raw(0);
        let result = validate_accounted_statuses(zero.as_bytes(), &exit).unwrap();
        assert!(result.normal);
        assert_eq!(result.runtime_ns, 0);
        assert_eq!(result.cause, CompletionCause::Exited);
        let actual = result.accounting.unwrap();
        assert_eq!(actual.cpu_times, Some(CpuTimes { user_ns: 0, system_ns: 0 }));
        assert_eq!(actual.peak_rss_bytes, Some(0));
        let unknown = accounted_transcript("null", "null", 0, "exited");
        let result = validate_accounted_statuses(unknown.as_bytes(), &exit).unwrap();
        assert_eq!(result.accounting, Some(Observation::uncollected()));
        assert!(validate_statuses(zero.as_bytes(), &exit).is_err());
        for invalid in [
            zero.replace(",\"cpu_times\":{\"user_ns\":0,\"system_ns\":0}", ""),
            zero.replace(",\"peak_rss_bytes\":0", ""),
            zero.replace("child-and-waited-descendants-v1", "whole-process-tree"),
            zero.replace("\"user_ns\":0", "\"user_ns\":0.0"),
            zero.replace("\"user_ns\":0", "\"user_ns\":0,\"user_ns\":0"),
            zero.replace("\"peak_rss_bytes\":0", "\"peak_rss_bytes\":false"),
            zero.replace("\"cpu_times\":{\"user_ns\":0,\"system_ns\":0}", "\"cpu_times\":{}"),
            zero.replace("\"scope\":\"child-and-waited-descendants-v1\"", "\"scope\":null"),
            zero.replace("\"peak_rss_bytes\":0", "\"peak_rss_bytes\":0,\"extra\":1"),
        ] {
            assert!(validate_accounted_statuses(invalid.as_bytes(), &exit).is_err(), "{invalid}");
        }
    }
    #[test]
    fn accounted_terminal_does_not_upgrade_failure_or_cancellation_and_old_route_never_satisfies_it()
     {
        let failed = accounted_transcript(r#"{"user_ns":12,"system_ns":3}"#, "4096", 7, "exited");
        let result = validate_accounted_statuses(
            failed.as_bytes(),
            &std::process::ExitStatus::from_raw(7 << 8),
        )
        .unwrap();
        assert!(!result.normal);
        assert_eq!(result.outcome, trust_qualification::dependencies::ResolverOutcome::Exit(7));
        assert_eq!(result.accounting.unwrap().cpu_times.unwrap().user_ns, 12);
        let cancelled = accounted_transcript("null", "null", 0, "cancelled");
        let result = validate_accounted_statuses(
            cancelled.as_bytes(),
            &std::process::ExitStatus::from_raw(0),
        )
        .unwrap();
        assert!(!result.normal);
        assert_eq!(result.cause, CompletionCause::Cancelled);
        let mut frames = failed
            .lines()
            .map(|line| serde_json::from_str::<Value>(line).unwrap())
            .collect::<Vec<_>>();
        frames[2].as_object_mut().unwrap().remove("accounting");
        let legacy = frames.iter().map(|frame| format!("{frame}\n")).collect::<String>();
        let exit = std::process::ExitStatus::from_raw(7 << 8);
        assert!(validate_statuses(legacy.as_bytes(), &exit).is_ok());
        assert!(validate_accounted_statuses(legacy.as_bytes(), &exit).is_err());
        frames[2]["accounting"] = json!({"scope":"child-and-waited-descendants-v1","cpu_times":null,"peak_rss_bytes":null});
        for phase in 0..2 {
            let mut misplaced = frames.clone();
            misplaced[phase]["accounting"] = frames[2]["accounting"].clone();
            let transcript = misplaced.iter().map(|frame| format!("{frame}\n")).collect::<String>();
            assert!(validate_accounted_statuses(transcript.as_bytes(), &exit).is_err());
        }
    }
    #[test]
    fn root_lifecycle_requires_real_order_binding_exact_fields_and_matching_exit() {
        let prefix = r#""version":3,"session":"s-ab","attempt":"01010101010101010101010101010101""#;
        let queued = format!("{{{prefix},\"event\":\"queued\"}}\n");
        let started = format!(
            "{{{prefix},\"event\":\"started\",\"pid\":42,\"birth\":123,\"monotonic_ns\":1,\"unix_ns\":2}}\n"
        );
        let finished = format!(
            "{{{prefix},\"event\":\"finished\",\"outcome\":{{\"exit\":0}},\"cause\":\"exited\",\"runtime_ns\":0}}\n"
        );
        let valid = format!("{queued}{started}{finished}");
        assert!(
            validate_statuses(valid.as_bytes(), &std::process::ExitStatus::from_raw(0))
                .unwrap()
                .normal
        );
        for invalid in [
            format!("{started}{finished}"),
            format!("{queued}{finished}"),
            format!("{queued}{queued}{started}{finished}"),
            format!("{valid}{finished}"),
            format!("{valid}\n"),
            valid.replace("\"version\":3", "\"version\":3.0"),
            valid.replace("\"version\":3", "\"version\":{\"$serde_json::private::Number\":\"3\"}"),
            valid.replace("\"birth\":123", "\"birth\":true"),
            valid.replace("\"exit\":0", "\"exit\":0,\"signal\":9"),
            valid.replace("\"pid\":42", "\"pid\":null"),
            valid.replace("\"pid\":42", "\"pid\":42,\"pid\":42"),
            valid.trim_end().to_string(),
        ] {
            assert!(
                validate_statuses(invalid.as_bytes(), &std::process::ExitStatus::from_raw(0))
                    .is_err(),
                "{invalid}"
            );
        }
        assert!(
            validate_statuses(valid.as_bytes(), &std::process::ExitStatus::from_raw(1 << 8))
                .is_err()
        );
    }
    #[test]
    fn actual_root_signal_remains_a_signal_and_timeout_is_not_normal_success() {
        let prefix = r#""version":3,"session":"s-ab","attempt":"01010101010101010101010101010101""#;
        let start = format!(
            "{{{prefix},\"event\":\"queued\"}}\n{{{prefix},\"event\":\"started\",\"pid\":42,\"birth\":123,\"monotonic_ns\":1,\"unix_ns\":2}}\n"
        );
        let signal = format!(
            "{start}{{{prefix},\"event\":\"finished\",\"outcome\":{{\"signal\":9}},\"cause\":\"exited\",\"runtime_ns\":1}}\n"
        );
        let observed =
            validate_statuses(signal.as_bytes(), &std::process::ExitStatus::from_raw(137 << 8))
                .unwrap();
        assert_eq!(observed.outcome, trust_qualification::dependencies::ResolverOutcome::Signal(9));
        assert!(!observed.normal);
        let timeout = format!(
            "{start}{{{prefix},\"event\":\"finished\",\"outcome\":{{\"exit\":0}},\"cause\":\"timeout\",\"runtime_ns\":1}}\n"
        );
        assert!(
            !validate_statuses(timeout.as_bytes(), &std::process::ExitStatus::from_raw(0))
                .unwrap()
                .normal
        );
    }
}
