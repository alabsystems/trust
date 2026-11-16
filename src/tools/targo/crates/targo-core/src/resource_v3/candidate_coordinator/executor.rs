//! A NoFork candidate sends compiler proposals on its original parent broker.
//! It keeps its own paid CPU. The parent retains a SECOND original bank unit,
//! actual native member, output readers and retirement; no local child exists.
use super::Original;
use crate::resource_v3::Startup;
use cargo_util::{
    CaptureCompletionCause, CaptureOwnerObservation, CaptureStreamEnd, CapturedProcess, CpuTimes,
    ExecStats, ProcessBuilder, ProcessError, ProcessExecutor, StreamingOutputLimits,
};
use std::io;
use std::os::unix::{ffi::OsStrExt as _, process::ExitStatusExt as _};
use std::process::{ExitStatus, Output};
use std::sync::{Arc, atomic::Ordering};
use std::time::{Duration, Instant};
use trust_resource_controller::workload::host::coordinator::{
    BrokerCaptureData, BrokerLimits, StreamEnd,
};
use trust_resource_controller::{CommandSpec, CompletionCause, Outcome, Status};

pub(in crate::resource_v3) fn install(startup: Arc<Startup>) -> io::Result<()> {
    cargo_util::install_process_executor(Arc::new(Executor {
        startup,
        metadata: true,
        _owner: None,
    }))
}
pub(in crate::resource_v3) fn compiler(
    startup: Arc<Startup>,
    owner: Arc<dyn Send + Sync>,
) -> Arc<dyn ProcessExecutor> {
    Arc::new(Executor {
        startup,
        metadata: false,
        _owner: Some(owner),
    })
}
struct Executor {
    startup: Arc<Startup>,
    metadata: bool,
    _owner: Option<Arc<dyn Send + Sync>>,
}
struct Activity<'a>(&'a Original);
impl Drop for Activity<'_> {
    fn drop(&mut self) {
        if std::thread::panicking() {
            self.0.poison();
        }
        self.0.busy.store(false, Ordering::Release);
    }
}
fn error(message: impl Into<String>) -> io::Error {
    io::Error::other(message.into())
}
fn deliver_lines(
    bytes: &[u8],
    callback: &mut dyn FnMut(&str) -> anyhow::Result<()>,
) -> anyhow::Result<()> {
    for line in bytes.split_inclusive(|byte| *byte == b'\n') {
        callback(
            std::str::from_utf8(line)?
                .trim_end_matches('\n')
                .trim_end_matches('\r'),
        )?;
    }
    Ok(())
}
#[derive(Debug)]
struct ForeignCompletion {
    frame: trust_resource_controller::StatusFrame,
    started: bool,
}
impl std::fmt::Display for ForeignCompletion {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "broker completion has a foreign original binding: {:?}; reported_started={}",
            self.frame, self.started
        )
    }
}
impl std::error::Error for ForeignCompletion {}

fn description(process: &ProcessBuilder, metadata: bool) -> io::Result<CommandSpec> {
    if process.has_action_sandbox()
        || process.get_arg0().is_some()
        || process.get_stdin().is_some_and(|bytes| !bytes.is_empty())
    {
        return Err(error(
            "candidate broker refuses wrappers, producing stdin and alternative sandbox",
        ));
    }
    let actual = process.build_command();
    let args = actual
        .get_args()
        .map(|arg| arg.as_bytes().to_vec())
        .collect::<Vec<_>>();
    if args.iter().any(|arg| arg.starts_with(b"@")) {
        return Err(error("candidate broker refuses argument files"));
    }
    if metadata {
        query(&args)?;
    }
    Ok(CommandSpec {
        program: actual.get_program().as_bytes().to_vec(),
        arg0: None,
        args,
        cwd: process
            .get_cwd()
            .map(ToOwned::to_owned)
            .map_or_else(std::env::current_dir, Ok)?
            .as_os_str()
            .as_bytes()
            .to_vec(),
        // Full observation, including exact original locator inputs. These are
        // DATA, never credentials for the parent's different compiler unit.
        // The parent's trusted constructor validates and installs its OWN
        // typed transport and records the complete actual final environment.
        environment: process
            .get_effective_envs()?
            .into_iter()
            .map(|(key, value)| (key.as_bytes().to_vec(), value.as_bytes().to_vec()))
            .collect(),
    })
}
fn query(args: &[Vec<u8>]) -> io::Result<()> {
    if matches!(args, [arg] if matches!(arg.as_slice(), b"-vV" | b"--version" | b"--print=sysroot" | b"--print=target-list"))
    {
        return Ok(());
    }
    trust_resource_controller::resolver::classify_resolver_query(args).map(drop)
}
pub(in crate::resource_v3) fn is_query(args: &[Vec<u8>]) -> bool {
    query(args).is_ok()
}
fn end(end: StreamEnd) -> CaptureStreamEnd {
    match end {
        StreamEnd::Eof => CaptureStreamEnd::Eof,
        StreamEnd::LeaderExitDrained => CaptureStreamEnd::LeaderExitDrained,
        StreamEnd::Pending | StreamEnd::ReadFailed | StreamEnd::LimitExceeded => {
            CaptureStreamEnd::Incomplete
        }
    }
}
fn exit(outcome: Outcome) -> io::Result<ExitStatus> {
    match outcome {
        Outcome::Exit(code) => code
            .checked_mul(256)
            .map(ExitStatus::from_raw)
            .ok_or_else(|| error("broker exit status overflow")),
        Outcome::Signal(signal) => Ok(ExitStatus::from_raw(signal)),
    }
}
fn projection(
    data: BrokerCaptureData,
    limits: StreamingOutputLimits,
    measured: bool,
) -> (ExecStats, CapturedProcess) {
    let endings = format!("stdout={:?}, stderr={:?}", data.stdout_end, data.stderr_end);
    let stats = if measured {
        ExecStats {
            peak_rss: data.accounting.peak_rss_bytes,
            cpu_times: data.accounting.cpu_times.map(|cpu| CpuTimes {
                user: Duration::from_nanos(cpu.user_ns),
                system: Duration::from_nanos(cpu.system_ns),
            }),
        }
    } else {
        ExecStats::default()
    };
    let mut capture = CapturedProcess {
        stdout: data.stdout,
        stderr: data.stderr,
        started: data.started,
        stdout_end: end(data.stdout_end),
        stderr_end: end(data.stderr_end),
        stdout_truncated: data.truncated,
        stderr_truncated: data.truncated,
        limits: Some(limits),
        failure: data.failure.map(|reason| anyhow::anyhow!(reason)),
        ..CapturedProcess::default()
    };
    if let Some(frame) = data.status {
        match frame.status {
            Status::Finished {
                outcome,
                cause,
                runtime_ns,
            } => {
                if !capture.started {
                    capture.failure.get_or_insert_with(|| {
                        anyhow::anyhow!("broker terminal contradicts unavailable target start")
                    });
                }
                capture.status = exit(outcome).ok();
                capture.owner_observation = Some(CaptureOwnerObservation {
                    native_member_attempt: Some(frame.member_attempt),
                    target_runtime: Some(Duration::from_nanos(runtime_ns)),
                    cause: Some(match cause {
                        CompletionCause::Exited => CaptureCompletionCause::Exited,
                        CompletionCause::Timeout => CaptureCompletionCause::Timeout,
                        CompletionCause::Cancelled => CaptureCompletionCause::Cancelled,
                        CompletionCause::ResourceLimit => CaptureCompletionCause::ResourceLimit,
                        CompletionCause::HostFault => CaptureCompletionCause::HostFault,
                    }),
                    // The candidate received observations. Original native
                    // closure/loan settlement stays with the parent owner.
                    retirement_confirmed: false,
                });
                if cause != CompletionCause::Exited {
                    capture.failure.get_or_insert_with(|| {
                        ProcessError::new(
                            &format!("original broker target ended: {cause:?}"),
                            capture.status,
                            None,
                        )
                        .into()
                    });
                }
            }
            Status::Refused { reason } | Status::Unknown { reason, .. } => {
                capture
                    .failure
                    .get_or_insert_with(|| anyhow::anyhow!(reason));
            }
            Status::Attached | Status::Started(_) => {
                capture.failure.get_or_insert_with(|| {
                    anyhow::anyhow!("broker omitted native target terminal")
                });
            }
        }
    } else {
        capture
            .failure
            .get_or_insert_with(|| anyhow::anyhow!("original broker target status is unavailable"));
    }
    if !capture.complete() {
        capture.failure.get_or_insert_with(|| {
            anyhow::anyhow!("original broker capture is incomplete: {endings}")
        });
    }
    (stats, capture)
}
impl Executor {
    fn original(&self) -> io::Result<&Arc<Original>> {
        self.startup
            .candidate
            .as_ref()
            .ok_or_else(|| error("candidate broker lost original startup"))
    }
    fn capture_inner(
        &self,
        process: &ProcessBuilder,
        limits: StreamingOutputLimits,
        measured: bool,
    ) -> (ExecStats, CapturedProcess) {
        let limits = if self.metadata {
            StreamingOutputLimits::new(
                limits.line_bytes().min(64 * 1024),
                limits.stream_bytes().min(64 * 1024),
            )
            .with_timeout(
                limits
                    .runtime_timeout()
                    .unwrap_or(Duration::from_secs(30))
                    .min(Duration::from_secs(30)),
            )
        } else {
            limits
        };
        let result = (|| -> io::Result<_> {
            let original = self.original()?;
            original.check()?;
            if original
                .busy
                .compare_exchange(false, true, Ordering::AcqRel, Ordering::Acquire)
                .is_err()
            {
                return Err(io::Error::new(
                    io::ErrorKind::WouldBlock,
                    "candidate already has an original broker request",
                ));
            }
            let _activity = Activity(original);
            let command = description(process, self.metadata)?;
            original.validate_command(&command)?;
            let remaining = original.deadline.saturating_duration_since(Instant::now());
            let requested = limits.runtime_timeout().unwrap_or(remaining).min(remaining);
            let timeout_ns = u64::try_from(requested.as_nanos())
                .map_err(|_| error("candidate compiler timeout overflow"))?;
            if timeout_ns == 0 {
                return Err(io::ErrorKind::TimedOut.into());
            }
            let broker_limits = BrokerLimits {
                line_bytes: limits.line_bytes(),
                stream_bytes: limits.stream_bytes(),
                timeout_ns,
                capture_rusage: measured,
            };
            let cancelled = process.execution_cancellation();
            let mut cancellation_seen = false;
            let mut cancellation = || {
                cancellation_seen |= cancelled
                    .as_ref()
                    .is_some_and(|value| value.load(Ordering::Acquire));
                cancellation_seen
            };
            let mut broker = original.broker.try_lock().map_err(|_| {
                original.poison();
                error("original candidate broker is busy or poisoned")
            })?;
            let received = broker.execute(
                &command,
                broker_limits,
                original.deadline,
                &mut cancellation,
            );
            let capture = match received {
                Ok(received) => received.into_observation(),
                Err(error) => {
                    original.poison();
                    return Err(error);
                }
            };
            cancellation_seen |= cancelled
                .as_ref()
                .is_some_and(|value| value.load(Ordering::Acquire));
            let foreign = capture
                .status
                .as_ref()
                .filter(|frame| {
                    frame.root_attempt != self.startup.query.binding.root_attempt
                        || frame.member_attempt == [0; 16]
                        || frame.member_attempt == frame.root_attempt
                })
                .cloned();
            let (stats, mut capture) = projection(capture, limits, measured);
            if let Some(frame) = foreign {
                original.poison();
                capture.failure = Some(
                    ForeignCompletion {
                        frame,
                        started: capture.started,
                    }
                    .into(),
                );
                capture.status = None;
                capture.started = false;
                capture.owner_observation = None;
                capture.stdout_end = CaptureStreamEnd::Incomplete;
                capture.stderr_end = CaptureStreamEnd::Incomplete;
                // Keep every received byte and the foreign raw frame as
                // diagnosed DATA; it is not this invocation's owning wait.
            }
            if let Err(error) = original.check() {
                let cause = if let Some(previous) = capture.failure.take() {
                    anyhow::Error::new(error)
                        .context(format!("prior broker target failure: {previous:#}"))
                } else {
                    anyhow::Error::new(error)
                };
                capture.failure = Some(match capture.status {
                    Some(status) => cargo_util::TargetExecutionError::new(status, cause).into(),
                    None => cargo_util::TargetExecutionError::unobserved(cause).into(),
                });
            }
            if cancellation_seen {
                original.poison();
                capture.failure.get_or_insert_with(|| {
                    anyhow::anyhow!("candidate cancellation prevents further compiler dispatch")
                });
            }
            if capture.failure.is_some() || capture.status.is_some_and(|status| !status.success()) {
                original.poison();
            }
            Ok((stats, capture))
        })();
        result.unwrap_or_else(|failure| {
            (
                ExecStats::default(),
                CapturedProcess {
                    limits: Some(limits),
                    failure: Some(failure.into()),
                    ..CapturedProcess::default()
                },
            )
        })
    }
    fn limits(&self) -> StreamingOutputLimits {
        if self.metadata {
            StreamingOutputLimits::new(64 * 1024, 64 * 1024).with_timeout(Duration::from_secs(30))
        } else {
            StreamingOutputLimits::new(8 * 1024 * 1024, 64 * 1024 * 1024)
        }
    }
    fn output_inner(&self, process: &ProcessBuilder) -> io::Result<Output> {
        let (_, mut capture) = self.capture_inner(process, self.limits(), false);
        if let Some(failure) = capture.failure.take() {
            return Err(io::Error::other(failure));
        }
        let status = capture
            .status
            .ok_or_else(|| error("broker target exit unavailable"))?;
        Ok(Output {
            status,
            stdout: capture.stdout,
            stderr: capture.stderr,
        })
    }
}
impl ProcessExecutor for Executor {
    fn supports_structured_capture(&self) -> bool {
        true
    }
    fn capture(
        &self,
        process: &ProcessBuilder,
        limits: StreamingOutputLimits,
        measured: bool,
    ) -> (ExecStats, CapturedProcess) {
        self.capture_inner(process, limits, measured)
    }
    fn output(&self, process: &ProcessBuilder) -> io::Result<Output> {
        self.output_inner(process)
    }
    fn status(&self, process: &ProcessBuilder) -> io::Result<ExitStatus> {
        self.output_inner(process).map(|output| output.status)
    }
    fn streaming(
        &self,
        process: &ProcessBuilder,
        stdout: &mut dyn FnMut(&str) -> anyhow::Result<()>,
        stderr: &mut dyn FnMut(&str) -> anyhow::Result<()>,
        capture: bool,
        limits: Option<StreamingOutputLimits>,
        measured: bool,
    ) -> (ExecStats, anyhow::Result<Output>) {
        let (stats, mut observed) =
            self.capture_inner(process, limits.unwrap_or_else(|| self.limits()), measured);
        let result = (|| {
            deliver_lines(&observed.stdout, stdout)?;
            deliver_lines(&observed.stderr, stderr)?;
            if let Some(error) = observed.failure.take() {
                return Err(error);
            }
            let status = observed
                .status
                .ok_or_else(|| anyhow::anyhow!("broker target status unavailable"))?;
            let output = Output {
                status,
                stdout: std::mem::take(&mut observed.stdout),
                stderr: std::mem::take(&mut observed.stderr),
            };
            if !status.success() {
                return Err(ProcessError::new(
                    "original broker compiler failed",
                    Some(status),
                    Some(&output),
                )
                .into());
            }
            if capture {
                Ok(output)
            } else {
                Ok(Output {
                    status,
                    stdout: Vec::new(),
                    stderr: Vec::new(),
                })
            }
        })();
        let result = result.map_err(|failure| match observed.status {
            Some(status) => cargo_util::TargetExecutionError::new(status, failure).into(),
            None => cargo_util::TargetExecutionError::unobserved(failure).into(),
        });
        (stats, result)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn compiler_projection_preserves_full_raw_environment_and_closed_query_population() {
        let mut command = ProcessBuilder::new("/sdk/bin/trustc");
        command.arg("-vV").cwd("/source");
        command.env("TRUST_CPU_HANDOFF", "original-child-observation");
        command.env("ATERM_PROJECT_SEMANTIC", "must-not-disappear");
        let observed = description(&command, true).unwrap();
        for key in [b"TRUST_CPU_HANDOFF".as_slice(), b"ATERM_PROJECT_SEMANTIC"] {
            assert!(observed.environment.iter().any(|(name, _)| name == key));
        }
        assert!(query(&[b"--emit=link".to_vec(), b"/source/main.rs".to_vec()]).is_err());
        let mut argument_file = command.clone();
        argument_file.arg("@/source/flags");
        assert!(description(&argument_file, false).is_err());
        let target_info = vec![
            b"-".to_vec(),
            b"--crate-name".to_vec(),
            b"___".to_vec(),
            b"--print=cfg".to_vec(),
        ];
        query(&target_info).unwrap();
    }
    #[test]
    fn relay_observations_keep_signal_missing_status_and_incomplete_streams_distinct() {
        use trust_resource_controller::{
            StatusFrame,
            accounting::{Observation, Scope},
        };
        let data = |status| BrokerCaptureData {
            status,
            started: true,
            stdout: b"actual prefix".to_vec(),
            stderr: Vec::new(),
            stdout_end: StreamEnd::Eof,
            stderr_end: StreamEnd::Eof,
            truncated: false,
            failure: None,
            elapsed_ns: 10,
            accounting: Observation {
                scope: Scope::ChildAndWaitedDescendantsV1,
                peak_rss_bytes: None,
                cpu_times: None,
            },
        };
        let frame = StatusFrame {
            root_attempt: [1; 16],
            member_attempt: [2; 16],
            status: Status::Finished {
                outcome: Outcome::Signal(libc::SIGTERM),
                cause: CompletionCause::Cancelled,
                runtime_ns: 7,
            },
        };
        let (stats, signalled) = projection(
            data(Some(frame)),
            StreamingOutputLimits::new(1024, 4096),
            true,
        );
        assert_eq!(signalled.status.unwrap().signal(), Some(libc::SIGTERM));
        assert_eq!(stats.peak_rss, None);
        assert!(signalled.failure.is_some());
        assert!(!signalled.owner_observation.unwrap().retirement_confirmed);
        let (_, missing) = projection(data(None), StreamingOutputLimits::new(1024, 4096), true);
        assert!(missing.started && missing.status.is_none() && missing.failure.is_some());
        assert_eq!(missing.stdout, b"actual prefix");
        let mut broken = data(None);
        broken.stderr_end = StreamEnd::ReadFailed;
        let (_, broken) = projection(broken, StreamingOutputLimits::new(1024, 4096), false);
        assert!(!broken.complete());
        assert_eq!(broken.stderr_end, CaptureStreamEnd::Incomplete);
        // DATA conversion alone never creates an original CPU, native member,
        // output guard, source completion or descendant-retirement capability.
    }
}
