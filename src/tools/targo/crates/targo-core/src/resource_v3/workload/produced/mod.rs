//! Actual Role7 dispatch retains its original registered image and live phase.
//! No local child, serialized grant, CPU pool or legacy SDK-bin fallback.
use super::bank::broker::RegisteredArtifact;
use crate::ops::cargo_test::workload::evidence::{Binding, Kind};
use crate::resource_v3::Startup;
use cargo_util::{
    CaptureCompletionCause, CaptureOwnerObservation, CaptureStreamEnd, CapturedProcess, CpuTimes,
    ExecStats, ProcessBuilder, ProcessError, ProcessExecutor, StreamingOutputLimits,
};
use std::io;
use std::os::unix::process::ExitStatusExt as _;
use std::process::{ExitStatus, Output};
use std::sync::{
    Arc,
    atomic::{AtomicBool, Ordering},
};
use std::time::{Duration, Instant};
use trust_resource_controller::{
    CompletionCause, Delegations, GnuTransport, Outcome, Request, Role, Status,
    client::{
        ContainedProducedError, ContainedProducedMember, MetadataIo, MetadataOutputStream,
        ProducedResult,
    },
    workload::host::{MemberKind, contained, produced::ProducedRequest},
};

pub(crate) mod command;
mod streaming;

pub(crate) fn executor(
    startup: Arc<Startup>,
    artifact: Arc<RegisteredArtifact>,
    active: Arc<AtomicBool>,
) -> Arc<dyn ProcessExecutor> {
    Arc::new(Executor {
        startup,
        artifact,
        active,
        used: AtomicBool::new(false),
    })
}
struct Executor {
    startup: Arc<Startup>,
    artifact: Arc<RegisteredArtifact>,
    active: Arc<AtomicBool>,
    used: AtomicBool,
}
fn error(reason: impl Into<String>) -> io::Error {
    io::Error::other(reason.into())
}
fn action_kind(
    phase: trust_resource_controller::workload::host::phase::Kind,
    args: &[Vec<u8>],
) -> io::Result<MemberKind> {
    use trust_resource_controller::workload::host::phase::Kind as Phase;
    match (phase, args) {
        (Phase::BuildScript, []) => Ok(MemberKind::BuildScript),
        (Phase::Harnesses, [arg]) if arg == b"--list" => Ok(MemberKind::Inventory),
        (Phase::Harnesses, [arg]) if arg == b"--test-threads=1" => Ok(MemberKind::Sample),
        _ => Err(error(
            "produced action differs from its original retained phase/closed queue profile",
        )),
    }
}
fn failed(
    limits: StreamingOutputLimits,
    failure: impl Into<anyhow::Error>,
) -> (ExecStats, CapturedProcess) {
    (
        ExecStats::default(),
        CapturedProcess {
            limits: Some(limits),
            failure: Some(failure.into()),
            ..CapturedProcess::default()
        },
    )
}
impl Executor {
    fn output_capture(&self, process: &ProcessBuilder) -> io::Result<CapturedProcess> {
        let timeout = self
            .startup
            .workload_process
            .as_ref()
            .ok_or_else(|| error("missing original workload inputs"))?
            .invocation
            .header()
            .timeout_ns;
        Ok(self
            .capture_inner(
                process,
                StreamingOutputLimits::new(1024 * 1024, 64 * 1024 * 1024)
                    .with_timeout(Duration::from_nanos(timeout)),
                false,
                None,
            )
            .1)
    }

    fn capture_inner(
        &self,
        process: &ProcessBuilder,
        limits: StreamingOutputLimits,
        measured: bool,
        mut on_bytes: Option<&mut dyn FnMut(MetadataOutputStream, &[u8]) -> io::Result<()>>,
    ) -> (ExecStats, CapturedProcess) {
        let result = (|| -> io::Result<_> {
            if self.used.swap(true, Ordering::AcqRel) || !self.active.load(Ordering::Acquire) {
                return Err(error(
                    "produced original action reused or phase is no longer active",
                ));
            }
            let inputs = self
                .startup
                .workload_process
                .as_ref()
                .ok_or_else(|| error("produced work lost original process inputs"))?;
            let timeout = limits
                .runtime_timeout()
                .filter(|timeout| !timeout.is_zero())
                .ok_or_else(|| {
                    error("produced native work requires its finite target runtime budget")
                })?;
            let timeout_ns = u64::try_from(timeout.as_nanos())
                .map_err(|_| error("produced target budget is unrepresentable"))?;
            if timeout_ns > inputs.invocation.header().timeout_ns
                || limits.stream_bytes()
                    > trust_resource_controller::workload::host::produced::MAX_OUTPUT_BYTES
            {
                return Err(error(
                    "produced capture exceeds the original closed phase budget",
                ));
            }
            self.artifact
                .validate(inputs.deadline)
                .map_err(io::Error::other)?;
            let (command, observed) = command::command(
                process,
                &self.artifact.original().image().runtime_environment()?,
            )?;
            let registration = self.artifact.registered().registration();
            let kind = action_kind(self.artifact.phase().kind, &command.args)?;
            let request = ProducedRequest {
                member: Request {
                    binding: self.startup.query.binding.clone(),
                    member_attempt: super::super::call_attempt(
                        self.startup.query.binding.root_attempt,
                    )?,
                    role: Role::WorkloadProduced,
                    command,
                    // Actual host PhaseResources supplies its held backing.
                    // This request cannot create a fixed/shared CPU or GNU grant.
                    delegations: Delegations {
                        cpu: None,
                        gnu: GnuTransport::None,
                        fences: Vec::new(),
                    },
                    timeout_ns: Some(timeout_ns),
                },
                key: registration.key.clone(),
                kind,
                program_sha256: registration.program.sha256,
                runtime_roots: registration.runtime_roots.clone(),
            };
            request.validate_registered(registration)?;
            let sink = self
                .startup
                .workload_evidence
                .as_ref()
                .ok_or_else(|| error("produced work lost original durable sink"))?;
            let evidence = sink.action(
                Binding {
                    member: request.member.member_attempt,
                    kind: match kind {
                        MemberKind::Inventory => Kind::Inventory,
                        MemberKind::Sample => Kind::Sample,
                        MemberKind::BuildScript => Kind::BuildScript,
                        MemberKind::CompilerQuery | MemberKind::Coordinator => {
                            return Err(error(
                                "query cannot enter a produced script/harness phase",
                            ));
                        }
                    },
                    description_sha256: super::super::executor::command_description(&observed),
                },
                limits.stream_bytes() as u64,
                limits.stream_bytes() as u64,
            )?;
            let mut lengths = [0usize; 2];
            let mut tails = [0usize; 2];
            let mut observe = |stream, bytes: &[u8]| -> io::Result<()> {
                let index = usize::from(stream == MetadataOutputStream::Stderr);
                // Persist every actually received byte before limit/callback
                // failure can abort. Short writes remain explicitly incomplete.
                if index == 0 {
                    evidence.stdout.append(bytes)?;
                } else {
                    evidence.stderr.append(bytes)?;
                }
                lengths[index] = lengths[index]
                    .checked_add(bytes.len())
                    .ok_or_else(|| error("produced byte count overflow"))?;
                if lengths[index] > limits.stream_bytes() {
                    return Err(error(
                        "produced output exceeds its original finite stream bound",
                    ));
                }
                for byte in bytes {
                    tails[index] = tails[index]
                        .checked_add(1)
                        .ok_or_else(|| error("produced line count overflow"))?;
                    if tails[index] > limits.line_bytes() {
                        return Err(error(
                            "produced output exceeds its original finite line bound",
                        ));
                    }
                    if *byte == b'\n' {
                        tails[index] = 0;
                    }
                }
                if let Some(observer) = on_bytes.as_deref_mut() {
                    // A callback panic cannot unwind past a delivered native
                    // member and continue the graph. Preserve original raw
                    // prefixes through the existing unconditional Unknown abort.
                    struct PanicAbort;
                    impl Drop for PanicAbort {
                        fn drop(&mut self) {
                            if std::thread::panicking() {
                                crate::resource_v3::workload::abort_unknown();
                            }
                        }
                    }
                    let _original = PanicAbort;
                    observer(stream, bytes)?;
                }
                Ok(())
            };
            if inputs.cancelled.load(Ordering::Acquire)
                || process
                    .execution_cancellation()
                    .is_some_and(|cancel| cancel.load(Ordering::Acquire))
            {
                return Err(io::Error::new(
                    io::ErrorKind::Interrupted,
                    "produced action cancelled before delivery",
                ));
            }
            let setup = inputs
                .deadline
                .min(Instant::now() + Duration::from_secs(30));
            let contained = contained::Request {
                operation: super::super::call_attempt(request.key.root_attempt)?,
                gnu: self.artifact.phase().gnu,
                produced: request,
            };
            let mut member = match self.startup.client.workload_contained_produced(
                self.artifact.registered(),
                &contained,
                MetadataIo {
                    descriptions: Vec::new(),
                },
                setup,
            ) {
                Ok(member) => member,
                Err(ContainedProducedError::BeforeRequest(error)) => return Err(error),
                Err(ContainedProducedError::Refused) => {
                    return Err(io::Error::new(
                        io::ErrorKind::PermissionDenied,
                        "original host refused produced action before attachment",
                    ));
                }
                Err(ContainedProducedError::Unknown { mut member, .. }) => {
                    fail_unknown(&mut member, &mut observe, sink)
                }
            };
            let mut cancelled = false;
            loop {
                let until = inputs
                    .deadline
                    .min(Instant::now() + Duration::from_millis(250));
                if Instant::now() >= inputs.deadline {
                    let _ = member.cancel(until);
                    fail_unknown(&mut member, &mut observe, sink);
                }
                if !cancelled
                    && (inputs.cancelled.load(Ordering::Acquire)
                        || process
                            .execution_cancellation()
                            .is_some_and(|cancel| cancel.load(Ordering::Acquire)))
                {
                    cancelled = true;
                    if member.cancel(until).is_err() {
                        fail_unknown(&mut member, &mut observe, sink);
                    }
                }
                match member.poll_with_observer(until, &mut observe) {
                    Ok(Some(mut operation)) => {
                        let result = operation.take_observation().ok_or_else(|| {
                            error("contained output observation already consumed")
                        })?;
                        let mut captured = projection(result, limits, measured);
                        if let Err(error) = self.artifact.retain_completed(operation) {
                            self.active.store(false, Ordering::Release);
                            captured.1.failure = Some(error.into());
                        }
                        if let Err(error) = self.artifact.validate(inputs.deadline) {
                            captured.1.failure = Some(error);
                        }
                        return Ok(captured);
                    }
                    Ok(None) => std::thread::sleep(Duration::from_millis(1)),
                    Err(error) => match member.workload_refusal(until) {
                        Ok(Some(_)) => {
                            if let Ok(Some(observation)) =
                                member.take_failure_observation_with_observer(&mut observe)
                            {
                                sink.publish_produced_failure(&observation)?;
                            }
                            self.artifact
                                .validate(inputs.deadline)
                                .map_err(io::Error::other)?;
                            return Err(error);
                        }
                        _ => fail_unknown(&mut member, &mut observe, sink),
                    },
                }
            }
        })();
        result.unwrap_or_else(|failure| failed(limits, failure))
    }
}
fn fail_unknown(
    member: &mut ContainedProducedMember,
    observer: &mut dyn FnMut(MetadataOutputStream, &[u8]) -> io::Result<()>,
    sink: &Arc<crate::ops::cargo_test::workload::evidence::Evidence>,
) -> ! {
    if let Ok(Some(observation)) = member.take_failure_observation_with_observer(observer) {
        let _ = sink.publish_produced_failure(&observation);
    }
    super::abort_unknown()
}
fn projection(
    result: ProducedResult,
    limits: StreamingOutputLimits,
    measured: bool,
) -> (ExecStats, CapturedProcess) {
    let mut stats = ExecStats::default();
    if measured {
        stats.peak_rss = result.completion.observation.peak_rss_bytes;
        stats.cpu_times = result.completion.observation.cpu_times.map(|cpu| CpuTimes {
            user: Duration::from_nanos(cpu.user_ns),
            system: Duration::from_nanos(cpu.system_ns),
        });
    }
    let mut capture = CapturedProcess {
        stdout: result.stdout,
        stderr: result.stderr,
        started: true,
        stdout_end: CaptureStreamEnd::Eof,
        stderr_end: CaptureStreamEnd::Eof,
        stdout_truncated: result.output_limit_exceeded,
        stderr_truncated: result.output_limit_exceeded,
        limits: Some(limits),
        ..CapturedProcess::default()
    };
    let Status::Finished {
        outcome,
        cause,
        runtime_ns,
    } = result.completion.completed.finished.status
    else {
        unreachable!("ProducedMember requires its actual completed lifecycle")
    };
    capture.status = match outcome {
        Outcome::Exit(code) => code.checked_mul(256).map(ExitStatus::from_raw),
        Outcome::Signal(signal) => Some(ExitStatus::from_raw(signal)),
    };
    capture.owner_observation = Some(CaptureOwnerObservation {
        native_member_attempt: Some(result.completion.completed.finished.member_attempt),
        target_runtime: Some(Duration::from_nanos(runtime_ns)),
        cause: Some(match cause {
            CompletionCause::Exited => CaptureCompletionCause::Exited,
            CompletionCause::Timeout => CaptureCompletionCause::Timeout,
            CompletionCause::Cancelled => CaptureCompletionCause::Cancelled,
            CompletionCause::ResourceLimit => CaptureCompletionCause::ResourceLimit,
            CompletionCause::HostFault => CaptureCompletionCause::HostFault,
        }),
        retirement_confirmed: true,
    });
    if let Err(reason) = result.completion.completed.inputs_unchanged {
        capture.failure = Some(anyhow::anyhow!("produced inputs changed: {reason}"));
    } else if cause != CompletionCause::Exited
        || capture.status.is_none_or(|status| !status.success())
    {
        capture.failure = Some(
            ProcessError::new(
                &format!("native produced action ended: {cause:?}"),
                capture.status,
                None,
            )
            .into(),
        );
    }
    (stats, capture)
}
impl ProcessExecutor for Executor {
    fn supports_structured_capture(&self) -> bool {
        true
    }
    fn capture(
        &self,
        process: &ProcessBuilder,
        limits: StreamingOutputLimits,
        capture_rusage: bool,
    ) -> (ExecStats, CapturedProcess) {
        self.capture_inner(process, limits, capture_rusage, None)
    }
    fn output(&self, process: &ProcessBuilder) -> io::Result<Output> {
        let capture = self.output_capture(process)?;
        if let Some(failure) = capture.failure {
            return Err(io::Error::other(failure));
        }
        Ok(Output {
            status: capture
                .status
                .ok_or_else(|| error("native produced output has no original exit"))?,
            stdout: capture.stdout,
            stderr: capture.stderr,
        })
    }
    fn status(&self, process: &ProcessBuilder) -> io::Result<ExitStatus> {
        process.report_captured_completion(
            self.output_capture(process)?,
            "native produced output has no original exit",
        )
    }
    fn streaming(
        &self,
        process: &ProcessBuilder,
        on_stdout: &mut dyn FnMut(&str) -> anyhow::Result<()>,
        on_stderr: &mut dyn FnMut(&str) -> anyhow::Result<()>,
        capture: bool,
        limits: Option<StreamingOutputLimits>,
        _capture_rusage: bool,
    ) -> (ExecStats, anyhow::Result<Output>) {
        streaming::run(self, process, on_stdout, on_stderr, capture, limits)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_resource_controller::{
        BirthKind, Identity, MetadataCompletion, MetadataFile, Started, StatusFrame,
        accounting::{CpuTimes as NativeCpu, Observation},
        workload::host::{
            Completion,
            produced::{Key, ProducedPrepared},
        },
    };

    // Decoder/projection fixtures are data only. They construct no actual
    // host, registration, phase, UnitOutput, SDK or execution eligibility.
    fn result(cause: CompletionCause, exit: i32) -> ProducedResult {
        let identity = Identity {
            pid: 42,
            birth: 1,
            birth_kind: BirthKind::LinuxStartTicks,
        };
        ProducedResult {
            prepared: ProducedPrepared {
                key: Key {
                    root_attempt: [1; 16],
                    invocation_sha256: [2; 32],
                    phase: [3; 16],
                    ordinal: 4,
                    output: [5; 16],
                },
                member_attempt: [6; 16],
                identity,
                output_root: b"/output".to_vec(),
                sdk_root: b"/sdk".to_vec(),
                policy: trust_resource_controller::workload::host::produced::INPUT_POLICY.into(),
                scope: trust_resource_controller::workload::host::produced::INPUT_SCOPE.into(),
                executable: MetadataFile {
                    path: b"/output/test".to_vec(),
                    sha256: [7; 32],
                    bytes: 1,
                    device: 1,
                    inode: 1,
                },
                runtime: Vec::new(),
                loader_paths: Vec::new(),
                system_dependencies: Vec::new(),
                host: "host".into(),
                boot: "boot".into(),
            },
            started: Started {
                identity,
                monotonic_ns: 9,
                unix_ns: 10,
            },
            completion: Completion {
                phase: 4,
                kind: MemberKind::Sample,
                completed: MetadataCompletion {
                    finished: StatusFrame {
                        root_attempt: [1; 16],
                        member_attempt: [6; 16],
                        status: Status::Finished {
                            outcome: Outcome::Exit(exit),
                            cause,
                            runtime_ns: 1234,
                        },
                    },
                    inputs_unchanged: Ok(()),
                },
                observation: Observation::uncollected(),
            },
            stdout: b"actual\0binary\xffprefix".to_vec(),
            stderr: b"stderr".to_vec(),
            output_limit_exceeded: false,
        }
    }
    fn limits() -> StreamingOutputLimits {
        StreamingOutputLimits::new(1024, 4096).with_timeout(Duration::from_secs(1))
    }
    #[test]
    fn native_completion_projection_preserves_real_scope_optional_zero_and_failure_causes() {
        let (stats, capture) = projection(result(CompletionCause::Exited, 7), limits(), true);
        assert!(stats.cpu_times.is_none() && stats.peak_rss.is_none());
        assert_eq!(capture.stdout, b"actual\0binary\xffprefix");
        assert_eq!(capture.status.unwrap().code(), Some(7));
        assert!(
            capture
                .failure
                .unwrap()
                .downcast_ref::<ProcessError>()
                .is_some()
        );
        assert_eq!(
            capture.owner_observation.unwrap().target_runtime,
            Some(Duration::from_nanos(1234))
        );
        assert_eq!(
            capture.owner_observation.unwrap().native_member_attempt,
            Some([6; 16])
        );
        let mut native = result(CompletionCause::Timeout, 0);
        native.completion.observation.cpu_times = Some(NativeCpu {
            user_ns: 0,
            system_ns: 17,
        });
        native.completion.observation.peak_rss_bytes = Some(0);
        let (stats, capture) = projection(native, limits(), true);
        assert_eq!(stats.cpu_times.unwrap().user, Duration::ZERO);
        assert_eq!(stats.cpu_times.unwrap().system, Duration::from_nanos(17));
        assert_eq!(stats.peak_rss, Some(0));
        assert_eq!(
            capture.owner_observation.unwrap().cause,
            Some(CaptureCompletionCause::Timeout)
        );
        assert!(capture.owner_observation.unwrap().retirement_confirmed);
        assert!(!capture.succeeded());
        let mut drift = result(CompletionCause::Exited, 0);
        drift.completion.completed.inputs_unchanged = Err("original output changed".into());
        drift.output_limit_exceeded = true;
        let (_, capture) = projection(drift, limits(), true);
        assert!(capture.failure.is_some());
        assert!(capture.stdout_truncated && capture.stderr_truncated);
        assert!(!capture.complete());
        assert_eq!(capture.status.unwrap().code(), Some(0));
    }
}
