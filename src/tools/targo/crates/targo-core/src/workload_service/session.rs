//! Original live graph observer and its actual bounded diagnostic writers.
//! Checkpoint bytes/ACKs never replace SDK/output/native phase ownership.
use super::transport::{Control, Input, Output};
use crate::{
    compiler::Compilation,
    ops::cargo_test::{
        graph::TestCompletion,
        workload::{
            Inputs, Observer, OwnedOutputs,
            evidence::{ActionEvidence, Binding as ActionBinding, Kind},
        },
    },
    resource_v3::{Startup, workload::startup::Prepared},
    util::CargoResult,
};
use anyhow::Context as _;
use cargo_util::{CaptureCompletionCause, CaptureStreamEnd};
use std::io;
use std::sync::{
    Arc, Mutex,
    atomic::{AtomicU32, Ordering},
};
use std::time::{Duration, Instant};
use trust_resource_controller::{
    CompletionCause, Cpu, MetadataFile, Outcome,
    accounting::{CpuTimes, Observation, Scope},
    workload::{
        Decision, WorkloadInvocation, budget,
        service::{
            self, Binding, Chunk, OutputEnd, OutputScope, Stream,
            checkpoint::{Action, Artifact, Body, Capture, Checkpoint},
        },
    },
};
use trust_test_execution::workload::TARGETS;

fn error(reason: impl Into<String>) -> io::Error {
    io::Error::other(reason.into())
}
fn reason(value: impl std::fmt::Display) -> String {
    let mut value = value.to_string();
    if value.len() > 4000 {
        let mut end = 3900;
        while !value.is_char_boundary(end) {
            end -= 1;
        }
        value.truncate(end);
        value.push_str(" [truncated; original bytes retained]");
    }
    value
}
fn capture_failure(
    actual: &crate::ops::cargo_test::workload::CapturedAction,
    validation: Option<&anyhow::Error>,
) -> Option<String> {
    if actual.native_terminal() {
        // A complete known failed sample is an actual outcome, not a broken
        // capture. The caller separately retains semantic validation errors.
        return None;
    }
    actual
        .capture
        .failure
        .as_ref()
        .map(reason)
        .or_else(|| actual.capture.read_error.clone())
        .or_else(|| actual.capture.cleanup_error.clone())
        .or_else(|| validation.map(reason))
        .or_else(|| Some("native action has no original complete native terminal".into()))
}
struct Counts {
    compile: [u64; 2],
    later: [u64; 2],
    compiler_retired: bool,
}
struct Diagnostics {
    binding: Binding,
    output: Arc<Output>,
    evidence: Arc<ActionEvidence>,
    deadline: Instant,
    counts: Mutex<Counts>,
}
struct Writer {
    diagnostics: Arc<Diagnostics>,
    stream: Stream,
}
impl std::io::Write for Writer {
    fn write(&mut self, bytes: &[u8]) -> io::Result<usize> {
        let mut counts = self
            .diagnostics
            .counts
            .lock()
            .map_err(|_| error("original diagnostic owner poisoned"))?;
        let index = usize::from(self.stream == Stream::Stderr);
        // Same original output/evidence owner. These post-Cargo formatting
        // bytes are graph diagnostics, never raw native child pipe claims.
        if index == 0 {
            self.diagnostics.evidence.stdout.append(bytes)?;
        } else {
            self.diagnostics.evidence.stderr.append(bytes)?;
        }
        for bytes in bytes.chunks(service::MAX_CHUNK_BYTES) {
            let retired = counts.compiler_retired;
            let lengths = if retired {
                &mut counts.later
            } else {
                &mut counts.compile
            };
            let offset = lengths[index];
            if offset
                .checked_add(bytes.len() as u64)
                .is_none_or(|n| n > service::MAX_STREAM_BYTES)
            {
                return Err(error(
                    "root diagnostics exceed original finite stream budget",
                ));
            }
            let frame = if retired {
                service::finish::Diagnostic {
                    binding: self.diagnostics.binding.clone(),
                    stream: self.stream,
                    offset,
                    bytes: bytes.to_vec(),
                }
                .encode()?
            } else {
                Chunk {
                    binding: self.diagnostics.binding.clone(),
                    checkpoint: 1,
                    stream: self.stream,
                    offset,
                    bytes: bytes.to_vec(),
                }
                .encode()?
            };
            self.diagnostics
                .output
                .frame(&frame, self.diagnostics.deadline)?;
            lengths[index] += bytes.len() as u64;
        }
        Ok(bytes.len())
    }
    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}

pub(super) struct Session {
    pub(super) startup: Arc<Startup>,
    pub(super) inputs: Arc<Inputs>,
    pub(super) invocation: Arc<WorkloadInvocation>,
    pub(super) binding: Binding,
    pub(super) deadline: Instant,
    output: Arc<Output>,
    control: Mutex<Control>,
    diagnostics: Arc<Diagnostics>,
    jobs: AtomicU32,
    compiled: std::sync::atomic::AtomicBool,
    ready_record: Vec<u8>,
}
impl std::fmt::Debug for Session {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("OriginalWorkloadSession")
            .field("root_attempt", &hex::encode(self.binding.root_attempt))
            .finish_non_exhaustive()
    }
}
impl Session {
    pub(super) fn new(
        prepared: Prepared,
        input: Input,
    ) -> CargoResult<(Arc<Self>, crate::context::root_control::RootControl)> {
        let startup = prepared.startup;
        let process = startup
            .workload_process
            .as_ref()
            .context("service lost original process owner")?;
        let invocation = match &process.invocation {
            crate::resource_v3::workload::ProcessPlan::Workload(invocation) => {
                Arc::clone(invocation)
            }
            crate::resource_v3::workload::ProcessPlan::NativeJob(_) => {
                anyhow::bail!("fixed workload service cannot consume a native job plan")
            }
        };
        let binding = Binding {
            root_attempt: startup.query.binding.root_attempt,
            invocation_sha256: prepared.ready.invocation_sha256(),
        };
        let output = Output::capture_stdout(prepared.deadline, process.cancelled.clone())?;
        let sink = startup
            .workload_evidence
            .as_ref()
            .context("service lost original native sink")?;
        let mut description = cargo_util::Sha256::new();
        description.update(b"native-workload-root-diagnostics-v1");
        description.update(&binding.invocation_sha256);
        let evidence = sink.action(
            ActionBinding {
                member: crate::resource_v3::call_attempt(binding.root_attempt)?,
                kind: Kind::Diagnostic,
                description_sha256: description.finish(),
            },
            service::MAX_STREAM_BYTES,
            service::MAX_STREAM_BYTES,
        )?;
        let diagnostics = Arc::new(Diagnostics {
            binding: binding.clone(),
            output: output.clone(),
            evidence,
            deadline: prepared.deadline,
            counts: Mutex::new(Counts {
                compile: [0, 0],
                later: [0, 0],
                compiler_retired: false,
            }),
        });
        let (control, queue) = Control::start(
            binding.clone(),
            input,
            prepared.deadline,
            process.cancelled.clone(),
        )?;
        let context = prepared.ready.context();
        let Cpu::CooperativeShared {
            native_manifest,
            ceiling: original_ceiling,
        } = context.cpu
        else {
            anyhow::bail!("service lost actual original cooperative context")
        };
        let initial = matches!(
            &prepared.ready,
            crate::resource_v3::workload::startup::ReadyEvidence::Initial(_)
        );
        let jobs = startup.local_ceiling;
        let ready = service::Ready {
            binding: binding.clone(),
            original_root: context.original_root,
            native_manifest,
            reserved_domain: prepared.ready.funded_width() as u32,
            dispatch_ceiling: if initial { 1 } else { jobs },
            memory_bytes: context.memory.bytes,
        };
        let ready_record = if initial {
            service::InitialReady {
                funded: ready,
                original_ceiling,
                maximum_dispatch: jobs,
            }
            .encode()?
        } else {
            ready.encode()?
        };
        Ok((
            Arc::new(Self {
                startup,
                inputs: Arc::new(prepared.inputs),
                invocation,
                binding,
                deadline: prepared.deadline,
                output,
                control: Mutex::new(control),
                diagnostics,
                jobs: AtomicU32::new(jobs),
                compiled: std::sync::atomic::AtomicBool::new(false),
                ready_record,
            }),
            queue,
        ))
    }
    pub(super) fn shell(&self) -> cargo_util_terminal::Shell {
        cargo_util_terminal::Shell::from_writes(
            Box::new(Writer {
                diagnostics: self.diagnostics.clone(),
                stream: Stream::Stdout,
            }),
            Box::new(Writer {
                diagnostics: self.diagnostics.clone(),
                stream: Stream::Stderr,
            }),
        )
    }
    pub(super) fn ready(&self) -> CargoResult<()> {
        anyhow::ensure!(
            !self
                .startup
                .workload_process
                .as_ref()
                .context("lost original workload process owner")?
                .cancelled
                .load(Ordering::Acquire),
            "original input ended before live service readiness"
        );
        self.inputs.validate()?;
        self.output.frame(&self.ready_record, self.deadline)?;
        Ok(())
    }
    pub(super) fn begin_compile(&self, jobs: u32) -> CargoResult<()> {
        anyhow::ensure!(
            jobs > 0 && jobs <= self.startup.local_ceiling,
            "normal workload BuildConfig exceeds original live ceiling"
        );
        self.jobs.store(jobs, Ordering::Release);
        let deadline = Instant::now()
            .checked_add(Duration::from_nanos(self.invocation.timeout_ns))
            .context("original compile deadline unrepresentable")?
            .min(self.deadline);
        self.control
            .lock()
            .map_err(|_| error("original service control poisoned"))?
            .begin_compile(deadline)?;
        Ok(())
    }
    pub(super) fn record_jobs(&self, jobs: u32) -> CargoResult<()> {
        anyhow::ensure!(
            jobs > 0 && jobs <= self.startup.local_ceiling,
            "normal compiler jobs exceed original closed workload ceiling"
        );
        self.jobs.store(jobs, Ordering::Release);
        Ok(())
    }
    pub(super) fn has_compiler_checkpoint(&self) -> bool {
        self.compiled.load(Ordering::Acquire)
    }
    pub(super) fn failed_before_compiler_checkpoint(&self, failure: String) -> CargoResult<()> {
        if self.has_compiler_checkpoint() {
            return Ok(());
        }
        self.emit_compiled(false, Vec::new(), Some(reason(failure)))
    }
    fn emit_compiled(
        &self,
        succeeded: bool,
        artifacts: Vec<Artifact>,
        failure: Option<String>,
    ) -> CargoResult<()> {
        anyhow::ensure!(
            !self.compiled.swap(true, Ordering::AcqRel),
            "original compiler checkpoint repeated"
        );
        self.control
            .lock()
            .map_err(|_| error("original service control poisoned"))?
            .compiler_retired()?;
        let lengths = {
            let mut counts = self
                .diagnostics
                .counts
                .lock()
                .map_err(|_| error("original diagnostic owner poisoned"))?;
            anyhow::ensure!(
                !counts.compiler_retired,
                "compiler diagnostic boundary repeated"
            );
            counts.compiler_retired = true;
            counts.compile
        };
        self.output.frame(
            &OutputEnd {
                binding: self.binding.clone(),
                checkpoint: 1,
                scope: OutputScope::CompilerGraph,
                lengths,
                closed: [true, true],
                truncated: [false, false],
            }
            .encode()?,
            self.deadline,
        )?;
        self.checkpoint(Checkpoint {
            binding: self.binding.clone(),
            sequence: 1,
            body: Body::Compiled {
                succeeded,
                workers_retired: true,
                output_complete: true,
                jobs: self.jobs.load(Ordering::Acquire),
                artifacts,
                failure,
            },
        })
    }
    fn checkpoint(&self, checkpoint: Checkpoint) -> CargoResult<()> {
        self.inputs.validate()?;
        let bytes = checkpoint.encode(&self.invocation)?;
        let mut digest = cargo_util::Sha256::new();
        digest.update(&bytes);
        let until = Instant::now()
            .checked_add(Duration::from_nanos(budget::CHECKPOINT_NS))
            .context("checkpoint deadline unrepresentable")?
            .min(self.deadline);
        let mut control = self
            .control
            .lock()
            .map_err(|_| error("original service continuation owner poisoned"))?;
        control.expect(checkpoint.sequence, digest.finish(), until)?;
        self.output.frame(&bytes, until)?;
        let decision = control.wait(until)?;
        drop(control);
        self.inputs.validate()?;
        anyhow::ensure!(
            decision == Decision::Continue,
            "original workload continuation stopped its graph"
        );
        Ok(())
    }
    pub(super) fn finish_input(&self) -> CargoResult<()> {
        let mut control = self
            .control
            .lock()
            .map_err(|_| error("original service input owner poisoned"))?;
        let finished = control.finish();
        let observation = control.observation().map_err(|error| reason(error));
        let published = self.inputs.evidence.publish_service_input(observation);
        finished?;
        published?;
        Ok(())
    }
    pub(super) fn send(&self, bytes: &[u8]) -> CargoResult<()> {
        self.output.frame(bytes, self.deadline)?;
        Ok(())
    }
}
impl Observer for Session {
    fn compiler_retired(
        &self,
        _compilation: &Compilation<'_>,
        succeeded: bool,
        outputs: Option<&OwnedOutputs>,
    ) -> CargoResult<()> {
        let mut artifacts = Vec::new();
        if let Some(outputs) = outputs {
            outputs.validate()?;
            for (target, input) in outputs.observations() {
                let target = TARGETS
                    .iter()
                    .position(|candidate| *candidate == target)
                    .context("compiled target outside original population")?
                    as u32;
                let file = &input.executable;
                let mut sha256 = [0; 32];
                hex::decode_to_slice(&file.sha256, &mut sha256)?;
                artifacts.push(Artifact {
                    target,
                    executable: MetadataFile {
                        path: file.path.as_os_str().as_encoded_bytes().to_vec(),
                        sha256,
                        bytes: file.bytes,
                        device: file.device,
                        inode: file.inode,
                    },
                });
            }
        }
        let succeeded = succeeded && outputs.is_some();
        self.emit_compiled(
            succeeded,
            artifacts,
            (!succeeded).then(|| {
                "original compiler graph failed or has no complete output population".into()
            }),
        )
    }
    fn action_finished(&self, completion: &TestCompletion) -> CargoResult<()> {
        let target = TARGETS
            .iter()
            .position(|candidate| *candidate == completion.action.unit.target.name())
            .context("native action outside original target population")?
            as u32;
        let action = match completion
            .action
            .workload_action
            .context("service observed an ordinary test action")?
        {
            trust_test_execution::workload::Action::Inventory => Action::Inventory,
            trust_test_execution::workload::Action::Sample { repetition } => {
                Action::Sample { repetition }
            }
        };
        let sequence = completion.action.index as u64 + 2;
        let mut capture = Capture {
            started: false,
            outcome: None,
            cause: None,
            runtime_ns: None,
            retirement_confirmed: false,
            accounting: None,
            member_attempt: None,
            failure: completion.result.as_ref().err().map(reason),
        };
        let mut lengths = [0, 0];
        let mut closed = [false, false];
        let mut truncated = [false, false];
        if let Some(actual) = &completion.workload {
            let original = &actual.capture;
            capture.failure = capture_failure(actual, completion.result.as_ref().err());
            if actual.native_terminal()
                && let Err(validation) = &completion.result
            {
                // Separate Root diagnostics cannot contaminate the native
                // harness's raw output/counts or turn exit7 into missing IO.
                let mut shell = self.shell();
                writeln!(
                    shell.err(),
                    "native workload action validation failed: {}",
                    reason(validation)
                )?;
            }
            capture.started = original.started;
            #[cfg(unix)]
            {
                use std::os::unix::process::ExitStatusExt as _;
                capture.outcome = original.status.and_then(|status| {
                    status
                        .code()
                        .map(Outcome::Exit)
                        .or_else(|| status.signal().map(Outcome::Signal))
                });
            }
            if let Some(owner) = original.owner_observation {
                capture.member_attempt = owner.native_member_attempt;
                capture.runtime_ns = owner
                    .target_runtime
                    .map(|value| u64::try_from(value.as_nanos()))
                    .transpose()?;
                capture.retirement_confirmed = owner.retirement_confirmed;
                capture.cause = owner.cause.map(|cause| match cause {
                    CaptureCompletionCause::Exited => CompletionCause::Exited,
                    CaptureCompletionCause::Timeout => CompletionCause::Timeout,
                    CaptureCompletionCause::Cancelled => CompletionCause::Cancelled,
                    CaptureCompletionCause::ResourceLimit => CompletionCause::ResourceLimit,
                    CaptureCompletionCause::HostFault => CompletionCause::HostFault,
                });
            }
            capture.accounting = Some(Observation {
                scope: Scope::ChildAndWaitedDescendantsV1,
                cpu_times: actual
                    .stats
                    .cpu_times
                    .map(|cpu| {
                        Ok::<_, std::num::TryFromIntError>(CpuTimes {
                            user_ns: u64::try_from(cpu.user.as_nanos())?,
                            system_ns: u64::try_from(cpu.system.as_nanos())?,
                        })
                    })
                    .transpose()?,
                peak_rss_bytes: actual.stats.peak_rss,
            });
            for (index, (stream, bytes)) in [
                (Stream::Stdout, &original.stdout),
                (Stream::Stderr, &original.stderr),
            ]
            .into_iter()
            .enumerate()
            {
                for chunk in bytes.chunks(service::MAX_CHUNK_BYTES) {
                    self.output.frame(
                        &Chunk {
                            binding: self.binding.clone(),
                            checkpoint: sequence,
                            stream,
                            offset: lengths[index],
                            bytes: chunk.to_vec(),
                        }
                        .encode()?,
                        self.deadline,
                    )?;
                    lengths[index] += chunk.len() as u64;
                }
            }
            closed = [
                original.stdout_end == CaptureStreamEnd::Eof,
                original.stderr_end == CaptureStreamEnd::Eof,
            ];
            truncated = [original.stdout_truncated, original.stderr_truncated];
        }
        self.output.frame(
            &OutputEnd {
                binding: self.binding.clone(),
                checkpoint: sequence,
                scope: OutputScope::NativeAction,
                lengths,
                closed,
                truncated,
            }
            .encode()?,
            self.deadline,
        )?;
        self.checkpoint(Checkpoint {
            binding: self.binding.clone(),
            sequence,
            body: Body::Harness {
                target,
                action,
                capture,
            },
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::os::unix::process::ExitStatusExt as _;

    #[test]
    fn known_failed_sample_is_separate_from_unknown_owner_or_incomplete_capture() {
        // Projection data only: no SDK, registration, retirement or output
        // eligibility owner is constructed by this consistency control.
        let status = std::process::ExitStatus::from_raw(7 * 256);
        let mut actual = crate::ops::cargo_test::workload::CapturedAction {
            capture: cargo_util::CapturedProcess {
                started: true,
                status: Some(status),
                stdout_end: CaptureStreamEnd::Eof,
                stderr_end: CaptureStreamEnd::Eof,
                failure: Some(
                    cargo_util::ProcessError::new("actual failed sample", Some(status), None)
                        .into(),
                ),
                owner_observation: Some(cargo_util::CaptureOwnerObservation {
                    native_member_attempt: Some([1; 16]),
                    target_runtime: Some(Duration::from_nanos(10)),
                    cause: Some(CaptureCompletionCause::Exited),
                    retirement_confirmed: true,
                }),
                ..Default::default()
            },
            stats: cargo_util::ExecStats::default(),
        };
        let validation = anyhow::anyhow!("the native sample exited7");
        assert!(actual.native_terminal());
        assert!(capture_failure(&actual, Some(&validation)).is_none());
        actual.capture.read_error = Some("actual reader failed".into());
        assert!(capture_failure(&actual, Some(&validation)).is_some());
        actual.capture.read_error = None;
        actual
            .capture
            .owner_observation
            .as_mut()
            .unwrap()
            .retirement_confirmed = false;
        assert!(capture_failure(&actual, Some(&validation)).is_some());
        actual.capture.owner_observation = None;
        actual.capture.status = Some(std::process::ExitStatus::from_raw(0));
        actual.capture.failure = None;
        assert!(
            capture_failure(&actual, None).is_some(),
            "successful bytes cannot supply a native owner"
        );
    }
}
