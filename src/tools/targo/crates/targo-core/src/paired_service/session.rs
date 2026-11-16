//! Actual original paired session, its bounded sinks and graph observations.
//! All native admissions stay in the existing runtime/bank/host owners.
use super::control::Control;
use crate::compiler::{Compilation, qualification, qualification_command::UnitIdentity};
use crate::context::root_control::RootControl;
use crate::ops::cargo_test::{
    graph::TestCompletion,
    workload::{
        self, Inputs, OwnedOutputs,
        evidence::{ActionEvidence, Binding as ActionBinding, Kind},
    },
};
use crate::resource_v3::{Startup, paired::startup::Prepared};
use crate::util::{CargoResult, log_message::LogMessage};
use crate::workload_service::transport::{Input, Output};
use anyhow::Context as _;
use cargo_util_terminal::Shell;
use std::collections::{BTreeMap, BTreeSet};
use std::io;
use std::os::unix::ffi::OsStrExt as _;
use std::sync::{Arc, Mutex, atomic::Ordering};
use std::time::{Duration, Instant};
use trust_resource_controller::{
    Cpu, MetadataFile,
    paired_qualification::{
        PairedInvocation,
        service::{self, Binding, Node, OutputScope, Stream},
    },
};

fn error(reason: impl Into<String>) -> io::Error {
    io::Error::other(reason.into())
}
pub(super) fn reason(value: impl std::fmt::Display) -> String {
    let mut value = value.to_string();
    if value.len() > 4000 {
        let mut keep = 3900;
        while !value.is_char_boundary(keep) {
            keep -= 1
        }
        value.truncate(keep);
        value.push_str(" [incomplete; original prefix retained]");
    }
    value
}
struct Stage {
    diagnostic: Arc<ActionEvidence>,
    report: Arc<ActionEvidence>,
    diagnostic_lengths: [u64; 2],
    report_length: u64,
    report_bytes: Vec<u8>,
    run_id: Option<String>,
    closed: bool,
}
struct NativeFact {
    capture: service::Capture,
    complete: bool,
}
struct State {
    registered: BTreeSet<Node>,
    finished: BTreeSet<Node>,
    blocked: BTreeSet<Node>,
    next: u64,
    stages: BTreeMap<Node, Stage>,
    native: BTreeMap<Node, NativeFact>,
}
pub(super) struct Session {
    pub(super) startup: Arc<Startup>,
    pub(super) inputs: Arc<Inputs>,
    pub(super) plan: Arc<PairedInvocation>,
    pub(super) binding: Binding,
    pub(super) deadline: Instant,
    output: Arc<Output>,
    control: Mutex<Control>,
    state: Mutex<State>,
    ready: service::Ready,
}
impl std::fmt::Debug for Session {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("OriginalPairedSession")
            .field("root_attempt", &hex::encode(self.binding.root_attempt))
            .finish_non_exhaustive()
    }
}
impl Session {
    pub(super) fn new(prepared: Prepared, input: Input) -> CargoResult<(Arc<Self>, RootControl)> {
        let startup = prepared.startup;
        let plan = startup
            .paired_invocation
            .clone()
            .context("paired session lost actual complete60 startup")?;
        let binding = Binding {
            root_attempt: startup.query.binding.root_attempt,
            invocation_sha256: prepared.ready.invocation_sha256,
        };
        let process = startup
            .workload_process
            .as_ref()
            .context("paired session lost original process owner")?;
        let output = Output::capture_stdout(prepared.deadline, process.cancelled.clone())?;
        let writer = startup
            .workload_evidence
            .as_ref()
            .context("paired session lost actual original sink")?;
        let mut stages = BTreeMap::new();
        for node in [Node::AyCompile, Node::ConsumerCompile] {
            let action = |scope: &[u8]| -> CargoResult<Arc<ActionEvidence>> {
                let mut hash = cargo_util::Sha256::new();
                hash.update(b"native-paired-stage-diagnostics-v1\0");
                hash.update(&binding.invocation_sha256);
                hash.update(&[u8::from(node == Node::ConsumerCompile)]);
                hash.update(scope);
                Ok(writer.action(
                    ActionBinding {
                        member: crate::resource_v3::call_attempt(binding.root_attempt)?,
                        kind: Kind::Diagnostic,
                        description_sha256: hash.finish(),
                    },
                    service::MAX_STREAM_BYTES,
                    service::MAX_STREAM_BYTES,
                )?)
            };
            stages.insert(
                node,
                Stage {
                    diagnostic: action(b"diagnostic")?,
                    report: action(b"compiler-primary-process-report")?,
                    diagnostic_lengths: [0; 2],
                    report_length: 0,
                    report_bytes: Vec::new(),
                    run_id: None,
                    closed: false,
                },
            );
        }
        let (control, root) = Control::start(
            binding.clone(),
            plan.consumer.repetitions,
            input,
            prepared.deadline,
            process.cancelled.clone(),
        )?;
        let context = &prepared.ready.context.context;
        let Cpu::CooperativeShared {
            native_manifest, ..
        } = context.cpu
        else {
            anyhow::bail!("paired session lost original cooperative context")
        };
        let ready = service::Ready {
            binding: binding.clone(),
            original_root: context.original_root,
            native_manifest,
            reserved_domain: prepared.ready.cpu_set().count() as u32,
            dispatch_ceiling: startup.local_ceiling,
            memory_bytes: context.memory.bytes,
            repetitions: plan.consumer.repetitions,
        };
        Ok((
            Arc::new(Self {
                startup,
                inputs: Arc::new(prepared.inputs),
                plan,
                binding,
                deadline: prepared.deadline,
                output,
                control: Mutex::new(control),
                state: Mutex::new(State {
                    registered: BTreeSet::new(),
                    finished: BTreeSet::new(),
                    blocked: BTreeSet::new(),
                    next: 1,
                    stages,
                    native: BTreeMap::new(),
                }),
                ready,
            }),
            root,
        ))
    }
    fn poisoned(&self) {
        if let Some(process) = &self.startup.workload_process {
            process.poisoned.store(true, Ordering::Release);
            process.cancelled.store(true, Ordering::Release);
        }
    }
    pub(super) fn send(&self, bytes: &[u8]) -> CargoResult<()> {
        if let Err(cause) = self.output.frame(bytes, self.deadline) {
            self.poisoned();
            return Err(cause.into());
        }
        Ok(())
    }
    pub(super) fn ready(&self) -> CargoResult<()> {
        self.inputs.validate()?;
        self.send(
            &service::compiler_observation::Ready {
                original: self.ready.clone(),
            }
            .encode()?,
        )?;
        Ok(())
    }
    pub(super) fn register(&self, node: Node, unit: Option<&UnitIdentity>) -> CargoResult<()> {
        let original_compile_unit = unit
            .map(|unit| {
                anyhow::ensure!(
                    unit.root_attempt == self.binding.root_attempt
                        && unit.invocation_sha256 == self.binding.invocation_sha256,
                    "selected compile unit changed original complete-plan binding"
                );
                Ok::<_, anyhow::Error>(service::CompileUnit {
                    index: unit.index.0,
                    unit_hash: unit.unit_hash.clone(),
                    package: unit.package.clone(),
                    target: unit.target.clone(),
                    source: unit.source.as_os_str().as_bytes().to_vec(),
                })
            })
            .transpose()?;
        let mut state = self
            .state
            .lock()
            .map_err(|_| error("paired graph observer poisoned"))?;
        anyhow::ensure!(
            state.registered.insert(node),
            "paired node registered twice"
        );
        drop(state);
        self.send(
            &service::Registered {
                binding: self.binding.clone(),
                node,
                original_compile_unit,
            }
            .encode(self.plan.consumer.repetitions)?,
        )
    }
    pub(super) fn has_finished(&self, node: Node) -> CargoResult<bool> {
        let state = self
            .state
            .lock()
            .map_err(|_| error("paired graph observer poisoned"))?;
        Ok(state.finished.contains(&node) || state.blocked.contains(&node))
    }
    pub(super) fn begin_phase(&self) -> CargoResult<()> {
        let until = Instant::now()
            .checked_add(Duration::from_nanos(self.plan.consumer.timeout_ns))
            .context("paired phase deadline unrepresentable")?
            .min(self.deadline);
        self.control
            .lock()
            .map_err(|_| error("paired input owner poisoned"))?
            .begin_phase(until)?;
        Ok(())
    }
    fn end_phase(&self) -> CargoResult<()> {
        self.control
            .lock()
            .map_err(|_| error("paired input owner poisoned"))?
            .end_phase()?;
        Ok(())
    }
    fn bytes(
        &self,
        node: Node,
        scope: OutputScope,
        stream: Stream,
        bytes: &[u8],
    ) -> io::Result<usize> {
        let result = (|| {
            let index = usize::from(stream == Stream::Stderr);
            let mut state = self
                .state
                .lock()
                .map_err(|_| error("paired writer state poisoned"))?;
            let stage = state
                .stages
                .get_mut(&node)
                .ok_or_else(|| error("diagnostics selected a native action node"))?;
            if stage.closed {
                return Err(error("diagnostics after original stage writer closure"));
            }
            let offset = if scope == OutputScope::CompilerReport {
                if index != 0 {
                    return Err(error("compiler report selected stderr"));
                }
                stage.report_length
            } else {
                stage.diagnostic_lengths[index]
            };
            if offset
                .checked_add(bytes.len() as u64)
                .is_none_or(|n| n > service::MAX_STREAM_BYTES)
            {
                return Err(error("paired diagnostic stream budget exhausted"));
            }
            let sink = if scope == OutputScope::CompilerReport {
                stage.report.clone()
            } else {
                stage.diagnostic.clone()
            };
            if scope == OutputScope::CompilerReport {
                stage.report_length += bytes.len() as u64
            } else {
                stage.diagnostic_lengths[index] += bytes.len() as u64
            }
            // Persist the actual diagnostic prefix before framing/judging IO.
            // These formatted bytes never become a native child's raw output.
            let persisted = if index == 0 {
                sink.stdout.append(bytes)
            } else {
                sink.stderr.append(bytes)
            };
            let delivered = (|| {
                let mut position = offset;
                for chunk in bytes.chunks(service::MAX_CHUNK_BYTES) {
                    self.output.frame(
                        &service::Chunk {
                            binding: self.binding.clone(),
                            node,
                            scope,
                            stream,
                            offset: position,
                            bytes: chunk.to_vec(),
                        }
                        .encode(self.plan.consumer.repetitions)?,
                        self.deadline,
                    )?;
                    position += chunk.len() as u64;
                }
                Ok::<_, io::Error>(())
            })();
            persisted?;
            delivered?;
            Ok(bytes.len())
        })();
        if result.is_err() {
            self.poisoned()
        }
        result
    }
    pub(super) fn shell(self: &Arc<Self>, node: Node) -> Shell {
        Shell::from_writes(
            Box::new(Writer {
                session: self.clone(),
                node,
                stream: Stream::Stdout,
            }),
            Box::new(Writer {
                session: self.clone(),
                node,
                stream: Stream::Stderr,
            }),
        )
    }
    fn report(&self, node: Node, run_id: &str, message: &LogMessage) -> io::Result<()> {
        {
            let mut state = self
                .state
                .lock()
                .map_err(|_| error("paired report state poisoned"))?;
            let stage = state
                .stages
                .get_mut(&node)
                .ok_or_else(|| error("compiler report has wrong scope"))?;
            if let Some(original) = &stage.run_id {
                if original != run_id {
                    return Err(error("compiler report changed original run ID"));
                }
            } else {
                stage.run_id = Some(run_id.to_owned());
            }
        }
        struct Bounded {
            bytes: Vec<u8>,
        }
        impl io::Write for Bounded {
            fn write(&mut self, bytes: &[u8]) -> io::Result<usize> {
                let keep = bytes
                    .len()
                    .min((1024 * 1024usize).saturating_sub(self.bytes.len()));
                if keep == 0 {
                    return Err(io::ErrorKind::WriteZero.into());
                }
                self.bytes.extend_from_slice(&bytes[..keep]);
                Ok(keep)
            }
            fn flush(&mut self) -> io::Result<()> {
                Ok(())
            }
        }
        let mut line = Bounded { bytes: Vec::new() };
        let encoded = message.write_json_log(&mut line, run_id);
        let delivered = self.bytes(
            node,
            OutputScope::CompilerReport,
            Stream::Stdout,
            &line.bytes,
        );
        // The original durable sink and transport receive their prefix FIRST.
        // This bounded second copy is only input to the maintained report
        // reducer after the actual writer closes; it grants no cached verdict.
        let retained = (|| {
            let mut state = self
                .state
                .lock()
                .map_err(|_| error("paired report state poisoned"))?;
            let stage = state
                .stages
                .get_mut(&node)
                .ok_or_else(|| error("wrong report scope"))?;
            if stage
                .report_bytes
                .len()
                .checked_add(line.bytes.len())
                .is_none_or(|n| n as u64 > service::MAX_STREAM_BYTES)
            {
                return Err(error(
                    "original compiler report exceeds its native byte bound",
                ));
            }
            stage
                .report_bytes
                .try_reserve(line.bytes.len())
                .map_err(|cause| error(cause.to_string()))?;
            stage.report_bytes.extend_from_slice(&line.bytes);
            Ok::<_, io::Error>(())
        })();
        if let Err(cause) = encoded {
            self.poisoned();
            return Err(cause);
        }
        delivered?;
        retained?;
        Ok(())
    }
    fn synchronize_report(&self, node: Node) -> io::Result<()> {
        let sink = {
            let state = self
                .state
                .lock()
                .map_err(|_| error("paired report state poisoned"))?;
            state
                .stages
                .get(&node)
                .ok_or_else(|| error("compiler report has wrong scope"))?
                .report
                .clone()
        };
        let result = sink.sync_prefix(
            self.deadline
                .min(Instant::now() + Duration::from_millis(250)),
        );
        if result.is_err() {
            self.poisoned()
        }
        result
    }
    pub(super) fn close_stage(&self, node: Node) -> CargoResult<()> {
        self.control
            .lock()
            .map_err(|_| error("paired stage timer owner poisoned"))?
            .stage_joined()?;
        let mut state = self
            .state
            .lock()
            .map_err(|_| error("paired writer state poisoned"))?;
        let stage = state
            .stages
            .get_mut(&node)
            .context("unknown original stage")?;
        anyhow::ensure!(!stage.closed, "stage closed twice");
        stage.closed = true;
        let report = stage.report.clone();
        let run_id = stage.run_id.clone();
        let report_bytes = std::mem::take(&mut stage.report_bytes);
        let ends = [
            (
                OutputScope::Diagnostics,
                Stream::Stdout,
                stage.diagnostic_lengths[0],
                true,
            ),
            (
                OutputScope::Diagnostics,
                Stream::Stderr,
                stage.diagnostic_lengths[1],
                true,
            ),
            (
                OutputScope::CompilerReport,
                Stream::Stdout,
                stage.report_length,
                stage.run_id.is_some(),
            ),
        ];
        drop(state);
        // No projection precedes actual writer closure and prefix sync. A
        // failure here remains an incomplete original graph/transport.
        report.sync_prefix(
            self.deadline
                .min(Instant::now() + Duration::from_millis(250)),
        )?;
        for (scope, stream, length, writer_closed) in ends {
            self.send(
                &service::DiagnosticEnd {
                    binding: self.binding.clone(),
                    node,
                    scope,
                    stream,
                    length,
                    writer_closed,
                    truncated: false,
                }
                .encode(self.plan.consumer.repetitions)?,
            )?;
        }
        let mut hash = cargo_util::Sha256::new();
        hash.update(&report_bytes);
        let analyzed = run_id
            .as_deref()
            .context("original compiler report writer was never initialized")
            .and_then(|run| {
                crate::ops::cargo_report::execution::native_compiler_counts(
                    std::io::Cursor::new(&report_bytes),
                    run,
                )
            });
        let (counts, unavailable) = match analyzed {
            Ok(counts) => (Some(counts), None),
            Err(cause) => (None, Some(reason(cause))),
        };
        self.send(
            &service::compiler_observation::Observation {
                binding: self.binding.clone(),
                node,
                run_id,
                report_bytes: report_bytes.len() as u64,
                report_sha256: hash.finish(),
                counts,
                unavailable,
            }
            .encode()?,
        )?;
        Ok(())
    }
    pub(super) fn close_remaining_stage(&self, node: Node) -> CargoResult<()> {
        let closed = self
            .state
            .lock()
            .map_err(|_| error("paired writer state poisoned"))?
            .stages
            .get(&node)
            .context("unknown original stage")?
            .closed;
        if closed {
            Ok(())
        } else {
            self.close_stage(node)
        }
    }
    pub(super) fn finish_node(&self, finished: service::Finished) -> CargoResult<()> {
        let before = self.inputs.validate();
        let bytes = finished.encode(self.plan.consumer.repetitions)?;
        let mut hash = cargo_util::Sha256::new();
        hash.update(&bytes);
        let sequence = {
            let mut state = self
                .state
                .lock()
                .map_err(|_| error("paired graph state poisoned"))?;
            anyhow::ensure!(
                state.registered.contains(&finished.node)
                    && !state.finished.contains(&finished.node)
                    && !state.blocked.contains(&finished.node),
                "paired terminal missing, duplicated or unregistered"
            );
            match finished.result {
                service::Result::Blocked { .. } => {
                    state.blocked.insert(finished.node);
                }
                _ => {
                    state.finished.insert(finished.node);
                }
            }
            let sequence = state.next;
            state.next += 1;
            sequence
        };
        let checkpoint = service::Checkpoint {
            binding: self.binding.clone(),
            sequence,
            node: finished.node,
            outcome_sha256: hash.finish(),
        };
        let until = (Instant::now()
            + Duration::from_nanos(trust_resource_controller::workload::budget::CHECKPOINT_NS))
        .min(self.deadline);
        // Preserve the actual observed terminal even if the subsequent input
        // check withholds continuation. These bytes grant no comparison credit.
        self.send(&bytes)?;
        if let Err(cause) = before {
            self.poisoned();
            return Err(cause);
        }
        let mut control = self
            .control
            .lock()
            .map_err(|_| error("paired continuation owner poisoned"))?;
        control.expect(checkpoint.clone(), until)?;
        self.send(&checkpoint.encode(self.plan.consumer.repetitions)?)?;
        let continued = control.wait(until);
        drop(control);
        let rebound = self.inputs.validate();
        continued?;
        rebound?;
        Ok(())
    }
    pub(super) fn compile_finished(
        &self,
        node: Node,
        succeeded: bool,
        failure: Option<String>,
    ) -> CargoResult<()> {
        self.end_phase()?;
        let lengths = self
            .state
            .lock()
            .map_err(|_| error("paired writer state poisoned"))?
            .stages
            .get(&node)
            .context("unknown original stage")?
            .diagnostic_lengths;
        self.finish_node(service::Finished {
            binding: self.binding.clone(),
            node,
            result: service::Result::Compiled {
                succeeded,
                local_workers_joined: true,
                failure,
            },
            lengths,
            ends: [service::StreamEnd::Unobserved; 2],
            truncated: [false; 2],
        })
    }
    pub(super) fn finish_input(&self) -> CargoResult<()> {
        let mut control = self
            .control
            .lock()
            .map_err(|_| error("paired input owner poisoned"))?;
        let finished = control.finish();
        let observation = control.observation().map_err(reason);
        let published = self.inputs.evidence.publish_service_input(observation);
        finished?;
        published?;
        Ok(())
    }

    pub(super) fn blocked(&self, node: Node, cause: &str) -> CargoResult<()> {
        if self.has_finished(node)? {
            return Ok(());
        }
        let registered = self
            .state
            .lock()
            .map_err(|_| error("paired graph state poisoned"))?
            .registered
            .contains(&node);
        if !registered {
            self.register(node, None)?;
        }
        self.finish_node(service::Finished {
            binding: self.binding.clone(),
            node,
            result: service::Result::Blocked {
                reason: reason(cause),
            },
            lengths: [0; 2],
            ends: [service::StreamEnd::Unobserved; 2],
            truncated: [false; 2],
        })
    }
    fn captured(
        &self,
        node: Node,
        actual: &workload::CapturedAction,
        elapsed: Duration,
        input_failure: Option<String>,
    ) -> CargoResult<()> {
        use cargo_util::{CaptureCompletionCause as Cause, CaptureStreamEnd as End};
        use std::os::unix::process::ExitStatusExt as _;
        use trust_resource_controller::{
            CompletionCause, Outcome,
            accounting::{CpuTimes, Observation, Scope},
        };
        let original = &actual.capture;
        let owner = original.owner_observation;
        let capture = service::Capture {
            started: original.started,
            outcome: original.status.and_then(|status| {
                status
                    .code()
                    .map(Outcome::Exit)
                    .or_else(|| status.signal().map(Outcome::Signal))
            }),
            cause: owner.and_then(|owner| {
                owner.cause.map(|cause| match cause {
                    Cause::Exited => CompletionCause::Exited,
                    Cause::Timeout => CompletionCause::Timeout,
                    Cause::Cancelled => CompletionCause::Cancelled,
                    Cause::ResourceLimit => CompletionCause::ResourceLimit,
                    Cause::HostFault => CompletionCause::HostFault,
                })
            }),
            runtime_ns: owner
                .and_then(|owner| owner.target_runtime)
                .map(|time| u64::try_from(time.as_nanos()))
                .transpose()?,
            retirement_confirmed: owner.is_some_and(|owner| owner.retirement_confirmed),
            accounting: Some(Observation {
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
            }),
            member_attempt: owner.and_then(|owner| owner.native_member_attempt),
            failure: (!actual.native_terminal()).then(|| {
                original
                    .read_error
                    .clone()
                    .or_else(|| original.cleanup_error.clone())
                    .or_else(|| original.failure.as_ref().map(reason))
                    .unwrap_or_else(|| "native action lacks original complete terminal".into())
            }),
        };
        {
            let mut state = self
                .state
                .lock()
                .map_err(|_| error("paired native census state poisoned"))?;
            anyhow::ensure!(
                state
                    .native
                    .insert(
                        node,
                        NativeFact {
                            capture: capture.clone(),
                            complete: actual.native_terminal() && input_failure.is_none()
                        }
                    )
                    .is_none(),
                "paired native action observed twice"
            );
        }
        for (stream, bytes) in [
            (Stream::Stdout, &original.stdout),
            (Stream::Stderr, &original.stderr),
        ] {
            let mut offset = 0;
            for chunk in bytes.chunks(service::MAX_CHUNK_BYTES) {
                self.send(
                    &service::Chunk {
                        binding: self.binding.clone(),
                        node,
                        scope: OutputScope::NativeAction,
                        stream,
                        offset,
                        bytes: chunk.to_vec(),
                    }
                    .encode(self.plan.consumer.repetitions)?,
                )?;
                offset += chunk.len() as u64;
            }
        }
        let end = |end| match end {
            End::Incomplete => service::StreamEnd::Unobserved,
            End::Eof => service::StreamEnd::Eof,
            End::LeaderExitDrained => service::StreamEnd::RetiredDrain,
        };
        self.finish_node(service::Finished {
            binding: self.binding.clone(),
            node,
            result: service::Result::Captured {
                capture,
                elapsed_ns: u64::try_from(elapsed.as_nanos())?,
                input_failure,
            },
            lengths: [original.stdout.len() as u64, original.stderr.len() as u64],
            ends: [end(original.stdout_end), end(original.stderr_end)],
            truncated: [original.stdout_truncated, original.stderr_truncated],
        })
    }
    pub(super) fn counts(&self) -> CargoResult<(u32, u32)> {
        let state = self
            .state
            .lock()
            .map_err(|_| error("paired graph state poisoned"))?;
        Ok((state.finished.len() as u32, state.blocked.len() as u32))
    }
    pub(super) fn validate_census(
        &self,
        entries: &[trust_resource_controller::workload::host::census::Entry],
    ) -> CargoResult<()> {
        use trust_resource_controller::{Status, workload::host::census::SourceKind};
        let state = self
            .state
            .lock()
            .map_err(|_| error("paired native census state poisoned"))?;
        let mut observed = BTreeSet::new();
        for (node, fact) in &state.native {
            let kind = match node {
                Node::Advisory | Node::Strict => SourceKind::Compiler,
                Node::Inventory { .. } => SourceKind::Inventory,
                Node::Sample { .. } => SourceKind::Sample,
                _ => anyhow::bail!("native action used a compiler graph node"),
            };
            let member = fact
                .capture
                .member_attempt
                .context("native capture omitted its original member binding")?;
            let matching = entries
                .iter()
                .filter(|entry| entry.member_attempt == member && entry.kind == kind)
                .collect::<Vec<_>>();
            anyhow::ensure!(
                fact.complete && observed.insert(member) && matching.len() == 1,
                "native action missing, duplicate or incomplete in full original census"
            );
            let entry = matching[0];
            let Status::Finished {
                outcome,
                cause,
                runtime_ns,
            } = entry.terminal
            else {
                anyhow::bail!("native action census lacks original terminal")
            };
            anyhow::ensure!(
                entry.started.is_some()
                    && entry.retired
                    && entry.drained
                    && fact.capture.retirement_confirmed
                    && fact.capture.outcome == Some(outcome)
                    && fact.capture.cause == Some(cause)
                    && fact.capture.runtime_ns == Some(runtime_ns)
                    && fact.capture.accounting == Some(entry.accounting),
                "native action differs from original identity/outcome/owning-wait census"
            );
        }
        anyhow::ensure!(
            entries.iter().all(|entry| entry.retired && entry.drained),
            "full original census contains uncertain retirement/drain"
        );
        anyhow::ensure!(
            entries
                .iter()
                .filter(|entry| matches!(entry.kind, SourceKind::Inventory | SourceKind::Sample))
                .all(|entry| observed.contains(&entry.member_attempt)),
            "full original census contains an unreported native harness action"
        );
        Ok(())
    }
}
struct Writer {
    session: Arc<Session>,
    node: Node,
    stream: Stream,
}
impl io::Write for Writer {
    fn write(&mut self, bytes: &[u8]) -> io::Result<usize> {
        self.session
            .bytes(self.node, OutputScope::Diagnostics, self.stream, bytes)
    }
    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}

pub(super) struct AyObserver(pub(super) Arc<Session>);
fn verification_node(action: qualification::Action) -> Node {
    match action.policy {
        crate::compiler::qualification_command::Policy::Advisory => Node::Advisory,
        crate::compiler::qualification_command::Policy::Strict => Node::Strict,
    }
}
impl qualification::Observer for AyObserver {
    fn compiler_message(&self, id: &str, message: &LogMessage) -> io::Result<()> {
        self.0.report(Node::AyCompile, id, message)
    }
    fn synchronize_compiler_report(&self) -> io::Result<()> {
        self.0.synchronize_report(Node::AyCompile)
    }
    fn compiler_retired(&self, _: &Compilation<'_>, succeeded: bool) -> CargoResult<()> {
        self.0.compile_finished(
            Node::AyCompile,
            succeeded,
            (!succeeded).then(|| "original AY compilation failed".into()),
        )
    }
    fn registered(&self, action: qualification::Action, unit: &UnitIdentity) -> CargoResult<()> {
        self.0.register(verification_node(action), Some(unit))
    }
    fn scheduled(&self, _: qualification::Action) -> CargoResult<()> {
        self.0.begin_phase()
    }
    fn completed(&self, completion: &qualification::Completion) -> CargoResult<()> {
        self.0.end_phase()?;
        self.0.captured(
            verification_node(completion.action),
            &completion.capture,
            completion.elapsed,
            completion.input_failure.clone(),
        )
    }
    fn blocked(&self, action: qualification::Action, cause: &str) -> CargoResult<()> {
        self.0.blocked(verification_node(action), cause)
    }
}
#[derive(Debug)]
pub(super) struct ConsumerObserver(pub(super) Arc<Session>);
impl workload::Observer for ConsumerObserver {
    fn compiler_message(&self, id: &str, message: &LogMessage) -> io::Result<()> {
        self.0.report(Node::ConsumerCompile, id, message)
    }
    fn synchronize_compiler_report(&self) -> io::Result<()> {
        self.0.synchronize_report(Node::ConsumerCompile)
    }
    fn compiler_retired(
        &self,
        _: &Compilation<'_>,
        succeeded: bool,
        outputs: Option<&OwnedOutputs>,
    ) -> CargoResult<()> {
        if let Some(outputs) = outputs {
            outputs.validate()?;
            for (target, file) in outputs.observations() {
                let target = trust_test_execution::workload::TARGETS
                    .iter()
                    .position(|name| *name == target)
                    .context("native target outside complete paired population")?
                    as u32;
                let mut sha256 = [0; 32];
                hex::decode_to_slice(&file.executable.sha256, &mut sha256)?;
                self.0.send(
                    &service::Artifact {
                        binding: self.0.binding.clone(),
                        target,
                        executable: MetadataFile {
                            path: file.executable.path.as_os_str().as_bytes().to_vec(),
                            sha256,
                            bytes: file.executable.bytes,
                            device: file.executable.device,
                            inode: file.executable.inode,
                        },
                    }
                    .encode(&self.0.plan.consumer.output_root)?,
                )?;
            }
        }
        self.0.compile_finished(
            Node::ConsumerCompile,
            succeeded && outputs.is_some(),
            (!(succeeded && outputs.is_some()))
                .then(|| "original consumer compilation/output population incomplete".into()),
        )
    }
    fn action_finished(&self, completion: &TestCompletion) -> CargoResult<()> {
        if let Err(cause) = &completion.result {
            let text = format!(
                "native paired harness validation failed: {}\n",
                reason(cause)
            );
            self.0.bytes(
                Node::ConsumerCompile,
                OutputScope::Diagnostics,
                Stream::Stderr,
                text.as_bytes(),
            )?;
        }
        let node = super::harness_node(
            completion.action.unit.target.name(),
            completion
                .action
                .workload_action
                .context("paired observer received ordinary test")?,
        )?;
        self.0.register(node, None)?;
        match &completion.workload {
            Some(actual) => self.0.captured(node, actual, completion.elapsed, None),
            None => self.0.blocked(
                node,
                &completion
                    .result
                    .as_ref()
                    .err()
                    .map(reason)
                    .unwrap_or_else(|| "native action has no original capture".into()),
            ),
        }
    }
}
