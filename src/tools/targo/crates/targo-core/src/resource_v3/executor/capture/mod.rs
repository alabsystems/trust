//! Structured bytes from the SAME original compiler member and owning helper.
//! This does not confer output eligibility or a verifier verdict.
use super::*;
use cargo_util::{
    CaptureCompletionCause, CaptureOwnerObservation, CaptureStreamEnd, CapturedProcess,
};

const MAX_STREAM: usize = 64 * 1024 * 1024;

struct Stream {
    bytes: Vec<u8>,
    tail: usize,
    truncated: bool,
}
impl Stream {
    fn new() -> Self {
        Self {
            bytes: Vec::new(),
            tail: 0,
            truncated: false,
        }
    }
    fn accept(&mut self, bytes: &[u8], limits: StreamingOutputLimits) -> anyhow::Result<()> {
        let keep = bytes
            .len()
            .min(limits.stream_bytes().saturating_sub(self.bytes.len()));
        self.truncated |= keep != bytes.len();
        if let Err(error) = self.bytes.try_reserve_exact(keep) {
            self.truncated = true;
            anyhow::bail!("could not retain original bounded compiler prefix: {error}");
        }
        self.bytes.extend_from_slice(&bytes[..keep]);
        // Retain the actual bounded binary prefix before judging line limits.
        // The independent durable sink has already seen the ENTIRE read.
        for byte in bytes {
            self.tail = self
                .tail
                .checked_add(1)
                .ok_or_else(|| error("original compiler line length overflow"))?;
            if self.tail > limits.line_bytes() {
                anyhow::bail!("original compiler output exceeds its finite line bound");
            }
            if *byte == b'\n' {
                self.tail = 0;
            }
        }
        anyhow::ensure!(
            !self.truncated,
            "original compiler output exceeds its finite stream bound"
        );
        Ok(())
    }
}

fn accept(
    stream: &mut Stream,
    evidence: Option<&ActionEvidence>,
    is_stdout: bool,
    bytes: &mut Vec<u8>,
    limits: StreamingOutputLimits,
) -> anyhow::Result<()> {
    // Attempt both: IO/quota failure must not discard the received memory prefix.
    let persisted = evidence
        .map(|evidence| {
            if is_stdout {
                evidence.stdout.append(bytes)
            } else {
                evidence.stderr.append(bytes)
            }
        })
        .transpose();
    let retained = stream.accept(bytes, limits);
    bytes.clear();
    persisted
        .map(drop)
        .map_err(anyhow::Error::from)
        .and(retained)
}

fn observation(status: &Status, member: Option<[u8; 16]>) -> Option<CaptureOwnerObservation> {
    let Status::Finished {
        cause, runtime_ns, ..
    } = status
    else {
        return None;
    };
    Some(CaptureOwnerObservation {
        native_member_attempt: member,
        target_runtime: Some(Duration::from_nanos(*runtime_ns)),
        cause: Some(match cause {
            CompletionCause::Exited => CaptureCompletionCause::Exited,
            CompletionCause::Timeout => CaptureCompletionCause::Timeout,
            CompletionCause::Cancelled => CaptureCompletionCause::Cancelled,
            CompletionCause::ResourceLimit => CaptureCompletionCause::ResourceLimit,
            CompletionCause::HostFault => CaptureCompletionCause::HostFault,
        }),
        retirement_confirmed: true,
    })
}

/// Actual native child/helper/input custody, retained by the trusted parent.
/// DATA projections cannot construct this owner or return the worker loan.
pub(crate) struct NativeCapture {
    entered: Instant,
    // Keep the SAME actual child, descriptors and original WorkGuard alive.
    _native: Option<(ProxyChild, WorkGuard)>,
    _attempt_owner: Option<Arc<dyn Send + Sync>>,
    _startup: Arc<Startup>,
    native_status: Option<trust_resource_controller::StatusFrame>,
    accounting: Option<trust_resource_controller::accounting::Observation>,
    stats: ExecStats,
    captured: CapturedProcess,
}
impl NativeCapture {
    /// The original verification context may release its active descriptor
    /// slot only from THIS retained native child/guard and physical streams.
    /// No successful exit projection or caller Boolean can satisfy this.
    pub(crate) fn require_verification_retirement(
        &self,
        startup: &Arc<Startup>,
        loan: &Arc<super::super::workload::bank::PrimaryLoan>,
        owner: &Arc<dyn Send + Sync>,
    ) -> io::Result<()> {
        if !Arc::ptr_eq(startup, &self._startup)
            || !startup.original_root
            || !self.captured.complete()
            || self.captured.read_error.is_some()
            || self.captured.cleanup_error.is_some()
            || self
                ._attempt_owner
                .as_ref()
                .is_none_or(|actual| !Arc::ptr_eq(actual, owner))
        {
            return Err(error(
                "verification has no SAME original complete physical capture",
            ));
        }
        let (child, guard) = self
            ._native
            .as_ref()
            .ok_or_else(|| error("verification has no actual native child/helper owner"))?;
        // This observation is populated only by the SAME Child owner's actual
        // wait. Target terminal DATA and pipe EOF cannot establish helper exit.
        if child
            .helper_observation()
            .is_none_or(|helper| helper.outcome != Some(Outcome::Exit(0)))
        {
            return Err(error(
                "verification owning helper has no successful actual wait",
            ));
        }
        let status = self
            .native_status
            .as_ref()
            .ok_or_else(|| error("verification has no actual native terminal"))?;
        if !guard.compiler_terminal
            || guard._coordinator.is_some()
            || guard
                .workload_loan
                .as_ref()
                .is_none_or(|actual| !Arc::ptr_eq(actual, loan))
            || guard
                ._owner
                .as_ref()
                .is_none_or(|actual| !Arc::ptr_eq(actual, owner))
            || guard.native_binding != Some((status.root_attempt, status.member_attempt))
            || status.root_attempt != startup.query.binding.root_attempt
            || !matches!(
                &status.status,
                Status::Finished { .. } | Status::Refused { .. }
            )
        {
            return Err(error(
                "verification capture differs from actual context/loan/terminal",
            ));
        }
        loan.require_closed_compiler(status.member_attempt)
    }
    /// Capacity accounting for this retained compiler prefix/request. This
    /// observes memory only and establishes no execution or materialization.
    pub(crate) fn retained_bytes(&self) -> Option<usize> {
        let mut bytes = std::mem::size_of::<Self>()
            .checked_add(self.captured.stdout.capacity())?
            .checked_add(self.captured.stderr.capacity())?;
        if let Some((child, guard)) = &self._native {
            bytes = bytes
                .checked_add(child.retained_compiler_bytes()?)?
                .checked_add(std::mem::size_of::<WorkGuard>())?;
            if let Some(command) = &guard.coordinator_request {
                bytes = bytes.checked_add(command.retained_bytes()?)?;
            }
            if let Some(inputs) = &guard.compiler_inputs {
                bytes = bytes.checked_add(inputs.retained_bytes()?)?;
            }
        }
        if let Some(trust_resource_controller::StatusFrame {
            status: Status::Refused { reason } | Status::Unknown { reason, .. },
            ..
        }) = &self.native_status
        {
            bytes = bytes.checked_add(reason.capacity())?;
        }
        Some(bytes)
    }
    /// Only this SAME original capture/WorkGuard can establish this predicate.
    /// Neither StatusFrame, exit zero, file bytes nor a saved digest can call
    /// it in place of the producing member and its completed loan barrier.
    /// The compared command is the coordinator request BEFORE the native
    /// Host command constructor. Its SAME child/guard additionally retains
    /// actual originals and the one-shot whole final-command selection.
    /// Artifact inventory/validity and proof grades remain separate checks.
    pub(crate) fn require_compiler_materialization(
        &self,
        startup: &Arc<Startup>,
        command: &CommandSpec,
        coordinator_attempt: [u8; 16],
        issued: Instant,
    ) -> io::Result<()> {
        if !Arc::ptr_eq(startup, &self._startup)
            || !startup.original_root
            || !self.captured.succeeded()
            || self.entered < issued
        {
            return Err(error(
                "dependency producer lacks same original complete compiler capture",
            ));
        }
        let (_, guard) = self
            ._native
            .as_ref()
            .ok_or_else(|| error("dependency producer has no original native child/guard"))?;
        let loan = guard
            .workload_loan
            .as_ref()
            .ok_or_else(|| error("dependency producer has no original primary loan"))?;
        let bank = startup
            .workload_bank
            .as_ref()
            .ok_or_else(|| error("dependency producer has no original Root bank"))?;
        let status = self
            .native_status
            .as_ref()
            .ok_or_else(|| error("dependency producer lacks actual original terminal"))?;
        if !guard.compiler_terminal
            || !guard.final_selected
            || guard.compiler_inputs.is_none()
            || !loan.belongs_to(bank)
            || loan.completed_compiler() != Some(status.member_attempt)
            || guard.native_binding != Some((status.root_attempt, status.member_attempt))
            || guard.coordinator_request.as_ref() != Some(command)
            || guard
                ._coordinator
                .as_ref()
                .and_then(|primary| primary.coordinator_attempt())
                != Some(coordinator_attempt)
        {
            return Err(error(
                "dependency producer differs from actual completed compiler request/loan",
            ));
        }
        Ok(())
    }

    /// Release dependency read leases only after this SAME actual compiler has
    /// stopped and its helper/pipes have closed. A known failed execution may
    /// release reads without becoming an eligible producer. Missing delivery,
    /// Unknown, incomplete streams or a different command cannot satisfy it.
    pub(crate) fn require_compiler_read_retirement(
        &self,
        startup: &Arc<Startup>,
        command: &CommandSpec,
        coordinator_attempt: [u8; 16],
        issued: Instant,
    ) -> io::Result<()> {
        if !Arc::ptr_eq(startup, &self._startup)
            || !startup.original_root
            || !self.captured.complete()
            || self.captured.read_error.is_some()
            || self.captured.cleanup_error.is_some()
            || self.entered < issued
        {
            return Err(error("dependency reads lack original complete retirement"));
        }
        let (_, guard) = self
            ._native
            .as_ref()
            .ok_or_else(|| error("dependency reads have no command-bound native retirement"))?;
        let loan = guard
            .workload_loan
            .as_ref()
            .ok_or_else(|| error("dependency reads have no original compiler loan"))?;
        let bank = startup
            .workload_bank
            .as_ref()
            .ok_or_else(|| error("dependency reads have no original Root bank"))?;
        let status = self
            .native_status
            .as_ref()
            .ok_or_else(|| error("dependency reads have no original terminal"))?;
        if !guard.compiler_terminal
            || guard.compiler_inputs.is_none()
            || !loan.belongs_to(bank)
            || loan.retired_compiler_attempt() != Some(status.member_attempt)
            || guard.native_binding != Some((status.root_attempt, status.member_attempt))
            || guard.coordinator_request.as_ref() != Some(command)
            || guard
                ._coordinator
                .as_ref()
                .and_then(|primary| primary.coordinator_attempt())
                != Some(coordinator_attempt)
            || !matches!(
                status.status,
                Status::Finished { .. } | Status::Refused { .. }
            )
        {
            return Err(error(
                "dependency read retirement belongs to another native compiler",
            ));
        }
        Ok(())
    }
    pub(crate) fn native_status(&self) -> Option<&trust_resource_controller::StatusFrame> {
        self.native_status.as_ref()
    }
    pub(crate) fn accounting(&self) -> Option<&trust_resource_controller::accounting::Observation> {
        self.accounting.as_ref()
    }
    pub(crate) fn capture(&self) -> &CapturedProcess {
        &self.captured
    }
    /// Synchronous query projection. The actual native owner stays alive
    /// through every check and through construction of the returned result.
    pub(super) fn into_output(mut self) -> io::Result<Output> {
        query_output(&mut self.captured, self.native_status.as_ref())
    }
}

// DATA projection only. Only NativeCapture::into_output supplies this with a
// live original execution owner; tests of these predicates confer no custody.
fn query_output(
    captured: &mut CapturedProcess,
    native_status: Option<&trust_resource_controller::StatusFrame>,
) -> io::Result<Output> {
    if !captured.succeeded() {
        let reason = anyhow::anyhow!(
            "original coordinator query capture is incomplete or failed; native terminal: {:?}; stdout: {:?}; stderr: {:?}; failure: {:#?}; read: {:?}; cleanup: {:?}",
            native_status,
            captured.stdout_end,
            captured.stderr_end,
            captured.failure,
            captured.read_error,
            captured.cleanup_error,
        );
        let failure = match captured.status {
            Some(status) => cargo_util::TargetExecutionError::new(status, reason),
            None => cargo_util::TargetExecutionError::unobserved(reason),
        };
        return Err(io::Error::other(failure));
    }
    Ok(Output {
        status: captured.status.expect("successful capture has status"),
        stdout: std::mem::take(&mut captured.stdout),
        stderr: std::mem::take(&mut captured.stderr),
    })
}

pub(super) fn run(
    executor: &OwnedExecutor,
    process: &ProcessBuilder,
    limits: StreamingOutputLimits,
    measured: bool,
) -> (ExecStats, CapturedProcess) {
    let retained = run_owned(executor, process, limits, measured);
    (retained.stats, retained.captured)
}
pub(super) fn run_owned(
    executor: &OwnedExecutor,
    process: &ProcessBuilder,
    limits: StreamingOutputLimits,
    measured: bool,
) -> NativeCapture {
    let entered = Instant::now();
    let mut native = None;
    let mut native_status = None;
    let mut accounting = None;
    let mut captured = CapturedProcess {
        limits: Some(limits),
        ..CapturedProcess::default()
    };
    let mut stats = ExecStats::default();
    let result = (|| -> anyhow::Result<()> {
        anyhow::ensure!(
            matches!(executor.dispatch, Dispatch::Compile { .. }),
            "compiler capture cannot widen a closed metadata query profile"
        );
        let timeout = limits
            .runtime_timeout()
            .filter(|timeout| !timeout.is_zero())
            .ok_or_else(|| error("original compiler capture needs a finite runtime budget"))?;
        anyhow::ensure!(
            limits.stream_bytes() <= MAX_STREAM,
            "original compiler capture exceeds its durable stream bound"
        );
        let (mut child, mut backing) = executor.start(process, true, Some(timeout), measured)?;
        let (Some(out), Some(err)) = (child.take_stdout(), child.take_stderr()) else {
            super::super::monitor::custodian_lost();
        };
        let evidence = backing.evidence.clone();
        let mut stdout = Stream::new();
        let mut stderr = Stream::new();
        let mut terminal = None;
        let mut cancelled = false;
        let mut failure = None;
        let mut physical_eof = [false; 2];
        let cancellation = process.execution_cancellation();
        let original = executor.startup.workload_process.as_ref();
        let read = cargo_util::read2_controlled_with_eof(
            out,
            err,
            None,
            &mut |is_stdout, bytes, _final_callback| {
                let stream = if is_stdout { &mut stdout } else { &mut stderr };
                // No parser or callback runs before the original durable write.
                // Even a sink error retains the received bounded memory prefix.
                if let Err(error) = accept(stream, evidence.as_deref(), is_stdout, bytes, limits) {
                    failure.get_or_insert(error);
                    Read2Action::Stop
                } else {
                    Read2Action::Continue
                }
            },
            &mut || {
                if !cancelled
                    && (cancellation
                        .as_ref()
                        .is_some_and(|cancel| cancel.load(Ordering::Acquire))
                        || original.is_some_and(|original| {
                            original.cancelled.load(Ordering::Acquire)
                                || Instant::now() >= original.deadline
                        }))
                {
                    child.cancel(Instant::now() + Duration::from_secs(1))?;
                    cancelled = true;
                }
                if terminal.is_none() {
                    if !cancelled {
                        backing.bind_prepared(&executor.startup, &mut child)?;
                    }
                    terminal = child.try_wait(Instant::now() + Duration::from_millis(250));
                }
                Ok(match terminal {
                    Some(Status::Unknown { .. }) => Read2Control::Stop,
                    Some(_) => Read2Control::Drain,
                    None => Read2Control::Continue,
                })
            },
            &mut physical_eof,
        );
        if read.is_err() || failure.is_some() {
            if let Err(error) = child.cancel(Instant::now() + Duration::from_secs(1)) {
                captured.cleanup_error = Some(error.to_string());
            }
        }
        let actual = terminal.unwrap_or_else(|| child.wait());
        captured.started = child.started().is_some();
        captured.stdout = stdout.bytes;
        captured.stderr = stderr.bytes;
        captured.stdout_truncated = stdout.truncated;
        captured.stderr_truncated = stderr.truncated;
        captured.stdout_end = end(physical_eof[0], &read);
        captured.stderr_end = end(physical_eof[1], &read);
        let member = evidence.as_ref().map(|evidence| evidence.member_attempt());
        let helper = match (&executor.startup.workload_evidence, &evidence) {
            (Some(sink), Some(evidence)) => {
                sink.publish_helper(evidence.member_attempt(), child.helper_observation())
            }
            _ => Ok(()),
        };
        // Settle the SAME retired CPU loan independently of every subsequent
        // byte/evidence check. Only the complete success barrier below may
        // record compiler materialization. Unknown still aborts unconditionally.
        let status = backing.settle(&actual);
        if let Some((root_attempt, member_attempt)) = backing.native_binding {
            native_status = Some(trust_resource_controller::StatusFrame {
                root_attempt,
                member_attempt,
                // SAME complete native wait result, before any ExitStatus projection.
                status: actual.clone(),
            });
        }
        accounting = child.accounting();
        captured.owner_observation = observation(&actual, member);
        if measured {
            stats = observed_stats(child.accounting());
        }
        if let Status::Finished { outcome, .. } = &actual {
            captured.status = match outcome {
                Outcome::Exit(code) => code.checked_mul(256).map(ExitStatus::from_raw),
                Outcome::Signal(signal) => Some(ExitStatus::from_raw(*signal)),
            };
        }
        if let Err(error) = &read {
            captured.read_error = Some(error.to_string());
        }
        native = Some((child, backing));
        // Keep every independently observed field even when a later check fails.
        status?;
        helper?;
        read?;
        if let Some(error) = failure {
            return Err(error);
        }
        anyhow::ensure!(
            captured.complete(),
            "original compiler streams did not reach physical EOF"
        );
        // Optional measurement availability is a comparison predicate, not a
        // missing-byte/lifecycle error. Preserve None independently; consumers
        // must require supported accounting before a performance comparison.
        if captured.status.is_none_or(|status| !status.success()) {
            return Err(ProcessError::new(
                "original native compiler failed",
                captured.status,
                None,
            )
            .into());
        }
        anyhow::ensure!(
            captured.succeeded(),
            "original compiler capture has an unresolved start, read or cleanup failure"
        );
        if let Some((_, backing)) = &native {
            backing.materialized(&actual);
        }
        Ok(())
    })();
    captured.failure = result.err();
    NativeCapture {
        entered,
        _native: native,
        _attempt_owner: match &executor.dispatch {
            Dispatch::Compile { owner, .. } => Some(owner.clone()),
            Dispatch::Metadata => None,
        },
        _startup: executor.startup.clone(),
        native_status,
        accounting,
        stats,
        captured,
    }
}

fn end(physical: bool, read: &io::Result<Read2Action>) -> CaptureStreamEnd {
    if physical {
        CaptureStreamEnd::Eof
    } else if matches!(read, Ok(Read2Action::Continue)) {
        CaptureStreamEnd::LeaderExitDrained
    } else {
        CaptureStreamEnd::Incomplete
    }
}

#[cfg(test)]
mod tests;
