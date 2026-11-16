//! First hosted phase: bounded compiler identity queries. Producing commands
//! require a separately supplied CPU/GNU dispatch context; no local fallback.
use super::Startup;
use crate::compiler::candidate_dependencies::{CompilerInputLease, PendingUnit};
use crate::ops::cargo_test::workload::evidence::{self, ActionEvidence, Binding, Kind};
use cargo_util::{
    CpuTimes, ExecStats, ProcessBuilder, ProcessError, ProcessExecutor, Read2Action, Read2Control,
    StreamingOutputLimits,
};
use std::ffi::OsStr;
use std::io;
use std::os::unix::{ffi::OsStrExt, process::ExitStatusExt};
use std::process::{ExitStatus, Output, Stdio};
use std::sync::{
    Arc,
    atomic::{AtomicBool, Ordering},
};
use std::time::{Duration, Instant};
use trust_resource_controller::{
    CommandSpec, CompletionCause, Outcome, Request, Role, Status,
    client::{MemberError, MemberIo, ProxyChild},
};
mod capture;
mod loan;
pub(crate) use loan::ExecutionLoan;
mod stream;
pub(super) fn abort_worker() -> ! {
    loan::abort_worker()
}

struct Borrow(Arc<AtomicBool>);
impl Drop for Borrow {
    fn drop(&mut self) {
        self.0.store(false, Ordering::Release);
    }
}
enum Dispatch {
    Metadata,
    Compile {
        lease: Arc<trust_build_cpu::Lease>,
        jobserver: cargo_util::Jobserver,
        owner: Arc<dyn Send + Sync>,
        workload_loan: Option<Arc<super::workload::bank::PrimaryLoan>>,
        coordinator: Option<(Arc<super::workload::bank::PrimaryLoan>, [u8; 16])>,
    },
}
struct WorkGuard {
    // FIRST: poison unresolved delivery before any implicit-borrow release.
    delivery: loan::ExecutionLoan,
    _borrow: Option<Borrow>,
    _owner: Option<Arc<dyn Send + Sync>>,
    workload_loan: Option<Arc<super::workload::bank::PrimaryLoan>>,
    _coordinator: Option<Arc<super::workload::bank::PrimaryLoan>>,
    native_binding: Option<([u8; 16], [u8; 16])>,
    // SAME complete coordinator request before the Host command constructor.
    // An evidence digest omits private transport values and cannot establish
    // exact request equality or actual Host transformation equivalence.
    coordinator_request: Option<CommandSpec>,
    preparation_deadline: Option<Instant>,
    final_selected: bool,
    compiler_terminal: bool,
    evidence: Option<Arc<ActionEvidence>>,
    workload_inputs: Option<Arc<super::workload::ProcessInputs>>,
    compiler_inputs: Option<Arc<CompilerInputLease>>,
}
impl WorkGuard {
    /// Planning queries use their closed native constructor. Producing units
    /// additionally require the SAME pending originals and live GNU witness.
    /// Both bind the actual full second-image command before native GO.
    fn bind_prepared(&mut self, startup: &Arc<Startup>, child: &mut ProxyChild) -> io::Result<()> {
        if self._coordinator.is_none() || self.final_selected {
            return Ok(());
        }
        let deadline = self
            .preparation_deadline
            .ok_or_else(|| error("coordinator compiler has no original preparation deadline"))?;
        if child.compiler_prepared(deadline)?.is_some() {
            let original = startup
                .workload_process
                .as_ref()
                .ok_or_else(|| error("coordinator query lost original compiler inputs"))?;
            original.sysroot.validate(deadline)?;
            if self.compiler_terminal {
                let inputs = self
                    .compiler_inputs
                    .as_ref()
                    .ok_or_else(|| error("producing compiler has no original pending inputs"))?;
                inputs.validate(deadline)?;
                let budget = startup
                    .descriptor_budget
                    .as_ref()
                    .ok_or_else(|| error("producing compiler lost SAME descriptor budget"))?;
                child.bind_compiler_producing(
                    &startup.query,
                    &original.compiler,
                    budget,
                    deadline,
                )?;
                inputs.validate(deadline)?;
            } else {
                child.bind_compiler_query(&original.compiler, deadline)?;
            }
            self.final_selected = true;
        }
        Ok(())
    }
    /// Positive native retirement settles the CPU loan even when a later
    /// output/evidence check fails. It does not establish materialization.
    fn settle(&mut self, status: &Status) -> io::Result<ExitStatus> {
        match status {
            Status::Finished { .. } | Status::Refused { .. } => {
                if let Some(loan) = &self.workload_loan {
                    if loan.retired().is_err() {
                        abort_worker();
                    }
                }
                self.delivery.settle();
            }
            _ => abort_worker(),
        }
        if let Some(inputs) = &self.workload_inputs {
            if let Err(error) = inputs.sysroot.validate(
                inputs
                    .deadline
                    .min(Instant::now() + Duration::from_secs(20)),
            ) {
                inputs.poisoned.store(true, Ordering::Release);
                return Err(postcheck_failure(status, error));
            }
        }
        if let Some(inputs) = &self.compiler_inputs {
            if let Err(error) = inputs.validate(Instant::now() + Duration::from_secs(20)) {
                return Err(postcheck_failure(status, error));
            }
        }
        finished(status.clone())
    }

    /// Called only after the SAME execution's helper, evidence, reads and
    /// physical pipe EOF have all passed. Query retirement cannot record a
    /// producing compiler, and a native failed terminal remains unsuccessful.
    fn materialized(&self, status: &Status) {
        if self.compiler_terminal {
            if let Some(loan) = &self.workload_loan {
                if loan.record_compiler_terminal(status).is_err() {
                    abort_worker();
                }
            }
        }
    }
}
struct OwnedExecutor {
    startup: Arc<Startup>,
    dispatch: Dispatch,
    deadline: Option<Instant>,
    compiler_inputs: Option<Arc<CompilerInputLease>>,
}
pub(super) fn install(startup: Arc<Startup>) -> io::Result<()> {
    if startup.candidate.is_some() {
        return super::candidate_coordinator::executor::install(startup);
    }
    if startup.workload_bank.is_some() {
        return super::workload::install_queries(startup);
    }
    cargo_util::install_process_executor(Arc::new(OwnedExecutor {
        startup,
        dispatch: Dispatch::Metadata,
        deadline: None,
        compiler_inputs: None,
    }))
}
pub(super) fn compiler(
    startup: Arc<Startup>,
    lease: Arc<trust_build_cpu::Lease>,
    jobserver: cargo_util::Jobserver,
    owner: Arc<dyn Send + Sync>,
    workload_loan: Option<Arc<super::workload::bank::PrimaryLoan>>,
) -> Arc<dyn ProcessExecutor> {
    if startup.candidate.is_some() {
        return super::candidate_coordinator::executor::compiler(startup, owner);
    }
    Arc::new(OwnedExecutor {
        startup,
        deadline: None,
        compiler_inputs: None,
        dispatch: Dispatch::Compile {
            lease,
            jobserver,
            owner,
            workload_loan,
            coordinator: None,
        },
    })
}
pub(crate) struct CoordinatorCompilerExecutor(OwnedExecutor);
pub(crate) use capture::NativeCapture as CoordinatorCompilerCapture;
pub(crate) use capture::NativeCapture as NativeVerificationCapture;
pub(super) fn verification_capture(
    startup: Arc<Startup>,
    lease: Arc<trust_build_cpu::Lease>,
    jobserver: cargo_util::Jobserver,
    owner: Arc<dyn Send + Sync>,
    loan: Arc<super::workload::bank::PrimaryLoan>,
    process: &ProcessBuilder,
    limits: StreamingOutputLimits,
) -> NativeVerificationCapture {
    let executor = OwnedExecutor {
        startup,
        deadline: None,
        compiler_inputs: None,
        dispatch: Dispatch::Compile {
            lease,
            jobserver,
            owner,
            workload_loan: Some(loan),
            coordinator: None,
        },
    };
    capture::run_owned(&executor, process, limits, false)
}
/// Same coordinator and Root bank; each query receives a fresh one-use
/// SECOND original. Reusing an executor for another query is not supported.
pub(crate) struct CoordinatorCompilerFactory {
    startup: Arc<Startup>,
    coordinator: Arc<super::workload::bank::PrimaryLoan>,
    jobserver: cargo_util::Jobserver,
    owner: Arc<dyn Send + Sync>,
    attempt: [u8; 16],
    deadline: Instant,
}
struct CoordinatorTransportOwner {
    _original: Arc<dyn Send + Sync>,
    // Actual helper/description owners close before their reservation returns.
    _descriptors: trust_resource_controller::descriptors::OriginalInputPermit,
}
impl CoordinatorCompilerFactory {
    pub(crate) fn require_coordinator(
        &self,
        startup: &Arc<Startup>,
        primary: &Arc<super::workload::bank::PrimaryLoan>,
        attempt: [u8; 16],
    ) -> io::Result<()> {
        if !Arc::ptr_eq(&self.startup, startup)
            || !Arc::ptr_eq(&self.coordinator, primary)
            || self.attempt != attempt
            || primary.coordinator_attempt() != Some(attempt)
        {
            return Err(error(
                "compiler factory belongs to another actual coordinator",
            ));
        }
        Ok(())
    }
    pub(crate) fn try_executor(&self) -> io::Result<Option<Arc<CoordinatorCompilerExecutor>>> {
        self.try_executor_with_inputs(None)
    }
    fn try_executor_with_inputs(
        &self,
        inputs: Option<Arc<CompilerInputLease>>,
    ) -> io::Result<Option<Arc<CoordinatorCompilerExecutor>>> {
        let bank = self
            .startup
            .workload_bank
            .as_ref()
            .ok_or_else(|| error("coordinator factory lost its Root bank"))?;
        let original = self
            .startup
            .workload_process
            .as_ref()
            .ok_or_else(|| error("coordinator factory lost original Root inputs"))?;
        if !self.startup.original_root
            || self.startup.candidate.is_some()
            || !self.coordinator.belongs_to(bank)
            || self.coordinator.coordinator_attempt() != Some(self.attempt)
            || Instant::now() >= self.deadline.min(original.deadline)
            || original.cancelled.load(Ordering::Acquire)
        {
            return Err(error(
                "original coordinator factory is unavailable, stopped or expired",
            ));
        }
        let budget = self
            .startup
            .descriptor_budget
            .as_ref()
            .ok_or_else(|| error("coordinator factory lost original descriptor budget"))?;
        let descriptors = budget.reserve_member_transport()?;
        Ok(bank
            .try_coordinator_worker(&self.coordinator)?
            .map(|worker| {
                let owner = Arc::new(CoordinatorTransportOwner {
                    _original: self.owner.clone(),
                    _descriptors: descriptors,
                });
                coordinator(
                    self.startup.clone(),
                    self.coordinator.clone(),
                    worker,
                    self.jobserver.clone(),
                    owner,
                    self.attempt,
                    self.deadline.min(original.deadline),
                    inputs,
                )
            }))
    }
    pub(crate) fn executor(&self) -> io::Result<Arc<CoordinatorCompilerExecutor>> {
        self.executor_with_cancellation(&AtomicBool::new(false))
    }
    pub(crate) fn executor_with_cancellation(
        &self,
        cancelled: &AtomicBool,
    ) -> io::Result<Arc<CoordinatorCompilerExecutor>> {
        loop {
            if cancelled.load(Ordering::Acquire) {
                return Err(io::Error::new(
                    io::ErrorKind::Interrupted,
                    "original compiler worker cancelled before admission",
                ));
            }
            if let Some(executor) = self.try_executor()? {
                return Ok(executor);
            }
            std::thread::sleep(Duration::from_millis(5));
        }
    }
    /// Consume only the retained inputs of the actual parent's PendingUnit.
    /// No path, digest, child report, fresh row or raw FD can make this capsule.
    /// This still requires separate actual Host transport/filesystem admission.
    pub(crate) fn prepare_unit(
        &self,
        pending: &PendingUnit,
    ) -> io::Result<Arc<CompilerInputLease>> {
        pending.compiler_inputs(&self.startup, self.attempt, self.deadline)
    }
    /// The parent can issue this FD-only capsule before spawning its worker;
    /// CPU waiting/capture never borrows or retains the parent's PendingUnit.
    pub(crate) fn executor_for_prepared_unit_with_cancellation(
        &self,
        inputs: Arc<CompilerInputLease>,
        cancelled: &AtomicBool,
    ) -> io::Result<Arc<CoordinatorCompilerExecutor>> {
        loop {
            if cancelled.load(Ordering::Acquire) {
                return Err(io::Error::new(
                    io::ErrorKind::Interrupted,
                    "original unit compiler cancelled before admission",
                ));
            }
            inputs.require_factory(&self.startup, self.attempt, self.deadline)?;
            if let Some(executor) = self.try_executor_with_inputs(Some(inputs.clone()))? {
                return Ok(executor);
            }
            std::thread::sleep(Duration::from_millis(5));
        }
    }
}
pub(super) fn coordinator_factory(
    startup: Arc<Startup>,
    coordinator: Arc<super::workload::bank::PrimaryLoan>,
    jobserver: cargo_util::Jobserver,
    owner: Arc<dyn Send + Sync>,
    attempt: [u8; 16],
    deadline: Instant,
) -> Arc<CoordinatorCompilerFactory> {
    Arc::new(CoordinatorCompilerFactory {
        startup,
        coordinator,
        jobserver,
        owner,
        attempt,
        deadline,
    })
}
impl CoordinatorCompilerExecutor {
    pub(crate) fn capture_owned(
        &self,
        process: &ProcessBuilder,
        limits: StreamingOutputLimits,
        measured: bool,
    ) -> CoordinatorCompilerCapture {
        capture::run_owned(&self.0, process, limits, measured)
    }
    fn query_limits(&self, process: &ProcessBuilder) -> io::Result<StreamingOutputLimits> {
        let mut args = Vec::new();
        let mut bytes = 0usize;
        for arg in process.get_args() {
            bytes = bytes
                .checked_add(arg.as_bytes().len())
                .ok_or_else(|| error("coordinator query argument size overflow"))?;
            if args.len() >= 4096 || bytes > 1024 * 1024 {
                return Err(error(
                    "coordinator query arguments exceed their finite bound",
                ));
            }
            args.push(arg.as_bytes().to_vec());
        }
        if !super::candidate_coordinator::executor::is_query(&args) {
            return Err(error(
                "coordinator synchronous execution requires a compiler query",
            ));
        }
        let timeout = self
            .0
            .deadline
            .and_then(|deadline| deadline.checked_duration_since(Instant::now()))
            .filter(|timeout| !timeout.is_zero())
            .ok_or_else(|| error("original coordinator query deadline expired"))?
            .min(Duration::from_secs(8));
        Ok(StreamingOutputLimits::new(65_536, 65_536)
            .with_timeout(timeout)
            .with_child_exit_cleanup())
    }
}
pub(super) fn coordinator(
    startup: Arc<Startup>,
    coordinator: Arc<super::workload::bank::PrimaryLoan>,
    worker: Arc<super::workload::bank::PrimaryLoan>,
    jobserver: cargo_util::Jobserver,
    owner: Arc<dyn Send + Sync>,
    attempt: [u8; 16],
    deadline: Instant,
    compiler_inputs: Option<Arc<CompilerInputLease>>,
) -> Arc<CoordinatorCompilerExecutor> {
    Arc::new(CoordinatorCompilerExecutor(OwnedExecutor {
        startup,
        deadline: Some(deadline),
        compiler_inputs,
        dispatch: Dispatch::Compile {
            lease: worker.lease(),
            jobserver,
            owner,
            workload_loan: Some(worker),
            coordinator: Some((coordinator, attempt)),
        },
    }))
}
fn error(message: impl Into<String>) -> io::Error {
    io::Error::other(message.into())
}
pub(super) fn command_description(command: &CommandSpec) -> [u8; 32] {
    evidence::command_description(command)
}

fn observed_exit(outcome: &Outcome) -> io::Result<ExitStatus> {
    Ok(match outcome {
        Outcome::Exit(code) => ExitStatus::from_raw(
            code.checked_mul(256)
                .ok_or_else(|| error("invalid native exit status"))?,
        ),
        Outcome::Signal(signal) => ExitStatus::from_raw(*signal),
    })
}
fn postcheck_failure(status: &Status, error: io::Error) -> io::Error {
    let failure = anyhow::Error::new(error).context(format!(
        "original compiler input postcheck failed; observed native completion: {status:?}"
    ));
    let failure = match status {
        Status::Finished { outcome, .. } => match observed_exit(outcome) {
            Ok(observed) => cargo_util::TargetExecutionError::new(observed, failure),
            Err(invalid) => cargo_util::TargetExecutionError::unobserved(failure.context(invalid)),
        },
        _ => cargo_util::TargetExecutionError::unobserved(failure),
    };
    io::Error::other(failure)
}

fn finished(status: Status) -> io::Result<ExitStatus> {
    match status {
        Status::Finished { outcome, cause, .. } => {
            let status = observed_exit(&outcome)?;
            if cause == CompletionCause::Exited {
                Ok(status)
            } else {
                Err(io::Error::other(ProcessError::new(
                    &format!("native execution ended: {cause:?}"),
                    Some(status),
                    None,
                )))
            }
        }
        Status::Refused { reason } => Err(io::Error::new(io::ErrorKind::PermissionDenied, reason)),
        // Reusing the implicit unit after unknown delivery would permit the
        // original target and another compiler to execute on the same credit.
        Status::Unknown { .. } => super::monitor::custodian_lost(),
        _ => Err(error("native metadata returned no terminal lifecycle")),
    }
}
impl OwnedExecutor {
    fn start(
        &self,
        process: &ProcessBuilder,
        capture: bool,
        timeout: Option<Duration>,
        accounted: bool,
    ) -> io::Result<(ProxyChild, WorkGuard)> {
        if self.startup.candidate.is_some() {
            return Err(io::Error::new(
                io::ErrorKind::Unsupported,
                "candidate cannot use a local proxy helper",
            ));
        }
        if let Dispatch::Compile {
            lease,
            workload_loan,
            coordinator: Some((coordinator, attempt)),
            ..
        } = &self.dispatch
        {
            let bank = self
                .startup
                .workload_bank
                .as_ref()
                .ok_or_else(|| error("coordinator worker lost original Root bank"))?;
            if !self.startup.original_root
                || !coordinator.belongs_to(bank)
                || workload_loan.as_ref().is_none_or(|worker| {
                    !worker.belongs_to(bank) || !worker.is_coordinator_worker_for(coordinator)
                })
                || coordinator.lease().slot() == lease.slot()
                || coordinator.coordinator_attempt() != Some(*attempt)
            {
                return Err(error(
                    "coordinator worker requires TWO distinct actual original bank primaries",
                ));
            }
        }
        if self
            .startup
            .workload_process
            .as_ref()
            .is_some_and(|inputs| inputs.cancelled.load(Ordering::Acquire))
        {
            return Err(io::Error::new(
                io::ErrorKind::Interrupted,
                "original workload stopped before compiler delivery",
            ));
        }
        match (&self.startup.workload_bank, &self.startup.workload_evidence) {
            (Some(bank), Some(sink))
                if evidence::is_installed(sink)
                    && sink.root_attempt() == self.startup.query.binding.root_attempt
                    && bank.binds(sink.root_attempt(), sink.invocation_sha256()) => {}
            (None, None) => {}
            _ => {
                return Err(error(
                    "workload dispatch lost its original registered evidence owner",
                ));
            }
        }
        match (&self.startup.workload_bank, &self.dispatch) {
            (
                Some(bank),
                Dispatch::Compile {
                    lease,
                    workload_loan: Some(loan),
                    ..
                },
            ) if loan.belongs_to(bank) && Arc::ptr_eq(lease, &loan.lease()) => {}
            (
                None,
                Dispatch::Compile {
                    workload_loan: Some(_),
                    ..
                },
            )
            | (Some(_), _) => {
                return Err(io::Error::new(
                    io::ErrorKind::Unsupported,
                    "workload dispatch requires its distinct original bank/query owner",
                ));
            }
            _ => {}
        }
        if process.has_action_sandbox() || process.get_stdin().is_some() {
            return Err(error(
                "native metadata phase cannot reinterpret confined or stdin work",
            ));
        }
        let command = process.build_command();
        let args: Vec<_> = command.get_args().collect();
        let coordinator_query = matches!(
            &self.dispatch,
            Dispatch::Compile {
                coordinator: Some(_),
                ..
            }
        ) && super::candidate_coordinator::executor::is_query(
            &args
                .iter()
                .map(|arg| arg.as_bytes().to_vec())
                .collect::<Vec<_>>(),
        );
        if matches!(
            &self.dispatch,
            Dispatch::Compile {
                coordinator: Some(_),
                ..
            }
        ) && (coordinator_query == self.compiler_inputs.is_some())
        {
            return Err(io::Error::new(
                io::ErrorKind::Unsupported,
                "coordinator producing dispatch requires SAME pending inputs; queries cannot borrow them",
            ));
        }
        let metadata = matches!(self.dispatch, Dispatch::Metadata) || coordinator_query;
        if matches!(self.dispatch, Dispatch::Metadata)
            && (args.len() != 1
                || !matches!(
                    args[0].to_str(),
                    Some("-vV" | "--version" | "--print=sysroot" | "--print=target-list")
                ))
        {
            return Err(error(
                "native producing phase has no hosted CPU/GNU dispatch context",
            ));
        }
        let (role, delegations, descriptions, mut borrowed) = match &self.dispatch {
            Dispatch::Metadata => {
                if self
                    .startup
                    .implicit_busy
                    .compare_exchange(false, true, Ordering::AcqRel, Ordering::Acquire)
                    .is_err()
                {
                    return Err(io::Error::new(
                        io::ErrorKind::WouldBlock,
                        "native implicit unit is already dispatched",
                    ));
                }
                let borrowed = Borrow(self.startup.implicit_busy.clone());
                let (delegations, descriptions) = super::gnu::cpu_only(&self.startup.implicit)?;
                (
                    if matches!(
                        args[0].to_str(),
                        Some("--print=sysroot" | "--print=target-list")
                    ) {
                        Role::MetadataProbe
                    } else {
                        Role::MetadataVersion
                    },
                    delegations,
                    descriptions,
                    WorkGuard {
                        delivery: loan::ExecutionLoan::new(),
                        _borrow: Some(borrowed),
                        _owner: None,
                        workload_loan: None,
                        _coordinator: None,
                        native_binding: None,
                        coordinator_request: None,
                        preparation_deadline: None,
                        final_selected: false,
                        compiler_terminal: false,
                        evidence: None,
                        workload_inputs: None,
                        compiler_inputs: None,
                    },
                )
            }
            Dispatch::Compile {
                lease,
                jobserver,
                owner,
                workload_loan,
                coordinator,
            } => {
                let (delegations, descriptions) = if coordinator.is_some() {
                    super::gnu::coordinator(lease, (!coordinator_query).then_some(jobserver))?
                } else {
                    super::gnu::shared(lease, jobserver)?
                };
                (
                    match coordinator {
                        Some((_, attempt)) => Role::CoordinatorCompiler(*attempt),
                        None => Role::Compile,
                    },
                    delegations,
                    descriptions,
                    WorkGuard {
                        delivery: loan::ExecutionLoan::new(),
                        _borrow: None,
                        _owner: Some(owner.clone()),
                        workload_loan: workload_loan.clone(),
                        _coordinator: coordinator.as_ref().map(|(loan, _)| loan.clone()),
                        native_binding: None,
                        coordinator_request: None,
                        preparation_deadline: None,
                        final_selected: false,
                        compiler_terminal: !coordinator_query,
                        evidence: None,
                        workload_inputs: None,
                        compiler_inputs: self.compiler_inputs.clone(),
                    },
                )
            }
        };
        let mut environment = process.get_effective_envs()?;
        // Identity queries do not own a GNU pool. Never advertise descriptors
        // that were not transferred as that same shared scheduler.
        if metadata {
            for name in [
                "CARGO_MAKEFLAGS",
                "MAKEFLAGS",
                "MFLAGS",
                "CARGO_JOBSERVER_HANDOFF",
            ] {
                environment.remove(OsStr::new(name));
            }
        }
        let mut request = Request {
            binding: self.startup.query.binding.clone(),
            member_attempt: super::call_attempt(self.startup.query.binding.root_attempt)?,
            role,
            command: CommandSpec {
                program: command.get_program().as_bytes().to_vec(),
                arg0: process.get_arg0().map(|value| value.as_bytes().to_vec()),
                args: args
                    .into_iter()
                    .map(|arg| arg.as_bytes().to_vec())
                    .collect(),
                environment: environment
                    .into_iter()
                    .map(|(key, value)| (key.as_bytes().to_vec(), value.as_bytes().to_vec()))
                    .collect(),
                cwd: command
                    .get_current_dir()
                    .map(ToOwned::to_owned)
                    .map_or_else(std::env::current_dir, Ok)?
                    .as_os_str()
                    .as_bytes()
                    .to_vec(),
            },
            delegations,
            timeout_ns: if metadata {
                Some(
                    timeout
                        .unwrap_or(Duration::from_secs(8))
                        .min(Duration::from_secs(8))
                        .as_nanos() as u64,
                )
            } else {
                timeout
                    .map(|value| {
                        u64::try_from(value.as_nanos())
                            .map_err(|_| error("native compiler timeout is too large"))
                    })
                    .transpose()?
            },
        };
        if let Some(deadline) = self.deadline {
            let remaining = u64::try_from(
                deadline
                    .saturating_duration_since(Instant::now())
                    .as_nanos(),
            )
            .map_err(|_| error("coordinator remaining target budget overflow"))?;
            if remaining == 0 {
                return Err(io::ErrorKind::TimedOut.into());
            }
            request.timeout_ns = Some(request.timeout_ns.unwrap_or(remaining).min(remaining));
        }
        borrowed.native_binding = Some((request.binding.root_attempt, request.member_attempt));
        let io = MemberIo {
            stdin: Stdio::null(),
            stdout: if capture {
                Stdio::piped()
            } else {
                process.status_stdout()
            },
            stderr: if capture {
                Stdio::piped()
            } else {
                process.status_stderr()
            },
            descriptions,
        };
        if let Some(inputs) = &self.startup.workload_process {
            inputs.sysroot.validate_invocation(
                &inputs.compiler,
                &request.command.program,
                request.command.arg0.as_deref(),
                &request.command.args,
                &request.command.environment,
                inputs
                    .deadline
                    .min(Instant::now() + Duration::from_secs(20)),
            )?;
            borrowed.workload_inputs = Some(inputs.clone());
        }
        if let Some(sink) = &self.startup.workload_evidence {
            let action = sink.action(
                Binding {
                    member: request.member_attempt,
                    kind: if coordinator_query {
                        Kind::CompilerQuery
                    } else {
                        Kind::Compile
                    },
                    description_sha256: command_description(&request.command),
                },
                64 * 1024 * 1024,
                64 * 1024 * 1024,
            )?;
            sink.publish_action_command(&action, &request.command)?;
            borrowed.evidence = Some(action);
        }
        if matches!(
            &self.dispatch,
            Dispatch::Compile {
                coordinator: Some(_),
                ..
            }
        ) {
            borrowed.coordinator_request = Some(request.command.clone());
        }
        if let Some(inputs) = &borrowed.compiler_inputs {
            let coordinator = borrowed
                ._coordinator
                .as_ref()
                .and_then(|primary| primary.coordinator_attempt())
                .ok_or_else(|| error("pending compiler inputs lost actual coordinator primary"))?;
            inputs.require_command(
                &self.startup,
                coordinator,
                &request.command,
                self.deadline
                    .ok_or_else(|| error("pending compiler input deadline missing"))?,
            )?;
        }
        if let Some(loan) = &borrowed.workload_loan {
            if coordinator_query {
                loan.begin_query(request.member_attempt)?;
            } else {
                loan.begin_compiler(request.member_attempt)?;
            }
        }
        borrowed.delivery.begin_delivery();
        let delivery_deadline = (Instant::now() + Duration::from_secs(8))
            .min(
                self.startup
                    .candidate
                    .as_ref()
                    .map_or(Instant::now() + Duration::from_secs(8), |original| {
                        original.deadline
                    }),
            )
            .min(
                self.deadline
                    .unwrap_or(Instant::now() + Duration::from_secs(8)),
            );
        if borrowed._coordinator.is_some() {
            borrowed.preparation_deadline = Some(delivery_deadline);
        }
        let scope = if let Some(inputs) = &borrowed.compiler_inputs {
            let coordinator = borrowed
                ._coordinator
                .as_ref()
                .and_then(|primary| primary.coordinator_attempt())
                .ok_or_else(|| error("pending compiler lost its actual coordinator"))?;
            let budget = self
                .startup
                .descriptor_budget
                .as_ref()
                .ok_or_else(|| error("pending compiler lost SAME descriptor budget"))?;
            let dependencies = inputs
                .dependencies()
                .files()
                .iter()
                .map(|file| (file.original().clone(), file.producer_member()))
                .collect();
            // SAFETY: only the SAME live PendingUnit issued this capsule after
            // independent command/retired producer selection. The actual
            // distinct second primary is retained/armed above; source, SDK,
            // Layout and FD originals remain in the WorkGuard through capture.
            match unsafe {
                self.startup.client.attach_compiler_scope(
                    &self.startup.query,
                    coordinator,
                    request.member_attempt,
                    trust_resource_controller::client::CompilerScopeInputs {
                        directory: inputs.output_directory().clone(),
                        dependencies,
                    },
                    budget,
                    delivery_deadline,
                )
            } {
                Ok(original) => Some(original),
                Err(trust_resource_controller::client::CompilerScopeError::BeforeRequest(
                    error,
                )) => {
                    if borrowed
                        .workload_loan
                        .as_ref()
                        .is_none_or(|loan| loan.before_request().is_err())
                    {
                        abort_worker();
                    }
                    borrowed.delivery.settle();
                    return Err(error);
                }
                Err(trust_resource_controller::client::CompilerScopeError::Unknown { .. }) => {
                    super::monitor::custodian_lost()
                }
            }
        } else {
            None
        };
        let delivery = if let Some(scope) = scope {
            self.startup.client.scoped_workload_member_accounted(
                &request,
                io,
                scope,
                delivery_deadline,
            )
        } else if self.startup.workload_bank.is_some() || self.startup.candidate.is_some() {
            // Distinct workload route retains the independently pinned
            // original Store directory in the shipped local helper. Its
            // accounting is explicit for the workload purpose, irrespective
            // of ordinary -Zmem-stats display. Never retry the legacy store.
            self.startup
                .client
                .workload_member_accounted(&request, io, delivery_deadline)
        } else if accounted {
            self.startup.client.member_accounted(
                &request,
                io,
                Instant::now() + Duration::from_secs(8),
            )
        } else {
            self.startup
                .client
                .member(&request, io, Instant::now() + Duration::from_secs(8))
        };
        let child = match delivery {
            Ok(child) => child,
            Err(MemberError::BeforeRequest(error)) => {
                if let Some(loan) = &borrowed.workload_loan {
                    if loan.before_request().is_err() {
                        abort_worker();
                    }
                }
                borrowed.delivery.settle();
                return Err(error);
            }
            Err(MemberError::Unknown { .. }) => super::monitor::custodian_lost(),
        };
        Ok((child, borrowed))
    }
    fn captured(&self, process: &ProcessBuilder, timeout: Option<Duration>) -> io::Result<Output> {
        let (mut child, mut borrowed) = self.start(process, true, timeout, false)?;
        let Some(out) = child.take_stdout() else {
            super::monitor::custodian_lost();
        };
        let Some(err) = child.take_stderr() else {
            super::monitor::custodian_lost();
        };
        let mut stdout = Vec::new();
        let mut stderr = Vec::new();
        let mut terminal = None;
        let mut too_large = false;
        let mut cancelled = false;
        let evidence = borrowed.evidence.clone();
        let mut evidence_error = None;
        let cancellation = process.execution_cancellation();
        let mut physical_eof = [false; 2];
        let read = cargo_util::read2_controlled_with_eof(
            out,
            err,
            None,
            &mut |is_out, data, _| {
                if let Some(evidence) = &evidence {
                    let stream = if is_out {
                        &evidence.stdout
                    } else {
                        &evidence.stderr
                    };
                    if let Err(error) = stream.append(data) {
                        evidence_error = Some(error);
                        return Read2Action::Stop;
                    }
                }
                let target = if is_out { &mut stdout } else { &mut stderr };
                if matches!(self.dispatch, Dispatch::Metadata)
                    && target.len().saturating_add(data.len()) > 65_536
                {
                    too_large = true;
                    return Read2Action::Stop;
                }
                target.extend_from_slice(data);
                data.clear();
                Read2Action::Continue
            },
            &mut || {
                if !cancelled
                    && cancellation
                        .as_ref()
                        .is_some_and(|value| value.load(Ordering::Acquire))
                {
                    child.cancel(Instant::now() + Duration::from_secs(1))?;
                    cancelled = true;
                }
                if terminal.is_none() {
                    if !cancelled {
                        borrowed.bind_prepared(&self.startup, &mut child)?;
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
        if read.is_err() || too_large || evidence_error.is_some() {
            let _ = child.cancel(Instant::now() + Duration::from_secs(1));
        }
        let actual = terminal.unwrap_or_else(|| child.wait());
        let helper = match (&self.startup.workload_evidence, &evidence) {
            (Some(sink), Some(evidence)) => {
                sink.publish_helper(evidence.member_attempt(), child.helper_observation())
            }
            _ => Ok(()),
        };
        let status = borrowed.settle(&actual)?;
        helper?;
        read?;
        if let Some(error) = evidence_error {
            return Err(error);
        }
        if too_large {
            return Err(error("native compiler identity output exceeded its bound"));
        }
        if physical_eof != [true; 2] || child.started().is_none() {
            return Err(error("native compiler output did not reach physical EOF"));
        }
        borrowed.materialized(&actual);
        Ok(Output {
            status,
            stdout,
            stderr,
        })
    }
}
impl ProcessExecutor for OwnedExecutor {
    fn supports_structured_capture(&self) -> bool {
        matches!(self.dispatch, Dispatch::Compile { .. })
    }
    fn capture(
        &self,
        process: &ProcessBuilder,
        limits: StreamingOutputLimits,
        capture_rusage: bool,
    ) -> (ExecStats, cargo_util::CapturedProcess) {
        capture::run(self, process, limits, capture_rusage)
    }
    fn status(&self, process: &ProcessBuilder) -> io::Result<ExitStatus> {
        if self.startup.workload_bank.is_some() {
            return Err(io::Error::new(
                io::ErrorKind::Unsupported,
                "workload compiler requires its bounded captured/streamed owner",
            ));
        }
        let (mut child, mut borrowed) = self.start(process, false, None, false)?;
        let cancel = process.execution_cancellation();
        let mut cancelled = false;
        loop {
            if !cancelled
                && cancel
                    .as_ref()
                    .is_some_and(|flag| flag.load(Ordering::Acquire))
            {
                if child
                    .cancel(Instant::now() + Duration::from_secs(1))
                    .is_err()
                {
                    super::monitor::custodian_lost();
                }
                cancelled = true;
            }
            if !cancelled {
                borrowed.bind_prepared(&self.startup, &mut child)?;
            }
            if let Some(status) = child.try_wait(Instant::now() + Duration::from_millis(250)) {
                // Uncaptured execution can settle custody, but cannot prove
                // complete compiler output/evidence materialization.
                return borrowed.settle(&status);
            }
            std::thread::sleep(Duration::from_millis(10));
        }
    }
    fn output(&self, process: &ProcessBuilder) -> io::Result<Output> {
        self.captured(process, None)
    }
    fn streaming(
        &self,
        process: &ProcessBuilder,
        on_stdout: &mut dyn FnMut(&str) -> anyhow::Result<()>,
        on_stderr: &mut dyn FnMut(&str) -> anyhow::Result<()>,
        capture: bool,
        limits: Option<StreamingOutputLimits>,
        capture_rusage: bool,
    ) -> (ExecStats, anyhow::Result<Output>) {
        let (stats, result) = stream::run(
            self,
            process,
            on_stdout,
            on_stderr,
            capture,
            limits,
            capture_rusage,
        );
        let result = result.and_then(|output| {
            if !output.status.success() {
                return Err(ProcessError::new(
                    "hosted native command failed",
                    Some(output.status),
                    Some(&output),
                )
                .into());
            }
            Ok(output)
        });
        (stats, result)
    }
}

impl ProcessExecutor for CoordinatorCompilerExecutor {
    fn supports_structured_capture(&self) -> bool {
        true
    }
    fn capture(
        &self,
        process: &ProcessBuilder,
        limits: StreamingOutputLimits,
        measured: bool,
    ) -> (ExecStats, cargo_util::CapturedProcess) {
        self.0.capture(process, limits, measured)
    }
    fn status(&self, process: &ProcessBuilder) -> io::Result<ExitStatus> {
        self.output(process).map(|output| output.status)
    }
    fn output(&self, process: &ProcessBuilder) -> io::Result<Output> {
        let limits = self.query_limits(process)?;
        self.capture_owned(process, limits, false).into_output()
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
        self.0
            .streaming(process, stdout, stderr, capture, limits, measured)
    }
}

impl ProcessExecutor for CoordinatorCompilerFactory {
    fn supports_structured_capture(&self) -> bool {
        true
    }
    fn capture(
        &self,
        process: &ProcessBuilder,
        limits: StreamingOutputLimits,
        measured: bool,
    ) -> (ExecStats, cargo_util::CapturedProcess) {
        match self.executor() {
            Ok(executor) => executor.capture(process, limits, measured),
            Err(error) => (
                ExecStats::default(),
                cargo_util::CapturedProcess {
                    failure: Some(error.into()),
                    limits: Some(limits),
                    ..cargo_util::CapturedProcess::default()
                },
            ),
        }
    }
    fn status(&self, process: &ProcessBuilder) -> io::Result<ExitStatus> {
        self.executor()?.status(process)
    }
    fn output(&self, process: &ProcessBuilder) -> io::Result<Output> {
        self.executor()?.output(process)
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
        match self.executor() {
            Ok(executor) => executor.streaming(process, stdout, stderr, capture, limits, measured),
            Err(error) => (ExecStats::default(), Err(error.into())),
        }
    }
}

fn observed_stats(
    observed: Option<trust_resource_controller::accounting::Observation>,
) -> ExecStats {
    let Some(observed) = observed else {
        return ExecStats::default();
    };
    match observed.scope {
        trust_resource_controller::accounting::Scope::ChildAndWaitedDescendantsV1 => {}
    }
    ExecStats {
        peak_rss: observed.peak_rss_bytes,
        cpu_times: observed.cpu_times.map(|cpu| CpuTimes {
            user: Duration::from_nanos(cpu.user_ns),
            system: Duration::from_nanos(cpu.system_ns),
        }),
    }
}

#[cfg(test)]
mod accounting_tests {
    use super::*;
    use trust_resource_controller::accounting::{CpuTimes as ObservedCpu, Observation, Scope};
    #[test]
    fn original_scope_conversion_preserves_unknown_and_observed_zero() {
        assert!(observed_stats(None).cpu_times.is_none());
        let missing = observed_stats(Some(Observation::uncollected()));
        assert!(missing.cpu_times.is_none() && missing.peak_rss.is_none());
        let zero = observed_stats(Some(Observation {
            scope: Scope::ChildAndWaitedDescendantsV1,
            cpu_times: Some(ObservedCpu {
                user_ns: 0,
                system_ns: 0,
            }),
            peak_rss_bytes: Some(0),
        }));
        assert_eq!(
            zero.cpu_times.unwrap(),
            CpuTimes {
                user: Duration::ZERO,
                system: Duration::ZERO
            }
        );
        assert_eq!(zero.peak_rss, Some(0));
    }
    #[test]
    fn failed_target_bookend_retains_observed_exit_without_making_exit_zero_a_cli_success() {
        for (outcome, cause) in [
            (Outcome::Exit(0), CompletionCause::Exited),
            (Outcome::Signal(9), CompletionCause::Cancelled),
        ] {
            let actual = Status::Finished {
                outcome,
                cause,
                runtime_ns: 1,
            };
            let error = postcheck_failure(&actual, io::Error::from_raw_os_error(libc::EIO));
            let failure = error
                .get_ref()
                .unwrap()
                .downcast_ref::<cargo_util::TargetExecutionError>()
                .unwrap();
            assert_eq!(
                failure.observed_status(),
                match &actual {
                    Status::Finished { outcome, .. } => Some(observed_exit(outcome).unwrap()),
                    _ => None,
                }
            );
            assert_eq!(
                failure
                    .completion_error()
                    .downcast_ref::<io::Error>()
                    .unwrap()
                    .raw_os_error(),
                Some(libc::EIO),
                "original native source and errno must survive finalization context"
            );
            assert!(
                failure
                    .completion_error()
                    .to_string()
                    .contains(&format!("{cause:?}"))
            );
            assert!(
                error
                    .get_ref()
                    .unwrap()
                    .downcast_ref::<ProcessError>()
                    .is_none(),
                "observed exit zero is data, not a ProcessError CLI code"
            );
        }
    }

    #[test]
    fn known_cancel_retains_actual_signal_in_process_error() {
        let error = finished(Status::Finished {
            outcome: Outcome::Signal(9),
            cause: CompletionCause::Cancelled,
            runtime_ns: 1,
        })
        .unwrap_err();
        let original = error
            .get_ref()
            .unwrap()
            .downcast_ref::<ProcessError>()
            .unwrap();
        assert_eq!(original.code, None);
        assert!(original.desc.contains("Cancelled") && original.desc.contains("signal: 9"));
    }
}
