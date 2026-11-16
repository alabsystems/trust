//! One control reader for bank continuations and retained foreign phases.
use super::*;
use crate::compiler::build_runner::OriginalOutputLeases;
use crate::compiler::resource_fifo::ForeignGnuEscrow;
use crate::compiler::resource_fifo::PrivateFifo;
use crate::ops::cargo_test::workload::NativeOutput;
use std::collections::BTreeMap;
use std::os::fd::BorrowedFd;
use std::sync::Mutex;
use std::sync::mpsc::{self, Receiver, SyncSender, TryRecvError};
use std::time::{Duration, Instant};
use trust_resource_controller::client::workload::WorkloadControl;
use trust_resource_controller::client::workload::{
    CompletedLocalOperation, LocalAdmission, LocalCompletion, LocalIoScope, RegisteredOutput,
    RetainedOutputLocks, WorkloadControlError,
};
use trust_resource_controller::descriptors::DescriptorBudget;
use trust_resource_controller::workload::host::output;
use trust_resource_controller::workload::host::phase;
use trust_resource_controller::workload::host::produced;
use trust_resource_controller::workload::host::publication as local_wire;
use trust_resource_provenance::program::produced::HeldOutputRoot;

/// Observation of the active original host phase. This value alone cannot
/// admit a produced input: the broker retains its actual GNU escrow and the
/// host retains its original SDK/output/resources/retirement owner.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Phase {
    pub(crate) nonce: Attempt,
    /// The exact accepted Enter key sequence, not a guessed local counter.
    pub(crate) ordinal: u64,
    pub(crate) kind: phase::Kind,
    pub(crate) gnu: trust_resource_controller::FileIdentity,
}

struct Active {
    observation: Phase,
    // None only while SAME adaptive::Owner retains the offered partial
    // escrow in Step::Foreign. Every return requires that original owner.
    escrow: Option<ForeignGnuEscrow>,
    // Retain every actual offered image through positive Leave, including a
    // refused registration. Per-phase images may legitimately become stale
    // when the SAME DAG resumes; original graph-wide locks remain elsewhere.
    outputs: BTreeMap<Attempt, Arc<NativeOutput>>,
}
enum PhaseOffer<'a> {
    Full(ForeignGnuEscrow),
    Current {
        descriptions: [BorrowedFd<'a>; 2],
        backing: trust_resource_controller::FileIdentity,
    },
}
impl PhaseOffer<'_> {
    fn backing(&self) -> trust_resource_controller::FileIdentity {
        match self {
            Self::Full(escrow) => escrow.backing(),
            Self::Current { backing, .. } => *backing,
        }
    }
    fn descriptions(&self) -> [BorrowedFd<'_>; 2] {
        match self {
            Self::Full(escrow) => escrow.descriptors(),
            Self::Current { descriptions, .. } => *descriptions,
        }
    }
}
impl Active {
    fn validate_outputs(&self, deadline: Instant) -> io::Result<()> {
        let mut failure = None;
        for output in self.outputs.values() {
            if let Err(error) = output.validate(deadline) {
                failure.get_or_insert_with(|| io::Error::other(error));
            }
        }
        failure.map_or(Ok(()), Err)
    }
}

/// Nonserialized native input owner and opaque live registry continuation.
/// Sharing this owner never replaces actual host phase/member admission.
pub(crate) struct RegisteredArtifact {
    original: Arc<NativeOutput>,
    registered: RegisteredOutput,
    phase: Phase,
    completed: Mutex<Vec<trust_resource_controller::client::CompletedProducedOperation>>,
}
impl RegisteredArtifact {
    pub(crate) fn original(&self) -> &NativeOutput {
        &self.original
    }
    pub(crate) fn registered(&self) -> &RegisteredOutput {
        &self.registered
    }
    pub(crate) fn phase(&self) -> Phase {
        self.phase
    }
    pub(crate) fn validate(&self, deadline: Instant) -> crate::CargoResult<()> {
        self.original.validate(deadline)
    }
    /// Retain the SAME actual completed operation with its original artifact
    /// and phase. A poisoned data mutex only extends retention and reports a
    /// failure; it cannot authorize another action or any resource return.
    pub(crate) fn retain_completed(
        &self,
        operation: trust_resource_controller::client::CompletedProducedOperation,
    ) -> io::Result<()> {
        let matched = operation.matches_registration(&self.registered)
            && operation.request().gnu == self.phase.gnu;
        match self.completed.lock() {
            Ok(mut owners) => owners.push(operation),
            Err(poisoned) => {
                poisoned.into_inner().push(operation);
                return Err(invalid("completed operation retention was poisoned"));
            }
        }
        if !matched {
            return Err(invalid(
                "completed operation differs from original artifact/phase",
            ));
        }
        Ok(())
    }
}
enum Command {
    TryEnter {
        nonce: Attempt,
        kind: phase::Kind,
        reply: SyncSender<io::Result<Option<Phase>>>,
    },
    BindInitialFifo {
        fifo: Arc<PrivateFifo>,
        escrow: ForeignGnuEscrow,
        reply: SyncSender<io::Result<()>>,
    },
    BindFifo {
        fifo: Arc<PrivateFifo>,
        reply: SyncSender<io::Result<()>>,
    },
    Full {
        reply: SyncSender<io::Result<()>>,
    },
    LocalBegin {
        loan: Arc<LocalLoan>,
        begin: local_wire::Begin,
        selected: Arc<HeldOutputRoot>,
        budget: Arc<DescriptorBudget>,
        reply: SyncSender<io::Result<Option<LocalIoScope>>>,
    },
    LocalComplete {
        loan: Arc<LocalLoan>,
        completion: LocalCompletion,
        reply: SyncSender<io::Result<CompletedLocalOperation>>,
    },
    OutputLocks {
        capsule: Arc<OriginalOutputLeases>,
        root: std::path::PathBuf,
        attempt: Attempt,
        reply: SyncSender<io::Result<RetainedOutputLocks>>,
    },
    SelectOutput {
        retained: Arc<RetainedOutputLocks>,
        attempt: Attempt,
        reply: SyncSender<io::Result<()>>,
    },
    Register {
        phase: Phase,
        original: Arc<NativeOutput>,
        reply: SyncSender<io::Result<RegisteredArtifact>>,
    },
    Enter {
        nonce: Attempt,
        kind: phase::Kind,
        escrow: ForeignGnuEscrow,
        reply: SyncSender<io::Result<Phase>>,
    },
    Leave {
        phase: Phase,
        reply: SyncSender<io::Result<()>>,
    },
    Drained {
        reply: SyncSender<io::Result<bool>>,
    },
    Finish,
}

/// The only reader/writer of the original authenticated 48/49 channel while
/// the graph lives. The queue sends bounded commands to this SAME owner;
/// neither phase coordination nor bank loans clone a second protocol reader.
pub(crate) struct Broker {
    bank: Arc<RootCreditBank>,
    commands: SyncSender<Command>,
    deadline: Instant,
    thread: Option<std::thread::JoinHandle<WorkloadControl>>,
}

impl Broker {
    pub(crate) fn begin_local(
        &mut self,
        coordinator: &Arc<PrimaryLoan>,
        selected: Arc<HeldOutputRoot>,
        budget: Arc<DescriptorBudget>,
        kind: local_wire::Kind,
        producer: Option<Attempt>,
        intents: Vec<local_wire::Intent>,
    ) -> io::Result<Option<CoordinatorLocalOperation>> {
        let Some(loan) = self.bank.try_coordinator_local(coordinator)? else {
            return Ok(None);
        };
        let owner = trust_resource_provenance::process::read_identity(std::process::id())?;
        let birth_kind = if cfg!(target_os = "macos") {
            trust_resource_controller::BirthKind::MacosWallMicroseconds
        } else {
            trust_resource_controller::BirthKind::LinuxStartTicks
        };
        use std::os::unix::ffi::OsStrExt as _;
        let timeout = self
            .deadline
            .saturating_duration_since(Instant::now())
            .as_nanos()
            .min(local_wire::MAX_TIMEOUT_NS as u128) as u64;
        let begin = local_wire::Begin {
            kind,
            cpu: loan.cpu(),
            owner: Identity {
                pid: owner.pid,
                birth: owner.birth,
                birth_kind,
            },
            output_root: selected.path().as_os_str().as_bytes().to_vec(),
            timeout_ns: timeout,
            producer,
            intents,
        };
        begin.validate()?;
        let (reply, read) = mpsc::sync_channel(1);
        self.send(Command::LocalBegin {
            loan: loan.clone(),
            begin,
            selected,
            budget,
            reply,
        })?;
        Ok(self
            .receive(read)?
            .map(|io| CoordinatorLocalOperation { loan, io }))
    }
    pub(crate) fn complete_local(
        &mut self,
        operation: CoordinatorLocalOperation,
    ) -> io::Result<CompletedLocalOperation> {
        if !Arc::ptr_eq(&self.bank, &operation.loan.bank) {
            return Err(invalid("local completion belongs to another original bank"));
        }
        let CoordinatorLocalOperation { loan, io } = operation;
        let completion = io.finish();
        let (reply, read) = mpsc::sync_channel(1);
        self.send(Command::LocalComplete {
            loan,
            completion,
            reply,
        })?;
        self.receive(read)
    }
    pub(crate) fn uses_bank(&self, bank: &RootCreditBank) -> bool {
        std::ptr::eq(self.bank.as_ref(), bank)
    }
    pub(crate) fn start(
        bank: Arc<RootCreditBank>,
        control: WorkloadControl,
        debt: Arc<trust_build_cpu::ExternalDebt>,
        deadline: Instant,
    ) -> io::Result<Self> {
        let (commands, receiver) = mpsc::sync_channel(1);
        let original = bank.clone();
        let thread = std::thread::Builder::new()
            .name("targo-workload-bank".into())
            .spawn(move || run(original, control, receiver, Some(debt), deadline))?;
        Ok(Self {
            bank,
            commands,
            deadline,
            thread: Some(thread),
        })
    }

    pub(crate) fn bind_fifo(&self, fifo: Arc<PrivateFifo>) -> io::Result<()> {
        let (reply, receiver) = mpsc::sync_channel(1);
        self.send(Command::BindFifo { fifo, reply })?;
        self.receive(receiver)
    }
    pub(crate) fn bind_initial_fifo(
        &self,
        fifo: Arc<PrivateFifo>,
        escrow: ForeignGnuEscrow,
    ) -> io::Result<()> {
        let (reply, receiver) = mpsc::sync_channel(1);
        self.send(Command::BindInitialFifo {
            fifo,
            escrow,
            reply,
        })?;
        self.receive(receiver)
    }
    /// Full-width V1 foreign/output handoffs remain full-width. Actual native
    /// replacements and SAME GNU restoration precede this positive return.
    pub(crate) fn ensure_full(&self) -> io::Result<()> {
        let (reply, receiver) = mpsc::sync_channel(1);
        self.send(Command::Full { reply })?;
        self.receive(receiver)
    }

    pub(crate) fn enter(
        &mut self,
        nonce: Attempt,
        kind: phase::Kind,
        escrow: ForeignGnuEscrow,
    ) -> io::Result<Phase> {
        self.ensure_full()?;
        if !self.bank.is_drained()? {
            return Err(invalid("workload phase before original loan drain"));
        }
        let (reply, receiver) = mpsc::sync_channel(1);
        self.send(Command::Enter {
            nonce,
            kind,
            escrow,
            reply,
        })?;
        self.receive(receiver)
    }
    pub(crate) fn try_enter_owned(
        &mut self,
        nonce: Attempt,
        kind: phase::Kind,
    ) -> io::Result<Option<Phase>> {
        let (reply, receiver) = mpsc::sync_channel(1);
        self.send(Command::TryEnter { nonce, kind, reply })?;
        self.receive(receiver)
    }

    /// The actual SDK BuildRunner calls this immediately after Layout prepare,
    /// before queue dispatch. Only its live original capsule can supply the
    /// guard borrows; no request/JSON/path constructs that owner.
    pub(crate) fn retain_output_locks(
        &mut self,
        capsule: Arc<OriginalOutputLeases>,
        root: std::path::PathBuf,
    ) -> crate::CargoResult<RetainedOutputLocks> {
        let initial = self.bank.initial_pending()?;
        if !initial {
            self.ensure_full()?;
        }
        let attempt = super::super::super::call_attempt(self.bank.root_attempt)?;
        let key = output::Key {
            root_attempt: self.bank.root_attempt,
            invocation_sha256: self.bank.invocation_sha256,
            attempt,
        };
        // Preserve typed population/identity refusals before delivery.
        capsule.output_offer(key, &root)?;
        if !self.bank.before_output_handoff()? {
            return Err(invalid("output custody follows a compiler binding").into());
        }
        if initial {
            self.bank.park_initial_output()?;
        } else {
            self.bank.park()?;
        }
        // SAME broker continues positive query returns while we wait. No
        // acquire/new guard/count reconstruction accompanies this transition.
        while !(self.bank.is_drained()? || (initial && self.bank.initial_ready()?.is_some())) {
            check_deadline(self.deadline);
            std::thread::sleep(Duration::from_millis(5));
        }
        let (reply, receiver) = mpsc::sync_channel(1);
        self.send(Command::OutputLocks {
            capsule,
            root,
            attempt,
            reply,
        })?;
        Ok(self.receive(receiver)?)
    }

    pub(crate) fn select_output_locks(
        &mut self,
        retained: Arc<RetainedOutputLocks>,
    ) -> io::Result<()> {
        self.ensure_full()?;
        if !self.bank.native_output_selection()? {
            return Err(invalid(
                "output selection lacks original native-job quiescence",
            ));
        }
        self.bank.park()?;
        while !self.bank.is_drained()? {
            check_deadline(self.deadline);
            std::thread::sleep(Duration::from_millis(5));
        }
        let attempt = super::super::super::call_attempt(self.bank.root_attempt)?;
        let (reply, receiver) = mpsc::sync_channel(1);
        self.send(Command::SelectOutput {
            retained,
            attempt,
            reply,
        })?;
        self.receive(receiver)
    }

    pub(crate) fn leave(&mut self, phase: Phase) -> io::Result<()> {
        let (reply, receiver) = mpsc::sync_channel(1);
        self.send(Command::Leave { phase, reply })?;
        self.receive(receiver)
    }

    pub(crate) fn register_output(
        &mut self,
        phase: Phase,
        original: Arc<NativeOutput>,
    ) -> io::Result<RegisteredArtifact> {
        if !self.bank.current_drained()? {
            return Err(invalid("output registration before original loan drain"));
        }
        let (reply, receiver) = mpsc::sync_channel(1);
        self.send(Command::Register {
            phase,
            original,
            reply,
        })?;
        self.receive(receiver)
    }

    /// The SAME parked parent bank, original accepted phase and held artifact
    /// select the primary. This never resumes the compile queue or acquires a
    /// replacement native unit. Host admission still proves the live grant.
    pub(crate) fn coordinator_primary(
        &self,
        artifact: &Arc<RegisteredArtifact>,
    ) -> io::Result<Option<Arc<PrimaryLoan>>> {
        artifact.validate(self.deadline).map_err(io::Error::other)?;
        if artifact.phase().kind != phase::Kind::Coordinator {
            return Err(invalid(
                "coordinator requires its distinct accepted original phase",
            ));
        }
        self.bank.try_coordinator(artifact)
    }

    /// Positive command settlement is separate from actual root exit/drain.
    /// The outer original process owner must still await those facts.
    pub(crate) fn drained(&mut self) -> io::Result<()> {
        loop {
            check_deadline(self.deadline);
            let (reply, receiver) = mpsc::sync_channel(1);
            self.send(Command::Drained { reply })?;
            if self.receive(receiver)? {
                return Ok(());
            }
            std::thread::sleep(
                Duration::from_millis(5)
                    .min(self.deadline.saturating_duration_since(Instant::now())),
            );
        }
    }

    fn send(&self, command: Command) -> io::Result<()> {
        if Instant::now() >= self.deadline {
            return Err(io::ErrorKind::TimedOut.into());
        }
        // Only &mut coordinator operations can send. A full/disconnected
        // channel cannot start another owner or extend the original deadline.
        self.commands
            .try_send(command)
            .map_err(|_| invalid("original workload broker unavailable"))
    }

    fn receive<T>(&self, receiver: Receiver<io::Result<T>>) -> io::Result<T> {
        match receiver.recv_timeout(self.deadline.saturating_duration_since(Instant::now())) {
            Ok(result) => result,
            // Delivery may already have happened. Never return tokens or
            // catch-and-resume while the actual host result is uncertain.
            Err(_) => super::super::abort_unknown(),
        }
    }

    /// Return the SAME connection for the immutable final census. Host
    /// Drained is mandatory; it does not substitute for outer target retirement.
    pub(crate) fn finish(mut self) -> io::Result<WorkloadControl> {
        if !self.bank.current_drained()? {
            return Err(invalid(
                "workload control stopped before original loan drain",
            ));
        }
        self.send(Command::Finish)?;
        match self.thread.take().expect("original workload broker").join() {
            Ok(control) => Ok(control),
            Err(_) => super::super::abort_unknown(),
        }
    }
}

impl Drop for Broker {
    fn drop(&mut self) {
        if self.thread.is_some() {
            super::super::abort_unknown();
        }
    }
}

// Kept generic only so real original GNU guards and the single-owner state
// machine can be exercised without forging an authenticated production host.
trait Control {
    fn original_output_ready(&self) -> bool {
        false
    }
    fn prepare_initial(
        &mut self,
        _implicit: trust_resource_controller::workload::host::partial::CpuUnit,
        _gnu: [BorrowedFd<'_>; 2],
        _bank: &mut dyn trust_resource_controller::client::workload::PartialBank,
        _deadline: Instant,
    ) -> io::Result<Option<trust_resource_controller::client::workload::PreparedPartialPhase>> {
        Err(io::ErrorKind::Unsupported.into())
    }
    fn phase_sequence(&self) -> Option<u64> {
        None
    }
    fn partial_absent(&self) -> bool {
        true
    }
    fn prepare_partial(
        &mut self,
        _phase: Attempt,
        _implicit: trust_resource_controller::workload::host::partial::CpuUnit,
        _gnu: [BorrowedFd<'_>; 2],
        _bank: &mut dyn trust_resource_controller::client::workload::PartialBank,
        _deadline: Instant,
    ) -> io::Result<Option<trust_resource_controller::client::workload::PreparedPartialPhase>> {
        Ok(None)
    }
    unsafe fn release_partial(
        &mut self,
        _phase: Attempt,
        _bank: &mut dyn trust_resource_controller::client::workload::PartialBank,
        _deadline: Instant,
    ) -> io::Result<bool> {
        Err(io::ErrorKind::Unsupported.into())
    }
    fn restore_partial(
        &mut self,
        _phase: Attempt,
        _bank: &mut dyn trust_resource_controller::client::workload::PartialBank,
        _deadline: Instant,
    ) -> io::Result<Option<trust_resource_controller::client::workload::AuthenticatedPartialFunding>>
    {
        Err(io::ErrorKind::Unsupported.into())
    }
    unsafe fn commit_partial(
        &mut self,
        _phase: Attempt,
        _bank: &mut dyn trust_resource_controller::client::workload::PartialBank,
        _deadline: Instant,
    ) -> io::Result<trust_resource_controller::client::workload::CommittedPartialPhase> {
        Err(io::ErrorKind::Unsupported.into())
    }
    fn select_output(
        &mut self,
        _retained: &RetainedOutputLocks,
        _attempt: Attempt,
        _deadline: Instant,
    ) -> Result<(), WorkloadControlError> {
        Err(WorkloadControlError::BeforeRequest(
            io::ErrorKind::Unsupported.into(),
        ))
    }
    fn local_sequence(&self) -> io::Result<u64> {
        Err(io::ErrorKind::Unsupported.into())
    }
    fn begin_local(
        &mut self,
        _request: local_wire::Request,
        _selected: Arc<HeldOutputRoot>,
        _budget: Arc<DescriptorBudget>,
        _cancel: Arc<AtomicBool>,
        _deadline: Instant,
    ) -> Result<LocalAdmission, WorkloadControlError> {
        Err(WorkloadControlError::BeforeRequest(
            io::ErrorKind::Unsupported.into(),
        ))
    }
    fn complete_local(
        &mut self,
        _completion: LocalCompletion,
        _deadline: Instant,
    ) -> Result<CompletedLocalOperation, WorkloadControlError> {
        Err(WorkloadControlError::BeforeRequest(
            io::ErrorKind::Unsupported.into(),
        ))
    }
    /// Called only with actual original close-only capsule borrows from run.
    unsafe fn output(
        &mut self,
        request: &output::Request,
        descriptions: &[BorrowedFd<'_>],
        deadline: Instant,
    ) -> Result<RetainedOutputLocks, WorkloadControlError>;
    unsafe fn register(
        &mut self,
        request: &produced::Registration,
        executable: BorrowedFd<'_>,
        deadline: Instant,
    ) -> Result<RegisteredOutput, WorkloadControlError>;
    fn poll_bank(
        &mut self,
        bank: &RootCreditBank,
        deadline: Instant,
    ) -> io::Result<Option<bank::Request>>;
    fn reply_bank(&mut self, answer: &Answer, deadline: Instant) -> io::Result<()>;
    fn phase(
        &mut self,
        request: &phase::Request,
        gnu: Option<[BorrowedFd<'_>; 2]>,
        deadline: Instant,
    ) -> io::Result<phase::Reply>;
}
impl Control for WorkloadControl {
    fn original_output_ready(&self) -> bool {
        self.has_original_output_locks()
    }
    fn prepare_initial(
        &mut self,
        implicit: trust_resource_controller::workload::host::partial::CpuUnit,
        gnu: [BorrowedFd<'_>; 2],
        bank: &mut dyn trust_resource_controller::client::workload::PartialBank,
        deadline: Instant,
    ) -> io::Result<Option<trust_resource_controller::client::workload::PreparedPartialPhase>> {
        self.prepare_initial_phase(implicit, gnu, bank, deadline)
    }
    fn phase_sequence(&self) -> Option<u64> {
        Some(WorkloadControl::phase_sequence(self))
    }
    fn partial_absent(&self) -> bool {
        self.partial_support_absent()
    }
    fn prepare_partial(
        &mut self,
        phase: Attempt,
        implicit: trust_resource_controller::workload::host::partial::CpuUnit,
        gnu: [BorrowedFd<'_>; 2],
        bank: &mut dyn trust_resource_controller::client::workload::PartialBank,
        deadline: Instant,
    ) -> io::Result<Option<trust_resource_controller::client::workload::PreparedPartialPhase>> {
        self.prepare_partial_phase(phase, implicit, gnu, bank, deadline)
    }
    unsafe fn release_partial(
        &mut self,
        phase: Attempt,
        bank: &mut dyn trust_resource_controller::client::workload::PartialBank,
        deadline: Instant,
    ) -> io::Result<bool> {
        // SAFETY: the sole adaptive owner retains RootPartialPhase, with its
        // actual supplementary FDs closed and SAME offered GNU escrow held.
        unsafe { self.release_after_sdk_park(phase, bank, deadline) }
    }
    fn restore_partial(
        &mut self,
        phase: Attempt,
        bank: &mut dyn trust_resource_controller::client::workload::PartialBank,
        deadline: Instant,
    ) -> io::Result<Option<trust_resource_controller::client::workload::AuthenticatedPartialFunding>>
    {
        self.restore_partial_phase(phase, bank, deadline)
    }
    unsafe fn commit_partial(
        &mut self,
        phase: Attempt,
        bank: &mut dyn trust_resource_controller::client::workload::PartialBank,
        deadline: Instant,
    ) -> io::Result<trust_resource_controller::client::workload::CommittedPartialPhase> {
        // SAFETY: adaptive::Owner installed actual adopted same-phase native
        // guards in the SAME bank before this callback; GNU remains escrowed.
        unsafe { self.commit_after_funding_install(phase, bank, deadline) }
    }
    fn select_output(
        &mut self,
        retained: &RetainedOutputLocks,
        attempt: Attempt,
        deadline: Instant,
    ) -> Result<(), WorkloadControlError> {
        self.select_output_locks(retained, attempt, deadline)
    }
    fn local_sequence(&self) -> io::Result<u64> {
        self.next_local_sequence()
    }
    fn begin_local(
        &mut self,
        request: local_wire::Request,
        selected: Arc<HeldOutputRoot>,
        budget: Arc<DescriptorBudget>,
        cancel: Arc<AtomicBool>,
        deadline: Instant,
    ) -> Result<LocalAdmission, WorkloadControlError> {
        self.begin_local(request, selected, budget, cancel, deadline)
    }
    fn complete_local(
        &mut self,
        completion: LocalCompletion,
        deadline: Instant,
    ) -> Result<CompletedLocalOperation, WorkloadControlError> {
        self.complete_local(completion, deadline)
    }
    unsafe fn output(
        &mut self,
        request: &output::Request,
        descriptions: &[BorrowedFd<'_>],
        deadline: Instant,
    ) -> Result<RetainedOutputLocks, WorkloadControlError> {
        // SAFETY: the sole run owner validated the actual nonClone original
        // capsule, parked/drained its bank before first compiler binding and
        // retains that capsule through this exact transfer.
        unsafe { self.retain_output_locks(request, descriptions, deadline) }
    }
    unsafe fn register(
        &mut self,
        request: &produced::Registration,
        executable: BorrowedFd<'_>,
        deadline: Instant,
    ) -> Result<RegisteredOutput, WorkloadControlError> {
        // SAFETY: Phases::register retains the SAME actual NativeOutput,
        // including original SDK/output/Layout owners and exact current unit
        // materialization. The original bank is parked/drained and the SAME
        // accepted phase/escrow remains live through positive Leave.
        unsafe { self.register_output(request, executable, deadline) }
    }
    fn poll_bank(
        &mut self,
        bank: &RootCreditBank,
        deadline: Instant,
    ) -> io::Result<Option<bank::Request>> {
        adaptive::poll_owned_bank(bank, self, deadline)
    }
    fn reply_bank(&mut self, answer: &Answer, deadline: Instant) -> io::Result<()> {
        self.reply_bank(
            &answer.reply,
            answer.original.as_ref().map(|lease| lease.as_fd()),
            deadline,
        )
    }
    fn phase(
        &mut self,
        request: &phase::Request,
        gnu: Option<[BorrowedFd<'_>; 2]>,
        deadline: Instant,
    ) -> io::Result<phase::Reply> {
        if self.uses_current_share_phases() {
            let reply = self.request_current_share_phase(
                &phase::CurrentShareRequest {
                    key: request.key,
                    operation: request.operation,
                },
                gnu,
                deadline,
            )?;
            Ok(phase::Reply {
                key: reply.key,
                decision: reply.decision,
            })
        } else {
            self.request_phase(request, gnu, deadline)
        }
    }
}

struct Phases {
    sequence: u64,
    active: Option<Active>,
    drained: bool,
}
impl Phases {
    fn request(
        &mut self,
        bank: &RootCreditBank,
        operation: phase::Operation,
    ) -> io::Result<phase::Request> {
        let sequence = self
            .sequence
            .checked_add(1)
            .ok_or_else(|| invalid("workload phase sequence overflow"))?;
        let request = phase::Request {
            key: bank::Key {
                root_attempt: bank.root_attempt,
                invocation_sha256: bank.invocation_sha256,
                sequence,
            },
            operation,
        };
        request.encode()?;
        self.sequence = sequence;
        Ok(request)
    }

    fn enter<C: Control>(
        &mut self,
        bank: &RootCreditBank,
        control: &mut C,
        nonce: Attempt,
        kind: phase::Kind,
        escrow: ForeignGnuEscrow,
        deadline: Instant,
    ) -> io::Result<Phase> {
        if escrow.ceiling() > bank.ceiling as usize || escrow.ceiling() > bank.original_width {
            return Err(invalid("foreign GNU exceeds original ceiling"));
        }
        self.enter_owned(
            bank,
            control,
            nonce,
            kind,
            PhaseOffer::Full(escrow),
            deadline,
        )
    }
    fn enter_current<C: Control>(
        &mut self,
        bank: &RootCreditBank,
        control: &mut C,
        nonce: Attempt,
        kind: phase::Kind,
        original: &adaptive::Owner,
        deadline: Instant,
    ) -> io::Result<Phase> {
        self.enter_owned(
            bank,
            control,
            nonce,
            kind,
            PhaseOffer::Current {
                descriptions: original.current_descriptors()?,
                backing: original.current_backing()?,
            },
            deadline,
        )
    }
    fn enter_owned<C: Control>(
        &mut self,
        bank: &RootCreditBank,
        control: &mut C,
        nonce: Attempt,
        kind: phase::Kind,
        mut offer: PhaseOffer<'_>,
        deadline: Instant,
    ) -> io::Result<Phase> {
        if self.drained
            || self.active.is_some()
            || !match offer {
                PhaseOffer::Full(_) => bank.is_drained()?,
                PhaseOffer::Current { .. } => bank.current_drained()?,
            }
        {
            return Err(invalid(
                "workload Enter outside parked original graph or original GNU width",
            ));
        }
        // Validate local input BEFORE offer so a malformed coordinator request
        // cannot turn a known before-delivery refusal into fabricated custody.
        let backing = offer.backing();
        let mut request = self.request(
            bank,
            phase::Operation::Enter {
                phase: nonce,
                kind,
                gnu: backing,
            },
        )?;
        if let PhaseOffer::Full(escrow) = &mut offer {
            escrow.offered();
        }
        loop {
            check_deadline(deadline);
            let response = control
                .phase(&request, Some(offer.descriptions()), deadline)
                .unwrap_or_else(|_| super::super::abort_unknown());
            if phase::Reply::decode(
                &response
                    .encode()
                    .unwrap_or_else(|_| super::super::abort_unknown()),
                &request,
            )
            .is_err()
            {
                super::super::abort_unknown();
            }
            match response.decision {
                phase::Decision::Busy => {
                    std::thread::sleep(
                        Duration::from_millis(5)
                            .min(deadline.saturating_duration_since(Instant::now())),
                    );
                    request = self
                        .request(bank, request.operation)
                        .unwrap_or_else(|_| super::super::abort_unknown());
                }
                phase::Decision::Refused { reason } => {
                    if let PhaseOffer::Full(escrow) = offer {
                        escrow.settled();
                    }
                    return Err(io::Error::new(io::ErrorKind::PermissionDenied, reason));
                }
                phase::Decision::Ready {
                    phase,
                    reserved_domain,
                    gnu,
                } if response.key == request.key
                    && phase == nonce
                    && gnu == backing
                    && reserved_domain as usize == bank.funded_width()? =>
                {
                    let observation = Phase {
                        nonce,
                        ordinal: request.key.sequence,
                        kind,
                        gnu: backing,
                    };
                    self.active = Some(Active {
                        observation,
                        escrow: match offer {
                            PhaseOffer::Full(escrow) => Some(escrow),
                            PhaseOffer::Current { .. } => None,
                        },
                        outputs: BTreeMap::new(),
                    });
                    return Ok(observation);
                }
                _ => super::super::abort_unknown(),
            }
        }
    }

    fn register<C: Control>(
        &mut self,
        bank: &RootCreditBank,
        control: &mut C,
        phase: Phase,
        original: Arc<NativeOutput>,
        deadline: Instant,
    ) -> io::Result<RegisteredArtifact> {
        if self.drained || !bank.current_drained()? {
            return Err(invalid("native registration outside original parked phase"));
        }
        let active = self
            .active
            .as_mut()
            .filter(|active| active.observation == phase)
            .ok_or_else(|| invalid("native registration differs from actual accepted phase"))?;
        // The live BuildRunner supplies one actual compiled script or the
        // exact two final harness UnitOutputs. Data/path decoding constructs
        // neither materialization nor this original input owner.
        let maximum = match phase.kind {
            phase::Kind::BuildScript => 1,
            phase::Kind::Harnesses => 2,
            phase::Kind::Coordinator => 1,
        };
        if active.outputs.len() >= maximum {
            return Err(invalid(
                "native registration exceeds its original phase population",
            ));
        }
        let output = super::super::super::call_attempt(bank.root_attempt)?;
        let key = produced::Key {
            root_attempt: bank.root_attempt,
            invocation_sha256: bank.invocation_sha256,
            phase: phase.nonce,
            ordinal: phase.ordinal,
            output,
        };
        let (request, descriptor) = original
            .registration(key, deadline)
            .map_err(io::Error::other)?;
        if active.outputs.insert(output, original.clone()).is_some() {
            return Err(invalid("native output registration nonce reused"));
        }
        // Retain the owner BEFORE delivery. Neither a known refusal nor a
        // later input drift releases an image offered to the original host.
        // SAFETY: see WorkloadControl adapter above. Cold provenance comes
        // from this actual Unit's successful original compiler, never None.
        let result = unsafe { control.register(&request, descriptor, deadline) };
        if matches!(result, Err(WorkloadControlError::Unknown(_))) {
            super::super::abort_unknown();
        }
        original.validate(deadline).map_err(io::Error::other)?;
        match result {
            Ok(registered) => {
                if registered.registration() != &request {
                    super::super::abort_unknown();
                }
                Ok(RegisteredArtifact {
                    original,
                    registered,
                    phase,
                    completed: Mutex::new(Vec::new()),
                })
            }
            Err(WorkloadControlError::BeforeRequest(error)) => Err(error),
            Err(WorkloadControlError::Refused { reason }) => {
                Err(io::Error::new(io::ErrorKind::PermissionDenied, reason))
            }
            Err(WorkloadControlError::Unknown(_)) => unreachable!("Unknown already aborts"),
        }
    }

    fn leave<C: Control>(
        &mut self,
        bank: &RootCreditBank,
        control: &mut C,
        observed: Phase,
        deadline: Instant,
    ) -> io::Result<()> {
        if self.drained
            || !bank.current_drained()?
            || self.active.as_ref().map(|active| active.observation) != Some(observed)
        {
            return Err(invalid("workload Leave differs from original active phase"));
        }
        // Drift disqualifies the attempt but cannot skip actual host cleanup.
        // Recheck every retained image and preserve its error through Left.
        let mut input_error = self
            .active
            .as_ref()
            .expect("checked original phase")
            .validate_outputs(deadline)
            .err();
        loop {
            check_deadline(deadline);
            let request = self.request(
                bank,
                phase::Operation::Leave {
                    phase: observed.nonce,
                },
            )?;
            let response = control
                .phase(&request, None, deadline)
                .unwrap_or_else(|_| super::super::abort_unknown());
            if phase::Reply::decode(
                &response
                    .encode()
                    .unwrap_or_else(|_| super::super::abort_unknown()),
                &request,
            )
            .is_err()
            {
                super::super::abort_unknown();
            }
            match response.decision {
                phase::Decision::Busy => std::thread::sleep(Duration::from_millis(5)),
                phase::Decision::Left { phase }
                    if response.key == request.key && phase == observed.nonce =>
                {
                    let after = self
                        .active
                        .as_ref()
                        .expect("checked original phase")
                        .validate_outputs(deadline)
                        .err();
                    input_error = input_error.or(after);
                    let escrow = self.active.take().expect("checked original phase").escrow;
                    let current = escrow.is_none();
                    if let Some(escrow) = escrow {
                        escrow.settled();
                    }
                    // Tokens return before local compile dispatch can resume.
                    if let Some(error) = input_error {
                        // Positive retirement returns the original GNU bytes;
                        // a failed graph remains parked and cannot dispatch.
                        return Err(error);
                    }
                    if !current {
                        bank.resume()?;
                    }
                    return Ok(());
                }
                // A refused Leave does not establish retirement. Retain the
                // offered escrow and preserve unconditional Unknown abort.
                _ => super::super::abort_unknown(),
            }
        }
    }

    fn drain<C: Control>(
        &mut self,
        bank: &RootCreditBank,
        control: &mut C,
        deadline: Instant,
    ) -> io::Result<()> {
        if self.drained || self.active.is_some() || !bank.current_drained()? {
            return Err(invalid(
                "workload Drained before original phase/loan closure",
            ));
        }
        loop {
            check_deadline(deadline);
            let request = self.request(bank, phase::Operation::Drained)?;
            let response = control
                .phase(&request, None, deadline)
                .unwrap_or_else(|_| super::super::abort_unknown());
            if phase::Reply::decode(
                &response
                    .encode()
                    .unwrap_or_else(|_| super::super::abort_unknown()),
                &request,
            )
            .is_err()
            {
                super::super::abort_unknown();
            }
            match response.decision {
                phase::Decision::Busy => std::thread::sleep(Duration::from_millis(5)),
                phase::Decision::Drained if response.key == request.key => {
                    self.drained = true;
                    return Ok(());
                }
                _ => super::super::abort_unknown(),
            }
        }
    }
}

fn check_deadline(deadline: Instant) {
    if Instant::now() >= deadline {
        super::super::abort_unknown();
    }
}

fn run<C: Control>(
    bank: Arc<RootCreditBank>,
    mut control: C,
    receiver: Receiver<Command>,
    debt: Option<Arc<trust_build_cpu::ExternalDebt>>,
    deadline: Instant,
) -> C {
    struct AbortOnDrop(bool);
    impl Drop for AbortOnDrop {
        fn drop(&mut self) {
            if self.0 {
                super::super::abort_unknown();
            }
        }
    }
    let mut unresolved = AbortOnDrop(true);
    let mut phases = Phases {
        sequence: 0,
        active: None,
        drained: false,
    };
    let mut adaptive = adaptive::Owner::new(debt);
    loop {
        check_deadline(deadline);
        match receiver.try_recv() {
            Ok(Command::BindInitialFifo {
                fifo,
                escrow,
                reply,
            }) => {
                let result = adaptive.bind_initial(&bank, fifo, escrow);
                let failed = result.is_err();
                let _ = reply.send(result);
                if failed {
                    super::super::abort_unknown();
                }
            }
            Ok(Command::BindFifo { fifo, reply }) => {
                let result = adaptive.bind(&bank, fifo);
                if reply.send(result).is_err() {
                    super::super::abort_unknown();
                }
            }
            Ok(Command::Full { reply }) => adaptive.require_full(reply),
            Ok(Command::LocalBegin {
                loan,
                begin,
                selected,
                budget,
                reply,
            }) => {
                let result = (|| -> io::Result<_> {
                    let request = local_wire::Request {
                        key: loan.key(control.local_sequence()?)?,
                        operation: local_wire::Operation::Begin(begin),
                    };
                    request.encode()?;
                    loan.offered(&request)?;
                    match control.begin_local(
                        request,
                        selected,
                        budget,
                        loan.cancellation(),
                        deadline,
                    ) {
                        Ok(LocalAdmission::Ready(scope)) => {
                            loan.admitted(&scope)
                                .unwrap_or_else(|_| super::super::abort_unknown());
                            Ok(Some(scope))
                        }
                        Ok(LocalAdmission::NotAdmitted(receipt)) => {
                            loan.not_admitted(&receipt)
                                .unwrap_or_else(|_| super::super::abort_unknown());
                            if receipt.busy() {
                                Ok(None)
                            } else {
                                Err(io::Error::other(receipt.reason().to_owned()))
                            }
                        }
                        Err(_) => super::super::abort_unknown(),
                    }
                })();
                if reply.send(result).is_err() {
                    super::super::abort_unknown()
                }
            }
            Ok(Command::LocalComplete {
                loan,
                completion,
                reply,
            }) => {
                let completed = control
                    .complete_local(completion, deadline)
                    .unwrap_or_else(|_| super::super::abort_unknown());
                loan.completed(&completed)
                    .unwrap_or_else(|_| super::super::abort_unknown());
                if reply.send(Ok(completed)).is_err() {
                    super::super::abort_unknown()
                }
            }
            Ok(Command::OutputLocks {
                capsule,
                root,
                attempt,
                reply,
            }) => {
                let result = (|| -> io::Result<_> {
                    let initial = bank.initial_ready()?.is_some();
                    if phases.drained
                        || phases.active.is_some()
                        || !(bank.is_drained()? || initial)
                        || !bank.before_output_handoff()?
                    {
                        return Err(invalid(
                            "original output handoff outside precompile quiescence",
                        ));
                    }
                    let key = output::Key {
                        root_attempt: bank.root_attempt,
                        invocation_sha256: bank.invocation_sha256,
                        attempt,
                    };
                    let (request, descriptions) =
                        capsule.output_offer(key, &root).map_err(io::Error::other)?;
                    // SAFETY: these are borrows from the actual same live
                    // capsule, already close-only before any export; queue
                    // dispatch is parked and no compiler was ever bound.
                    match unsafe { control.output(&request, &descriptions, deadline) } {
                        Ok(retained) => {
                            if initial {
                                bank.initial_output_retained(&retained)?;
                            } else {
                                bank.resume()?;
                            }
                            Ok(retained)
                        }
                        Err(WorkloadControlError::BeforeRequest(error)) => Err(error),
                        Err(WorkloadControlError::Refused { reason }) => {
                            Err(io::Error::new(io::ErrorKind::PermissionDenied, reason))
                        }
                        Err(WorkloadControlError::Unknown(_)) => super::super::abort_unknown(),
                    }
                })();
                if result.is_ok() {
                    adaptive.allow();
                }
                if reply.send(result).is_err() {
                    super::super::abort_unknown();
                }
            }
            Ok(Command::SelectOutput {
                retained,
                attempt,
                reply,
            }) => {
                let result = (|| -> io::Result<()> {
                    if phases.drained
                        || phases.active.is_some()
                        || !bank.is_drained()?
                        || !bank.native_output_selection()?
                    {
                        return Err(invalid(
                            "native output selection precedes actual phase/member/loan drain",
                        ));
                    }
                    match control.select_output(&retained, attempt, deadline) {
                        Ok(()) => {
                            bank.resume()?;
                            Ok(())
                        }
                        Err(WorkloadControlError::BeforeRequest(error)) => Err(error),
                        Err(WorkloadControlError::Refused { reason }) => {
                            Err(io::Error::new(io::ErrorKind::PermissionDenied, reason))
                        }
                        Err(WorkloadControlError::Unknown(_)) => super::super::abort_unknown(),
                    }
                })();
                if result.is_ok() {
                    adaptive.allow();
                }
                if reply.send(result).is_err() {
                    super::super::abort_unknown();
                }
            }
            Ok(Command::TryEnter { nonce, kind, reply }) => {
                if let Some(sequence) = control.phase_sequence() {
                    phases.sequence = sequence;
                }
                let result = (|| -> io::Result<Option<Phase>> {
                    if phases.drained || phases.active.is_some() {
                        return Err(invalid("original foreign phase already active"));
                    }
                    if adaptive.owns_partial() {
                        if matches!(kind, phase::Kind::Coordinator)
                            && !bank.request_minimum_funding(2)?
                        {
                            return Ok(None);
                        }
                        if !adaptive.park_current()? {
                            return Ok(None);
                        }
                        Ok(Some(phases.enter_current(
                            &bank,
                            &mut control,
                            nonce,
                            kind,
                            &adaptive,
                            deadline,
                        )?))
                    } else {
                        if !bank.is_drained()? {
                            return Ok(None);
                        }
                        let Some(escrow) = adaptive.full_escrow()? else {
                            return Ok(None);
                        };
                        Ok(Some(phases.enter(
                            &bank,
                            &mut control,
                            nonce,
                            kind,
                            escrow,
                            deadline,
                        )?))
                    }
                })();
                if reply.send(result).is_err() {
                    super::super::abort_unknown();
                }
            }
            Ok(Command::Enter {
                nonce,
                kind,
                escrow,
                reply,
            }) => {
                if let Some(sequence) = control.phase_sequence() {
                    phases.sequence = sequence;
                }
                let result = phases.enter(&bank, &mut control, nonce, kind, escrow, deadline);
                if reply.send(result).is_err() {
                    super::super::abort_unknown();
                }
            }
            Ok(Command::Register {
                phase,
                original,
                reply,
            }) => {
                let result = phases.register(&bank, &mut control, phase, original, deadline);
                if reply.send(result).is_err() {
                    super::super::abort_unknown();
                }
            }
            Ok(Command::Leave { phase, reply }) => {
                if let Some(sequence) = control.phase_sequence() {
                    phases.sequence = sequence;
                }
                let result = phases
                    .leave(&bank, &mut control, phase, deadline)
                    .and_then(|()| adaptive.resume_current());
                if result.is_ok() {
                    adaptive.allow();
                }
                if reply.send(result).is_err() {
                    super::super::abort_unknown();
                }
            }
            Ok(Command::Drained { reply }) => {
                if let Some(sequence) = control.phase_sequence() {
                    phases.sequence = sequence;
                }
                let result = (|| -> io::Result<bool> {
                    let current = adaptive.owns_partial();
                    if current {
                        if !adaptive.park_current()? {
                            return Ok(false);
                        }
                    } else if !bank.is_drained()? {
                        return Ok(false);
                    }
                    phases.drain(&bank, &mut control, deadline)?;
                    if current {
                        adaptive.retire_current()?;
                    }
                    Ok(true)
                })();
                if reply.send(result).is_err() {
                    super::super::abort_unknown();
                }
            }
            Ok(Command::Finish) => {
                if !phases.drained
                    || phases.active.is_some()
                    || !bank.current_drained().unwrap_or(false)
                {
                    super::super::abort_unknown();
                }
                unresolved.0 = false;
                return control;
            }
            Err(TryRecvError::Disconnected) => super::super::abort_unknown(),
            Err(TryRecvError::Empty) => {}
        }
        // Positive Drained closes bank/phase dispatch. Keep the original
        // connection for final census; poll_bank would now correctly refuse.
        if phases.drained {
            std::thread::sleep(Duration::from_millis(5));
            continue;
        }
        if phases.active.is_none() && adaptive.tick(&bank, &mut control, deadline).is_err() {
            super::super::abort_unknown();
        }
        let frame_deadline = deadline.min(Instant::now() + Duration::from_millis(250));
        match control.poll_bank(&bank, frame_deadline) {
            Ok(Some(request)) => {
                let answer = bank
                    .handle(&request)
                    .unwrap_or_else(|_| super::super::abort_unknown());
                if control.reply_bank(&answer, frame_deadline).is_err() {
                    super::super::abort_unknown();
                }
            }
            Ok(None) => std::thread::sleep(Duration::from_millis(5)),
            Err(_) => super::super::abort_unknown(),
        }
    }
}

mod adaptive;
#[cfg(test)]
mod tests;
