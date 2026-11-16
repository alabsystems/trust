//! The ONE dispatch table over the workload's original native CPU guards.
//! Counts and wire replies cannot construct this owner. The host continues to
//! retain the same guards and durable exclusion through whole-root drain.

use std::collections::BTreeSet;
use std::io;
use std::os::fd::AsFd;
use std::os::unix::fs::MetadataExt;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Mutex, OnceLock, Weak};

use trust_build_cpu::Lease;
use trust_resource_controller::workload::host::{self, ReadyReply, bank};
use trust_resource_controller::{Cpu, FileIdentity, Identity};

type Attempt = [u8; 16];
const MAX_MEMBERS: usize = 65_536;
const MAX_WORKERS: usize = 65_536;

fn invalid(reason: &'static str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, reason)
}

struct Original {
    lease: Arc<Lease>,
    backing: FileIdentity,
}

#[derive(Clone, Copy)]
enum Purpose {
    Compiler,
    Query,
    Coordinator,
}
#[derive(Clone, Copy)]
enum PrimaryPermission {
    Ordinary,
    Query,
}
struct InitialRestriction {
    width: u32,
    phase: Attempt,
    ceiling: u32,
}

#[derive(Clone, Copy)]
struct Member {
    attempt: Attempt,
    purpose: Purpose,
    granted: bool,
    host_returned: bool,
    local_retired: bool,
    producer: Option<Identity>,
}

#[derive(Clone, Copy)]
enum Occupancy {
    Primary {
        loan: Attempt,
        member: Option<Member>,
    },
    Extra {
        loan: Attempt,
        member: Attempt,
    },
    Local {
        loan: Attempt,
        // Retain coordinator DATA; LocalLoan validates its live binding.
        _coordinator: Attempt,
        stage: local::Stage,
    },
}

struct State {
    pending_keepers:
        Vec<Arc<trust_resource_controller::client::workload::AuthenticatedPendingKeeper>>,
    originals: Vec<Original>,
    published: usize,
    demand: bool,
    funding: Option<partial::FundingState>,
    slots: Vec<Option<Occupancy>>,
    members: BTreeSet<Attempt>,
    workers: BTreeSet<(Attempt, Attempt)>,
    next_loan: u64,
    last_sequence: u64,
    parked: bool,
    restriction: Restriction,
    poisoned: bool,
    compiler_bound: bool,
    local_cancel: Option<(Attempt, Arc<AtomicBool>)>,
    initial_phase: Option<Attempt>,
}

#[derive(Clone, Copy)]
enum Restriction {
    Running,
    InitialQueries,
    InitialOutput,
    Quiescing,
}
impl Restriction {
    fn parked(self) -> bool {
        !matches!(self, Self::Running)
    }
}

/// Retains every actual original guard. Logical lending never releases or
/// reacquires a kernel slot, creates a pool, or bypasses external exclusion.
pub(crate) struct RootCreditBank {
    original_width: usize,
    root_attempt: Attempt,
    invocation_sha256: [u8; 32],
    ceiling: u32,
    /// Cached physical CPU/memory/current local policy over OUR held set.
    /// Its argument is actual occupied logical loans, never retained N. The
    /// bounded callback runs under this table lock: no RPC, process scan or
    /// recursive bank/native admission transaction is permitted.
    /// This must not call fresh native_limit: durable N deliberately makes
    /// fresh external admission zero while these actual guards stay funded.
    live_limit: Arc<dyn Fn(u32) -> u32 + Send + Sync>,
    state: Mutex<State>,
    initial_keeper:
        OnceLock<Arc<trust_resource_controller::client::workload::AuthenticatedInitialKeeper>>,
    descriptor_budget: OnceLock<Arc<trust_resource_controller::descriptors::DescriptorBudget>>,
    // LAST: all actual CPU guards/loans close before incoming FD accounting.
    _native_job: Option<trust_build_cpu::NativeJobOriginals>,
}

/// One logical primary, created only by the original bank. Sharing this owner
/// through Arc does not allocate another slot. Bound Drop is Unknown and uses
/// the existing original-worker abort path, rather than returning the credit.
pub(crate) struct PrimaryLoan {
    bank: Arc<RootCreditBank>,
    original: Weak<Lease>,
    original_slot: u32,
    index: usize,
    permission: PrimaryPermission,
    loan: Attempt,
    local_settled: AtomicBool,
    target_retired: AtomicBool,
    compiler_attempt: OnceLock<Attempt>,
    compiler_succeeded: AtomicBool,
    coordinator_attempt: OnceLock<Attempt>,
    coordinator_observed: AtomicBool,
    // Actual original output/SDK capsule precedes the bank/loan's last Arc
    // release on normal completion; Unknown still uses the owning abort path.
    coordinator: Option<Arc<broker::RegisteredArtifact>>,
    coordinator_worker: bool,
}

pub(crate) struct Answer {
    pub(crate) reply: bank::Reply,
    /// SAME actual guard, borrowed only for this authenticated transfer.
    pub(crate) original: Option<Arc<Lease>>,
}

pub(crate) mod broker;
mod partial;
pub(crate) use partial::RootPartialPhase;
mod local;
pub(crate) use local::CoordinatorLocalOperation;
pub(crate) use local::LocalLoan;

impl RootCreditBank {
    pub(in crate::resource_v3) fn original_implicit(&self) -> io::Result<Arc<Lease>> {
        let state = self.lock()?;
        state.usable()?;
        Ok(state.originals[0].lease.clone())
    }
    pub(crate) fn binds(&self, root_attempt: Attempt, invocation_sha256: [u8; 32]) -> bool {
        self.root_attempt == root_attempt && self.invocation_sha256 == invocation_sha256
    }

    /// Called only after ExternalDebt::adopt_workload_startup consumes opaque
    /// authenticated startup custody. A decoded reply without actual Lease
    /// values cannot enter this constructor or manufacture their locks.
    pub(crate) fn from_originals(
        reply: &ReadyReply,
        leases: Vec<Lease>,
        ceiling: u32,
        live_limit: Arc<dyn Fn(u32) -> u32 + Send + Sync>,
    ) -> io::Result<Arc<Self>> {
        reply.encode()?;
        Self::from_observed_originals(
            &reply.context,
            reply.invocation_sha256,
            reply.cpu_set().cloned(),
            leases,
            ceiling,
            live_limit,
        )
    }

    /// The genuine general-job adopter retains its authenticated receipt and
    /// descriptor reservation through this SAME bank and every descendant loan.
    pub(crate) fn from_native_job_originals(
        mut originals: trust_build_cpu::NativeJobOriginals,
        ceiling: u32,
        live_limit: Arc<dyn Fn(u32) -> u32 + Send + Sync>,
    ) -> io::Result<Arc<Self>> {
        let leases = originals.take_leases()?;
        let reply = originals.observation();
        reply.encode()?;
        let mut bank = Self::from_observed_originals(
            &reply.context,
            reply.invocation_sha256,
            reply.cpu_set().cloned(),
            leases,
            ceiling,
            live_limit,
        )?;
        Arc::get_mut(&mut bank)
            .ok_or_else(|| invalid("new native-job bank unexpectedly shared"))?
            ._native_job = Some(originals);
        Ok(bank)
    }

    /// Plain observations shared by distinct authenticated startup protocols.
    /// Only their opaque native adopters supply actual SAME-OFD Lease owners.
    /// The caller must validate its own Ready wire; this never encodes or
    /// reconstructs a workload-v1 startup from another protocol's facts.
    pub(crate) fn from_observed_originals(
        context: &trust_resource_controller::ContextReply,
        invocation_sha256: [u8; 32],
        observations: impl IntoIterator<Item = host::PrimaryCpu>,
        leases: Vec<Lease>,
        ceiling: u32,
        live_limit: Arc<dyn Fn(u32) -> u32 + Send + Sync>,
    ) -> io::Result<Arc<Self>> {
        Self::from_startup_originals(
            context,
            invocation_sha256,
            observations,
            leases,
            ceiling,
            live_limit,
            StartupFunding::Full,
        )
    }

    /// Only the opaque native adopter can supply the first pair. The domain
    /// width remains an upper restriction; just one actual unit is published.
    pub(crate) fn from_initial_originals(
        originals: trust_build_cpu::InitialNativeOriginals,
        ceiling: u32,
        live_limit: Arc<dyn Fn(u32) -> u32 + Send + Sync>,
    ) -> io::Result<(
        Arc<Self>,
        trust_resource_controller::workload::host::initial::ReadyReply,
        trust_resource_controller::client::workload::WorkloadControl,
    )> {
        let (reply, lease, control, keeper) = originals.into_originals();
        reply.encode()?;
        let bank = Self::from_startup_originals(
            &reply.context,
            reply.invocation_sha256,
            [reply.primary.clone()],
            vec![lease],
            ceiling,
            live_limit,
            StartupFunding::Initial(reply.phase),
        )?;
        bank.initial_keeper
            .set(keeper)
            .map_err(|_| invalid("Initial keeper already installed"))?;
        Ok((bank, reply, control))
    }

    fn from_startup_originals(
        context: &trust_resource_controller::ContextReply,
        invocation_sha256: [u8; 32],
        observations: impl IntoIterator<Item = host::PrimaryCpu>,
        leases: Vec<Lease>,
        ceiling: u32,
        live_limit: Arc<dyn Fn(u32) -> u32 + Send + Sync>,
        funding: StartupFunding,
    ) -> io::Result<Arc<Self>> {
        context.encode()?;
        let Cpu::CooperativeShared {
            ceiling: domain, ..
        } = context.context.cpu
        else {
            return Err(invalid(
                "workload bank requires original cooperative custody",
            ));
        };
        let expected = match funding {
            StartupFunding::Full => domain as usize,
            StartupFunding::Initial(_) => 1,
        };
        if leases.len() != expected
            || domain as usize > host::MAX_CPU_SET
            || leases.is_empty()
            || leases.len() > host::MAX_CPU_SET
            || ceiling == 0
            || ceiling > domain
            || context.context.root_attempt == [0; 16]
            || invocation_sha256 == [0; 32]
        {
            return Err(invalid(
                "workload original CPU set or dispatch ceiling differs",
            ));
        }
        let observations: Vec<_> = observations
            .into_iter()
            .take(host::MAX_CPU_SET + 1)
            .collect();
        if observations.len() != leases.len() {
            return Err(invalid("workload original CPU observations differ"));
        }
        let mut originals: Vec<Original> = Vec::with_capacity(leases.len());
        for (lease, observed) in leases.into_iter().zip(observations) {
            // Observe the SAME real lease FD; no pathname open/try_lock/adopt.
            let file = lease.as_fd().try_clone_to_owned()?;
            let meta = std::fs::File::from(file).metadata()?;
            let backing = FileIdentity {
                device: meta.dev(),
                inode: meta.ino(),
            };
            if lease.slot() != observed.slot
                || backing != observed.backing
                || !meta.is_file()
                || meta.nlink() != 1
                || originals
                    .iter()
                    .any(|other| other.lease.slot() == lease.slot() || other.backing == backing)
            {
                return Err(invalid("workload original CPU backing or slot differs"));
            }
            originals.push(Original {
                lease: Arc::new(lease),
                backing,
            });
        }
        match funding {
            StartupFunding::Full => Self::retained(
                originals,
                context.context.root_attempt,
                invocation_sha256,
                ceiling,
                live_limit,
            ),
            StartupFunding::Initial(phase) => Self::retained_initial(
                originals,
                context.context.root_attempt,
                invocation_sha256,
                InitialRestriction {
                    width: domain,
                    phase,
                    ceiling,
                },
                live_limit,
            ),
        }
    }
    fn retained_initial(
        originals: Vec<Original>,
        root: Attempt,
        invocation: [u8; 32],
        restriction: InitialRestriction,
        live_limit: Arc<dyn Fn(u32) -> u32 + Send + Sync>,
    ) -> io::Result<Arc<Self>> {
        let InitialRestriction {
            width: domain,
            phase,
            ceiling,
        } = restriction;
        if originals.len() != 1
            || root == [0; 16]
            || invocation == [0; 32]
            || domain == 0
            || domain as usize > host::MAX_CPU_SET
            || ceiling == 0
            || ceiling > domain
            || phase == [0; 16]
            || phase == root
        {
            return Err(invalid(
                "initial bank differs from original pair/restriction",
            ));
        }
        let mut bank = Self::retained(originals, root, invocation, 1, live_limit)?;
        {
            let bank = Arc::get_mut(&mut bank)
                .ok_or_else(|| invalid("initial bank prematurely shared"))?;
            bank.original_width = domain as usize;
            bank.ceiling = ceiling;
            let state = bank
                .state
                .get_mut()
                .map_err(|_| invalid("initial bank poisoned"))?;
            state
                .slots
                .try_reserve_exact(domain as usize - 1)
                .map_err(io::Error::other)?;
            state.slots.resize(domain as usize, None);
            state.initial_phase = Some(phase);
            state.parked = true;
            state.restriction = Restriction::InitialQueries;
        }
        Ok(bank)
    }

    fn retained(
        originals: Vec<Original>,
        root_attempt: Attempt,
        invocation_sha256: [u8; 32],
        ceiling: u32,
        live_limit: Arc<dyn Fn(u32) -> u32 + Send + Sync>,
    ) -> io::Result<Arc<Self>> {
        if originals.is_empty() || ceiling == 0 || ceiling as usize > originals.len() {
            return Err(invalid("empty retained workload bank"));
        }
        let count = originals.len();
        Ok(Arc::new(Self {
            original_width: count,
            root_attempt,
            invocation_sha256,
            ceiling,
            live_limit,
            _native_job: None,
            initial_keeper: OnceLock::new(),
            descriptor_budget: OnceLock::new(),
            state: Mutex::new(State {
                pending_keepers: Vec::new(),
                originals,
                published: count,
                demand: false,
                funding: None,
                slots: vec![None; count],
                members: BTreeSet::new(),
                workers: BTreeSet::new(),
                next_loan: 0,
                last_sequence: 0,
                parked: false,
                restriction: Restriction::Running,
                poisoned: false,
                compiler_bound: false,
                local_cancel: None,
                initial_phase: None,
            }),
        }))
    }

    pub(crate) fn bind_descriptor_budget(
        &self,
        budget: Arc<trust_resource_controller::descriptors::DescriptorBudget>,
    ) -> io::Result<()> {
        self.descriptor_budget
            .set(budget)
            .map_err(|_| invalid("original descriptor budget already bound"))
    }

    fn lock(&self) -> io::Result<std::sync::MutexGuard<'_, State>> {
        self.state
            .lock()
            .map_err(|_| invalid("original workload CPU table poisoned"))
    }

    fn retain_pending_keeper(
        &self,
        owner: Arc<trust_resource_controller::client::workload::AuthenticatedPendingKeeper>,
    ) -> io::Result<()> {
        let request = owner.observation();
        let mut state = self.lock()?;
        state.usable()?;
        if let Some(existing) = state
            .pending_keepers
            .iter()
            .find(|kept| kept.observation().nonce == request.nonce)
        {
            if existing.observation() == request
                && request.root_attempt == self.root_attempt
                && request.invocation_sha256 == self.invocation_sha256
                && state
                    .funding
                    .as_ref()
                    .is_some_and(|funding| funding.keeper_phase(request.phase))
            {
                return Ok(());
            }
            return Err(invalid("pending keeper retry changed original backing"));
        }
        if request.root_attempt != self.root_attempt
            || request.invocation_sha256 != self.invocation_sha256
            || !state
                .funding
                .as_ref()
                .is_some_and(|funding| funding.keeper_phase(request.phase))
            || state.pending_keepers.len() >= self.original_width
            || state
                .originals
                .iter()
                .any(|original| original.backing == request.native)
            || state.pending_keepers.iter().any(|kept| {
                let old = kept.observation();
                old.nonce == request.nonce
                    || old.native_slot == request.native_slot
                    || old.native == request.native
                    || old.shadow == request.shadow
                    || old.memory_guard != request.memory_guard
                    || old.memory_epoch != request.memory_epoch
                    || old.memory_scope_sha256 != request.memory_scope_sha256
            })
        {
            return Err(invalid(
                "pending keeper differs from original root/phase/backing",
            ));
        }
        state
            .pending_keepers
            .try_reserve(1)
            .map_err(io::Error::other)?;
        state.pending_keepers.push(owner);
        Ok(())
    }

    pub(crate) fn try_primary(self: &Arc<Self>) -> io::Result<Option<Arc<PrimaryLoan>>> {
        self.try_primary_for(PrimaryPermission::Ordinary)
    }
    /// Closed metadata queries may use only the genuine initial implicit
    /// pair before Layout/GNU setup. Producing compiler work remains parked.
    pub(crate) fn try_query(self: &Arc<Self>) -> io::Result<Option<Arc<PrimaryLoan>>> {
        self.try_primary_for(PrimaryPermission::Query)
    }
    fn try_primary_for(
        self: &Arc<Self>,
        permission: PrimaryPermission,
    ) -> io::Result<Option<Arc<PrimaryLoan>>> {
        let mut state = self.lock()?;
        state.usable()?;
        let limit = (self.live_limit)(state.occupied() as u32)
            .min(self.ceiling)
            .min(state.published as u32);
        let initial_query = matches!(permission, PrimaryPermission::Query)
            && state.initial_phase.is_some()
            && !state.compiler_bound
            && state.funding.is_none()
            && matches!(state.restriction, Restriction::InitialQueries)
            && state.originals.len() == 1
            && state.published == 1;
        if (state.parked && !initial_query) || state.occupied() >= limit as usize {
            if state.funding.is_some() {
                state.demand = true;
            }
            return Ok(None);
        }
        let Some(index) = state
            .slots
            .iter()
            .take(state.published)
            .position(Option::is_none)
        else {
            return Ok(None);
        };
        let loan = state.next_loan()?;
        state.demand = false;
        state.slots[index] = Some(Occupancy::Primary { loan, member: None });
        Ok(Some(Arc::new(PrimaryLoan {
            bank: self.clone(),
            original: Arc::downgrade(&state.originals[index].lease),
            original_slot: state.originals[index].lease.slot(),
            index,
            permission,
            loan,
            local_settled: AtomicBool::new(false),
            target_retired: AtomicBool::new(false),
            compiler_attempt: OnceLock::new(),
            compiler_succeeded: AtomicBool::new(false),
            coordinator_attempt: OnceLock::new(),
            coordinator_observed: AtomicBool::new(false),
            coordinator: None,
            coordinator_worker: false,
        })))
    }

    /// Reserve one existing unit for a registered produced coordinator while
    /// the SAME parent queue remains parked. Compiler/linker continuations
    /// require a distinct second original from this bank.
    pub(crate) fn try_coordinator(
        self: &Arc<Self>,
        artifact: &Arc<broker::RegisteredArtifact>,
    ) -> io::Result<Option<Arc<PrimaryLoan>>> {
        use trust_resource_controller::workload::host::phase;
        let registration = artifact.registered().registration();
        if artifact.phase().kind != phase::Kind::Coordinator
            || registration.key.root_attempt != self.root_attempt
            || registration.key.invocation_sha256 != self.invocation_sha256
        {
            return Err(invalid(
                "coordinator belongs to another original phase/bank",
            ));
        }
        artifact
            .validate(std::time::Instant::now() + std::time::Duration::from_secs(20))
            .map_err(io::Error::other)?;
        let mut state = self.lock()?;
        state.usable()?;
        if !state.parked
            || state.occupied() != 0
            || state
                .funding
                .as_ref()
                .is_some_and(|funding| !funding.running())
        {
            return Err(invalid(
                "coordinator requires the parked, positively drained parent bank",
            ));
        }
        if state.originals.len() < 2 || self.ceiling < 2 {
            return Err(invalid(
                "native produced coordinator requires two distinct original units",
            ));
        }
        if (self.live_limit)(0).min(self.ceiling) < 2 {
            return Ok(None);
        }
        let index = state
            .slots
            .iter()
            .take(state.published)
            .position(Option::is_none)
            .ok_or_else(|| invalid("drained original bank has no free actual unit"))?;
        let loan = state.next_loan()?;
        state.slots[index] = Some(Occupancy::Primary { loan, member: None });
        Ok(Some(Arc::new(PrimaryLoan {
            bank: self.clone(),
            original: Arc::downgrade(&state.originals[index].lease),
            original_slot: state.originals[index].lease.slot(),
            index,
            loan,
            local_settled: AtomicBool::new(false),
            target_retired: AtomicBool::new(false),
            compiler_attempt: OnceLock::new(),
            compiler_succeeded: AtomicBool::new(false),
            coordinator_attempt: OnceLock::new(),
            coordinator_observed: AtomicBool::new(false),
            coordinator: Some(Arc::clone(artifact)),
            permission: PrimaryPermission::Ordinary,
            coordinator_worker: false,
        })))
    }

    /// Reserve the selected second actual original while its coordinator
    /// retains the first. The parent alone owns compiler/capture; no child
    /// offer, count, synchronous wait or GNU token supplies another unit.
    pub(crate) fn try_coordinator_worker(
        self: &Arc<Self>,
        coordinator: &Arc<PrimaryLoan>,
    ) -> io::Result<Option<Arc<PrimaryLoan>>> {
        if !coordinator.belongs_to(self)
            || coordinator.coordinator_worker
            || coordinator.coordinator.is_none()
        {
            return Err(invalid("worker has no original coordinator in this bank"));
        }
        let mut state = self.lock()?;
        state.usable()?;
        let Some(Occupancy::Primary {
            loan,
            member: Some(member),
        }) = state.slots[coordinator.index]
        else {
            return Err(invalid("original coordinator primary is not bound"));
        };
        if loan != coordinator.loan
            || !matches!(member.purpose, Purpose::Coordinator)
            || !member.granted
            || member.host_returned
            || member.local_retired
            || !state.parked
        {
            return Err(invalid(
                "original coordinator is not actively retained in parked parent",
            ));
        }
        if state.occupied() != 1 || (self.live_limit)(1).min(self.ceiling) < 2 {
            return Ok(None);
        }
        let index = state
            .slots
            .iter()
            .take(state.published)
            .position(Option::is_none)
            .ok_or_else(|| invalid("coordinator lacks second original unit"))?;
        if index == coordinator.index {
            return Err(invalid("coordinator cannot lend its own executing unit"));
        }
        let loan = state.next_loan()?;
        state.slots[index] = Some(Occupancy::Primary { loan, member: None });
        Ok(Some(Arc::new(PrimaryLoan {
            bank: self.clone(),
            original: Arc::downgrade(&state.originals[index].lease),
            original_slot: state.originals[index].lease.slot(),
            index,
            loan,
            local_settled: AtomicBool::new(false),
            target_retired: AtomicBool::new(false),
            compiler_attempt: OnceLock::new(),
            compiler_succeeded: AtomicBool::new(false),
            coordinator_attempt: OnceLock::new(),
            coordinator_observed: AtomicBool::new(false),
            coordinator: coordinator.coordinator.clone(),
            permission: PrimaryPermission::Ordinary,
            coordinator_worker: true,
        })))
    }

    /// Park BEFORE inspecting current workers, then join original workers and
    /// drain their positive host/local loan returns. Park never frees a loan.
    pub(crate) fn park(&self) -> io::Result<()> {
        let mut state = self.lock()?;
        state.usable()?;
        state.parked = true;
        state.restriction = Restriction::Quiescing;
        Ok(())
    }
    pub(crate) fn request_minimum_funding(&self, minimum: usize) -> io::Result<bool> {
        let mut state = self.lock()?;
        state.usable()?;
        if minimum == 0 || minimum > self.ceiling as usize || minimum > self.original_width {
            return Err(invalid(
                "operation exceeds original dispatch/memory restriction",
            ));
        }
        if state.published < minimum {
            state.demand = true;
            return Ok(false);
        }
        Ok(true)
    }
    pub(crate) fn initial_output_retained(
        &self,
        retained: &trust_resource_controller::client::workload::RetainedOutputLocks,
    ) -> io::Result<()> {
        let original = retained.observation();
        if original.key.root_attempt != self.root_attempt
            || original.key.invocation_sha256 != self.invocation_sha256
        {
            return Err(invalid(
                "initial output belongs to another original operation",
            ));
        }
        let state = self.lock()?;
        state.usable()?;
        if state.initial_phase.is_none()
            || !matches!(state.restriction, Restriction::InitialOutput)
            || state.compiler_bound
            || state.occupied() != 0
            || !state.parked
        {
            return Err(invalid("initial output no longer precedes dispatch"));
        }
        Ok(())
    }
    pub(crate) fn park_initial_output(&self) -> io::Result<()> {
        let mut state = self.lock()?;
        state.usable()?;
        if state.initial_phase.is_none()
            || state.compiler_bound
            || !matches!(state.restriction, Restriction::InitialQueries)
        {
            return Err(invalid(
                "initial output cannot override another dispatch restriction",
            ));
        }
        state.parked = true;
        state.restriction = Restriction::InitialOutput;
        Ok(())
    }

    pub(crate) fn is_drained(&self) -> io::Result<bool> {
        let state = self.lock()?;
        state.usable()?;
        Ok(state.parked
            && state.occupied() == 0
            && state.funding.is_none()
            && state.originals.len() == self.original_width)
    }
    pub(crate) fn current_drained(&self) -> io::Result<bool> {
        let state = self.lock()?;
        state.usable()?;
        Ok(state.parked
            && state.occupied() == 0
            && state.local_cancel.is_none()
            && !state.originals.is_empty()
            && state.originals.len() == state.published
            && state.initial_phase.is_none()
            && state
                .funding
                .as_ref()
                .is_none_or(|funding| funding.running()))
    }
    pub(crate) fn funded_width(&self) -> io::Result<usize> {
        let state = self.lock()?;
        state.usable()?;
        if state.originals.is_empty() || state.originals.len() != state.published {
            return Err(invalid("current funded originals are unpublished"));
        }
        Ok(state.published)
    }
    pub(crate) fn fully_funded(&self) -> io::Result<bool> {
        let state = self.lock()?;
        state.usable()?;
        Ok(state.funding.is_none()
            && state.originals.len() == self.original_width
            && state.published == self.original_width)
    }

    /// An empty current table does not imply no compiler was previously
    /// delivered. Output guards must be retained BEFORE the first binding.
    pub(crate) fn before_compilation(&self) -> io::Result<bool> {
        let state = self.lock()?;
        state.usable()?;
        Ok(!state.compiler_bound)
    }
    /// Legacy startup has one precompiler output handoff. Only the opaque
    /// native-job original-set owner permits later epochs, each beginning
    /// with an actually empty current loan table and no local operation.
    pub(crate) fn before_output_handoff(&self) -> io::Result<bool> {
        let state = self.lock()?;
        state.usable()?;
        if self._native_job.is_none() {
            return Ok(!state.compiler_bound);
        }
        Ok(state.occupied() == 0 && state.local_cancel.is_none())
    }
    pub(crate) fn native_output_selection(&self) -> io::Result<bool> {
        Ok(self._native_job.is_some() && self.before_output_handoff()?)
    }

    /// Resume only after the actual host foreign phase has positively retired;
    /// the caller still owns that separate phase/SDK/output continuation.
    pub(crate) fn resume(&self) -> io::Result<()> {
        let mut state = self.lock()?;
        state.usable()?;
        if !state.parked
            || state.occupied() != 0
            || state.funding.is_some()
            || state.originals.len() != self.original_width
        {
            return Err(invalid("workload bank resume before original loan drain"));
        }
        state.parked = false;
        state.restriction = Restriction::Running;
        Ok(())
    }

    /// Only the ONE authenticated control owner calls this. It transfers no
    /// new grant: Primary selects its previously reserved member/slot, Extra
    /// lends another currently free original subject to the SAME live policy.
    pub(crate) fn handle(&self, request: &bank::Request) -> io::Result<Answer> {
        let mut state = self.lock()?;
        state.usable()?;
        let result = (|| {
            request.encode()?;
            if request.key.root_attempt != self.root_attempt
                || request.key.invocation_sha256 != self.invocation_sha256
                || request.key.sequence
                    != state
                        .last_sequence
                        .checked_add(1)
                        .ok_or_else(|| invalid("workload bank sequence overflow"))?
            {
                return Err(invalid(
                    "workload bank root, invocation or sequence differs",
                ));
            }
            state.last_sequence = request.key.sequence;
            let decision = match request.operation {
                bank::Operation::Primary {
                    member_attempt,
                    slot,
                } => {
                    let index = state
                        .originals
                        .iter()
                        .position(|item| item.lease.slot() == slot)
                        .ok_or_else(|| invalid("unknown original primary slot"))?;
                    let Some(Occupancy::Primary {
                        loan,
                        member: Some(member),
                    }) = state.slots[index]
                    else {
                        return Err(invalid("primary has no original queue loan"));
                    };
                    if member.attempt != member_attempt || member.granted || member.local_retired {
                        return Err(invalid("primary member reused, retired or mismatched"));
                    }
                    // A queued primary was already funded and counted by the
                    // live policy. Never acquire or count another unit here.
                    state.slots[index] = Some(Occupancy::Primary {
                        loan,
                        member: Some(Member {
                            granted: true,
                            ..member
                        }),
                    });
                    self.grant(&state, member_attempt, loan, index)
                }
                bank::Operation::Extra {
                    member_attempt,
                    worker_request,
                    producer,
                } => {
                    let primary = state.primary(member_attempt)?;
                    let Some(Occupancy::Primary {
                        member: Some(mut member),
                        ..
                    }) = state.slots[primary]
                    else {
                        unreachable!("primary index validated")
                    };
                    if !matches!(member.purpose, Purpose::Compiler)
                        || !member.granted
                        || member.host_returned
                        || member.local_retired
                        || member.producer.is_some_and(|expected| expected != producer)
                        || state.workers.contains(&(member_attempt, worker_request))
                    {
                        return Err(invalid(
                            "worker request has no live original compiler primary",
                        ));
                    }
                    let limit = (self.live_limit)(state.occupied() as u32)
                        .min(self.ceiling)
                        .min(state.published as u32);
                    if state.parked || state.occupied() >= limit as usize {
                        if state.funding.is_some() {
                            state.demand = true;
                        }
                        bank::Decision::Busy
                    } else {
                        let index = state
                            .slots
                            .iter()
                            .take(state.published)
                            .position(Option::is_none)
                            .ok_or_else(|| invalid("workload occupied credit count differs"))?;
                        if state.workers.len() == MAX_WORKERS {
                            return Err(invalid("workload worker census bound exhausted"));
                        }
                        member.producer = Some(producer);
                        if let Some(Occupancy::Primary { member: stored, .. }) =
                            &mut state.slots[primary]
                        {
                            *stored = Some(member);
                        }
                        state.workers.insert((member_attempt, worker_request));
                        let loan = state.next_loan()?;
                        state.demand = false;
                        state.slots[index] = Some(Occupancy::Extra {
                            loan,
                            member: member_attempt,
                        });
                        self.grant(&state, member_attempt, loan, index)
                    }
                }
                bank::Operation::Returned {
                    member_attempt,
                    loan,
                    slot,
                } => {
                    let index = state
                        .originals
                        .iter()
                        .position(|item| item.lease.slot() == slot)
                        .ok_or_else(|| invalid("unknown returned original slot"))?;
                    match state.slots[index] {
                        Some(Occupancy::Extra {
                            loan: expected,
                            member,
                        }) if expected == loan && member == member_attempt => {
                            state.slots[index] = None;
                        }
                        Some(Occupancy::Primary {
                            loan: expected,
                            member: Some(member),
                        }) if expected == loan
                            && member.attempt == member_attempt
                            && member.granted
                            && !member.host_returned =>
                        {
                            if state.has_extras(member_attempt) {
                                return Err(invalid("primary returned before its actual workers"));
                            }
                            if matches!(member.purpose, Purpose::Coordinator)
                                && let Some((coordinator, cancelled)) = &state.local_cancel
                                && *coordinator == member_attempt
                            {
                                // A still-funded local operation must stop
                                // IO, not pretend its coordinator remained.
                                cancelled.store(true, Ordering::Release);
                            }
                            state.slots[index] = if member.local_retired {
                                None
                            } else {
                                Some(Occupancy::Primary {
                                    loan,
                                    member: Some(Member {
                                        host_returned: true,
                                        ..member
                                    }),
                                })
                            };
                        }
                        _ => {
                            return Err(invalid(
                                "returned original loan differs or was already returned",
                            ));
                        }
                    }
                    bank::Decision::Returned
                }
            };
            let original = match decision {
                bank::Decision::Granted { slot, .. } => Some(
                    state
                        .originals
                        .iter()
                        .find(|item| item.lease.slot() == slot)
                        .ok_or_else(|| invalid("granted original slot missing"))?
                        .lease
                        .clone(),
                ),
                _ => None,
            };
            Ok(Answer {
                reply: bank::Reply {
                    key: request.key,
                    decision,
                },
                original,
            })
        })();
        if result.is_err() {
            state.poisoned = true;
        }
        result
    }

    fn grant(
        &self,
        state: &State,
        member_attempt: Attempt,
        loan: Attempt,
        index: usize,
    ) -> bank::Decision {
        let original = &state.originals[index];
        bank::Decision::Granted {
            member_attempt,
            loan,
            slot: original.lease.slot(),
            backing: original.backing,
        }
    }
}

#[derive(Clone, Copy)]
enum StartupFunding {
    Full,
    Initial(Attempt),
}

impl State {
    fn usable(&self) -> io::Result<()> {
        if self.poisoned {
            Err(invalid("original workload bank is unusable; never retry"))
        } else {
            Ok(())
        }
    }
    fn occupied(&self) -> usize {
        self.slots.iter().filter(|slot| slot.is_some()).count()
    }
    fn primary(&self, member: Attempt) -> io::Result<usize> {
        self.slots.iter().position(|slot| matches!(slot,
            Some(Occupancy::Primary { member: Some(current), .. }) if current.attempt == member
        )).ok_or_else(|| invalid("compiler has no original primary loan"))
    }
    fn has_extras(&self, member: Attempt) -> bool {
        self.slots.iter().any(|slot| {
            matches!(slot,
                Some(Occupancy::Extra { member: current, .. }) if *current == member
            )
        })
    }
    fn next_loan(&mut self) -> io::Result<Attempt> {
        self.next_loan = self
            .next_loan
            .checked_add(1)
            .ok_or_else(|| invalid("workload original loan identifiers exhausted"))?;
        // This is a one-use identifier, never a secret or admission grant.
        let mut result = [0; 16];
        result[..8].copy_from_slice(b"TARGOBNK");
        result[8..].copy_from_slice(&self.next_loan.to_be_bytes());
        Ok(result)
    }
}

impl PrimaryLoan {
    /// Read-only pre-delivery preparation under the SAME already reserved
    /// original unit. This creates no admission and never settles, resets or
    /// refunds a loan. The caller separately retains SAME Startup/no-foreign
    /// RootContext custody through the preparation.
    pub(crate) fn require_preparation(&self, lease: &Arc<Lease>) -> io::Result<()> {
        let state = self.bank.lock()?;
        state.usable()?;
        if matches!(self.permission, PrimaryPermission::Query)
            || state.parked
            || !state
                .originals
                .get(self.index)
                .is_some_and(|original| Arc::ptr_eq(&original.lease, lease))
            || self.local_settled.load(Ordering::Acquire)
            || self.target_retired.load(Ordering::Acquire)
            || self.compiler_attempt.get().is_some()
            || self.coordinator_attempt.get().is_some()
            || !matches!(state.slots.get(self.index),
                Some(Some(Occupancy::Primary { loan, member: None })) if *loan == self.loan)
        {
            return Err(invalid(
                "preparation lost SAME unbound original primary reservation",
            ));
        }
        Ok(())
    }
    pub(crate) fn coordinator_attempt(&self) -> Option<Attempt> {
        self.coordinator_attempt.get().copied()
    }
    pub(crate) fn is_coordinator_worker_for(&self, coordinator: &PrimaryLoan) -> bool {
        self.coordinator_worker
            && !coordinator.coordinator_worker
            && Arc::ptr_eq(&self.bank, &coordinator.bank)
            && self.index != coordinator.index
            && self.original_slot != coordinator.original_slot
            && match (&self.coordinator, &coordinator.coordinator) {
                (Some(worker), Some(parent)) => Arc::ptr_eq(worker, parent),
                _ => false,
            }
            && coordinator.coordinator_attempt().is_some()
            && !coordinator.local_settled.load(Ordering::Acquire)
    }
    pub(crate) fn belongs_to(&self, bank: &RootCreditBank) -> bool {
        std::ptr::eq(self.bank.as_ref(), bank)
    }

    pub(crate) fn lease(&self) -> Arc<Lease> {
        // Metadata for an already retired logical loan must not prolong or
        // rebind its physical guard across a partial phase. A stale execution
        // request cannot silently select a replacement at the same index.
        self.original
            .upgrade()
            .unwrap_or_else(|| super::abort_unknown())
    }

    /// Bind before any delivery that could create a registered compiler.
    pub(crate) fn begin_compiler(&self, member_attempt: Attempt) -> io::Result<()> {
        if self.coordinator.is_some() && !self.coordinator_worker {
            return Err(invalid(
                "coordinator unit is not a compiler materialization",
            ));
        }
        self.begin(member_attempt, Purpose::Compiler)?;
        self.compiler_attempt
            .set(member_attempt)
            .map_err(|_| invalid("original compiler materialization bound twice"))
    }

    /// Called only by the original execution owner after its known successful
    /// terminal AND local helper/output retirement. Host return remains a
    /// separate bank predicate required before registration/foreign Enter.
    pub(crate) fn record_compiler_terminal(
        &self,
        terminal: &trust_resource_controller::Status,
    ) -> io::Result<()> {
        use trust_resource_controller::{CompletionCause, Outcome, Status};
        if !matches!(
            terminal,
            Status::Finished {
                outcome: Outcome::Exit(0),
                cause: CompletionCause::Exited,
                ..
            }
        ) {
            return Ok(());
        }
        if self.compiler_attempt.get().is_none()
            || !self.local_settled.load(Ordering::Acquire)
            || !self.target_retired.load(Ordering::Acquire)
            || self.compiler_succeeded.swap(true, Ordering::AcqRel)
        {
            return Err(invalid(
                "compiler success without original positive local retirement",
            ));
        }
        Ok(())
    }

    pub(crate) fn completed_compiler(&self) -> Option<Attempt> {
        (self.local_settled.load(Ordering::Acquire)
            && self.compiler_succeeded.load(Ordering::Acquire))
        .then(|| self.compiler_attempt.get().copied())
        .flatten()
    }

    /// Local retirement of this actual bound compiler, including a known
    /// failure/refusal. This is not success, materialization, or Host Return;
    /// only the execution owner can conjoin it with its terminal and pipe EOF.
    pub(crate) fn retired_compiler_attempt(&self) -> Option<Attempt> {
        self.local_settled
            .load(Ordering::Acquire)
            .then(|| self.compiler_attempt.get().copied())
            .flatten()
    }
    /// Read-only actual local/Host closure. A granted member keeps THIS
    /// occupancy until both its original local retirement and exact Host
    /// Return; an ungranted native refusal has no Host credit to return.
    /// This is insufficient alone: the actual capture must independently
    /// retain its SAME child/helper and error-free physical EOF.
    pub(crate) fn require_closed_compiler(&self, member: Attempt) -> io::Result<()> {
        let state = self.bank.lock()?;
        state.usable()?;
        if !self.local_settled.load(Ordering::Acquire)
            || self.compiler_attempt.get() != Some(&member)
        {
            return Err(invalid(
                "compiler original has no actual completed local and Host return",
            ));
        }
        if matches!(state.slots[self.index],Some(Occupancy::Primary {loan,..})if loan==self.loan) {
            return Err(io::Error::new(
                io::ErrorKind::WouldBlock,
                "same original compiler Host return is pending",
            ));
        }
        Ok(())
    }

    pub(crate) fn successful_job_compiler(&self) -> io::Result<Option<Attempt>> {
        match self.compiler_attempt.get() {
            None => Ok(None),
            Some(_) => self.completed_compiler().map(Some).ok_or_else(|| {
                invalid("successful job has an uncompleted or unsuccessful compiler")
            }),
        }
    }

    /// The distinct non-producing query owner cannot lend SDK compiler startup
    /// custody or request compiler workers, even though it uses the SAME bank.
    pub(crate) fn begin_query(&self, member_attempt: Attempt) -> io::Result<()> {
        if self.coordinator.is_some() && !self.coordinator_worker {
            return Err(invalid("coordinator unit is not a standalone query"));
        }
        self.begin(member_attempt, Purpose::Query)
    }

    pub(crate) fn begin_coordinator(&self, member_attempt: Attempt) -> io::Result<()> {
        if self.coordinator.is_none() || self.coordinator_worker {
            return Err(invalid("coordinator has no original registered output"));
        }
        self.begin(member_attempt, Purpose::Coordinator)?;
        self.coordinator_attempt
            .set(member_attempt)
            .map_err(|_| invalid("coordinator materialization bound twice"))
    }

    /// Observation only. Native completion and local/Host return are separate
    /// prerequisites; this never produces compiler success or output authority.
    pub(crate) fn record_coordinator_terminal(
        &self,
        terminal: &trust_resource_controller::Status,
    ) -> io::Result<()> {
        if !matches!(terminal, trust_resource_controller::Status::Finished { .. })
            || self.coordinator_attempt.get().is_none()
            || !self.local_settled.load(Ordering::Acquire)
            || !self.target_retired.load(Ordering::Acquire)
            || self.coordinator_observed.swap(true, Ordering::AcqRel)
        {
            return Err(invalid(
                "coordinator observation without native original retirement",
            ));
        }
        Ok(())
    }

    fn begin(&self, member_attempt: Attempt, purpose: Purpose) -> io::Result<()> {
        let mut state = self.bank.lock()?;
        state.usable()?;
        if (matches!(self.permission, PrimaryPermission::Query)
            && !matches!(purpose, Purpose::Query))
            || self.local_settled.load(Ordering::Acquire)
            || member_attempt == [0; 16]
            || member_attempt == self.bank.root_attempt
            || state.members.len() == MAX_MEMBERS
            || state.members.contains(&member_attempt)
        {
            return Err(invalid("workload primary member binding reused or invalid"));
        }
        match state.slots[self.index] {
            Some(Occupancy::Primary { loan, member: None }) if loan == self.loan => {}
            _ => return Err(invalid("workload primary already bound or no longer owned")),
        }
        state.members.insert(member_attempt);
        if matches!(purpose, Purpose::Compiler) {
            state.compiler_bound = true;
        }
        state.slots[self.index] = Some(Occupancy::Primary {
            loan: self.loan,
            member: Some(Member {
                attempt: member_attempt,
                purpose,
                granted: false,
                host_returned: false,
                local_retired: false,
                producer: None,
            }),
        });
        Ok(())
    }

    /// Only affirmative BeforeRequest may cancel an armed but unexposed loan.
    pub(crate) fn before_request(&self) -> io::Result<()> {
        self.settle_local(true)
    }

    /// The SAME original target/helper has positively retired and drained.
    /// A compiler which borrowed startup custody additionally needs the host's
    /// exact Return; neither arrival order can return the credit early.
    pub(crate) fn retired(&self) -> io::Result<()> {
        self.settle_local(false)
    }

    fn settle_local(&self, before_request: bool) -> io::Result<()> {
        let mut state = self.bank.lock()?;
        state.usable()?;
        if self.local_settled.load(Ordering::Acquire) {
            return Err(invalid("workload local primary retirement repeated"));
        }
        let Some(Occupancy::Primary {
            loan,
            member: Some(mut member),
        }) = state.slots[self.index]
        else {
            return Err(invalid("local primary retirement has no bound member"));
        };
        if loan != self.loan || member.local_retired || (before_request && member.granted) {
            return Err(invalid(
                "local primary retirement differs from original delivery",
            ));
        }
        member.local_retired = true;
        self.target_retired
            .store(!before_request && member.granted, Ordering::Release);
        state.slots[self.index] = if !member.granted || member.host_returned {
            None
        } else {
            Some(Occupancy::Primary {
                loan,
                member: Some(member),
            })
        };
        self.local_settled.store(true, Ordering::Release);
        Ok(())
    }
}

impl Drop for PrimaryLoan {
    fn drop(&mut self) {
        if self.local_settled.load(Ordering::Acquire) {
            return;
        }
        if let Ok(mut state) = self.bank.state.lock() {
            if matches!(state.slots[self.index],
                Some(Occupancy::Primary { loan, member: None }) if loan == self.loan
            ) {
                state.slots[self.index] = None;
                return;
            }
            state.poisoned = true;
        }
        // Preserve the original Unknown semantics; no Drop frees an offered
        // logical credit while its real target/worker may still execute.
        super::super::executor::abort_worker()
    }
}

#[cfg(test)]
mod tests;
