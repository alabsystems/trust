//! A second SAME original for fixed trusted Root-local IO. No hosted target,
//! Status, synthetic group retirement, new pool or GNU token is involved.
use super::*;
use trust_resource_controller::client::workload::{
    CompletedLocalOperation, LocalIoScope, LocalNotAdmitted,
};
use trust_resource_controller::workload::host::publication as wire;
use trust_resource_provenance::program::produced::HeldOutputRoot;

/// Fixed native local admission coupled to the SAME original bank. Neither
/// the wire manifest nor a path/hash constructs this operation.
pub(crate) struct CoordinatorLocalOperation {
    pub(super) loan: Arc<LocalLoan>,
    pub(super) io: LocalIoScope,
}
impl CoordinatorLocalOperation {
    pub(crate) fn require(
        &self,
        startup: &Arc<crate::resource_v3::Startup>,
        selected: &Arc<HeldOutputRoot>,
    ) -> io::Result<()> {
        if !startup.original_root
            || startup.candidate.is_some()
            || !startup
                .workload_bank
                .as_ref()
                .is_some_and(|bank| Arc::ptr_eq(bank, &self.loan.bank))
            || !startup
                .descriptor_budget
                .as_ref()
                .is_some_and(|budget| Arc::ptr_eq(budget, self.io.descriptor_budget()))
            || !Arc::ptr_eq(selected, self.io.output_root())
        {
            return Err(invalid(
                "local operation belongs to another original Root/bank/output",
            ));
        }
        self.loan.matches(self.io.request())?;
        self.io.require_live()
    }
    pub(crate) fn io(
        &mut self,
        startup: &Arc<crate::resource_v3::Startup>,
        selected: &Arc<HeldOutputRoot>,
    ) -> io::Result<&mut LocalIoScope> {
        self.require(startup, selected)?;
        Ok(&mut self.io)
    }
    pub(crate) fn request(&self) -> &wire::Request {
        self.io.request()
    }
    pub(crate) fn fail(&mut self, error: impl std::fmt::Display) {
        self.io.fail(error);
    }
}

#[derive(Clone, Copy)]
pub(super) enum Stage {
    Reserved,
    Offered { sequence: u64 },
    Granted { sequence: u64 },
}

pub(crate) struct LocalLoan {
    pub(super) bank: Arc<RootCreditBank>,
    coordinator: Arc<PrimaryLoan>,
    index: usize,
    loan: Attempt,
    original_cpu: wire::CpuOriginal,
    cancelled: Arc<AtomicBool>,
    settled: AtomicBool,
}
impl RootCreditBank {
    pub(crate) fn try_coordinator_local(
        self: &Arc<Self>,
        coordinator: &Arc<PrimaryLoan>,
    ) -> io::Result<Option<Arc<LocalLoan>>> {
        if !coordinator.belongs_to(self)
            || coordinator.coordinator_worker
            || coordinator.coordinator.is_none()
        {
            return Err(invalid("local operation has no SAME original coordinator"));
        }
        let mut state = self.lock()?;
        state.usable()?;
        let Some(Occupancy::Primary {
            loan,
            member: Some(member),
        }) = state.slots[coordinator.index]
        else {
            return Err(invalid("local operation coordinator is unbound"));
        };
        if loan != coordinator.loan
            || !matches!(member.purpose, Purpose::Coordinator)
            || !member.granted
            || member.host_returned
            || member.local_retired
            || !state.parked
            || state.local_cancel.is_some()
        {
            return Err(invalid(
                "local operation lacks active original coordinator/phase",
            ));
        }
        if state.occupied() != 1 || (self.live_limit)(1).min(self.ceiling) < 2 {
            return Ok(None);
        }
        let index = state
            .slots
            .iter()
            .position(Option::is_none)
            .ok_or_else(|| invalid("local operation has no distinct original"))?;
        if index == coordinator.index {
            return Err(invalid(
                "local operation cannot use executing coordinator unit",
            ));
        }
        let loan = state.next_loan()?;
        if loan == member.attempt || loan == self.root_attempt {
            return Err(invalid("local operation identifier collides with original"));
        }
        let cancelled = Arc::new(AtomicBool::new(false));
        state.slots[index] = Some(Occupancy::Local {
            loan,
            _coordinator: member.attempt,
            stage: Stage::Reserved,
        });
        state.local_cancel = Some((member.attempt, cancelled.clone()));
        Ok(Some(Arc::new(LocalLoan {
            bank: self.clone(),
            coordinator: coordinator.clone(),
            index,
            loan,
            original_cpu: wire::CpuOriginal {
                loan,
                slot: state.originals[index].lease.slot(),
                backing: state.originals[index].backing,
            },
            cancelled,
            settled: AtomicBool::new(false),
        })))
    }
}
impl LocalLoan {
    pub(crate) fn cpu(&self) -> wire::CpuOriginal {
        self.original_cpu
    }
    pub(crate) fn cancellation(&self) -> Arc<AtomicBool> {
        self.cancelled.clone()
    }
    pub(crate) fn key(&self, sequence: u64) -> io::Result<wire::Key> {
        let artifact = self
            .coordinator
            .coordinator
            .as_ref()
            .ok_or_else(|| invalid("local operation lost coordinator artifact"))?;
        let phase = artifact.phase();
        Ok(wire::Key {
            root_attempt: self.bank.root_attempt,
            invocation_sha256: self.bank.invocation_sha256,
            sequence,
            phase: phase.nonce,
            ordinal: phase.ordinal,
            coordinator: self
                .coordinator
                .coordinator_attempt()
                .ok_or_else(|| invalid("local operation coordinator attempt missing"))?,
            operation: self.loan,
        })
    }
    fn matches(&self, request: &wire::Request) -> io::Result<()> {
        if request.key != self.key(request.key.sequence)?
            || !matches!(&request.operation,wire::Operation::Begin(begin)if begin.cpu==self.cpu())
        {
            return Err(invalid(
                "local operation differs from SAME reserved original",
            ));
        }
        Ok(())
    }
    pub(crate) fn offered(&self, request: &wire::Request) -> io::Result<()> {
        self.matches(request)?;
        let mut state = self.bank.lock()?;
        state.usable()?;
        if self.settled.load(Ordering::Acquire)
            || !matches!(state.slots[self.index],Some(Occupancy::Local{loan,stage:Stage::Reserved,..})if loan==self.loan)
        {
            return Err(invalid("local operation original was already offered"));
        }
        state.slots[self.index] = Some(Occupancy::Local {
            loan: self.loan,
            _coordinator: request.key.coordinator,
            stage: Stage::Offered {
                sequence: request.key.sequence,
            },
        });
        Ok(())
    }
    pub(crate) fn admitted(&self, scope: &LocalIoScope) -> io::Result<()> {
        let request = scope.request();
        self.matches(request)?;
        let mut state = self.bank.lock()?;
        state.usable()?;
        if !matches!(state.slots[self.index],Some(Occupancy::Local{loan,stage:Stage::Offered{sequence},..})if loan==self.loan&&sequence==request.key.sequence)
        {
            return Err(invalid(
                "native local admission differs from original offer",
            ));
        }
        state.slots[self.index] = Some(Occupancy::Local {
            loan: self.loan,
            _coordinator: request.key.coordinator,
            stage: Stage::Granted {
                sequence: request.key.sequence,
            },
        });
        Ok(())
    }
    pub(crate) fn not_admitted(&self, receipt: &LocalNotAdmitted) -> io::Result<()> {
        let request = receipt.request();
        self.matches(request)?;
        let mut state = self.bank.lock()?;
        state.usable()?;
        if !matches!(state.slots[self.index],Some(Occupancy::Local{loan,stage:Stage::Offered{sequence},..})if loan==self.loan&&sequence==request.key.sequence)
        {
            return Err(invalid(
                "no-admission receipt differs from actual offered original",
            ));
        }
        state.slots[self.index] = None;
        state.local_cancel = None;
        self.settled.store(true, Ordering::Release);
        Ok(())
    }
    pub(crate) fn completed(&self, receipt: &CompletedLocalOperation) -> io::Result<()> {
        let request = receipt.begin();
        self.matches(request)?;
        let mut state = self.bank.lock()?;
        state.usable()?;
        if !matches!(state.slots[self.index],Some(Occupancy::Local{loan,stage:Stage::Granted{sequence},..})if loan==self.loan&&sequence==request.key.sequence)
        {
            return Err(invalid(
                "local completion differs from SAME native admitted original",
            ));
        }
        state.slots[self.index] = None;
        state.local_cancel = None;
        self.settled.store(true, Ordering::Release);
        Ok(())
    }
}
impl Drop for LocalLoan {
    fn drop(&mut self) {
        if self.settled.load(Ordering::Acquire) {
            return;
        }
        if let Ok(mut state) = self.bank.state.lock() {
            if matches!(state.slots[self.index],Some(Occupancy::Local{loan,stage:Stage::Reserved,..})if loan==self.loan)
            {
                state.slots[self.index] = None;
                state.local_cancel = None;
                return;
            }
            state.poisoned = true;
        }
        super::super::abort_unknown()
    }
}
