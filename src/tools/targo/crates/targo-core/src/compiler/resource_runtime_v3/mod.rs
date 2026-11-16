//! Retained-host compiler dispatch: one actual global unit and the original
//! shared GNU transport per runnable command. No fixed foreign-phase fallback.
use super::{
    BuildContext,
    resource_descriptors::{DescriptorBudget, RootPermit},
    resource_fifo::{ForeignGnuEscrow, PrivateFifo},
};
use crate::{
    resource_v3::{self, Startup},
    util::CargoResult,
};
use anyhow::{Context as _, bail};
use cargo_util::{Jobserver, ProcessBuilder};
use std::sync::{
    Arc, Mutex,
    atomic::{AtomicBool, Ordering},
};
use trust_build_cpu::{Lease, process_cpu};
pub(in crate::compiler) mod native_coordinator;
static PAIRED_RUNTIME_CREATED: AtomicBool = AtomicBool::new(false);

pub(super) struct ResourceRuntime {
    startup: Arc<Startup>,
    jobserver: Jobserver,
    _fifo: Option<Arc<PrivateFifo>>,
    owner: trust_build_cpu::Owner,
    descriptors: Arc<DescriptorBudget>,
    foreign: Mutex<Option<Arc<ForeignPhase>>>,
    outputs: Mutex<std::collections::BTreeMap<std::path::PathBuf, OutputCustody>>,
}
struct OutputCustody {
    capsule: Arc<super::build_runner::OriginalOutputLeases>,
    retained: Arc<trust_resource_controller::client::workload::RetainedOutputLocks>,
}

struct ForeignPhase {
    phase: resource_v3::workload::bank::broker::Phase,
    artifacts: Vec<Arc<resource_v3::workload::bank::broker::RegisteredArtifact>>,
    active: Arc<AtomicBool>,
    busy: Arc<AtomicBool>,
}

struct BorrowRelease(Arc<AtomicBool>);
impl Drop for BorrowRelease {
    fn drop(&mut self) {
        self.0.store(false, Ordering::Release);
    }
}

pub(super) struct RootContext {
    runtime: Arc<ResourceRuntime>,
    lease: Option<Arc<Lease>>,
    workload_loan: Option<Arc<resource_v3::workload::bank::PrimaryLoan>>,
    foreign: Option<Arc<ForeignPhase>>,
    // Only return the implicit unit after all per-command state is dropped.
    _borrowed: Option<BorrowRelease>,
    // LAST: retired captures keep descriptor charges after releasing only
    // their active-member slot through the actual native closure barrier.
    _descriptors: Mutex<DescriptorCustody>,
}
enum DescriptorCustody {
    Active(Option<RootPermit>),
    Retained {
        _permit: trust_resource_controller::descriptors::OriginalInputPermit,
    },
}

impl ResourceRuntime {
    pub(super) fn new(bcx: &BuildContext<'_, '_>) -> CargoResult<Arc<Self>> {
        let startup = resource_v3::current().context("native v3 has no authenticated startup")?;
        if let Some(candidate) = &startup.candidate {
            candidate.check()?;
            anyhow::ensure!(
                bcx.jobs() == 1,
                "candidate coordinator requires serial native work"
            );
        }
        if (startup.paired_invocation.is_some() || startup.native_job_plan.is_some())
            && PAIRED_RUNTIME_CREATED.swap(true, Ordering::AcqRel)
        {
            bail!(
                "sequential native graphs must continue the original runtime; a second GNU pool is refused"
            );
        }
        let ceiling = bcx.jobs().min(startup.local_ceiling);
        if ceiling == 0 {
            bail!("native v3 has no permitted local workers");
        }
        let descriptors = match &startup.descriptor_budget {
            Some(original) => original.clone(),
            None if startup.workload_process.is_none() => {
                DescriptorBudget::prepare(ceiling as usize)?;
                DescriptorBudget::new(ceiling as usize, 0)?
            }
            None => bail!("workload runtime lost original pre-materialization descriptor budget"),
        };
        let inherited = bcx.gctx.jobserver_from_env()?;
        if startup.original_root && inherited.is_some() {
            bail!("original native v3 root cannot import an unrelated ambient GNU pool");
        }
        let mut initial_escrow = None;
        let (jobserver, fifo) = match inherited {
            Some(inherited) if startup.candidate.is_some() => {
                // The candidate continues the actual Host-inherited transport.
                // No anonymous-pipe fallback or replacement FIFO is created.
                // Host matches these SAME descriptions on compiler delivery.
                inherited.client().transport_witnesses()?;
                (inherited.clone(), None)
            }
            Some(inherited) => {
                super::resource_inherited::scheduler(inherited, Some(&startup.implicit))?
            }
            None if startup.original_root => {
                let fifo = if startup
                    .workload_bank
                    .as_ref()
                    .map(|bank| bank.initial_pending())
                    .transpose()?
                    .unwrap_or(false)
                {
                    let (fifo, escrow) = PrivateFifo::new_captive(ceiling)?;
                    initial_escrow = Some(escrow);
                    fifo
                } else {
                    Arc::new(PrivateFifo::new(ceiling)?)
                };
                (fifo.jobserver.clone(), Some(fifo))
            }
            None => bail!("native borrowed member lost its original shared GNU transport"),
        };
        let owner = process_cpu::read(std::process::id())
            .context("native v3 dispatch cannot identify its CPU owner")?
            .owner;
        if let (Some(fifo), Some(control)) = (&fifo, &startup.workload_control) {
            let original = control
                .lock()
                .map_err(|_| anyhow::anyhow!("original workload control coordinator poisoned"))?;
            let broker = original
                .as_ref()
                .context("original workload control already settled")?;
            match initial_escrow.take() {
                Some(escrow) => broker.bind_initial_fifo(fifo.clone(), escrow)?,
                None => broker.bind_fifo(fifo.clone())?,
            }
        }
        Ok(Arc::new(Self {
            startup,
            jobserver,
            _fifo: fifo,
            owner,
            descriptors,
            foreign: Mutex::new(None),
            outputs: Mutex::new(std::collections::BTreeMap::new()),
        }))
    }
    pub(super) fn jobserver(&self) -> Jobserver {
        self.jobserver.clone()
    }

    pub(super) fn retain_workload_outputs(
        &self,
        capsule: Arc<super::build_runner::OriginalOutputLeases>,
        root: &std::path::Path,
    ) -> CargoResult<()> {
        let mut retained = self
            .outputs
            .lock()
            .map_err(|_| anyhow::anyhow!("original output capsule poisoned"))?;
        let existing = if let Some(original) = retained.get(root) {
            anyhow::ensure!(
                Arc::ptr_eq(&original.capsule, &capsule),
                "another graph cannot replace original output guards"
            );
            original.capsule.validate(root)?;
            if self.startup.native_job_plan.is_none() {
                return Ok(());
            }
            Some(original.retained.clone())
        } else {
            None
        };
        if self.startup.native_job_plan.is_some() {
            self.startup
                .native_outputs
                .get()
                .context("native output registry missing")?
                .require_registered(root, &capsule)?;
        } else {
            anyhow::ensure!(
                retained.is_empty(),
                "fixed workload cannot register another output root"
            );
        }
        let bank = self
            .startup
            .workload_bank
            .as_ref()
            .context("output custody has no original workload bank")?;
        let control = self
            .startup
            .workload_control
            .as_ref()
            .context("output custody has no original workload control")?;
        let mut original = control
            .lock()
            .map_err(|_| anyhow::anyhow!("original workload control coordinator poisoned"))?;
        let broker = original
            .as_mut()
            .context("original workload control already settled")?;
        anyhow::ensure!(
            broker.uses_bank(bank),
            "output custody uses a different original native bank"
        );
        if let Some(receipt) = existing {
            broker.select_output_locks(receipt)?;
        } else {
            let receipt = Arc::new(broker.retain_output_locks(capsule.clone(), root.to_owned())?);
            retained.insert(
                root.to_owned(),
                OutputCustody {
                    capsule,
                    retained: receipt,
                },
            );
        }
        Ok(())
    }

    /// Called after the original queue invocation returns through its actual
    /// scoped join (including known failure). Park first; then require every
    /// actual local context, host/bank loan and foreign phase to have retired.
    /// Acquiring ALL original GNU tokens is custody, not a numeric idle claim.
    pub(super) fn suspend_paired_graph(
        &self,
        outputs: Option<&Arc<super::build_runner::OriginalOutputLeases>>,
        root: &std::path::Path,
    ) -> CargoResult<ForeignGnuEscrow> {
        let plan = self
            .startup
            .paired_invocation
            .as_ref()
            .context("graph continuation requires actual paired startup")?;
        let current = resource_v3::paired::require(plan)?;
        anyhow::ensure!(
            std::ptr::eq(current.as_ref(), self.startup.as_ref()),
            "continuation selected another original startup"
        );
        let bank = self
            .startup
            .workload_bank
            .as_ref()
            .context("continuation lost original bank")?;
        let registered = self
            .outputs
            .lock()
            .map_err(|_| anyhow::anyhow!("original output capsule poisoned"))?;
        match (registered.get(root), outputs) {
            (Some(held), Some(outputs)) => {
                anyhow::ensure!(
                    Arc::ptr_eq(&held.capsule, outputs),
                    "continuation substituted original output guards"
                );
                outputs.validate(root)?;
            }
            // A known preparation failure before any Layout/Compiler binding
            // can still continue into independent consumer coverage. No
            // missing/failed produced output becomes eligible here.
            (None, None) => anyhow::ensure!(
                bank.before_compilation()?,
                "missing original output owner after compiler delivery"
            ),
            _ => bail!("continuation lost actual registered original output owner"),
        }
        drop(registered);
        bank.park()?;
        anyhow::ensure!(
            self.descriptors.idle()
                && self
                    .foreign
                    .lock()
                    .map_err(|_| anyhow::anyhow!("original phase poisoned"))?
                    .is_none(),
            "continuation precedes actual local/foreign retirement"
        );
        let deadline = self
            .startup
            .workload_process
            .as_ref()
            .context("continuation lost original process")?
            .deadline;
        loop {
            anyhow::ensure!(
                std::time::Instant::now() < deadline,
                "continuation exceeded original root deadline"
            );
            resource_v3::paired::require(plan)?;
            if let Some(escrow) = self.try_workload_escrow()? {
                return Ok(escrow);
            }
            std::thread::sleep(std::time::Duration::from_millis(5));
        }
    }

    pub(super) fn resume_paired_graph(&self, escrow: ForeignGnuEscrow) -> CargoResult<()> {
        let plan = self
            .startup
            .paired_invocation
            .as_ref()
            .context("continuation requires original paired startup")?;
        resource_v3::paired::require(plan)?;
        anyhow::ensure!(
            self.descriptors.idle()
                && self
                    .foreign
                    .lock()
                    .map_err(|_| anyhow::anyhow!("original phase poisoned"))?
                    .is_none(),
            "next graph resumed before original contexts retired"
        );
        let fifo = self
            ._fifo
            .as_ref()
            .context("continuation lost original FIFO")?;
        anyhow::ensure!(
            escrow.belongs_to(fifo),
            "continuation substituted GNU custody"
        );
        let bank = self
            .startup
            .workload_bank
            .as_ref()
            .context("continuation lost original bank")?;
        anyhow::ensure!(
            bank.is_drained()?,
            "continuation precedes original positive loan returns"
        );
        // This escrow was never offered to a foreign member. Returning its
        // actual tokens to SAME FIFO precedes reopening the SAME bank.
        drop(escrow);
        bank.resume()?;
        Ok(())
    }

    pub(super) fn validate_paired_graph(&self, bcx: &BuildContext<'_, '_>) -> CargoResult<()> {
        let plan = self
            .startup
            .paired_invocation
            .as_ref()
            .context("continued graph requires original paired startup")?;
        resource_v3::paired::require(plan)?;
        let fifo = self
            ._fifo
            .as_ref()
            .context("continued graph lost original FIFO")?;
        anyhow::ensure!(
            bcx.jobs().min(self.startup.local_ceiling) == fifo.ceiling(),
            "next graph changed original local GNU dispatch width"
        );
        Ok(())
    }

    pub(super) fn suspend_native_job_graph(&self) -> CargoResult<ForeignGnuEscrow> {
        let plan = self
            .startup
            .native_job_plan
            .as_ref()
            .context("general continuation lacks original106 startup")?;
        let actual = resource_v3::native_job::require(plan)?;
        anyhow::ensure!(
            Arc::ptr_eq(&actual, &self.startup),
            "native continuation replaced Startup"
        );
        let registry = self
            .startup
            .native_outputs
            .get()
            .context("native continuation lacks original output registry")?;
        for (root, owner) in self
            .outputs
            .lock()
            .map_err(|_| anyhow::anyhow!("native output registry poisoned"))?
            .iter()
        {
            registry.require_registered(root, &owner.capsule)?;
        }
        let bank = self
            .startup
            .workload_bank
            .as_ref()
            .context("native continuation lost original bank")?;
        bank.park()?;
        anyhow::ensure!(
            self.descriptors.idle()
                && self
                    .foreign
                    .lock()
                    .map_err(|_| anyhow::anyhow!("original phase poisoned"))?
                    .is_none(),
            "native continuation precedes actual local/foreign retirement"
        );
        let deadline = self
            .startup
            .workload_process
            .as_ref()
            .context("native continuation lost original process")?
            .deadline;
        loop {
            anyhow::ensure!(
                std::time::Instant::now() < deadline,
                "native continuation exceeded original Root deadline"
            );
            resource_v3::native_job::require(plan)?;
            if let Some(escrow) = self.try_workload_escrow()? {
                return Ok(escrow);
            }
            std::thread::sleep(std::time::Duration::from_millis(5));
        }
    }
    pub(super) fn resume_native_job_graph(&self, escrow: ForeignGnuEscrow) -> CargoResult<()> {
        let plan = self
            .startup
            .native_job_plan
            .as_ref()
            .context("general continuation lacks original106 startup")?;
        resource_v3::native_job::require(plan)?;
        anyhow::ensure!(
            self.descriptors.idle()
                && self
                    .foreign
                    .lock()
                    .map_err(|_| anyhow::anyhow!("original phase poisoned"))?
                    .is_none(),
            "native resume precedes actual local/foreign retirement"
        );
        let fifo = self
            ._fifo
            .as_ref()
            .context("native continuation lost original FIFO")?;
        anyhow::ensure!(
            escrow.belongs_to(fifo),
            "native continuation substituted GNU custody"
        );
        let bank = self
            .startup
            .workload_bank
            .as_ref()
            .context("native continuation lost original bank")?;
        anyhow::ensure!(
            bank.is_drained()?,
            "native continuation precedes positive original loan returns"
        );
        drop(escrow);
        bank.resume()?;
        Ok(())
    }
    pub(super) fn validate_native_job_graph(
        &self,
        bcx: &BuildContext<'_, '_>,
        inputs: &Arc<crate::ops::cargo_test::workload::Inputs>,
    ) -> CargoResult<()> {
        let plan = self
            .startup
            .native_job_plan
            .as_ref()
            .context("general continuation lacks original106 startup")?;
        resource_v3::native_job::require(plan)?;
        anyhow::ensure!(
            inputs
                .native_plan()
                .is_some_and(|held| Arc::ptr_eq(held, plan)),
            "continued native graph substituted original plan"
        );
        inputs.validate_target(&bcx.ws.target_dir().into_path_unlocked())?;
        let fifo = self
            ._fifo
            .as_ref()
            .context("native continuation lost original FIFO")?;
        anyhow::ensure!(
            bcx.jobs().min(self.startup.local_ceiling) == fifo.ceiling(),
            "native continuation changed original GNU width"
        );
        Ok(())
    }
    /// Park original queue admission BEFORE joining current worker handles.
    /// This does not claim their retirement or grant a foreign phase.
    pub(super) fn park_workload(&self) -> CargoResult<()> {
        let bank = self
            .startup
            .workload_bank
            .as_ref()
            .context("foreign phase has no original workload bank")?;
        bank.park()?;
        Ok(())
    }

    /// Actual GNU custody follows positive local AND host bank returns. The
    /// coordinator must additionally join current scoped compiler writers;
    /// host Enter independently checks the original native members/loans.
    pub(super) fn try_workload_escrow(&self) -> CargoResult<Option<ForeignGnuEscrow>> {
        let bank = self
            .startup
            .workload_bank
            .as_ref()
            .context("foreign phase has no original workload bank")?;
        if !bank.is_drained()? {
            return Ok(None);
        }
        let fifo = self
            ._fifo
            .as_ref()
            .filter(|_| self.startup.original_root)
            .context("foreign phase lost its original locally owned GNU FIFO")?;
        Ok(fifo.try_escrow()?)
    }
    pub(super) fn try_root(
        self: &Arc<Self>,
        external_serial: bool,
    ) -> CargoResult<Option<Arc<RootContext>>> {
        let Some(descriptors) = self.descriptors.try_root()? else {
            return Ok(None);
        };
        if external_serial {
            anyhow::ensure!(
                self.startup.candidate.is_none(),
                "candidate cannot launch foreign phases"
            );
            let foreign = self
                .foreign
                .lock()
                .map_err(|_| anyhow::anyhow!("original foreign phase owner poisoned"))?
                .clone()
                .context("native v3 foreign phases require their actual retained phase owner")?;
            anyhow::ensure!(
                foreign.active.load(Ordering::Acquire),
                "original foreign phase already retired"
            );
            if foreign
                .busy
                .compare_exchange(false, true, Ordering::AcqRel, Ordering::Acquire)
                .is_err()
            {
                return Ok(None);
            }
            let borrowed = BorrowRelease(foreign.busy.clone());
            return Ok(Some(Arc::new(RootContext {
                runtime: self.clone(),
                lease: None,
                workload_loan: None,
                foreign: Some(foreign),
                _borrowed: Some(borrowed),
                _descriptors: Mutex::new(DescriptorCustody::Active(Some(descriptors))),
            })));
        }
        let (lease, borrowed, workload_loan) = if let Some(bank) = &self.startup.workload_bank {
            let Some(loan) = bank.try_primary()? else {
                return Ok(None);
            };
            (loan.lease(), None, Some(loan))
        } else if self
            .startup
            .implicit_busy
            .compare_exchange(false, true, Ordering::AcqRel, Ordering::Acquire)
            .is_ok()
        {
            let release = BorrowRelease(self.startup.implicit_busy.clone());
            if self.startup.policy.limit() == 0 {
                return Ok(None);
            }
            (self.startup.implicit.clone(), Some(release), None)
        } else {
            // A busy candidate's original primary is lent to its one actual
            // child. Waiting never becomes permission for fresh admission.
            if self.startup.candidate.is_some() {
                return Ok(None);
            }
            let Some(lease) = self
                .startup
                .debt
                .try_acquire_observed(self.owner, |held| self.startup.policy.limit_for(held))?
            else {
                return Ok(None);
            };
            (Arc::new(lease), None, None)
        };
        Ok(Some(Arc::new(RootContext {
            runtime: self.clone(),
            lease: Some(lease),
            workload_loan,
            foreign: None,
            _borrowed: borrowed,
            _descriptors: Mutex::new(DescriptorCustody::Active(Some(descriptors))),
        })))
    }

    /// Called by the coordinator only after the final compiler graph was
    /// finalized and its actual worker handles joined. Enter additionally
    /// requires the SAME parked bank, positive host/local loan returns, and
    /// actual escrow of this runtime's original GNU descriptions/tokens.
    pub(super) fn enter_workload_harnesses(
        &self,
        outputs: &crate::ops::cargo_test::workload::OwnedOutputs,
    ) -> CargoResult<()> {
        self.enter_workload_foreign(
            trust_resource_controller::workload::host::phase::Kind::Harnesses,
            outputs.native_outputs()?,
        )
    }

    pub(super) fn enter_workload_build_script(
        &self,
        original: Arc<crate::ops::cargo_test::workload::NativeOutput>,
    ) -> CargoResult<()> {
        self.enter_workload_foreign(
            trust_resource_controller::workload::host::phase::Kind::BuildScript,
            vec![original],
        )
    }

    fn enter_workload_foreign(
        &self,
        kind: trust_resource_controller::workload::host::phase::Kind,
        originals: Vec<Arc<crate::ops::cargo_test::workload::NativeOutput>>,
    ) -> CargoResult<()> {
        let inputs = self
            .startup
            .workload_process
            .as_ref()
            .context("foreign phase has no original process inputs")?;
        let mut active = self
            .foreign
            .lock()
            .map_err(|_| anyhow::anyhow!("original foreign phase owner poisoned"))?;
        anyhow::ensure!(active.is_none(), "original foreign phase entered twice");
        self.park_workload()?;
        let control = self
            .startup
            .workload_control
            .as_ref()
            .context("foreign phase lost original control")?;
        let mut control = control
            .lock()
            .map_err(|_| anyhow::anyhow!("original workload coordinator poisoned"))?;
        let broker = control
            .as_mut()
            .context("original workload control already settled")?;
        let nonce = resource_v3::call_attempt(self.startup.query.binding.root_attempt)?;
        let phase = loop {
            anyhow::ensure!(
                std::time::Instant::now() < inputs.deadline,
                "original foreign phase timed out before actual loan/GNU drain"
            );
            if let Some(phase) = broker.try_enter_owned(nonce, kind)? {
                break phase;
            }
            std::thread::sleep(
                std::time::Duration::from_millis(5).min(
                    inputs
                        .deadline
                        .saturating_duration_since(std::time::Instant::now()),
                ),
            );
        };
        let mut artifacts = Vec::new();
        for original in originals {
            match broker.register_output(phase, original) {
                Ok(registered) => artifacts.push(Arc::new(registered)),
                Err(error) => {
                    // A known registration refusal still needs actual same-
                    // phase Leave. Unknown control delivery aborts in broker.
                    broker.leave(phase)?;
                    return Err(error.into());
                }
            }
        }
        *active = Some(Arc::new(ForeignPhase {
            phase,
            artifacts,
            active: Arc::new(AtomicBool::new(true)),
            busy: Arc::new(AtomicBool::new(false)),
        }));
        Ok(())
    }

    /// Only after the queue's scoped test workers have actually joined. Leave
    /// returns the SAME GNU tokens after positive host member/phase retirement;
    /// it is separate from later original root/cohort settlement and EOF.
    pub(super) fn finish_workload_harnesses(&self) -> CargoResult<()> {
        self.finish_workload_foreign(
            trust_resource_controller::workload::host::phase::Kind::Harnesses,
        )
    }
    pub(super) fn finish_workload_build_script(&self) -> CargoResult<()> {
        self.finish_workload_foreign(
            trust_resource_controller::workload::host::phase::Kind::BuildScript,
        )
    }
    fn finish_workload_foreign(
        &self,
        kind: trust_resource_controller::workload::host::phase::Kind,
    ) -> CargoResult<()> {
        let mut owner = self
            .foreign
            .lock()
            .map_err(|_| anyhow::anyhow!("original foreign phase owner poisoned"))?;
        let Some(active) = owner.as_ref() else {
            anyhow::ensure!(
                kind == trust_resource_controller::workload::host::phase::Kind::Harnesses,
                "script finalization has no actual original foreign phase"
            );
            return Ok(());
        };
        anyhow::ensure!(
            active.phase.kind == kind,
            "foreign phase finalization kind differs from its original owner"
        );
        anyhow::ensure!(
            !active.busy.load(Ordering::Acquire),
            "foreign phase finalized before original action owners retired"
        );
        let control = self
            .startup
            .workload_control
            .as_ref()
            .context("foreign phase lost original control")?;
        let mut control = control
            .lock()
            .map_err(|_| anyhow::anyhow!("original workload coordinator poisoned"))?;
        let result = control
            .as_mut()
            .context("original workload control already settled")?
            .leave(active.phase);
        active.active.store(false, Ordering::Release);
        owner.take();
        result.map_err(Into::into)
    }
}

impl RootContext {
    pub(super) fn capture_verification(
        self: &Arc<Self>,
        mut command: ProcessBuilder,
        limits: cargo_util::StreamingOutputLimits,
    ) -> CargoResult<resource_v3::NativeVerificationCapture> {
        let startup = self.verification_preparation()?;
        // The maintained constructor owns native flags and SAME original GNU;
        // the caller supplies no transport exemption or alternate executor.
        self.configure(&mut command, true)?;
        let lease = self
            .lease
            .as_ref()
            .context("verification capture lost actual original lease")?
            .clone();
        let loan = self
            .workload_loan
            .as_ref()
            .context("verification capture lost original loan")?
            .clone();
        Ok(resource_v3::verification_capture(
            startup,
            lease,
            self.runtime.jobserver.clone(),
            self.clone(),
            loan,
            &command,
            limits,
        ))
    }
    pub(super) fn retire_verification(
        self: &Arc<Self>,
        capture: &resource_v3::NativeVerificationCapture,
    ) -> CargoResult<()> {
        let loan = self
            .workload_loan
            .as_ref()
            .context("verification retirement lost original loan")?;
        let owner: Arc<dyn Send + Sync> = self.clone();
        capture.require_verification_retirement(&self.runtime.startup, loan, &owner)?;
        let mut descriptors = self
            ._descriptors
            .lock()
            .map_err(|_| anyhow::anyhow!("verification descriptor custody poisoned"))?;
        let DescriptorCustody::Active(original) = &mut *descriptors else {
            anyhow::bail!("verification context retirement repeated")
        };
        let original = original
            .take()
            .context("verification descriptor original already moved")?;
        // SAFETY: the SAME sealed actual capture above proved native child/
        // helper closure, physical EOF and actual local/Host return. Keep the
        // SAME FD envelope in this retained context until all captures close.
        let retained = unsafe { original.into_retained() };
        *descriptors = DescriptorCustody::Retained { _permit: retained };
        Ok(())
    }
    /// Read-only preparation from the SAME genuine still-unbound Root loan.
    /// Identity custody and a command DTO cannot create this resource scope.
    pub(super) fn verification_preparation(&self) -> CargoResult<Arc<Startup>> {
        anyhow::ensure!(
            matches!(
                &*self
                    ._descriptors
                    .lock()
                    .map_err(|_| anyhow::anyhow!("verification descriptor custody poisoned"))?,
                DescriptorCustody::Active(Some(_))
            ),
            "retired verification context cannot authorize new preparation"
        );
        let startup =
            resource_v3::current().context("verification preparation has no actual Startup")?;
        anyhow::ensure!(
            Arc::ptr_eq(&startup, &self.runtime.startup)
                && startup.original_root
                && self.foreign.is_none(),
            "verification preparation replaced its original nonforeign Root context"
        );
        if let Some(plan) = &startup.native_job_plan {
            let actual = resource_v3::native_job::require(plan)?;
            anyhow::ensure!(
                Arc::ptr_eq(&actual, &startup),
                "verification preparation replaced actual native-job scope"
            );
        } else {
            let plan = startup
                .paired_invocation
                .as_ref()
                .context("verification preparation lacks actual paired/native scope")?;
            let actual = resource_v3::paired::require(plan)?;
            anyhow::ensure!(
                Arc::ptr_eq(&actual, &startup),
                "verification preparation replaced actual paired scope"
            );
        }
        let bank = startup
            .workload_bank
            .as_ref()
            .context("verification preparation lost original bank")?;
        let loan = self
            .workload_loan
            .as_ref()
            .context("verification preparation lost actual reserved Root loan")?;
        let lease = self
            .lease
            .as_ref()
            .context("verification preparation lost same original lease")?;
        anyhow::ensure!(
            loan.belongs_to(bank),
            "verification preparation substituted another original bank"
        );
        loan.require_preparation(lease)?;
        let process = startup
            .workload_process
            .as_ref()
            .context("verification preparation lost actual process lifetime")?;
        anyhow::ensure!(
            std::time::Instant::now() < process.deadline
                && !process.cancelled.load(Ordering::Acquire)
                && !process.poisoned.load(Ordering::Acquire),
            "verification preparation original lifetime is stopped or expired"
        );
        Ok(startup)
    }
    pub(super) fn completed_workload_compiler(&self) -> CargoResult<Option<[u8; 16]>> {
        self.workload_loan
            .as_ref()
            .map(|loan| loan.successful_job_compiler())
            .transpose()
            .map(Option::flatten)
            .map_err(Into::into)
    }

    pub(super) fn configure(
        self: &Arc<Self>,
        command: &mut ProcessBuilder,
        compiler: bool,
    ) -> CargoResult<()> {
        if !compiler {
            let foreign = self
                .foreign
                .as_ref()
                .context("native v3 cannot dispatch an unqualified external phase")?;
            anyhow::ensure!(
                foreign.active.load(Ordering::Acquire),
                "original native foreign phase already retired"
            );
            let artifact = foreign
                .artifacts
                .iter()
                .find(|artifact| {
                    artifact.original().image().program().as_os_str() == command.get_program()
                })
                .context("native action is not an actual registered original UnitOutput")?;
            artifact.validate(
                self.runtime
                    .startup
                    .workload_process
                    .as_ref()
                    .context("missing original workload inputs")?
                    .deadline,
            )?;
            command.process_executor(resource_v3::workload::produced::executor(
                self.runtime.startup.clone(),
                artifact.clone(),
                foreign.active.clone(),
            ));
            return Ok(());
        }
        anyhow::ensure!(
            self.foreign.is_none(),
            "native foreign phase cannot become a compiler loan"
        );
        finalize_compiler_command(command, &self.runtime.jobserver);
        command.process_executor(resource_v3::compiler_executor(
            self.runtime.startup.clone(),
            self.lease
                .clone()
                .context("native compiler lost its original actual CPU lease")?,
            self.runtime.jobserver.clone(),
            self.clone(),
            self.workload_loan.clone(),
        ));
        Ok(())
    }
}

/// The SAME ordinary native command finalization, before dispatch ownership.
/// This carries only the already supplied original GNU scheduler. It cannot
/// create a CPU loan, a Root context or a native process executor.
pub(super) fn finalize_compiler_command(command: &mut ProcessBuilder, jobserver: &Jobserver) {
    command.arg("-Zunstable-options");
    command.inherit_jobserver(jobserver);
}
