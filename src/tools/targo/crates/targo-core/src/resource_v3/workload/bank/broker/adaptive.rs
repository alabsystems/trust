// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

//! The sole original broker retains actual GNU escrow through every phase.
use super::*;
use trust_resource_controller::client::workload::{PartialBank, PartialBankReply};

enum Step {
    Returning,
    Running,
    Foreign,
}
struct Active {
    owner: super::super::RootPartialPhase,
    step: Step,
}
struct BankService<'a>(&'a RootCreditBank);
impl PartialBank for BankService<'_> {
    fn reserve_pending_keeper(
        &mut self,
    ) -> io::Result<trust_resource_controller::descriptors::OriginalInputPermit> {
        self.0
            .descriptor_budget
            .get()
            .ok_or_else(|| invalid("original descriptor budget unavailable"))?
            .reserve_original_inputs(3)
    }
    fn retain_pending_keeper(
        &mut self,
        owner: Arc<trust_resource_controller::client::workload::AuthenticatedPendingKeeper>,
    ) -> io::Result<()> {
        self.0.retain_pending_keeper(owner)
    }
    fn service(
        &mut self,
        request: &bank::Request,
        sink: &mut PartialBankReply<'_>,
    ) -> io::Result<()> {
        let answer = self.0.handle(request)?;
        sink.send(
            &answer.reply,
            answer.original.as_ref().map(|lease| lease.as_fd()),
        )
    }
}
pub(super) fn poll_owned_bank(
    bank: &RootCreditBank,
    control: &mut WorkloadControl,
    deadline: Instant,
) -> io::Result<Option<bank::Request>> {
    control.poll_owned_bank_request(&mut BankService(bank), deadline)
}

pub(super) struct Owner {
    debt: Option<Arc<trust_build_cpu::ExternalDebt>>,
    fifo: Option<Arc<PrivateFifo>>,
    active: Option<Active>,
    auto: bool,
    full: Option<SyncSender<io::Result<()>>>,
    initial_escrow: Option<ForeignGnuEscrow>,
}
impl Owner {
    pub(super) fn owns_partial(&self) -> bool {
        self.active.is_some() || self.initial_escrow.is_some()
    }
    pub(super) fn full_escrow(&self) -> io::Result<Option<ForeignGnuEscrow>> {
        if self.owns_partial() {
            return Err(invalid("full GNU capture cannot replace partial owner"));
        }
        self.fifo
            .as_ref()
            .ok_or_else(|| invalid("original GNU binding missing"))?
            .try_escrow()
    }
    pub(super) fn park_current(&mut self) -> io::Result<bool> {
        let Some(active) = self.active.as_mut() else {
            return Ok(false);
        };
        if !matches!(active.step, Step::Running) {
            return Ok(false);
        }
        if !active.owner.park_current()? {
            return Ok(false);
        }
        active.step = Step::Foreign;
        Ok(true)
    }
    pub(super) fn current_descriptors(&self) -> io::Result<[BorrowedFd<'_>; 2]> {
        let active = self
            .active
            .as_ref()
            .ok_or_else(|| invalid("current phase owner missing"))?;
        if !matches!(active.step, Step::Foreign) {
            return Err(invalid("current phase was not parked"));
        }
        active.owner.current_descriptors()
    }
    pub(super) fn current_backing(&self) -> io::Result<trust_resource_controller::FileIdentity> {
        let active = self
            .active
            .as_ref()
            .ok_or_else(|| invalid("current phase owner missing"))?;
        if !matches!(active.step, Step::Foreign) {
            return Err(invalid("current phase was not parked"));
        }
        Ok(active.owner.current_backing())
    }
    pub(super) fn resume_current(&mut self) -> io::Result<()> {
        let Some(active) = self.active.as_mut() else {
            return Ok(());
        };
        if !matches!(active.step, Step::Foreign) {
            return Err(invalid("current phase was not parked"));
        }
        active.owner.resume_current()?;
        active.step = Step::Running;
        Ok(())
    }
    pub(super) fn retire_current(&mut self) -> io::Result<()> {
        let Some(active) = self.active.as_mut() else {
            return Ok(());
        };
        if !matches!(active.step, Step::Foreign) {
            return Err(invalid("final current phase was not parked"));
        }
        active.owner.retire_current()?;
        self.active.take();
        Ok(())
    }
    pub(super) fn new(debt: Option<Arc<trust_build_cpu::ExternalDebt>>) -> Self {
        Self {
            debt,
            fifo: None,
            active: None,
            auto: false,
            full: None,
            initial_escrow: None,
        }
    }
    pub(super) fn bind_initial(
        &mut self,
        bank: &RootCreditBank,
        fifo: Arc<PrivateFifo>,
        escrow: ForeignGnuEscrow,
    ) -> io::Result<()> {
        if self.fifo.is_some()
            || self.active.is_some()
            || self.initial_escrow.is_some()
            || !bank.initial_pending()?
            || !escrow.captive_original(&fifo)
            || fifo.ceiling() as usize > bank.original_width
        {
            return Err(invalid(
                "initial GNU custody differs from original first pair",
            ));
        }
        self.fifo = Some(fifo);
        self.initial_escrow = Some(escrow);
        Ok(())
    }
    pub(super) fn bind(&mut self, bank: &RootCreditBank, fifo: Arc<PrivateFifo>) -> io::Result<()> {
        if self.fifo.is_some()
            || self.active.is_some()
            || fifo.ceiling() as usize > bank.original_width
        {
            return Err(invalid(
                "adaptive runtime substituted its original GNU server",
            ));
        }
        self.fifo = Some(fifo);
        Ok(())
    }
    pub(super) fn allow(&mut self) {
        self.auto = true;
    }
    pub(super) fn require_full(&mut self, reply: SyncSender<io::Result<()>>) {
        if self.full.is_some() {
            super::super::super::abort_unknown();
        }
        self.auto = false;
        self.full = Some(reply);
    }
    pub(super) fn tick<C: Control>(
        &mut self,
        bank: &Arc<RootCreditBank>,
        control: &mut C,
        deadline: Instant,
    ) -> io::Result<()> {
        check_deadline(deadline);
        if let Some(escrow) = &self.initial_escrow {
            if !control.original_output_ready() {
                return Ok(());
            }
            let Some((phase, implicit)) = bank.initial_ready()? else {
                return Ok(());
            };
            if let Some(prepared) = control.prepare_initial(
                implicit,
                escrow.descriptors(),
                &mut BankService(bank),
                deadline,
            )? {
                if prepared.binding().2 != phase {
                    return Err(invalid(
                        "initial Host substituted the retained startup phase",
                    ));
                }
                let escrow = self
                    .initial_escrow
                    .take()
                    .ok_or_else(|| invalid("initial GNU owner disappeared"))?;
                self.active = Some(Active {
                    owner: bank.withdraw_supplementary(prepared, escrow)?,
                    step: Step::Returning,
                });
            } else {
                return Ok(());
            }
        }
        if self.active.is_none() && self.full.is_some() {
            if !bank.fully_funded()? {
                return Err(invalid("full handoff has no actual native originals"));
            }
            if self
                .full
                .take()
                .ok_or_else(|| invalid("original full waiter missing"))?
                .send(Ok(()))
                .is_err()
            {
                super::super::super::abort_unknown();
            }
            return Ok(());
        }
        if self.active.is_none() && self.auto && !control.partial_absent() && self.debt.is_some() {
            if let Some(fifo) = &self.fifo {
                if let Some(implicit) = bank.begin_partial_probe()? {
                    match fifo.try_escrow()? {
                        None => bank.cancel_partial_probe()?,
                        Some(escrow) => {
                            let phase =
                                super::super::super::super::call_attempt(bank.root_attempt)?;
                            let prepared = control.prepare_partial(
                                phase,
                                implicit,
                                escrow.descriptors(),
                                &mut BankService(bank),
                                deadline,
                            )?;
                            match prepared {
                                None => {
                                    bank.cancel_partial_probe()?;
                                    drop(escrow);
                                }
                                Some(prepared) => {
                                    let owner = bank.withdraw_supplementary(prepared, escrow)?;
                                    self.active = Some(Active {
                                        owner,
                                        step: Step::Returning,
                                    });
                                }
                            }
                        }
                    }
                }
            }
        }
        let Some(active) = self.active.as_mut() else {
            return Ok(());
        };
        if matches!(active.step, Step::Foreign) {
            return Ok(());
        }
        let phase = active.owner.phase();
        if matches!(active.step, Step::Returning) {
            // SAFETY: this SAME RootPartialPhase owns offered original escrow,
            // a parked bank and actual supplementary FD closure. It survives
            // Busy; unknown/error drops abort, never restore unbacked tokens.
            if unsafe { control.release_partial(phase, &mut BankService(bank), deadline) }? {
                active.owner.run_implicit()?;
                active.step = Step::Running;
                if active.owner.initial_single_installed()? {
                    // SAFETY: the original initial adopter already installed
                    // the sole actual native pair. SAME offered empty escrow
                    // and original phase remain retained until Host commit.
                    let committed =
                        unsafe { control.commit_partial(phase, &mut BankService(bank), deadline) }?;
                    if !active.owner.publish(committed)? {
                        return Err(invalid(
                            "initial singleton did not complete its actual funding",
                        ));
                    }
                    self.active.take();
                    return Ok(());
                }
            } else {
                return Ok(());
            }
        }
        if self.full.is_none() && !bank.more_requested()? {
            return Ok(());
        }
        let Some(received) = control.restore_partial(phase, &mut BankService(bank), deadline)?
        else {
            return Ok(());
        };
        let debt = self
            .debt
            .as_ref()
            .ok_or_else(|| invalid("original adaptive domain missing"))?;
        active
            .owner
            .install(debt.adopt_partial_funding(received)?)?;
        // SAFETY: actual same-phase native originals are installed in THIS
        // bank but unpublished, and SAME GNU tokens remain in offered escrow.
        let committed = unsafe { control.commit_partial(phase, &mut BankService(bank), deadline) }?;
        check_deadline(deadline);
        if active.owner.publish(committed)? {
            self.active.take();
        }
        Ok(())
    }
}
