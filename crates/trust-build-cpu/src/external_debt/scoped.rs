//! Original occupied shadow custody follows each genuine Root loan. Mutable
//! bookkeeping cannot let an old bank/Root key settle a later borrower's unit.

use super::*;
use crate::PreparedRecovery;

/// Genuine native/shadow pairs with immutable borrower-bound recovery custody.
/// No decoded scope, snapshot, name, counter or PID constructs this owner.
pub struct ScopedNativeCapacityBank {
    bank: NativeCapacityBank,
    pending: Option<NativeCapacityLoan>,
    reacquiring: Option<Reacquiring>,
    keeper_outstanding: bool,
}
struct Reacquiring {
    index: usize,
    native: Lease,
    shadow: crate::retained::PendingRecoveryAcquisition,
}

/// MOVE-only ownership of the original pair before commit. No descriptor is
/// duplicated, no generation is written and no execution is authorized. The
/// original bank remains restricted until this same owner is returned.
///
/// The enclosing original keeper must separately retain the common M/claim
/// epoch and owning worker scope. This primitive does not authenticate a Host,
/// transport, closure ACK or a cross-process receiver, and cannot replace those
/// obligations. Dropping it does not clear the original bank's restriction.
pub struct PendingNativePairCustody {
    pair: Reacquiring,
    original: Arc<()>,
    domain: [u8; 32],
    context: [u8; 32],
}
impl PendingNativePairCustody {
    /// Borrow the SAME original native and shadow descriptions for an
    /// existing retained-owner transport. No funded lease can be extracted.
    pub fn descriptions(&self) -> io::Result<[std::os::fd::BorrowedFd<'_>; 2]> {
        use std::os::fd::AsFd as _;
        Ok([self.pair.native.as_fd(), self.pair.shadow.original_description()?])
    }
}

/// Borrowed actual pending pair BEFORE durable mutation. This is neither a
/// funded loan nor a retained generation witness. Only original live owners
/// may duplicate these descriptions into their real pre-write custody; no
/// snapshot, count or nonce can construct this view.
pub struct PendingNativePair<'a> {
    native: &'a Lease,
    shadow: &'a crate::retained::PendingRecoveryAcquisition,
    domain: [u8; 32],
    context: [u8; 32],
}
impl PendingNativePair<'_> {
    /// SAME native and shadow descriptions, in that order. Borrowing confers
    /// no funded status or permission to run a target.
    pub fn descriptions(&self) -> io::Result<[std::os::fd::BorrowedFd<'_>; 2]> {
        use std::os::fd::AsFd as _;
        Ok([self.native.as_fd(), self.shadow.original_description()?])
    }
    /// Slot of the actually captured original native guard.
    pub fn native_slot(&self) -> u32 {
        self.native.slot()
    }
    /// Slot of the actually captured, still unpublished shadow guard.
    pub fn shadow_slot(&self) -> io::Result<u32> {
        self.shadow.original_slot()
    }
    /// Expected original generation, never a current committed-debt witness.
    pub fn nonce(&self) -> io::Result<[u8; 16]> {
        self.shadow.original_nonce()
    }
    /// Original independently checked domain binding; DATA only.
    pub fn domain(&self) -> [u8; 32] {
        self.domain
    }
    /// Original recovery context, not another resource grant.
    pub fn context(&self) -> [u8; 32] {
        self.context
    }
}

impl ScopedNativeCapacityBank {
    pub(super) fn new(bank: NativeCapacityBank) -> Self {
        Self { bank, pending: None, reacquiring: None, keeper_outstanding: false }
    }

    fn check_custody(&self) -> io::Result<()> {
        self.bank.check_process()?;
        if self.keeper_outstanding {
            return Err(invalid("original pending pair is retained by its keeper"));
        }
        Ok(())
    }

    /// Move an ALREADY captured pair to its original keeper before any durable
    /// write. No new capacity is acquired. Until return, all bank transitions
    /// refuse; losing this owner can never silently renew the bank balance.
    pub fn take_pending_custody(&mut self) -> io::Result<Option<PendingNativePairCustody>> {
        self.check_custody()?;
        let Some(pair) = self.reacquiring.take() else { return Ok(None) };
        self.keeper_outstanding = true;
        Ok(Some(PendingNativePairCustody {
            pair,
            original: self.bank.original.clone(),
            domain: self.bank.domain,
            context: self.bank.idle_context,
        }))
    }

    /// Return only this SAME bank's actual moved owner. Refusal leaves the
    /// caller's owner untouched. IDs, counts, decoded ACKs or received raw FDs
    /// cannot construct it or clear a lost keeper's restriction.
    pub fn restore_pending_custody(
        &mut self,
        custody: &mut Option<PendingNativePairCustody>,
    ) -> io::Result<()> {
        self.bank.check_process()?;
        let owner = custody.as_ref().ok_or_else(|| invalid("original pending keeper missing"))?;
        if !self.keeper_outstanding
            || self.reacquiring.is_some()
            || self.pending.is_some()
            || self.bank.phase != Phase::Running
            || !Arc::ptr_eq(&owner.original, &self.bank.original)
            || owner.domain != self.bank.domain
            || owner.context != self.bank.idle_context
        {
            return Err(invalid("pending keeper belongs to another original bank"));
        }
        let owner = custody.take().ok_or_else(|| invalid("original pending keeper disappeared"))?;
        self.reacquiring = Some(owner.pair);
        self.keeper_outstanding = false;
        Ok(())
    }

    /// Original physical width; observing it grants no unit.
    pub fn width(&self) -> usize {
        self.bank.width()
    }

    /// Actual retained backing, not a decoded grant or the original ceiling.
    pub fn funded_width(&self) -> usize {
        self.bank.funded_width()
    }

    /// Negative steering only: V1 full-domain callers must not capture a
    /// partial prefix while any genuine loan or funding transition remains.
    /// A true observation grants no loan; the original owner must retain
    /// exclusive bank access through the actual acquisition operation.
    pub fn is_wholly_idle(&self) -> io::Result<bool> {
        self.check_custody()?;
        if self.pending.is_some()
            || self.reacquiring.is_some()
            || self.bank.phase != Phase::Running
            || self.bank.native.iter().any(Option::is_none)
            || self.bank.slots.iter().any(Option::is_some)
            || self.bank.retained.iter().any(Option::is_none)
        {
            return Ok(false);
        }
        for shadow in self.bank.retained.iter().flatten() {
            shadow.identity()?;
        }
        Ok(true)
    }

    /// Release only idle original pairs. A pending rekey retains its exact
    /// guard and blocks this transition; no partially rebound generation can
    /// disappear into a machine return.
    pub fn release_idle(&mut self, minimum: std::num::NonZeroU32) -> io::Result<Option<u32>> {
        self.check_custody()?;
        if self.pending.is_some() || self.reacquiring.is_some() {
            return Err(invalid("pending scoped loan excludes machine return"));
        }
        self.bank.release_idle(minimum)
    }

    /// Nonblocking acquisition of ONE genuinely new pair for a previously
    /// released hole. The scheduler must first select this original owner by
    /// its ordinary fairness policy; this method creates no queue or priority.
    /// Only actually held original native/shadow pairs are coalesced under the
    /// SAME manifest transaction. Generic readers never get this discount.
    /// A lost scoped loan has no live shadow witness and therefore refuses.
    pub fn try_reacquire_idle(
        &mut self,
        debt: &super::super::ExternalDebt,
        idle: &mut PreparedRecovery,
        policy_limit: u32,
    ) -> io::Result<Option<u32>> {
        self.reacquire_with(debt, idle, policy_limit, |pending, key| pending.finish(key))
    }

    fn reacquire_with(
        &mut self,
        debt: &super::super::ExternalDebt,
        idle: &mut PreparedRecovery,
        policy_limit: u32,
        mut finish: impl FnMut(
            &mut crate::retained::PendingRecoveryAcquisition,
            &PreparedRecovery,
        ) -> io::Result<RetainedLease>,
    ) -> io::Result<Option<u32>> {
        if !self.prepare_reacquisition(debt, idle, policy_limit)? {
            return Ok(None);
        }
        self.finish_reacquisition(idle, &mut finish).map(Some)
    }

    /// Capture a real pair without writing its new durable generation. The
    /// original caller must select this owner fairly before this acquisition.
    /// It must retain these SAME descriptions and its actual original scope
    /// before commit; this view alone proves no cross-process lifetime.
    pub fn prepare_reacquire_idle(
        &mut self,
        debt: &super::super::ExternalDebt,
        idle: &mut PreparedRecovery,
        policy_limit: u32,
    ) -> io::Result<Option<PendingNativePair<'_>>> {
        if !self.prepare_reacquisition(debt, idle, policy_limit)? {
            return Ok(None);
        }
        let pair =
            self.reacquiring.as_ref().ok_or_else(|| invalid("pending original pair missing"))?;
        pair.shadow.check_original(idle)?;
        Ok(Some(PendingNativePair {
            native: &pair.native,
            shadow: &pair.shadow,
            domain: self.bank.domain,
            context: self.bank.idle_context,
        }))
    }

    /// Commit only the already captured original pair under its exact key.
    /// No acquisition/replacement/policy balance is created on this path.
    /// Cross-process callers must first install actual retained owner custody;
    /// neither a decoded acknowledgement nor this method supplies it.
    pub fn commit_reacquire_idle(
        &mut self,
        debt: &super::super::ExternalDebt,
        idle: &PreparedRecovery,
    ) -> io::Result<u32> {
        self.check_custody()?;
        if self.pending.is_some() || self.bank.phase != Phase::Running {
            return Err(invalid("original bank is transitioning or retiring"));
        }
        if debt.recovery_domain()? != self.bank.domain || idle.context() != self.bank.idle_context {
            return Err(invalid("pending commit changed its original native domain or scope"));
        }
        let _transaction = super::super::transaction(&debt.native)?.ok_or_else(|| {
            io::Error::new(io::ErrorKind::WouldBlock, "original native commit transaction is busy")
        })?;
        self.finish_reacquisition(idle, &mut |pending, key| pending.finish(key))
    }

    fn prepare_reacquisition(
        &mut self,
        debt: &super::super::ExternalDebt,
        idle: &mut PreparedRecovery,
        policy_limit: u32,
    ) -> io::Result<bool> {
        self.check_custody()?;
        if self.pending.is_some() || self.bank.phase != Phase::Running {
            return Err(invalid("original bank is transitioning or retiring"));
        }
        let domain = debt.recovery_domain()?;
        idle.validate(domain)?;
        if domain != self.bank.domain
            || idle.context() != self.bank.idle_context
            || idle.width().get() != 1
        {
            return Err(invalid("reacquisition differs from original bank domain or idle scope"));
        }
        if self.reacquiring.is_some() {
            return Ok(true);
        }
        idle.validate_issuance(domain)?;
        let Some(index) = self.bank.native.iter().position(Option::is_none) else {
            return Ok(false);
        };
        let Some(_transaction) = super::super::transaction(&debt.native)? else { return Ok(false) };
        // Retain genuine borrowed capabilities throughout census+acquisition.
        // Weak references alone, old nonces and slot records cannot fund work.
        let mut borrowed = Vec::new();
        borrowed.try_reserve_exact(self.bank.funded_width()).map_err(io::Error::other)?;
        let mut pairs = 0u32;
        for (slot, native) in self.bank.native.iter().enumerate() {
            if native.is_none() {
                continue;
            }
            if let Some(shadow) = &self.bank.retained[slot] {
                shadow.identity()?;
            } else {
                let shadow = self.bank.borrowed_shadows[slot]
                    .upgrade()
                    .ok_or_else(|| invalid("lost borrower excludes original pair reacquisition"))?;
                shadow
                    .lock()
                    .map_err(|_| invalid("original shadow custody poisoned"))?
                    .identity()?;
                borrowed.push(shadow);
            }
            pairs = pairs.checked_add(1).ok_or_else(|| invalid("original pair count overflow"))?;
        }
        let native = debt
            .native
            .snapshot()?
            .iter()
            .filter(|slot| matches!(slot, super::super::SlotState::Held { .. }))
            .count() as u32;
        let occupied = native
            .checked_add(debt.reserved()?)
            .and_then(|total| total.checked_sub(pairs))
            .ok_or_else(|| invalid("original paired census is inconsistent"))?;
        if occupied >= policy_limit.min(debt.native.slots().get()) {
            return Ok(false);
        }
        let Some(native) = debt.native.try_acquire_in_transaction(idle.owner())? else {
            return Ok(false);
        };
        let Some(shadow) = debt.retained.prepare_recovery_acquisition(domain, idle)? else {
            return Ok(false);
        };
        self.reacquiring = Some(Reacquiring { index, native, shadow });
        drop(borrowed);
        Ok(true)
    }

    fn finish_reacquisition(
        &mut self,
        idle: &PreparedRecovery,
        finish: &mut impl FnMut(
            &mut crate::retained::PendingRecoveryAcquisition,
            &PreparedRecovery,
        ) -> io::Result<RetainedLease>,
    ) -> io::Result<u32> {
        let pending = self
            .reacquiring
            .as_mut()
            .ok_or_else(|| invalid("original reacquisition custody missing"))?;
        let shadow = finish(&mut pending.shadow, idle)?;
        let pending = self
            .reacquiring
            .take()
            .ok_or_else(|| invalid("original reacquisition changed during commit"))?;
        let slot = pending.native.slot();
        self.bank.native[pending.index] = Some(pending.native);
        self.bank.retained[pending.index] = Some(shadow);
        self.bank.borrowed_shadows[pending.index] = Weak::new();
        Ok(slot)
    }

    /// A negative steering observation only. Original native/key custody must
    /// be retained across any refusal; this Boolean cannot authorize a retry.
    pub fn has_pending_reacquisition(&self) -> bool {
        self.reacquiring.is_some() || self.keeper_outstanding
    }

    /// Complete only an already captured original pair during refusal cleanup.
    /// An absent pending owner performs no acquisition and consumes no key.
    pub fn retry_pending_reacquisition(
        &mut self,
        debt: &super::super::ExternalDebt,
        idle: &mut PreparedRecovery,
    ) -> io::Result<Option<u32>> {
        self.check_custody()?;
        if self.reacquiring.is_none() {
            return Ok(None);
        }
        self.try_reacquire_idle(debt, idle, 0)
    }

    /// Diagnostic pending-transition observation, used only to withhold later
    /// work. This Boolean cannot construct or authorize any capacity loan.
    pub fn has_pending_loan(&self) -> bool {
        self.pending.is_some()
    }

    /// Retry ONLY the already captured original loan. An absent pending
    /// transition returns None without acquiring/issuing any new unit. This
    /// permits original failed-launch cleanup after its request stopped.
    pub fn retry_pending_loan(
        &mut self,
        scope: &mut PreparedRecovery,
    ) -> io::Result<Option<NativeCapacityLoan>> {
        self.check_custody()?;
        if self.pending.is_none() {
            return Ok(None);
        }
        self.try_loan(scope)
    }

    /// Loan one original native/shadow pair only AFTER rebinding its SAME
    /// occupied shadow to an already-persisted per-unit scope capability.
    /// The host must bind that immutable context to the actual held Root M.
    /// An uncertain write keeps its SAME native loan and old/new recovery
    /// transition; only the original preparation may retry it.
    pub fn try_loan(
        &mut self,
        scope: &mut PreparedRecovery,
    ) -> io::Result<Option<NativeCapacityLoan>> {
        self.check_custody()?;
        if self.reacquiring.is_some() {
            return Err(invalid("pending reacquisition excludes new bank loans"));
        }
        scope.validate(self.bank.domain)?;
        if scope.width().get() != 1 {
            return Err(invalid("a scoped loan requires one original physical unit"));
        }
        if scope.context() == self.bank.idle_context {
            return Err(invalid("a Root loan cannot use the idle-bank recovery scope"));
        }
        if self.pending.is_none() {
            scope.validate_issuance(self.bank.domain)?;
            let Some(loan) = self.bank.try_loan()? else { return Ok(None) };
            self.pending = Some(loan);
        }
        let index = self
            .pending
            .as_ref()
            .ok_or_else(|| invalid("original pending native loan missing"))?
            .index;
        self.bank.retained[index]
            .as_mut()
            .ok_or_else(|| invalid("original pending shadow missing"))?
            .rekey_recoverable(self.bank.domain, scope)?;
        let shadow = self.bank.retained[index]
            .take()
            .ok_or_else(|| invalid("original scoped shadow missing"))?;
        let mut loan =
            self.pending.take().ok_or_else(|| invalid("original pending native loan missing"))?;
        let shadow = Arc::new(Mutex::new(shadow));
        self.bank.borrowed_shadows[index] = Arc::downgrade(&shadow);
        loan.shadow = Some(shadow);
        Ok(Some(loan))
    }

    /// Return genuine unexported custody to a FRESH idle-bank recovery key.
    /// The former scope key can never settle a later borrower's credit.
    pub fn return_unused(
        &mut self,
        loan: NativeCapacityLoan,
        idle: &mut PreparedRecovery,
    ) -> Result<(), NativeCapacityReturnError> {
        if loan.exported.get() {
            return Err(NativeCapacityReturnError {
                error: invalid("exported scoped loan needs original execution closure"),
                loan,
            });
        }
        self.return_closed(loan, idle)
    }

    /// Return an exported unit only after its original execution owner has
    /// established actual whole-scope closure or genuine SDK phase exclusion.
    ///
    /// # Safety
    /// Caller must retain original cohort/SDK/token authority and positively
    /// exclude EVERY borrower before this FIRST call, including on uncertain
    /// writes/replies. A PID, ACK, Book, decoded observation or empty queue is
    /// insufficient. The implicit running Root cannot be returned as idle.
    /// Live phase exclusion must survive controller/worker loss and may resume
    /// ONLY after genuine new backing; a local pause flag/Drop is insufficient.
    pub unsafe fn return_after_scope(
        &mut self,
        loan: NativeCapacityLoan,
        idle: &mut PreparedRecovery,
    ) -> Result<(), NativeCapacityReturnError> {
        self.return_closed(loan, idle)
    }

    fn return_closed(
        &mut self,
        mut loan: NativeCapacityLoan,
        idle: &mut PreparedRecovery,
    ) -> Result<(), NativeCapacityReturnError> {
        let checked = (|| {
            self.check_custody()?;
            self.bank.validate_origin(&loan)?;
            idle.validate(self.bank.domain)?;
            if idle.context() != self.bank.idle_context || idle.width().get() != 1 {
                return Err(invalid("idle return differs from original machine recovery context"));
            }
            if self.bank.retained[loan.index].is_some() {
                return Err(invalid("original shadow unit was already returned"));
            }
            let original_shadow =
                loan.shadow.as_ref().ok_or_else(|| invalid("original scoped shadow missing"))?;
            original_shadow
                .lock()
                .map_err(|_| invalid("original scoped shadow custody poisoned"))?
                .rekey_recoverable(self.bank.domain, idle)
        })();
        if let Err(error) = checked {
            return Err(NativeCapacityReturnError { error, loan });
        }
        // The weak bank witness is not another settlement owner. All temporary
        // validation borrows finish before this unique original is recovered.
        let Some(shadow) = loan.shadow.as_mut() else {
            return Err(NativeCapacityReturnError {
                error: invalid("original scoped shadow missing after return"),
                loan,
            });
        };
        if Arc::strong_count(shadow) != 1 {
            return Err(NativeCapacityReturnError {
                error: invalid("original shadow validation still active"),
                loan,
            });
        }
        let shadow = match loan.shadow.take() {
            Some(shadow) => match Arc::try_unwrap(shadow) {
                Ok(shadow) => match shadow.into_inner() {
                    Ok(shadow) => shadow,
                    Err(poisoned) => {
                        loan.shadow = Some(Arc::new(Mutex::new(poisoned.into_inner())));
                        return Err(NativeCapacityReturnError {
                            error: invalid("original shadow custody poisoned"),
                            loan,
                        });
                    }
                },
                Err(shadow) => {
                    loan.shadow = Some(shadow);
                    return Err(NativeCapacityReturnError {
                        error: invalid("original shadow ownership changed"),
                        loan,
                    });
                }
            },
            None => {
                return Err(NativeCapacityReturnError {
                    error: invalid("original scoped shadow missing"),
                    loan,
                });
            }
        };
        self.bank.borrowed_shadows[loan.index] = Weak::new();
        self.bank.retained[loan.index] = Some(shadow);
        self.bank.slots[loan.index] = None;
        drop(loan);
        Ok(())
    }

    /// No pending/issued native loan may disappear into settlement. Original
    /// shadow and native guards retire only after their actual safe returns.
    pub fn settle_drained(&mut self) -> io::Result<()> {
        self.check_custody()?;
        if self.reacquiring.is_some() {
            return Err(invalid("pending reacquisition excludes bank settlement"));
        }
        self.bank.settle_drained()
    }
}

#[cfg(test)]
#[path = "scoped_acquisition_tests.rs"]
mod acquisition_tests;
