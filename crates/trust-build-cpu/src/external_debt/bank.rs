//! Loan actual original paired backing, never a discount inferred from DATA.
//!
//! One machine custodian retains both native kernel guards and their durable
//! shadow exclusion. Returning a unit makes it available to that SAME owner,
//! not to a guessed external pool. Generic readers continue counting shadow
//! debt; a dead custodian cannot silently return live descendant capacity.

use std::cell::Cell;
use std::io;
use std::sync::{Arc, Mutex, Weak};

use super::NativeDomainReservation;
use crate::{Lease, RetainedLease, invalid};

#[path = "scoped.rs"]
mod scoped;
pub use scoped::{PendingNativePair, PendingNativePairCustody, ScopedNativeCapacityBank};
#[path = "initial.rs"]
mod initial;
pub use initial::PreparingNativeCapacityBank;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Phase {
    Running,
    Finishing,
    Settled,
}

/// The actual original native/shadow reservation, with one-use unit loans.
/// No count, record, PID, public Book or source echo constructs this owner.
/// Unscoped loans are local custody only, not cross-process recovery coverage.
/// A fresh original may be consumed into `ScopedNativeCapacityBank` BEFORE
/// lending; its shadow recovery key then follows each actual borrower.
pub struct NativeCapacityBank {
    native: Vec<Option<Lease>>,
    retained: Vec<Option<RetainedLease>>,
    borrowed_shadows: Vec<Weak<Mutex<RetainedLease>>>,
    domain: [u8; 32],
    idle_context: [u8; 32],
    process: u32,
    original: Arc<()>,
    slots: Vec<Option<u64>>,
    next: u64,
    phase: Phase,
}

/// Noncloneable custody of a real original native unit. Drop does not return
/// it to the bank. Exporting a descriptor requires actual execution retirement
/// before return; local Arc counts cannot prove cross-process closure.
pub struct NativeCapacityLoan {
    original: Arc<()>,
    index: usize,
    generation: u64,
    native: Lease,
    exported: Cell<bool>,
    shadow: Option<Arc<Mutex<RetainedLease>>>,
}

impl std::fmt::Debug for NativeCapacityLoan {
    fn fmt(&self, out: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        out.debug_struct("NativeCapacityLoan")
            .field("slot", &self.native.slot())
            .field("generation", &self.generation)
            .finish_non_exhaustive()
    }
}

/// A refused return preserves the exact genuine loan, never a reconstructed
/// descriptor or a replacement generation.
#[derive(Debug)]
pub struct NativeCapacityReturnError {
    error: io::Error,
    loan: NativeCapacityLoan,
}
impl NativeCapacityReturnError {
    /// Recover the same original loan for supervision or a legitimate retry.
    pub fn into_parts(self) -> (io::Error, NativeCapacityLoan) {
        (self.error, self.loan)
    }
}
impl std::fmt::Display for NativeCapacityReturnError {
    fn fmt(&self, out: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.error.fmt(out)
    }
}
impl std::error::Error for NativeCapacityReturnError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        Some(&self.error)
    }
}

impl NativeCapacityBank {
    pub(super) fn new(reservation: NativeDomainReservation) -> io::Result<Self> {
        if reservation.native.is_empty() || reservation.native.len() != reservation.retained.len() {
            return Err(invalid("capacity bank requires complete original paired backing"));
        }
        for debt in &reservation.retained {
            debt.identity()?;
        }
        let slots = vec![None; reservation.native.len()];
        let borrowed_shadows = (0..slots.len()).map(|_| Weak::new()).collect();
        Ok(Self {
            native: reservation.native.into_iter().map(Some).collect(),
            retained: reservation.retained.into_iter().map(Some).collect(),
            borrowed_shadows,
            domain: reservation.domain,
            idle_context: reservation.context,
            process: std::process::id(),
            original: Arc::new(()),
            slots,
            next: 0,
            phase: Phase::Running,
        })
    }

    /// Actual original width; this observation grants no unit.
    pub fn width(&self) -> usize {
        self.slots.len()
    }

    /// Count actual still-held native guards. This is an observation, never
    /// authority to restore a GNU token or issue a replacement unit.
    pub fn funded_width(&self) -> usize {
        self.native.iter().filter(|unit| unit.is_some()).count()
    }

    /// Return one genuinely idle pair to the original machine domain, keeping
    /// at least the caller's positive minimum. Unlike returning a loan to this
    /// bank, this settles the actual shadow and closes the original kernel
    /// guard. No outstanding or lost loan can be selected.
    ///
    /// A failed shadow write retains its SAME guard and settlement capability;
    /// no replacement or execution may be inferred from a failed return. The
    /// physical slot index remains a hole: width is the original ceiling, not
    /// a replenished balance. Reacquisition requires genuine new backing.
    pub fn release_idle(&mut self, minimum: std::num::NonZeroU32) -> io::Result<Option<u32>> {
        self.check_process()?;
        if self.phase != Phase::Running {
            return Err(invalid("capacity bank is retiring"));
        }
        if self.funded_width() <= minimum.get() as usize {
            return Ok(None);
        }
        let Some(index) = self.slots.iter().enumerate().rev().find_map(|(index, loan)| {
            (loan.is_none() && self.native[index].is_some()).then_some(index)
        }) else {
            return Ok(None);
        };
        let shadow = self.retained[index]
            .as_mut()
            .ok_or_else(|| invalid("idle native unit has no original shadow"))?;
        shadow.settle_held()?;
        self.retained[index].take();
        let native = self.native[index]
            .take()
            .ok_or_else(|| invalid("idle original native guard missing"))?;
        let slot = native.slot();
        drop(native);
        Ok(Some(slot))
    }

    /// Consume an unused cooperative bank into recovery-scoped custody. A
    /// refused conversion returns the SAME original bank; no active/local
    /// loan, fixed V1 handoff or observed record can be converted here.
    pub fn try_into_scoped(self) -> Result<ScopedNativeCapacityBank, (io::Error, Self)> {
        if self.process != std::process::id() || self.next != 0 || self.phase != Phase::Running {
            return Err((invalid("scoped bank requires its unused original owner"), self));
        }
        Ok(ScopedNativeCapacityBank::new(self))
    }

    /// Loan one actual original unit, or None when all are still owned. Caller
    /// scheduling/fairness and memory admission precede this operation. This
    /// bank never invokes a new machine allocator or changes a GNU server.
    pub fn try_loan(&mut self) -> io::Result<Option<NativeCapacityLoan>> {
        self.check_process()?;
        if self.phase != Phase::Running {
            return Err(invalid("capacity bank is retiring"));
        }
        let Some(index) = self.slots.iter().enumerate().find_map(|(index, loan)| {
            (loan.is_none() && self.native[index].is_some()).then_some(index)
        }) else {
            return Ok(None);
        };
        let generation = self
            .next
            .checked_add(1)
            .ok_or_else(|| invalid("capacity loan generation exhausted"))?;
        self.retained[index]
            .as_ref()
            .ok_or_else(|| invalid("original shadow backing is not in the bank"))?
            .identity()?;
        // Duplicate the actual original guard BEFORE publishing the loan. A
        // failure consumes no generation and exposes no execution authority.
        let native = self.native[index]
            .as_ref()
            .ok_or_else(|| invalid("original native backing is parked"))?
            .try_clone()?;
        self.next = generation;
        self.slots[index] = Some(generation);
        Ok(Some(NativeCapacityLoan {
            original: self.original.clone(),
            index,
            generation,
            native,
            exported: Cell::new(false),
            shadow: None,
        }))
    }

    fn validate_origin(&self, loan: &NativeCapacityLoan) -> io::Result<()> {
        self.check_process()?;
        if self.phase != Phase::Running
            || !Arc::ptr_eq(&self.original, &loan.original)
            || self.slots.get(loan.index) != Some(&Some(loan.generation))
        {
            return Err(invalid("foreign or stale original capacity loan"));
        }
        Ok(())
    }
    fn validate(&self, loan: &NativeCapacityLoan) -> io::Result<()> {
        self.validate_origin(loan)?;
        if let Some(shadow) = &loan.shadow {
            shadow.lock().map_err(|_| invalid("original shadow custody poisoned"))?.identity()?;
        } else {
            self.retained[loan.index]
                .as_ref()
                .ok_or_else(|| invalid("original shadow backing is not in the bank"))?
                .identity()?;
        }
        Ok(())
    }

    /// Return only a genuine loan whose native description was never exposed.
    /// No status/Boolean/PID or cloned observation qualifies as this non-use.
    pub fn return_unused(
        &mut self,
        loan: NativeCapacityLoan,
    ) -> Result<(), NativeCapacityReturnError> {
        let checked = self.validate(&loan).and_then(|()| {
            if loan.shadow.is_some() {
                Err(invalid("scoped capacity requires fresh idle recovery custody"))
            } else if loan.exported.get() {
                Err(invalid("exported capacity requires actual scope closure"))
            } else {
                Ok(())
            }
        });
        match checked {
            Ok(()) => {
                self.slots[loan.index] = None;
                drop(loan);
                Ok(())
            }
            Err(error) => Err(NativeCapacityReturnError { error, loan }),
        }
    }

    /// Return an exported actual unit AFTER the original execution owner has
    /// positively closed every scope using it. No shadow debt settles here;
    /// this same original bank remains the sole owner of machine backing.
    ///
    /// # Safety
    /// Caller must retain actual cohort/SDK phase ownership and establish that
    /// every original borrower/descendant has retired or entered its genuine
    /// excluded phase before this FIRST return. A decoded reply, child status,
    /// PID, Arc count or empty queue alone is insufficient. Uncertain return
    /// must retain the loan instead of calling this method.
    pub unsafe fn return_after_scope(
        &mut self,
        loan: NativeCapacityLoan,
    ) -> Result<(), NativeCapacityReturnError> {
        let checked = self.validate(&loan).and_then(|()| {
            if loan.shadow.is_some() {
                Err(invalid("scoped capacity requires fresh idle recovery custody"))
            } else {
                Ok(())
            }
        });
        match checked {
            Ok(()) => {
                self.slots[loan.index] = None;
                drop(loan);
                Ok(())
            }
            Err(error) => Err(NativeCapacityReturnError { error, loan }),
        }
    }

    /// Settle the actual original shadow only after EVERY issued loan has
    /// returned through its native closure or lexical non-use path. Uncertain
    /// settlement is sticky; retries retain the same settlement capabilities.
    pub fn settle_drained(&mut self) -> io::Result<()> {
        self.check_process()?;
        if self.slots.iter().any(Option::is_some) {
            return Err(io::Error::new(
                io::ErrorKind::WouldBlock,
                "original capacity loans remain outstanding",
            ));
        }
        self.phase = Phase::Finishing;
        for shadow in &mut self.retained {
            let Some(held) = shadow.as_mut() else { continue };
            held.settle_held()?;
            shadow.take();
        }
        // Every issued capability has positively returned. Only after ALL
        // durable shadow settlement succeeds may the actual original native
        // guards close. A failed partial settlement retains the complete
        // native set, so no sibling can race into a half-settled generation.
        self.native.clear();
        self.phase = Phase::Settled;
        Ok(())
    }
    fn check_process(&self) -> io::Result<()> {
        if self.process != std::process::id() {
            return Err(io::Error::new(
                io::ErrorKind::PermissionDenied,
                "fork copy cannot mutate original native bank custody",
            ));
        }
        Ok(())
    }
}

impl NativeCapacityLoan {
    /// Borrow the actual original native and retained-shadow descriptions for
    /// the SAME owning SDK transport. No file is opened or duplicated here.
    /// Exposure permanently excludes the unused-loan return path; actual
    /// original scope closure remains mandatory before return.
    pub fn with_original_descriptions<T>(
        &self,
        use_originals: impl FnOnce(
            [std::os::fd::BorrowedFd<'_>; 2],
            crate::RetainedLeaseIdentity,
        ) -> io::Result<T>,
    ) -> io::Result<T> {
        use std::os::fd::AsFd as _;
        let original_shadow =
            self.shadow.as_ref().ok_or_else(|| invalid("scoped original shadow missing"))?;
        let shadow =
            original_shadow.lock().map_err(|_| invalid("original shadow custody poisoned"))?;
        let descriptor = shadow.original_description()?;
        let generation = shadow.identity()?;
        self.exported.set(true);
        use_originals([self.native.as_fd(), descriptor], generation)
    }
    /// Diagnostic original slot identity. This exposes no native guard and
    /// does not change an unexported loan into execution authority.
    pub fn slot(&self) -> u32 {
        self.native.slot()
    }

    /// Borrow actual original backing for explicit child/SDK inheritance.
    /// Merely requesting this reference permanently leaves the non-use path.
    pub fn original(&self) -> &Lease {
        self.exported.set(true);
        &self.native
    }
}
