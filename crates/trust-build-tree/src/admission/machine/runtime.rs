//! Prelaunch native owner for reversible idle supplementary capacity.
//!
//! V1 couriers export every slot OFD to descendants. Such a claim CANNOT be
//! resized: closing the parent's copy does not release those locks. This type
//! therefore consumes an unlaunched FixedClaim and never exports its slot FDs
//! or a V1 courier. A future launcher must retain this exact owner, original
//! group, FIFO and generation through actual retirement; current launch paths
//! deliberately do not activate this protocol.

use std::ffi::CString;
use std::sync::Arc;
use std::sync::atomic::{AtomicU64, Ordering};

use jobserver_utils::{IdleTokenEscrow, Jobserver};

use super::*;

/// In-process currency, not serialized authority or a Host/SDK receipt.
pub struct RuntimeClaimCurrency {
    original: Arc<AtomicU64>,
    generation: u64,
}

/// Actual same-server escrow and original worktree/slot custody. All mutable
/// operations require the sole owner. No observed process count is used.
pub struct RuntimeFixedClaim {
    claim: Option<FixedClaim>,
    pool: Pool,
    original_ceiling: NonZeroU32,
    original: Arc<AtomicU64>,
    server: Jobserver,
    escrow: IdleTokenEscrow,
    directory: Option<tempfile::TempDir>,
    reacquire: Option<Coordinator>,
    poisoned: bool,
    exposed: std::cell::Cell<bool>,
    owner_pid: u32,
}

impl FixedClaim {
    /// Consume BEFORE prepare_command/spawn/export. Existing running/imported
    /// V1 types have no conversion into this owner. This opens, never activates
    /// or repairs, the original canonical native pool.
    pub fn into_runtime(self) -> io::Result<RuntimeFixedClaim> {
        let (legacy, _) = trust_build_cpu::LegacyRetirement::canonical_layout()?;
        if fs::canonicalize(legacy)? != fs::canonicalize(&self.reservation.namespace)? {
            return Err(invalid("runtime cannot replace its original machine namespace"));
        }
        let pool = Pool::open_existing(&trust_build_cpu::capacity_dir()?)?.ok_or_else(|| {
            io::Error::new(io::ErrorKind::NotFound, "original native pool absent")
        })?;
        RuntimeFixedClaim::new(self, pool)
    }
}

impl RuntimeFixedClaim {
    fn new(mut claim: FixedClaim, pool: Pool) -> io::Result<Self> {
        claim.check_current()?;
        if claim.reservation.exclusive {
            return Err(invalid("exclusive fixed claims cannot lend live capacity"));
        }
        if !matches!(claim.observe_in_pool(&pool)?, LegacyFixedRoom::Fits { .. }) {
            return Err(io::ErrorKind::WouldBlock.into());
        }
        let directory = tempfile::Builder::new().prefix("trust-runtime-gnu-").tempdir()?;
        let path = directory.path().join("credits");
        let name = CString::new(path.as_os_str().as_bytes()).map_err(io::Error::other)?;
        // SAFETY: NUL-terminated path in our freshly owned private directory;
        // only this owner creates/removes the original scheduling FIFO.
        if unsafe { libc::mkfifo(name.as_ptr(), 0o600) } != 0 {
            return Err(io::Error::last_os_error());
        }
        let mut server = Jobserver::from_fifo(&path)?;
        server.propagate_make_flags();
        // The root's implicit credit stays backed by the retained minimum
        // share. Seed only the supplementary bytes of THIS original server.
        for _ in 1..claim.budget.get() {
            server.client().release_raw()?;
        }
        let escrow = IdleTokenEscrow::new(&server, claim.budget.get() as usize - 1)?;
        // Explicit conversion hands the SAME actual claim to this runtime
        // owner. It is no longer an unlaunched fixed-command preparation.
        claim.release_prelaunch_admission();
        Ok(Self {
            original_ceiling: claim.budget,
            claim: Some(claim),
            pool,
            original: Arc::new(AtomicU64::new(0)),
            server,
            escrow,
            directory: Some(directory),
            reacquire: None,
            poisoned: false,
            exposed: std::cell::Cell::new(false),
            owner_pid: std::process::id(),
        })
    }

    /// Scheduling only. Consumers must keep using this same server, including
    /// after resize. This does NOT export a fixed/worker/Host admission courier.
    pub fn jobserver(&self) -> &Jobserver {
        self.exposed.set(true);
        &self.server
    }

    pub fn currency(&self) -> io::Result<RuntimeClaimCurrency> {
        self.check()?;
        Ok(RuntimeClaimCurrency {
            original: self.original.clone(),
            generation: self.original.load(Ordering::Acquire),
        })
    }

    pub fn check_currency(&self, currency: &RuntimeClaimCurrency) -> io::Result<()> {
        self.check()?;
        if !Arc::ptr_eq(&self.original, &currency.original)
            || self.original.load(Ordering::Acquire) != currency.generation
        {
            return Err(invalid("stale or foreign runtime claim currency"));
        }
        Ok(())
    }

    pub fn budget(&self) -> io::Result<NonZeroU32> {
        self.check()?;
        Ok(self.claim()?.budget)
    }

    fn claim(&self) -> io::Result<&FixedClaim> {
        self.claim.as_ref().ok_or_else(|| invalid("runtime claim has retired"))
    }

    fn check(&self) -> io::Result<()> {
        if self.poisoned || self.owner_pid != std::process::id() {
            return Err(invalid("runtime resize previously refused"));
        }
        self.claim()?.check_current()
    }

    fn next_generation(&self) -> io::Result<u64> {
        self.original
            .load(Ordering::Acquire)
            .checked_add(1)
            .ok_or_else(|| invalid("runtime claim generation exhausted"))
    }

    fn share(&self, slots: usize) -> io::Result<NonZeroU32> {
        let claim = self.claim()?;
        let share =
            u64::from(claim.cpus.get()) * slots as u64 / u64::from(claim.reservation.minimum_slots);
        NonZeroU32::new(share.min(u64::from(self.original_ceiling.get())).max(1) as u32)
            .ok_or_else(|| invalid("zero retained runtime share"))
    }

    /// Return at most one actual supplemental slot. The minimum slot/root
    /// remains retained. Pending means no machine capacity was released; any
    /// partially acquired idle tokens remain backed and in escrow for retry.
    pub fn try_lend(&mut self) -> io::Result<bool> {
        self.check()?;
        let slots = self.claim()?.reservation.slots.len();
        if slots <= self.claim()?.reservation.required_slots as usize {
            return Ok(false);
        }
        let reduced = self.share(slots - 1)?;
        let withheld = (self.original_ceiling.get() - reduced.get()) as usize;
        if !self.escrow.try_withhold(withheld)? {
            return Ok(false);
        }
        let generation = self.next_generation()?;
        // Serialize native/legacy readers across record change and lock close.
        let Some(_transaction) = self.pool.try_legacy_fixed_transaction()? else {
            return Ok(false);
        };
        self.check()?;
        self.poisoned = true;
        let claim = self.claim.as_mut().ok_or_else(|| invalid("runtime claim absent"))?;
        let released =
            claim.reservation.slots.pop().ok_or_else(|| invalid("lost supplemental slot"))?;
        claim.budget = reduced;
        if let Err(error) = claim.publish_owner(std::process::id(), None) {
            // A partial record write never releases its physical slot, and
            // no Drop refund can restore the scheduling credits.
            claim.reservation.slots.push(released);
            return Err(error);
        }
        self.original.store(generation, Ordering::Release);
        drop(released);
        self.poisoned = false;
        Ok(true)
    }

    /// Fair genuine reacquisition through the existing priority queue and
    /// original memory floor. No token is restored before complete claim
    /// publication and native-domain observation. Waiting preserves one ticket.
    pub fn try_reacquire(&mut self) -> io::Result<bool> {
        self.try_reacquire_observed(trust_build_cpu::available_memory())
    }

    fn try_reacquire_observed(&mut self, memory: Option<u64>) -> io::Result<bool> {
        self.check()?;
        let current = self.claim()?.budget;
        // A previous failed queue attempt may have drained some STILL-BACKED
        // tokens. Return only that funded portion before asking for more CPU.
        let unfunded = (self.original_ceiling.get() - current.get()) as usize;
        let funded = self
            .escrow
            .held()
            .checked_sub(unfunded)
            .ok_or_else(|| invalid("runtime escrow lost original custody"))?;
        self.escrow.return_backed(funded)?;
        if current == self.original_ceiling {
            return Ok(true);
        }
        if memory.is_none() {
            return Ok(false);
        }
        if self.reacquire.is_none() {
            let claim = self.claim()?;
            self.reacquire = Some(Coordinator::open_selected(
                &claim.reservation.namespace,
                &claim.reservation.adopted,
                Requirements::new(
                    None,
                    claim.reservation.minimum_slots,
                    1,
                    false,
                    claim.reservation.minimum_memory_bytes,
                )?,
            )?);
        }
        let mut queue = self.reacquire.take().ok_or_else(|| invalid("lost resize ticket"))?;
        let result = queue.attempt_with(memory, 1, |mut supplement| {
            let Some(transaction) = self.pool.try_legacy_fixed_transaction()? else {
                return Ok(None);
            };
            self.check()?;
            let generation = self.next_generation()?;
            let increased = self.share(self.claim()?.reservation.slots.len() + 1)?;
            self.poisoned = true;
            let claim = self.claim.as_mut().ok_or_else(|| invalid("runtime claim absent"))?;
            claim.reservation.slots.append(&mut supplement.slots);
            claim.budget = increased;
            claim.publish_owner(std::process::id(), None)?;
            let room = transaction.observe(
                &claim.reservation.namespace,
                NonZeroU32::new(claim.reservation.minimum_slots)
                    .ok_or_else(|| invalid("zero slot width"))?,
                None,
            )?;
            if !matches!(room, LegacyFixedRoom::Fits { .. }) {
                return Err(invalid("runtime reacquisition exceeds actual native room"));
            }
            claim.check_current()?;
            self.original.store(generation, Ordering::Release);
            self.poisoned = false;
            Ok(Some(()))
        });
        match result {
            Ok(Attempt::Waiting(_)) => {
                self.reacquire = Some(queue);
                Ok(false)
            }
            Ok(Attempt::Admitted(())) => {
                self.check()?;
                let backed = self
                    .escrow
                    .held()
                    .checked_sub(
                        (self.original_ceiling.get() - self.claim()?.budget.get()) as usize,
                    )
                    .ok_or_else(|| invalid("runtime escrow lost original custody"))?;
                self.escrow.return_backed(backed)?;
                Ok(true)
            }
            Err(error) => Err(error),
        }
    }
}

impl Drop for RuntimeFixedClaim {
    fn drop(&mut self) {
        if self.exposed.get() || self.poisoned {
            // There is deliberately no arbitrary-PID/boolean retirement API.
            // Until a V2 owning group/courier consumes this owner and proves
            // retirement, preserve backing and FIFO on unknown Drop. Escrow's
            // own Drop burns bytes; it cannot replenish an unfunded server.
            if let Some(claim) = self.claim.take() {
                std::mem::forget(claim);
            }
            if let Some(directory) = self.directory.take() {
                std::mem::forget(directory);
            }
        }
    }
}

#[cfg(test)]
#[path = "runtime/tests.rs"]
mod tests;
