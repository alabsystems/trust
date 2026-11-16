//! Size a fixed command from the original pool and its actual acquired slots.
//! Policy inputs and memory observations are not resource grants. The queue,
//! original leases and native manifest transaction still establish the claim.

use std::num::NonZeroU64;

use super::*;

/// Admission-time sizing for a fixed command. This does not resize live work or
/// substitute for the separate native worker protocol.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FixedCpuRequest {
    /// Borrow currently idle shares, bounded by current measured memory.
    Automatic,
    /// Reserve enough original shares for this exact CPU ceiling.
    Limit(NonZeroU32),
}

/// One native fixed-command request in the existing canonical namespace.
/// Retrying preserves the original priority ticket; no command starts here.
pub struct FixedCommandAdmission {
    coordinator: Coordinator,
    pool: Option<Pool>,
    cpus: NonZeroU32,
    request: FixedCpuRequest,
    check_lifecycle: fn(&Reservation) -> io::Result<()>,
}

impl FixedCommandAdmission {
    /// Open the canonical machine queue. Existing sealed pool width is reused.
    /// On first use, kernel online CPU width sizes this request, but backing is
    /// created only after its original canonical legacy exclusion is acquired.
    /// Neither observation nor backing creation grants an execution credit.
    pub fn for_current_user(
        worktree_lock: Option<PathBuf>,
        slots: Option<NonZeroU32>,
        exclusive: bool,
        request: FixedCpuRequest,
        minimum_memory_bytes: NonZeroU64,
    ) -> io::Result<Self> {
        let locations = Locations::current()?;
        let legacy = account_home()?.join(".cache/build-slot");
        check_canonical_namespace(&legacy, &locations.namespace)?;
        legacy_pool_lifecycle()?;
        let pool = Pool::open_existing(&trust_build_cpu::capacity_dir()?)?;
        let cpus = match &pool {
            Some(pool) => pool.slots(),
            None => online_machine_width()?,
        };
        // A smaller caller view cannot turn one idle original slot into the
        // whole machine while other canonical legacy slots remain occupied.
        let required = requirements(
            worktree_lock,
            canonical_slot_count(slots, cpus),
            exclusive,
            request,
            minimum_memory_bytes,
            cpus,
        )?;
        let coordinator =
            Coordinator::open_selected(&locations.namespace, &locations.adopted, required)?;
        check_canonical_namespace(&legacy, &coordinator.directory.path)?;
        Ok(Self {
            coordinator,
            pool,
            cpus,
            request,
            check_lifecycle: canonical_reservation_lifecycle,
        })
    }

    #[cfg(test)]
    fn open_existing(
        capacity: &Path,
        worktree_lock: Option<PathBuf>,
        slots: Option<NonZeroU32>,
        exclusive: bool,
        request: FixedCpuRequest,
        minimum_memory_bytes: NonZeroU64,
        open_coordinator: impl FnOnce(Requirements) -> io::Result<Coordinator>,
    ) -> io::Result<Self> {
        let pool = Pool::open_existing(capacity)?.ok_or_else(|| {
            io::Error::new(
                io::ErrorKind::NotFound,
                "original native CPU pool is absent. Inspect with `targo --unverified resource status --json`",
            )
        })?;
        let required = requirements(
            worktree_lock,
            slots.map_or((pool.slots().get() / 6).max(1), NonZeroU32::get),
            exclusive,
            request,
            minimum_memory_bytes,
            pool.slots(),
        )?;
        let coordinator = open_coordinator(required)?;
        let cpus = pool.slots();
        Ok(Self {
            coordinator,
            pool: Some(pool),
            cpus,
            request,
            check_lifecycle: |_| Ok(()),
        })
    }

    /// Take a fresh native memory observation and attempt the whole original
    /// claim without blocking. Unknown/insufficient memory grants no share.
    pub fn attempt(&mut self) -> io::Result<Attempt<FixedClaim>> {
        self.attempt_observed(trust_build_cpu::available_memory())
    }

    fn attempt_observed(&mut self, memory: Option<u64>) -> io::Result<Attempt<FixedClaim>> {
        self.attempt_observed_with(memory, Pool::try_for_current_user)
    }

    fn attempt_observed_with(
        &mut self,
        memory: Option<u64>,
        initialize: impl FnOnce(NonZeroU32) -> io::Result<Pool>,
    ) -> io::Result<Attempt<FixedClaim>> {
        let required = &self.coordinator.ticket.required;
        let maximum = match (required.exclusive, self.request, memory) {
            (false, FixedCpuRequest::Automatic, Some(bytes)) => {
                // This constructor requires a positive per-share floor. The
                // same observation also passes through the queue's floor check.
                (bytes / required.minimum_memory_bytes)
                    .min(u64::from(required.slots))
                    .max(1) as u32
            }
            _ => required.needed,
        };
        let cpus = self.cpus;
        let request = self.request;
        let existing = self.pool.clone();
        let check = self.check_lifecycle;
        let mut initialized = None;
        let result = self.coordinator.attempt_fixed_with_pool(
            memory,
            maximum,
            |reservation| {
                // These actual original guards, not the observed width or a
                // namespace string, precede any first-use backing creation.
                reservation.check_current()?;
                check(reservation)?;
                let pool = match existing {
                    Some(pool) => pool,
                    None => initialize(cpus)?,
                };
                if pool.slots() != cpus {
                    return Err(invalid(
                        "fixed machine pool width changed during initialization",
                    ));
                }
                initialized = Some(pool.clone());
                Ok(pool)
            },
            check,
            |reservation| {
                let budget = match request {
                    FixedCpuRequest::Limit(limit) => limit,
                    FixedCpuRequest::Automatic if reservation.exclusive => cpus,
                    FixedCpuRequest::Automatic => {
                        // Count only the successfully acquired original leases,
                        // inside the same manifest transaction that publishes them.
                        let share = u64::from(cpus.get()) * reservation.slots.len() as u64
                            / u64::from(reservation.minimum_slots);
                        NonZeroU32::new(share.max(1).min(u64::from(cpus.get())) as u32).unwrap()
                    }
                };
                Ok(budget)
            },
        );
        if let Some(pool) = initialized {
            self.pool = Some(pool);
        }
        result
    }
}

fn check_canonical_namespace(canonical: &Path, selected: &Path) -> io::Result<()> {
    if fs::canonicalize(canonical)?.as_path() != selected {
        return Err(invalid(
            "custom coordination namespace cannot select machine CPU authority",
        ));
    }
    Ok(())
}

fn canonical_slot_count(requested: Option<NonZeroU32>, cpus: NonZeroU32) -> u32 {
    let original = (cpus.get() / 6).max(1);
    requested.map_or(original, |value| value.get().max(original))
}

fn online_machine_width() -> io::Result<NonZeroU32> {
    // SAFETY: sysconf reads the kernel's online machine count. Unlike local
    // available_parallelism, this is not an affinity/quota or environment cap.
    let measured = unsafe { libc::sysconf(libc::_SC_NPROCESSORS_ONLN) };
    u32::try_from(measured)
        .ok()
        .filter(|width| *width <= trust_build_cpu::MAX_SLOTS)
        .and_then(NonZeroU32::new)
        .ok_or_else(|| {
            invalid("online machine CPU width is unavailable or outside the native bound")
        })
}

fn canonical_reservation_lifecycle(reservation: &Reservation) -> io::Result<()> {
    // Locations::current selected a physical namespace. Rebind the original
    // account path at both admission boundaries so a retargeted logical alias
    // cannot leave this request coordinating an abandoned namespace.
    check_canonical_namespace(
        &account_home()?.join(".cache/build-slot"),
        &reservation.namespace,
    )?;
    legacy_pool_lifecycle()
}

fn legacy_pool_lifecycle() -> io::Result<()> {
    legacy_pool_state(trust_build_cpu::NativeDomain::migration_status_canonical()?)
}

fn legacy_pool_state(state: trust_build_cpu::NativeMigrationStatus) -> io::Result<()> {
    use trust_build_cpu::NativeMigrationStatus;
    match state {
        NativeMigrationStatus::NotStarted => Ok(()),
        _ => Err(io::Error::new(io::ErrorKind::PermissionDenied,
            "fixed legacy admission cannot initialize or replace a prepared or retired native domain")),
    }
}

fn requirements(
    worktree: Option<PathBuf>,
    slots: u32,
    exclusive: bool,
    request: FixedCpuRequest,
    memory: NonZeroU64,
    cpus: NonZeroU32,
) -> io::Result<Requirements> {
    let needed = match request {
        FixedCpuRequest::Automatic => 1,
        FixedCpuRequest::Limit(limit) => {
            if limit > cpus {
                return Err(invalid(
                    "fixed CPU request exceeds the original native pool width",
                ));
            }
            // A fractional last share must still reserve its original slot.
            (u64::from(limit.get()) * u64::from(slots)).div_ceil(u64::from(cpus.get())) as u32
        }
    };
    Requirements::new(worktree, slots, needed, exclusive, memory.get())
}

#[cfg(test)]
#[path = "policy/tests.rs"]
mod tests;
