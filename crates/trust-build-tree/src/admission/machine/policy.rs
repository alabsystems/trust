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
    pool: Pool,
    request: FixedCpuRequest,
}

impl FixedCommandAdmission {
    /// Open the existing machine pool and queue. An omitted slot count uses
    /// the canonical width derived from that original pool, never scratch HOME
    /// or a caller's available_parallelism/affinity. Custom namespaces refuse.
    /// An absent pool returns `NotFound` before any queue ticket is opened.
    pub fn for_current_user(
        worktree_lock: Option<PathBuf>,
        slots: Option<NonZeroU32>,
        exclusive: bool,
        request: FixedCpuRequest,
        minimum_memory_bytes: NonZeroU64,
    ) -> io::Result<Self> {
        Self::open_existing(
            &trust_build_cpu::capacity_dir()?,
            worktree_lock,
            slots,
            exclusive,
            request,
            minimum_memory_bytes,
            |required| {
                let locations = Locations::current()?;
                let legacy = account_home()?.join(".cache/build-slot");
                let check_canonical = |selected: &Path| {
                    if fs::canonicalize(&legacy)?.as_path() != selected {
                        return Err(invalid(
                            "custom coordination namespace cannot select machine CPU authority",
                        ));
                    }
                    Ok(())
                };
                check_canonical(&locations.namespace)?;
                let coordinator =
                    Coordinator::open_selected(&locations.namespace, &locations.adopted, required)?;
                check_canonical(&coordinator.directory.path)?;
                Ok(coordinator)
            },
        )
    }

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
        Ok(Self { coordinator, pool, request })
    }

    /// Take a fresh native memory observation and attempt the whole original
    /// claim without blocking. Unknown/insufficient memory grants no share.
    pub fn attempt(&mut self) -> io::Result<Attempt<FixedClaim>> {
        self.attempt_observed(trust_build_cpu::available_memory())
    }

    fn attempt_observed(&mut self, memory: Option<u64>) -> io::Result<Attempt<FixedClaim>> {
        let required = &self.coordinator.ticket.required;
        let maximum = match (required.exclusive, self.request, memory) {
            (false, FixedCpuRequest::Automatic, Some(bytes)) => {
                // This constructor requires a positive per-share floor. The
                // same observation also passes through the queue's floor check.
                (bytes / required.minimum_memory_bytes).min(u64::from(required.slots)).max(1) as u32
            }
            _ => required.needed,
        };
        let cpus = self.pool.slots();
        let request = self.request;
        self.coordinator.attempt_fixed_with_budget(memory, maximum, &self.pool, |reservation| {
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
        })
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
                return Err(invalid("fixed CPU request exceeds the original native pool width"));
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
