//! Original shared legacy exclusion for a native worker epoch.
//!
//! The epoch coordinates admission and retains the original worktree. A
//! separate launcher must establish the compiler, CPU and child custody.

use super::*;

// LegacyFence accepts at most 127 descriptions including admission.lock.
const MAX_FENCE_SLOTS: u32 = 126;

/// One unlaunched native worker epoch request in the existing FIFO.
pub struct WorkerEpochAdmission {
    coordinator: Coordinator,
    draining: Option<Draining>,
}

struct Draining {
    worktree: Option<HeldLease>,
    barrier: HeldLease,
}

enum Acquisition {
    Ready(WorkerEpoch),
    Draining(Draining),
}

/// Original worktree lock and legacy shared exclusion, acquired together.
///
/// This is not a CPU allocation. Later legacy writers can request a larger
/// slot view, so validation of this fence cannot replace live CPU accounting.
pub struct WorkerEpoch {
    directory: Directory,
    minimum_slots: u32,
    worktree: Option<HeldLease>,
    fence: Vec<HeldLease>,
}

impl WorkerEpochAdmission {
    /// Use the same account namespace as native fixed admission. A wider
    /// known caller view may add coverage, never reduce the host default.
    pub fn for_current_user(
        worktree: Option<PathBuf>,
        requested_slots: u32,
        minimum_memory_bytes: u64,
    ) -> io::Result<Self> {
        if !cfg!(all(target_os = "macos", target_arch = "aarch64")) {
            return Err(io::Error::new(
                io::ErrorKind::Unsupported,
                "native worker epoch requires macOS arm64",
            ));
        }
        let locations = Locations::current()?;
        let (legacy, canonical_slots) = trust_build_cpu::LegacyRetirement::canonical_layout()?;
        if fs::canonicalize(legacy)? != locations.namespace {
            return Err(invalid("custom namespace cannot select native worker exclusion"));
        }
        let minimum_slots = requested_slots.max(canonical_slots);
        Self::open(
            &locations.namespace,
            &locations.adopted,
            worktree,
            minimum_slots,
            minimum_memory_bytes,
        )
    }

    fn open(
        namespace: &Path,
        adopted: &Path,
        worktree: Option<PathBuf>,
        minimum_slots: u32,
        minimum_memory_bytes: u64,
    ) -> io::Result<Self> {
        if minimum_slots == 0 || minimum_slots > MAX_FENCE_SLOTS {
            return Err(invalid("worker epoch slot view exceeds the original transport bound"));
        }
        let required = Requirements::new(worktree, minimum_slots, 1, true, minimum_memory_bytes)?;
        Ok(Self {
            coordinator: Coordinator::open_selected(namespace, adopted, required)?,
            draining: None,
        })
    }

    /// Advance a compatible join or the FIFO winner's legacy drain. Dropping
    /// a request releases its unlaunched barrier, worktree and ticket.
    pub fn attempt(&mut self, memory: Option<u64>) -> io::Result<Attempt<WorkerEpoch>> {
        let coordinator = &mut self.coordinator;
        let required = &coordinator.ticket.required;
        if memory.map_or(required.minimum_memory_bytes() != 0, |available| {
            available < required.minimum_memory_bytes()
        }) {
            self.draining = None;
            return Ok(Attempt::Waiting(Waiting::MemoryUnavailable));
        }

        let directory = &coordinator.directory;
        let adopted = &coordinator.adopted;
        let minimum_slots = required.slots();
        let draining = if let Some(draining) = self.draining.take() {
            draining
        } else {
            let acquired = coordinator.ticket.attempt(
                memory,
                |path| Ok(lease(path, false, adopted)?.is_some()),
                // A compatible join extends the shared locks blocking an
                // earlier fixed request. Its busy slots cannot make that
                // predecessor ineligible. Ticket still checks memory/worktree.
                |_, _| Ok(true),
                |required| acquire(directory, adopted, required),
            )?;
            match acquired {
                Attempt::Waiting(reason) => return Ok(Attempt::Waiting(reason)),
                Attempt::Admitted(Acquisition::Ready(epoch)) => {
                    return Ok(Attempt::Admitted(epoch));
                }
                Attempt::Admitted(Acquisition::Draining(draining)) => draining,
            }
        };

        draining.barrier.check()?;
        if let Some(worktree) = &draining.worktree {
            worktree.check()?;
        }
        let Some(slots) = fence_slots(directory, adopted, minimum_slots)? else {
            self.draining = Some(draining);
            return Ok(Attempt::Waiting(Waiting::ResourcesBusy));
        };
        // Convert the original admission description. Opening a second
        // description would contend against our own exclusive barrier.
        // flock conversion is not necessarily atomic. If another owner wins,
        // drop every partial lock and rejoin the FIFO on the next attempt.
        // SAFETY: the live original File owns this flock description. The
        // nonblocking conversion reads only that descriptor and flag word.
        if unsafe { libc::flock(draining.barrier.file.as_raw_fd(), libc::LOCK_SH | libc::LOCK_NB) }
            != 0
        {
            let error = io::Error::last_os_error();
            if error.kind() == io::ErrorKind::WouldBlock {
                return Ok(Attempt::Waiting(Waiting::ResourcesBusy));
            }
            return Err(error);
        }
        Ok(Attempt::Admitted(WorkerEpoch::new(
            directory,
            minimum_slots,
            draining.worktree,
            draining.barrier,
            slots,
        )?))
    }
}

fn fence_names(directory: &Directory, minimum: u32) -> io::Result<Vec<OsString>> {
    let names = slot_names(directory, minimum)?;
    if names.len() > MAX_FENCE_SLOTS as usize {
        return Err(invalid("historical slots exceed the worker fence transport bound"));
    }
    Ok(names)
}

fn fence_slots(
    directory: &Directory,
    adopted: &Path,
    minimum: u32,
) -> io::Result<Option<Vec<HeldLease>>> {
    let mut slots = Vec::new();
    for name in fence_names(directory, minimum)? {
        let Some(slot) = lease(&directory.path.join(name), true, adopted)? else {
            return Ok(None);
        };
        slots.push(slot);
    }
    Ok(Some(slots))
}

fn acquire(
    directory: &Directory,
    adopted: &Path,
    required: &Requirements,
) -> io::Result<Option<Acquisition>> {
    let worktree = if let Some(path) = required.worktree() {
        let Some(held) = lease(path, false, adopted)? else { return Ok(None) };
        Some(held)
    } else {
        None
    };
    let admission = directory.path.join("admission.lock");
    if let Some(shared) = lease(&admission, true, adopted)? {
        if let Some(slots) = fence_slots(directory, adopted, required.slots())? {
            return Ok(Some(Acquisition::Ready(WorkerEpoch::new(
                directory,
                required.slots(),
                worktree,
                shared,
                slots,
            )?)));
        }
    }
    let Some(barrier) = lease(&admission, false, adopted)? else { return Ok(None) };
    Ok(Some(Acquisition::Draining(Draining { worktree, barrier })))
}

impl WorkerEpoch {
    fn new(
        directory: &Directory,
        minimum_slots: u32,
        worktree: Option<HeldLease>,
        admission: HeldLease,
        slots: Vec<HeldLease>,
    ) -> io::Result<Self> {
        let epoch = Self {
            directory: Directory {
                path: directory.path.clone(),
                file: directory.file.try_clone()?,
            },
            minimum_slots,
            worktree,
            fence: std::iter::once(admission).chain(slots).collect(),
        };
        epoch.check_current()?;
        Ok(epoch)
    }

    /// Recheck original names and file identities before using the fence.
    pub fn check_current(&self) -> io::Result<()> {
        self.directory.check()?;
        if let Some(worktree) = &self.worktree {
            worktree.check()?;
        }
        let names = fence_names(&self.directory, self.minimum_slots)?;
        if !self.fence.iter().skip(1).map(|slot| &slot.name).eq(&names) {
            return Err(invalid("legacy slot view changed after worker epoch acquisition"));
        }
        for lease in &self.fence {
            lease.check()?;
        }
        Ok(())
    }
}

#[cfg(test)]
#[path = "worker_epoch/tests.rs"]
mod tests;
