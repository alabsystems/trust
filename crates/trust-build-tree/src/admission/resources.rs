//! Original kernel claims behind the native priority queue.
//!
//! These values coordinate the existing legacy namespace. They are not a CPU
//! budget, an original GNU credit, a host loan, SDK custody or launch authority.
//! The final native launcher must additionally settle those actual domains.

use std::ffi::OsString;

use super::*;

#[cfg(feature = "machine-admission")]
#[path = "resources/worker_epoch.rs"]
mod worker_epoch;
#[cfg(feature = "native-exec")]
pub use machine::{RuntimeClaimCurrency, RuntimeFixedClaim};
#[cfg(feature = "machine-admission")]
pub use worker_epoch::{WorkerEpoch, WorkerEpochAdmission};

#[cfg(feature = "machine-admission")]
#[path = "adoption.rs"]
mod adoption;
#[cfg(feature = "machine-admission")]
pub use adoption::{Adoption, AdoptionError, AdoptionObservation, AdoptionOutcome, Publication};

pub(super) struct HeldLease {
    directory: Directory,
    name: OsString,
    file: File,
}
impl HeldLease {
    fn path(&self) -> PathBuf {
        self.directory.path.join(&self.name)
    }
    fn check(&self) -> io::Result<()> {
        self.directory.check_file(&self.name, &self.file)
    }
}

fn lease(path: &Path, shared: bool, adopted: &Path) -> io::Result<Option<HeldLease>> {
    validate_path(path)?;
    let parent = path.parent().ok_or_else(|| invalid("lease has no parent"))?;
    let name = path.file_name().ok_or_else(|| invalid("lease has no leaf"))?.to_os_string();
    let directory = Directory::open(parent)?;
    let file = directory.open_file(&name, true)?;
    let locked = if shared { file.try_lock_shared() } else { file.try_lock() };
    match locked {
        Ok(()) => {}
        Err(std::fs::TryLockError::WouldBlock) => return Ok(None),
        Err(std::fs::TryLockError::Error(error)) => return Err(error),
    }
    let held = HeldLease { directory, name, file };
    held.check()?;
    // Logical adoption debt is checked AFTER the real flock is held. A new
    // complete publication cannot interleave on any path retained by this claim.
    let path = fs::canonicalize(held.path())?;
    if !adopted::available(adopted, &path)? {
        return Ok(None);
    }
    held.check()?;
    Ok(Some(held))
}

fn slot_names(directory: &Directory, minimum: u32) -> io::Result<Vec<OsString>> {
    let mut names: std::collections::BTreeSet<OsString> =
        (0..minimum).map(|index| OsString::from(format!("slot-{index}"))).collect();
    for name in directory.entries()? {
        if name
            .as_bytes()
            .strip_prefix(b"slot-")
            .is_some_and(|tail| !tail.is_empty() && tail.iter().all(u8::is_ascii_digit))
        {
            names.insert(name);
            if names.len() > MAX_TICKETS {
                return Err(invalid("legacy slot namespace exceeds its bound"));
            }
        }
    }
    Ok(names.into_iter().collect())
}

fn shared_slots(
    directory: &Directory,
    adopted: &Path,
    count: u32,
    needed: u32,
    maximum: u32,
) -> io::Result<Option<Vec<HeldLease>>> {
    let mut held = Vec::new();
    for index in 0..count {
        if let Some(lease) = lease(&directory.path.join(format!("slot-{index}")), false, adopted)? {
            held.push(lease);
            if held.len() == maximum as usize {
                break;
            }
        }
    }
    if held.len() < needed as usize {
        return Ok(None);
    }
    directory.check()?;
    Ok(Some(held))
}

/// Native coordination in an explicitly selected ORIGINAL namespace. No
/// alternate pool is created. Production selection must use the account's
/// canonical directory and canonical adoption registry, independent of HOME.
pub struct Coordinator {
    directory: Directory,
    adopted: PathBuf,
    ticket: Ticket,
}
impl Coordinator {
    /// Select the original namespace from the Unix account database, retaining
    /// the explicit BUILD_SLOT_DIR override. Scratch HOME never selects the
    /// canonical adoption registry. Missing/unsafe namespaces refuse.
    pub fn for_current_user(required: Requirements) -> io::Result<Self> {
        let locations = Locations::current()?;
        Self::open_selected(&locations.namespace, &locations.adopted, required)
    }

    #[cfg(test)]
    fn open(
        namespace: &Path,
        adoption_registry: &Path,
        required: Requirements,
    ) -> io::Result<Self> {
        Self::open_selected(namespace, adoption_registry, required)
    }

    fn open_selected(
        namespace: &Path,
        adoption_registry: &Path,
        required: Requirements,
    ) -> io::Result<Self> {
        validate_path(adoption_registry)?;
        let directory = Directory::open(namespace)?;
        let ticket = Ticket::open(namespace, required)?;
        Ok(Self { directory, adopted: adoption_registry.to_owned(), ticket })
    }

    /// Nonblocking full-claim acquisition. `maximum` permits idle-share
    /// borrowing within the same originally requested pool; it cannot enlarge
    /// that pool. Memory and CPU policy remain the native launcher's duty.
    pub fn attempt(
        &mut self,
        memory: Option<u64>,
        maximum: u32,
    ) -> io::Result<Attempt<Reservation>> {
        self.attempt_with(memory, maximum, |reservation| Ok(Some(reservation)))
    }

    fn attempt_with<T>(
        &mut self,
        memory: Option<u64>,
        maximum: u32,
        complete: impl FnOnce(Reservation) -> io::Result<Option<T>>,
    ) -> io::Result<Attempt<T>> {
        let required = &self.ticket.required;
        if maximum < required.needed || maximum > required.slots {
            return Err(invalid("invalid maximum reserved slot count"));
        }
        if required.exclusive && memory.is_none() {
            return Ok(Attempt::Waiting(super::Waiting::MemoryUnavailable));
        }
        let directory = &self.directory;
        let adopted = &self.adopted;
        self.ticket.attempt(
            memory,
            |path| Ok(lease(path, false, adopted)?.is_some()),
            |count, needed| Ok(shared_slots(directory, adopted, count, needed, needed)?.is_some()),
            |required| {
                let mut held = Vec::new();
                if let Some(path) = required.worktree() {
                    let Some(worktree) = lease(path, false, adopted)? else { return Ok(None) };
                    held.push(worktree);
                }
                let Some(admission) =
                    lease(&directory.path.join("admission.lock"), !required.exclusive, adopted)?
                else {
                    return Ok(None);
                };
                held.push(admission);
                let slots = if required.exclusive {
                    // Retain the winning admission/worktree reservation while
                    // draining old slots, exactly as the original protocol.
                    Vec::new()
                } else {
                    let Some(slots) =
                        shared_slots(directory, adopted, required.slots, required.needed, maximum)?
                    else {
                        return Ok(None);
                    };
                    slots
                };
                let reservation = Reservation {
                    held,
                    slots,
                    namespace: directory.path.clone(),
                    adopted: adopted.clone(),
                    minimum_slots: required.slots,
                    exclusive: required.exclusive,
                    drained: !required.exclusive,
                    minimum_memory_bytes: required.minimum_memory_bytes,
                    #[cfg(feature = "native-exec")]
                    required_slots: required.needed,
                };
                reservation.check_current()?;
                // Complete every additional unlaunched domain BEFORE retiring
                // the priority ticket. A refusal closes all partial resources.
                complete(reservation)
            },
        )
    }
}

struct Locations {
    namespace: PathBuf,
    adopted: PathBuf,
}
impl Locations {
    fn current() -> io::Result<Self> {
        let home = account_home()?;
        let canonical = home.join(".cache/build-slot");
        let selected = std::env::var_os("BUILD_SLOT_DIR")
            .filter(|value| !value.is_empty())
            .map(PathBuf::from)
            .unwrap_or_else(|| canonical.clone());
        let namespace = fs::canonicalize(selected)?;
        validate_path(&namespace)?;
        Ok(Self { namespace, adopted: canonical.join("adopted") })
    }
}

pub(super) fn account_home() -> io::Result<PathBuf> {
    // Real/effective UID divergence has no qualified native admission contract.
    let uid = unsafe { libc::getuid() };
    if uid != unsafe { libc::geteuid() } {
        return Err(invalid("native admission requires matching real/effective account IDs"));
    }
    let mut bytes = vec![0_u8; 4096];
    loop {
        let mut entry = std::mem::MaybeUninit::<libc::passwd>::zeroed();
        let mut found = std::ptr::null_mut();
        // SAFETY: the output structure, pointer and byte buffer are writable.
        let result = unsafe {
            libc::getpwuid_r(
                uid,
                entry.as_mut_ptr(),
                bytes.as_mut_ptr().cast(),
                bytes.len(),
                &mut found,
            )
        };
        if result == libc::ERANGE && bytes.len() < 1024 * 1024 {
            bytes.resize(bytes.len() * 2, 0);
            continue;
        }
        if result != 0 {
            return Err(io::Error::from_raw_os_error(result));
        }
        if found.is_null() {
            return Err(invalid("native admission account home is unavailable"));
        }
        // SAFETY: the successful call initialized entry; its strings remain
        // valid in the unchanged buffer until this iteration returns.
        let entry = unsafe { entry.assume_init() };
        if entry.pw_dir.is_null() {
            return Err(invalid("native admission account home is absent"));
        }
        let home = PathBuf::from(std::ffi::OsStr::from_bytes(
            unsafe { std::ffi::CStr::from_ptr(entry.pw_dir) }.to_bytes(),
        ));
        validate_path(&home)?;
        let home = fs::canonicalize(home)?;
        if !home.is_dir() {
            return Err(invalid("native admission account home is not a directory"));
        }
        return Ok(home);
    }
}

/// Original retained file descriptions, with no child launched. Dropping a
/// partial or unsuccessful attempt closes every lock; no PID text owns them.
pub struct Reservation {
    held: Vec<HeldLease>,
    slots: Vec<HeldLease>,
    namespace: PathBuf,
    adopted: PathBuf,
    minimum_slots: u32,
    exclusive: bool,
    drained: bool,
    minimum_memory_bytes: u64,
    // Original requested minimum; extra automatic shares may be lent, but
    // runtime adaptation cannot turn an explicit fixed request into a smaller one.
    #[cfg(feature = "native-exec")]
    required_slots: u32,
}

#[cfg(feature = "machine-admission")]
#[path = "machine.rs"]
mod machine;
#[cfg(all(feature = "native-exec", target_os = "macos", target_arch = "aarch64"))]
pub use machine::ExecutionStartPipe;
#[cfg(feature = "machine-admission")]
pub use machine::{
    EarlyFixedClaim, FIXED_HANDOFF_ENV, FixedClaim, FixedCommandAdmission, FixedCommandSignal,
    FixedCpuRequest, InheritedFixedClaim, MemberDirectory, PreparedFixedCommand,
    RunningFixedCommand, RunningFixedGroup,
};
#[cfg(all(feature = "native-exec", target_os = "macos", target_arch = "aarch64"))]
pub use machine::{PreparedNestedFixedCommand, RunningNestedFixedCommand};

impl Reservation {
    pub fn check_current(&self) -> io::Result<()> {
        for lease in self.held.iter().chain(&self.slots) {
            lease.check()?;
        }
        Ok(())
    }
    /// Actual held coordination slots; never infer a CPU budget from this.
    pub fn held_slot_count(&self) -> usize {
        self.slots.len()
    }
    pub fn is_exclusive(&self) -> bool {
        self.exclusive
    }
    /// Original requested memory floor. A reading is never a reservation.
    pub fn minimum_memory_bytes(&self) -> u64 {
        self.minimum_memory_bytes
    }
    /// Complete exclusive slot acquisition or retain only the original
    /// admission/worktree reservation. Every historical numeric slot is covered.
    /// This is pool draining, not the later measured quiet-host precondition.
    pub fn try_drain_exclusive(&mut self) -> io::Result<bool> {
        if !self.exclusive {
            return Err(invalid("shared admission cannot become exclusive"));
        }
        self.check_current()?;
        if self.drained {
            return Ok(true);
        }
        let directory = Directory::open(&self.namespace)?;
        let mut slots = Vec::new();
        for name in slot_names(&directory, self.minimum_slots)? {
            let Some(slot) = lease(&directory.path.join(name), false, &self.adopted)? else {
                return Ok(false);
            };
            slots.push(slot);
        }
        self.check_current()?;
        directory.check()?;
        self.slots = slots;
        self.drained = true;
        Ok(true)
    }
}

#[cfg(test)]
mod tests;
