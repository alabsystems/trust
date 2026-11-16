// SPDX-License-Identifier: MIT OR Apache-2.0
// Copyright 2026 Andrew Yates

use std::ffi::{CStr, CString, OsStr};
use std::fs::{DirBuilder, File};
use std::io::{self, Read, Seek, SeekFrom, Write};
use std::num::NonZeroU32;
use std::os::fd::{AsFd, AsRawFd, BorrowedFd, FromRawFd};
use std::os::unix::ffi::OsStrExt;
use std::os::unix::fs::{DirBuilderExt, MetadataExt};
use std::path::{Path, PathBuf};
use std::sync::Arc;
use std::sync::atomic::{AtomicU32, Ordering};

use crate::{DIRECTORY_NAME, MAX_RECORD_BYTES, MAX_SLOTS, Owner, Record, SlotState, invalid};

/// Native per-account capacity directory, independent of a scratch `HOME`.
/// The account database is the one authority for the Unix home directory.
pub fn capacity_dir() -> io::Result<PathBuf> {
    let home = account_home()?;
    Ok(if cfg!(target_os = "macos") {
        home.join("Library/Caches/aterm/capacity")
    } else {
        home.join(".cache/aterm/capacity")
    })
}

pub(crate) fn account_home() -> io::Result<PathBuf> {
    // SAFETY: getuid has no arguments and only reads this process's real uid.
    let uid = unsafe { libc::getuid() };
    let mut bytes = vec![0u8; 4096];
    loop {
        let mut entry = std::mem::MaybeUninit::<libc::passwd>::zeroed();
        let mut found = std::ptr::null_mut();
        // SAFETY: entry, found and bytes are writable for their declared sizes;
        // successful pointers are read only while this call's buffer is alive.
        let result = unsafe {
            libc::getpwuid_r(
                uid,
                entry.as_mut_ptr(),
                bytes.as_mut_ptr().cast(),
                bytes.len(),
                &raw mut found,
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
            return Err(io::Error::new(io::ErrorKind::NotFound, "account home is unavailable"));
        }
        // SAFETY: a successful getpwuid_r initialized entry and its home string
        // points into bytes, which is still alive and has not moved.
        let entry = unsafe { entry.assume_init() };
        if entry.pw_dir.is_null() {
            return Err(invalid("account home is absent"));
        }
        // SAFETY: pw_dir is the NUL-terminated string from getpwuid_r above.
        let home =
            PathBuf::from(OsStr::from_bytes(unsafe { CStr::from_ptr(entry.pw_dir) }.to_bytes()));
        if !home.is_absolute() {
            return Err(invalid("account home is not absolute"));
        }
        return Ok(home);
    }
}

#[derive(Debug)]
struct Inner {
    directory: File,
    path: PathBuf,
    config: Identity,
    identities: Vec<Identity>,
    slots: NonZeroU32,
    next: AtomicU32,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct Identity {
    pub(super) dev: u64,
    pub(super) ino: u64,
}

impl Identity {
    pub(super) fn of(file: &File) -> io::Result<Self> {
        let meta = file.metadata()?;
        Ok(Self { dev: meta.dev(), ino: meta.ino() })
    }
}

const CONFIG_MAX_BYTES: usize = 128 + MAX_SLOTS as usize * 64;

/// A shared CPU pool, with one kernel lock per permitted executing unit.
/// Clones share a directory handle and rotate their starting scan position.
#[derive(Clone, Debug)]
pub struct Pool(Arc<Inner>);

enum Initialization {
    Wait,
    Try,
}

impl Initialization {
    fn lock(self, file: &File) -> io::Result<()> {
        match self {
            Self::Wait => file.lock(),
            Self::Try => file.try_lock().map_err(|error| match error {
                std::fs::TryLockError::WouldBlock => io::ErrorKind::WouldBlock.into(),
                std::fs::TryLockError::Error(error) => error,
            }),
        }
    }
}

impl Pool {
    /// Only the authenticated workload receiver can call this path: `file` is
    /// transferred by the actual original live custodian, never caller-offered.
    /// There is deliberately no lock/acquire/repair syscall here. The original
    /// host and receiver retain the SAME description; closing copies, rather
    /// than an explicit unlock, is their only permitted release operation.
    #[cfg(all(feature = "native-host", any(target_os = "linux", target_os = "macos")))]
    pub(crate) fn continue_workload_original(&self, slot: u32, file: File) -> io::Result<Lease> {
        self.validate_path()?;
        check_private(&file, false)?;
        if self.0.identities.get(slot as usize) != Some(&Identity::of(&file)?) {
            return Err(invalid("original workload description differs from sealed slot"));
        }
        continue_original_workload_file(slot, file)
    }
    /// Open the current account's pool. `slots` is the machine-wide capacity,
    /// not this invocation's local `-j` limit. Conflicting capacities refuse.
    pub fn for_current_user(slots: NonZeroU32) -> io::Result<Self> {
        Self::open_in(&capacity_dir()?, slots)
    }

    /// Open or initialize the account's pool without waiting for a competing
    /// initializer's advisory lock. The computer-level owner supplies `slots`.
    /// Other filesystem operations retain their ordinary IO behavior.
    /// Opening backing grants no CPU lease or domain activation.
    pub fn try_for_current_user(slots: NonZeroU32) -> io::Result<Self> {
        Self::try_open_in(&capacity_dir()?, slots)
    }

    /// Open a pool under an explicit absolute capacity directory. Production
    /// callers should use `for_current_user`; this also permits isolated tests.
    /// The capacity parent must be owned and not writable by others; the pool
    /// directory and its regular single-link files must also remain private.
    pub fn open_in(capacity: &Path, slots: NonZeroU32) -> io::Result<Self> {
        Self::open_in_with(capacity, slots, Initialization::Wait)
    }

    /// Explicit-scope counterpart of [`Self::try_for_current_user`]. A competing
    /// initializer returns `WouldBlock`, including after an initial absence
    /// observation. Existing widths, identities and protocol refusals remain
    /// intact. Opening backing grants no CPU lease or domain activation.
    pub fn try_open_in(capacity: &Path, slots: NonZeroU32) -> io::Result<Self> {
        Self::open_in_with(capacity, slots, Initialization::Try)
    }

    fn open_in_with(
        capacity: &Path,
        slots: NonZeroU32,
        initialization: Initialization,
    ) -> io::Result<Self> {
        if !capacity.is_absolute() || slots.get() > MAX_SLOTS {
            return Err(invalid("invalid CPU pool path or slot count"));
        }
        // Existing published pools need no write access to their capacity parent.
        // In particular a retired legacy memory ledger can keep that parent
        // read-only while its independently private CPU child remains writable.
        if let Some(pool) = Self::open_existing(capacity)? {
            if pool.slots() != slots {
                return Err(invalid("CPU pool capacity differs"));
            }
            return Ok(pool);
        }
        Self::initialize_in(capacity, slots, initialization)
    }

    fn initialize_in(
        capacity: &Path,
        slots: NonZeroU32,
        initialization: Initialization,
    ) -> io::Result<Self> {
        if !capacity.exists() {
            DirBuilder::new().recursive(true).mode(0o700).create(capacity)?;
        }
        let capacity_handle = open_parent(capacity)?;
        let name = CString::new(DIRECTORY_NAME).expect("fixed directory name");
        // SAFETY: valid directory descriptor and fixed NUL-terminated leaf.
        if unsafe { libc::mkdirat(capacity_handle.as_raw_fd(), name.as_ptr(), 0o700) } < 0 {
            let error = io::Error::last_os_error();
            if error.kind() != io::ErrorKind::AlreadyExists {
                return Err(error);
            }
        }
        let path = capacity.join(DIRECTORY_NAME);
        let directory =
            open_at(&capacity_handle, DIRECTORY_NAME, libc::O_RDONLY | libc::O_DIRECTORY, false)?;
        check_private(&directory, true)?;
        // Typed, so a reader of the lock sites (aterm's lock-order census) can see this is an OS
        // advisory lock rather than an in-process mutex; nothing fallible runs between taking the
        // lock and the guard that lets it go.
        let initialization_file: std::fs::File =
            open_at(&directory, "init.lock", libc::O_RDWR, true)?;
        check_private(&initialization_file, false)?;
        initialization.lock(&initialization_file)?;
        let initialization = Probe(initialization_file);
        let mut config = match open_at(&directory, "pool", libc::O_RDONLY, false) {
            Err(error) if error.kind() == io::ErrorKind::NotFound => {
                let mut identities = Vec::with_capacity(slots.get() as usize);
                for slot in 0..slots.get() {
                    let file = open_at(&directory, &slot_name(slot), libc::O_RDWR, true)?;
                    check_private(&file, false)?;
                    identities.push(Identity::of(&file)?);
                }
                publish_config(&directory, &encode_config(&identities))?;
                open_at(&directory, "pool", libc::O_RDONLY, false)?
            }
            result => result?,
        };
        check_private(&config, false)?;
        let identities = parse_config(&read_text(&mut config, CONFIG_MAX_BYTES)?)?;
        if identities.len() != slots.get() as usize {
            return Err(invalid("CPU pool capacity differs"));
        }
        let config_identity = Identity::of(&config)?;
        drop(initialization);
        let pool = Self::from_parts(directory, path, config_identity, identities)?;
        pool.validate_path()?;
        Ok(pool)
    }

    /// Open an existing pool without creating or repairing any file.
    /// `None` means its capacity directory or pool does not exist. A pending
    /// initialization is an error, never a claim that every slot is free.
    pub fn open_existing(capacity: &Path) -> io::Result<Option<Self>> {
        if !capacity.is_absolute() {
            return Err(invalid("CPU pool path is not absolute"));
        }
        let parent = match open_parent(capacity) {
            Err(error) if error.kind() == io::ErrorKind::NotFound => return Ok(None),
            result => result?,
        };
        let directory =
            match open_at(&parent, DIRECTORY_NAME, libc::O_RDONLY | libc::O_DIRECTORY, false) {
                Err(error) if error.kind() == io::ErrorKind::NotFound => return Ok(None),
                result => result?,
            };
        check_private(&directory, true)?;
        let _initialization = observe_initialization(&directory)?;
        let mut config = open_at(&directory, "pool", libc::O_RDONLY, false)?;
        check_private(&config, false)?;
        let identities = parse_config(&read_text(&mut config, CONFIG_MAX_BYTES)?)?;
        let identity = Identity::of(&config)?;
        let pool =
            Self::from_parts(directory, capacity.join(DIRECTORY_NAME), identity, identities)?;
        pool.validate_path()?;
        Ok(Some(pool))
    }

    fn from_parts(
        directory: File,
        path: PathBuf,
        config: Identity,
        identities: Vec<Identity>,
    ) -> io::Result<Self> {
        let slots = NonZeroU32::new(
            u32::try_from(identities.len()).map_err(|_| invalid("CPU pool too large"))?,
        )
        .ok_or_else(|| invalid("CPU pool has no slots"))?;
        let pool = Self(Arc::new(Inner {
            directory,
            path,
            config,
            identities,
            slots,
            next: AtomicU32::new(0),
        }));
        for slot in 0..slots.get() {
            pool.open_slot(slot, false)?;
        }
        Ok(pool)
    }

    /// Pool location for diagnostics. Never remove or replace it while used.
    #[must_use]
    pub fn path(&self) -> &Path {
        &self.0.path
    }

    /// Machine-wide slot count, independent of a scheduler's local parallelism.
    #[must_use]
    pub fn slots(&self) -> NonZeroU32 {
        self.0.slots
    }

    #[cfg(feature = "jobserver")]
    pub(crate) fn contains(&self, lease: &Lease) -> io::Result<bool> {
        self.validate_path()?;
        Ok(self.0.identities.get(lease.slot as usize) == Some(&Identity::of(&lease.file)?))
    }

    /// Reuse a trusted producer's inherited CPU slot under serialized admission.
    ///
    /// The target must be observed exclusively held inside the same manifest
    /// transaction as adoption. If its previous holder closes during handoff,
    /// locking the same slot is a checked replacement, not an exact OFD proof.
    /// No participating grant can interleave, and held occupancy cannot exceed
    /// the entry snapshot. Slot metadata is diagnostic, never authorization.
    /// Busy admission returns WouldBlock; retain the original descriptor and
    /// use try_adopt_inherited for a nonblocking controller retry.
    pub fn adopt_inherited(&self, file: File) -> io::Result<Lease> {
        self.try_adopt_inherited(&file, |_| self.slots().get())?
            .ok_or_else(|| io::Error::from(io::ErrorKind::WouldBlock))
    }

    /// Nonblocking inherited continuation. None means busy or policy veto and
    /// leaves the caller's descriptor available for the same checked retry.
    /// Activated external backing requires ExternalDebt's corresponding route.
    /// The callback is a bounded cached GLOBAL native ceiling, not local -j.
    pub fn try_adopt_inherited(
        &self,
        file: &File,
        policy: impl FnOnce(u32) -> u32,
    ) -> io::Result<Option<Lease>> {
        self.validate_path()?;
        let Some(_transaction) = self.admission_lock()? else { return Ok(None) };
        if crate::external_debt::activation_present(self)? {
            return Err(invalid("activated CPU pool requires checked external-debt inheritance"));
        }
        let held =
            self.snapshot()?.iter().filter(|slot| matches!(slot, SlotState::Held { .. })).count()
                as u32;
        if held > policy(held).min(self.slots().get()) {
            return Ok(None);
        };
        self.adopt_in_transaction(file).map(Some)
    }

    /// Startup-only bounded retry, outside a custodian's event loop. It keeps
    /// the original descriptor alive while unrelated admission transactions finish.
    pub fn adopt_inherited_until(
        &self,
        file: &File,
        deadline: std::time::Instant,
    ) -> io::Result<Lease> {
        loop {
            if std::time::Instant::now() >= deadline {
                return Err(io::ErrorKind::WouldBlock.into());
            }
            if let Some(lease) = self.try_adopt_inherited(file, |_| self.slots().get())? {
                return Ok(lease);
            }
            if std::time::Instant::now() >= deadline {
                return Err(io::ErrorKind::WouldBlock.into());
            }
            std::thread::sleep(std::time::Duration::from_millis(1));
        }
    }

    // Caller retains the native manifest transaction and validated occupancy.
    pub(crate) fn adopt_in_transaction(&self, file: &File) -> io::Result<Lease> {
        self.adopt_in_transaction_with(file, || {})
    }
    pub(crate) fn adopt_in_transaction_with(
        &self,
        file: &File,
        after_probe: impl FnOnce(),
    ) -> io::Result<Lease> {
        self.validate_path()?;
        let mut file = file.try_clone()?;
        check_private(&file, false)?;
        // SAFETY: this is the newly owned descriptor. Only query its access mode.
        let access = unsafe { libc::fcntl(file.as_raw_fd(), libc::F_GETFL) };
        if access < 0 {
            return Err(io::Error::last_os_error());
        }
        if access & libc::O_ACCMODE != libc::O_RDWR {
            return Err(invalid("inherited CPU descriptor is not read/write"));
        }
        let identity = Identity::of(&file)?;
        let slot = self
            .0
            .identities
            .iter()
            .position(|&known| known == identity)
            .ok_or_else(|| invalid("inherited CPU descriptor is not a sealed slot"))?
            as u32;
        let probe = Probe(self.open_slot(slot, false)?);
        match probe.0.try_lock_shared() {
            Ok(()) => return Err(invalid("inherited CPU slot is not held")),
            Err(std::fs::TryLockError::WouldBlock) => {}
            Err(std::fs::TryLockError::Error(error)) => return Err(error),
        }
        after_probe();
        file.try_lock()
            .map_err(|_| invalid("inherited CPU slot is held by a different open description"))?;
        // A duplicated descriptor shares the writer's current offset.
        file.seek(SeekFrom::Start(0))?;
        let record = Record::parse(&bounded_text(&mut file)?)?;
        if record.slot != slot {
            return Err(invalid("inherited CPU slot record does not match its identity"));
        }
        // SAFETY: file owns this live descriptor. Descriptor flags are local
        // to this copy; this does not change the parent's open description.
        let flags = unsafe { libc::fcntl(file.as_raw_fd(), libc::F_GETFD) };
        if flags < 0 {
            return Err(io::Error::last_os_error());
        }
        // SAFETY: the same live, owned descriptor and flags validated above.
        if unsafe { libc::fcntl(file.as_raw_fd(), libc::F_SETFD, flags | libc::FD_CLOEXEC) } < 0 {
            return Err(io::Error::last_os_error());
        }
        Ok(Lease { slot, owner: record.owner, file })
    }

    /// Acquire one available unit lease without waiting. `None` means capacity
    /// or the admission lock was busy. It is not a permanent reservation.
    pub fn try_acquire(&self, owner: Owner) -> io::Result<Option<Lease>> {
        self.try_acquire_with_limit(owner, self.slots().get())
    }

    /// Observe fixed legacy reservations under this SAME manifest transaction.
    /// The caller has already published/retained its complete real fixed claim.
    /// Unknown held records never become a successful full-host fit. For an
    /// exclusive fixed claim, pass its original held admission description;
    /// a new open or an integer count cannot bypass a foreign fence. This is
    /// read-only readiness, not an execution/SDK/GNU grant or v3 activation.
    #[cfg(feature = "observations")]
    pub fn observe_legacy_fixed_room(
        &self,
        directory: &Path,
        slots: NonZeroU32,
        owned_exclusive_admission: Option<&File>,
    ) -> io::Result<crate::LegacyFixedRoom> {
        let Some(transaction) = self.try_legacy_fixed_transaction()? else {
            return Ok(crate::LegacyFixedRoom::Busy);
        };
        transaction.observe(directory, slots, owned_exclusive_admission)
    }

    /// Retain the original manifest while an unlaunched fixed claimant
    /// publishes and judges its complete legacy claim. Callers must perform
    /// bounded, nonblocking work and release every partial claim on refusal;
    /// no child may start under this transaction. This guard grants no CPU
    /// lease, GNU credit, SDK custody or execution permission.
    #[cfg(feature = "observations")]
    pub fn try_legacy_fixed_transaction(&self) -> io::Result<Option<LegacyFixedTransaction<'_>>> {
        self.validate_path()?;
        let Some(_transaction) = self.admission_lock()? else {
            return Ok(None);
        };
        if crate::external_debt::activation_present(self)? {
            return Err(invalid("activated CPU domain refuses legacy fixed readiness"));
        }
        Ok(Some(LegacyFixedTransaction { pool: self, _transaction }))
    }

    #[cfg(feature = "observations")]
    fn observe_legacy_in_transaction(
        &self,
        directory: &Path,
        slots: NonZeroU32,
        owned_exclusive_admission: Option<&File>,
    ) -> io::Result<crate::LegacyFixedRoom> {
        self.validate_path()?;
        if crate::external_debt::activation_present(self)? {
            return Err(invalid("activated CPU domain refuses legacy fixed readiness"));
        }
        let native_held =
            self.snapshot()?.iter().filter(|slot| matches!(slot, SlotState::Held { .. })).count()
                as u32;
        crate::external::observe_fixed(
            directory,
            self.slots().get(),
            slots.get(),
            owned_exclusive_admission,
            native_held,
        )
    }

    /// Apply a caller's conservative observed limit before acquiring work.
    ///
    /// The limit counts every held lease, including leases above a newly
    /// reduced limit. A reduction therefore pauses new admission until enough
    /// workers finish; it never moves or unlocks another worker's descriptor.
    /// This is intended for a host observation, not a build's `-j` ceiling.
    /// Participating callers serialize the count and acquisition on the sealed
    /// manifest inode. A busy admission lock returns `None`, without waiting.
    /// This does not publish policy: callers with a larger limit, including
    /// older clients, may still use other physical slots. It is not a global
    /// memory limit or authority to change the pool's physical capacity.
    /// A zero limit pauses all new work, for example during critical pressure.
    pub fn try_acquire_with_limit(&self, owner: Owner, limit: u32) -> io::Result<Option<Lease>> {
        self.try_acquire_observed(owner, |_| limit)
    }

    /// Observe a conservative ceiling inside the shared admission transaction.
    /// The callback receives the held count and must be bounded, nonblocking,
    /// and must not acquire another lease from this pool. In particular it can
    /// inspect cached pressure before the atomic worker acquisition. Once an
    /// external-debt domain exists this raw route refuses; use ExternalDebt's
    /// checked shared transaction instead, including for partial activation.
    pub fn try_acquire_observed(
        &self,
        owner: Owner,
        observe: impl FnOnce(u32) -> u32,
    ) -> io::Result<Option<Lease>> {
        self.validate_path()?;
        if owner.pid == 0 {
            return Err(invalid("CPU owner pid is zero"));
        }
        let admission = self.admission_lock()?;
        let Some(_admission) = admission else { return Ok(None) };
        if crate::external_debt::activation_present(self)? {
            return Err(invalid("activated CPU pool requires checked external-debt admission"));
        }
        let held =
            self.snapshot()?.iter().filter(|slot| matches!(slot, SlotState::Held { .. })).count();
        let limit = observe(held as u32);
        if held >= limit.min(self.slots().get()) as usize {
            return Ok(None);
        }
        self.try_acquire_in_transaction(owner)
    }

    // The v3 debt adapter and observed admission above already hold the sealed
    // manifest transaction. Re-entering that lock would refuse every grant.
    pub(crate) fn try_acquire_in_transaction(&self, owner: Owner) -> io::Result<Option<Lease>> {
        self.validate_path()?;
        if owner.pid == 0 {
            return Err(invalid("CPU owner pid is zero"));
        }
        let width = self.0.slots.get();
        let start = self.0.next.fetch_add(1, Ordering::Relaxed) % width;
        for offset in 0..width {
            let slot = (start + offset) % width;
            let mut claim = match Claim::lock(self.open_slot(slot, true)?) {
                Ok(claim) => claim,
                Err(std::fs::TryLockError::WouldBlock) => continue,
                Err(std::fs::TryLockError::Error(error)) => return Err(error),
            };
            // Tests copy the locked slot here, as a concurrent spawn can, and
            // fail the claim as a failed record write would: every error after
            // this point must unlock.
            #[cfg(test)]
            claim_tests::locked()?;
            // A failed record write leaves through the claim's unlock; only
            // the lease keeps the lock.
            let file = claim.file();
            file.set_len(0)?;
            file.seek(SeekFrom::Start(0))?;
            file.write_all(Record { slot, owner }.encode().as_bytes())?;
            file.flush()?;
            return Ok(Some(claim.into_lease(slot, owner)));
        }
        Ok(None)
    }

    fn admission_lock(&self) -> io::Result<Option<Probe>> {
        let file = open_at(&self.0.directory, "pool", libc::O_RDONLY, false)?;
        check_private(&file, false)?;
        if Identity::of(&file)? != self.0.config {
            return Err(invalid("CPU admission manifest identity changed"));
        }
        match file.try_lock() {
            Ok(()) => Ok(Some(Probe(file))),
            Err(std::fs::TryLockError::WouldBlock) => Ok(None),
            Err(std::fs::TryLockError::Error(error)) => Err(error),
        }
    }

    /// Read current slot states without modifying records or waiting on a
    /// holder. An unlocked stale record is always reported as available.
    pub fn snapshot(&self) -> io::Result<Vec<SlotState>> {
        self.validate_path()?;
        let mut states = Vec::with_capacity(self.0.slots.get() as usize);
        for slot in 0..self.0.slots.get() {
            let mut probe = Probe(self.open_slot(slot, false)?);
            states.push(match probe.0.try_lock_shared() {
                Ok(()) => SlotState::Available { slot },
                Err(std::fs::TryLockError::WouldBlock) => SlotState::Held {
                    slot,
                    reported_owner: bounded_text(&mut probe.0)
                        .ok()
                        .and_then(|text| Record::parse(&text).ok())
                        .filter(|record| record.slot == slot)
                        .map(|record| record.owner),
                },
                Err(std::fs::TryLockError::Error(error)) => return Err(error),
            });
        }
        Ok(states)
    }

    fn validate_path(&self) -> io::Result<()> {
        let path = std::fs::symlink_metadata(&self.0.path)?;
        let open = self.0.directory.metadata()?;
        if !path.is_dir() || path.dev() != open.dev() || path.ino() != open.ino() {
            return Err(invalid("CPU pool directory identity changed"));
        }
        check_private(&self.0.directory, true)?;
        let _initialization = observe_initialization(&self.0.directory)?;
        let mut config = open_at(&self.0.directory, "pool", libc::O_RDONLY, false)?;
        check_private(&config, false)?;
        if Identity::of(&config)? != self.0.config {
            return Err(invalid("CPU pool manifest identity changed"));
        }
        if parse_config(&read_text(&mut config, CONFIG_MAX_BYTES)?)? != self.0.identities {
            return Err(invalid("CPU pool manifest contents changed"));
        }
        Ok(())
    }

    fn open_slot(&self, slot: u32, write: bool) -> io::Result<File> {
        let file = open_at(
            &self.0.directory,
            &slot_name(slot),
            if write { libc::O_RDWR } else { libc::O_RDONLY },
            false,
        )?;
        check_private(&file, false)?;
        if Identity::of(&file)? != self.0.identities[slot as usize] {
            return Err(invalid("CPU slot file identity changed"));
        }
        Ok(file)
    }
}

#[cfg(test)]
#[path = "unix/initialization_tests.rs"]
mod initialization_tests;

/// Original native manifest exclusion during bounded fixed-claim publication.
/// Dropping it releases this temporary observer transaction. It never releases
/// an executing unit's CPU lease and does not permit starting a command.
#[cfg(feature = "observations")]
pub struct LegacyFixedTransaction<'a> {
    pool: &'a Pool,
    _transaction: Probe,
}

#[cfg(feature = "observations")]
impl LegacyFixedTransaction<'_> {
    /// Observe actual fixed/native occupancy under this same retained manifest.
    pub fn observe(
        &self,
        directory: &Path,
        slots: NonZeroU32,
        owned_exclusive_admission: Option<&File>,
    ) -> io::Result<crate::LegacyFixedRoom> {
        self.pool.observe_legacy_in_transaction(directory, slots, owned_exclusive_admission)
    }
}

/// A lock taken only to order initialization or to observe: the initializer's, an observer's, a
/// snapshot's, a legacy fence check's. Unlike a lease, no child inherits one on purpose, so it lets
/// go explicitly at drop. Any spawn in this process copies every descriptor into the child until
/// its exec, close-on-exec ones included: fork (a `pre_exec` hook forces it) and posix_spawn alike,
/// on macOS even std's posix_spawn with `POSIX_SPAWN_CLOEXEC_DEFAULT`. A lock released only by its
/// final close stays held that long: readers saw a pending initialization, and claimants a busy
/// slot.
pub(super) struct Probe(pub(super) File);

impl Drop for Probe {
    fn drop(&mut self) {
        // A failed unlock leaves the release to the final close.
        let _ = self.0.unlock();
    }
}

/// A slot locked to be claimed, until its record is written. Every outcome
/// but the lease unlocks it before close, for the reason `Probe` does: a slot
/// whose record write failed would otherwise read as held work for as long as
/// a concurrent spawn's copy of the descriptor lives. Only `into_lease` hands
/// the locked file on, to the lease's close-only release.
struct Claim(Option<File>);

impl Claim {
    fn lock(file: File) -> Result<Self, std::fs::TryLockError> {
        file.try_lock()?;
        Ok(Self(Some(file)))
    }

    fn file(&mut self) -> &mut File {
        self.0.as_mut().expect("only into_lease takes the claimed file, consuming the claim")
    }

    fn into_lease(mut self, slot: u32, owner: Owner) -> Lease {
        let file =
            self.0.take().expect("only into_lease takes the claimed file, consuming the claim");
        Lease { slot, owner, file }
    }
}

impl Drop for Claim {
    fn drop(&mut self) {
        if let Some(file) = &self.0 {
            // A failed unlock leaves the release to the final close.
            let _ = file.unlock();
        }
    }
}

#[cfg(test)]
mod claim_tests;

/// Private close-only materialization used ONLY after an opaque authenticated
/// member/worker original transfer (or the unchanged checked Pool path).
/// File contents/slot numbers alone never authorize entry to this function.
#[cfg(all(feature = "native-host", any(target_os = "linux", target_os = "macos")))]
pub(crate) fn continue_original_workload_file(slot: u32, file: File) -> io::Result<Lease> {
    check_private(&file, false)?;
    // SAFETY: observe access on this actual held original; no lock/flag changes.
    let flags = unsafe { libc::fcntl(file.as_raw_fd(), libc::F_GETFL) };
    if flags < 0 {
        return Err(io::Error::last_os_error());
    }
    if flags & libc::O_ACCMODE != libc::O_RDWR {
        return Err(invalid("original workload CPU lacks its retained read/write rights"));
    }
    // This is diagnostic attribution only; custody is supplied by the
    // opaque live transfer before this private method can be reached.
    use std::os::unix::fs::FileExt as _;
    let mut bytes = [0; MAX_RECORD_BYTES + 1];
    let mut read = 0;
    loop {
        match file.read_at(&mut bytes[read..], read as u64) {
            Ok(0) => break,
            Ok(count) => {
                read += count;
                if read > MAX_RECORD_BYTES {
                    return Err(invalid("original workload CPU record exceeds bound"));
                }
            }
            Err(error) if error.kind() == io::ErrorKind::Interrupted => {}
            Err(error) => return Err(error),
        }
    }
    let record = Record::parse(
        std::str::from_utf8(&bytes[..read])
            .map_err(|_| invalid("original workload CPU record is not text"))?,
    )?;
    if record.slot != slot {
        return Err(invalid("original workload slot record differs"));
    }
    Ok(Lease { slot, owner: record.owner, file })
}

#[cfg(all(test, feature = "native-host"))]
mod workload_original_tests;

/// One executing unit's lease. There is deliberately no explicit unlock in
/// `Drop`: the final close of all duplicated/inherited descriptors releases it.
#[derive(Debug)]
pub struct Lease {
    slot: u32,
    owner: Owner,
    file: File,
}

impl Lease {
    /// Update diagnostic attribution while retaining the same kernel lease.
    /// This grants no capacity and does not change the original ownership
    /// value returned by `owner`; readers tolerate an in-progress record.
    pub fn report_owner(&self, owner: Owner) -> io::Result<()> {
        if owner.pid == 0 {
            return Err(invalid("CPU owner pid is zero"));
        }
        let mut file = self.file.try_clone()?;
        file.set_len(0)?;
        file.seek(SeekFrom::Start(0))?;
        file.write_all(Record { slot: self.slot, owner }.encode().as_bytes())?;
        file.flush()
    }

    /// Slot held by this lease.
    #[must_use]
    pub fn slot(&self) -> u32 {
        self.slot
    }
    /// Reported unit owner.
    #[must_use]
    pub fn owner(&self) -> Owner {
        self.owner
    }
    /// Duplicate ownership of this same kernel lease. Releasing either copy
    /// alone cannot make the slot available.
    pub fn try_clone(&self) -> io::Result<Self> {
        Ok(Self { slot: self.slot, owner: self.owner, file: self.file.try_clone()? })
    }
    /// Transfer the descriptor to an existing checked child-launch mechanism.
    /// It stays close-on-exec until that mechanism explicitly inherits it.
    #[must_use]
    pub fn into_file(self) -> File {
        self.file
    }
}

impl AsFd for Lease {
    fn as_fd(&self) -> BorrowedFd<'_> {
        self.file.as_fd()
    }
}

impl AsRawFd for Lease {
    fn as_raw_fd(&self) -> std::os::fd::RawFd {
        self.file.as_raw_fd()
    }
}

pub(super) fn slot_name(slot: u32) -> String {
    format!("slot-{slot:08x}")
}

fn bounded_text(file: &mut File) -> io::Result<String> {
    read_text(file, MAX_RECORD_BYTES)
}

pub(super) fn read_text(file: &mut File, max: usize) -> io::Result<String> {
    let mut text = String::new();
    file.take((max + 1) as u64).read_to_string(&mut text)?;
    if text.len() > max {
        return Err(invalid("CPU pool record exceeds its size bound"));
    }
    Ok(text)
}

pub(super) fn open_parent(path: &Path) -> io::Result<File> {
    use std::os::unix::fs::OpenOptionsExt;
    let file = std::fs::OpenOptions::new()
        .read(true)
        .custom_flags(libc::O_DIRECTORY | libc::O_NOFOLLOW | libc::O_CLOEXEC | libc::O_NONBLOCK)
        .open(path)?;
    let meta = file.metadata()?;
    // SAFETY: geteuid only reads this process's effective uid.
    if !meta.is_dir() || meta.uid() != unsafe { libc::geteuid() } || meta.mode() & 0o022 != 0 {
        return Err(io::Error::new(
            io::ErrorKind::PermissionDenied,
            "CPU capacity parent must be owned and not writable by others",
        ));
    }
    Ok(file)
}

fn observe_initialization(directory: &File) -> io::Result<Probe> {
    let probe = Probe(open_at(directory, "init.lock", libc::O_RDONLY, false)?);
    check_private(&probe.0, false)?;
    probe.0.try_lock_shared().map_err(|error| match error {
        std::fs::TryLockError::WouldBlock => io::Error::from(io::ErrorKind::WouldBlock),
        std::fs::TryLockError::Error(error) => error,
    })?;
    Ok(probe)
}

fn publish_config(directory: &File, text: &str) -> io::Result<()> {
    use std::sync::atomic::AtomicU64;
    static NEXT: AtomicU64 = AtomicU64::new(0);
    let tick = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map_or(0, |duration| duration.as_nanos());
    let name = format!(
        ".pool-init-{}-{tick}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    );
    let mut staged = open_at(directory, &name, libc::O_RDWR | libc::O_EXCL, true)?;
    check_private(&staged, false)?;
    let source = CString::new(name).expect("numeric staged name");
    let destination = c"pool";
    let result = (|| {
        staged.write_all(text.as_bytes())?;
        staged.sync_all()?;
        // SAFETY: both leaves are NUL-terminated, relative to the same live
        // directory descriptor. The exclusive init lock orders publishers.
        if unsafe {
            libc::renameat(
                directory.as_raw_fd(),
                source.as_ptr(),
                directory.as_raw_fd(),
                destination.as_ptr(),
            )
        } < 0
        {
            return Err(io::Error::last_os_error());
        }
        directory.sync_all()?;
        Ok(())
    })();
    // SAFETY: this leaf was created exclusively by this invocation. After a
    // successful rename it is already absent; failure cleanup touches no peer.
    unsafe { libc::unlinkat(directory.as_raw_fd(), source.as_ptr(), 0) };
    result
}

fn encode_config(identities: &[Identity]) -> String {
    let mut text = format!("trust-build-cpu-v1 slots={}\n", identities.len());
    for (slot, identity) in identities.iter().enumerate() {
        use std::fmt::Write as _;
        writeln!(text, "slot={slot} dev={} ino={}", identity.dev, identity.ino)
            .expect("writing to String");
    }
    text
}

fn parse_config(text: &str) -> io::Result<Vec<Identity>> {
    if text.len() > CONFIG_MAX_BYTES {
        return Err(invalid("CPU pool manifest too large"));
    }
    let mut lines = text.lines();
    let count = lines
        .next()
        .and_then(|line| line.strip_prefix("trust-build-cpu-v1 slots="))
        .and_then(|value| value.parse::<u32>().ok())
        .filter(|count| (1..=MAX_SLOTS).contains(count))
        .ok_or_else(|| invalid("invalid CPU pool manifest header"))?;
    let mut identities = Vec::with_capacity(count as usize);
    for (slot, line) in lines.enumerate() {
        let fields: Vec<_> = line.split(' ').collect();
        if fields.len() != 3 || fields[0] != format!("slot={slot}") || slot >= count as usize {
            return Err(invalid("invalid CPU pool manifest slot"));
        }
        let read = |field: &str, prefix: &str| -> io::Result<u64> {
            field
                .strip_prefix(prefix)
                .and_then(|value| value.parse().ok())
                .ok_or_else(|| invalid("invalid CPU pool file identity"))
        };
        identities.push(Identity { dev: read(fields[1], "dev=")?, ino: read(fields[2], "ino=")? });
    }
    if identities.len() != count as usize || encode_config(&identities) != text {
        return Err(invalid("incomplete or non-canonical CPU pool manifest"));
    }
    Ok(identities)
}

pub(super) fn open_at(directory: &File, name: &str, flags: i32, create: bool) -> io::Result<File> {
    let name = CString::new(name).map_err(|_| invalid("CPU pool leaf contains NUL"))?;
    let flags = flags
        | libc::O_NOFOLLOW
        | libc::O_CLOEXEC
        | libc::O_NONBLOCK
        | if create { libc::O_CREAT } else { 0 };
    // SAFETY: directory is owned and open; name is a NUL-terminated relative
    // leaf; on success ownership of the fresh descriptor transfers once.
    let fd = unsafe { libc::openat(directory.as_raw_fd(), name.as_ptr(), flags, 0o600) };
    if fd < 0 {
        return Err(io::Error::last_os_error());
    }
    // SAFETY: successful openat returned this descriptor's sole owner.
    Ok(unsafe { File::from_raw_fd(fd) })
}

pub(super) fn check_private(file: &File, directory: bool) -> io::Result<()> {
    let meta = file.metadata()?;
    // SAFETY: geteuid only reads the effective uid of this process.
    let uid = unsafe { libc::geteuid() };
    if meta.uid() != uid
        || meta.mode() & 0o077 != 0
        || (directory && !meta.is_dir())
        || (!directory && (!meta.is_file() || meta.nlink() != 1))
    {
        return Err(io::Error::new(
            io::ErrorKind::PermissionDenied,
            "CPU pool requires private owner-only directories and regular single-link files",
        ));
    }
    Ok(())
}
