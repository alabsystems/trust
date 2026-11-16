// SPDX-License-Identifier: MIT OR Apache-2.0
// Copyright 2026 Andrew Yates

//! Private retained debt. This deliberately does not use v1's stale-record rules.

use std::ffi::CString;
use std::fs::File;
#[cfg(not(any(target_os = "macos", target_os = "linux")))]
use std::io::Read;
use std::io::{self, Seek, SeekFrom, Write};
use std::num::NonZeroU32;
use std::os::fd::AsRawFd;
use std::os::unix::fs::MetadataExt;
use std::path::{Path, PathBuf};
use std::sync::Arc;
use std::sync::atomic::{AtomicU32, Ordering};

use crate::unix::{Identity, Probe, check_private, open_at, open_parent, read_text, slot_name};
use crate::{DIRECTORY_NAME, MAX_RECORD_BYTES, MAX_SLOTS, Owner, invalid};

/// Backend directory inside a newly created retained private capacity domain.
pub const RETAINED_DIRECTORY_NAME: &str = "build-cpu-retained-v1";
const VERSION: &str = "trust-build-cpu-retained-v1";
const RECOVERABLE_VERSION: &str = "trust-build-cpu-retained-v2";
const MANIFEST_MAX: usize = 512 + MAX_SLOTS as usize * 64;
const FENCE_MAX: usize = 512;

#[path = "retained_rekey.rs"]
mod rekey;

/// A retained-domain observation. Both held and retained slots deny new work.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum RetainedSlotState {
    /// An explicit free record was read while a shared kernel lock was held.
    Available {
        /// Slot index.
        slot: u32,
    },
    /// The kernel lock is free but durable controller debt remains.
    Retained {
        /// Slot index.
        slot: u32,
        /// Diagnostic reported owner; this is not recovery authority.
        reported_owner: Owner,
    },
    /// A controller holds the kernel lock. A concurrent write can hide metadata.
    Held {
        /// Slot index.
        slot: u32,
        /// Diagnostic reported owner, if a complete record was observed.
        reported_owner: Option<Owner>,
    },
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Seal {
    root: Identity,
    fence: Identity,
    backend: Identity,
}

#[derive(Debug)]
struct Inner {
    parent: File,
    root: File,
    directory: File,
    path: PathBuf,
    seal: Seal,
    manifest: Identity,
    identities: Vec<Identity>,
    slots: NonZeroU32,
    next: AtomicU32,
}

/// A one-use generated CPU nonce bundle for a custodian's pre-grant journal.
/// Nonce bytes are observations, never constructors or settlement authority.
/// This type intentionally cannot be cloned or rebuilt from observed bytes.
pub struct PreparedReservation {
    width: NonZeroU32,
    nonces: Option<Vec<[u8; 16]>>,
}
impl PreparedReservation {
    /// Generate the complete bounded bundle before any slot record is written.
    pub fn new(width: NonZeroU32) -> io::Result<Self> {
        if width.get() > MAX_SLOTS {
            return Err(invalid("prepared CPU reservation is too large"));
        }
        let mut nonces = Vec::with_capacity(width.get() as usize);
        let mut distinct = std::collections::BTreeSet::new();
        for _ in 0..width.get() {
            let nonce = new_nonce()?;
            if !distinct.insert(nonce) {
                return Err(invalid("prepared CPU nonce collision"));
            }
            nonces.push(nonce);
        }
        Ok(Self { width, nonces: Some(nonces) })
    }
    /// Original requested width, not an acquired grant.
    pub const fn width(&self) -> NonZeroU32 {
        self.width
    }
    /// Persist these identities together with the exact memory cohort reference
    /// BEFORE calling reserve. Observing them cannot mint another prepared plan.
    pub fn nonces(&self) -> io::Result<&[[u8; 16]]> {
        self.nonces
            .as_deref()
            .ok_or_else(|| invalid("prepared CPU reservation was already consumed"))
    }
    pub(crate) fn take(&mut self) -> io::Result<Vec<[u8; 16]>> {
        self.nonces.take().ok_or_else(|| invalid("prepared CPU reservation was already consumed"))
    }
}

/// A private crash-retained pool. It is never an automatic alternate global pool.
/// Clones share observation state but cannot clone a settlement capability.
#[derive(Clone, Debug)]
pub struct RetainedPool(Arc<Inner>);

impl RetainedPool {
    /// Capture the actual free slot before consuming a recovery key. The
    /// caller retains this owner before any fallible durable write begins.
    pub(crate) fn prepare_recovery_acquisition(
        &self,
        domain: [u8; 32],
        prepared: &mut crate::PreparedRecovery,
    ) -> io::Result<Option<PendingRecoveryAcquisition>> {
        prepared.validate_issuance(domain)?;
        if prepared.width().get() != 1 {
            return Err(invalid("pending recovery acquisition requires one original unit"));
        }
        self.validate()?;
        let width = self.0.slots.get();
        let start = self.0.next.fetch_add(1, Ordering::Relaxed) % width;
        for offset in 0..width {
            let slot = (start + offset) % width;
            let mut file = self.open_slot(slot, true)?;
            match file.try_lock() {
                Ok(()) => match read_record(&mut file, slot)? {
                    State::Free => {
                        let unit = prepared
                            .take_units()?
                            .pop()
                            .ok_or_else(|| invalid("original recovery acquisition key missing"))?;
                        let owner = prepared.owner();
                        let context = prepared.context();
                        let recovery = crate::recovery_material::commitment(
                            &domain,
                            owner,
                            prepared.width(),
                            &context,
                            &unit,
                            slot,
                        );
                        return Ok(Some(PendingRecoveryAcquisition {
                            held: Some(RetainedLease {
                                pool: self.clone(),
                                slot,
                                owner,
                                nonce: unit.nonce,
                                recovery: Some(recovery),
                                file,
                                settlement_attempted: false,
                                rekey: None,
                            }),
                            domain,
                            context,
                            write_started: false,
                        }));
                    }
                    State::Retained { .. } => drop(Probe(file)),
                },
                Err(std::fs::TryLockError::WouldBlock) => {}
                Err(std::fs::TryLockError::Error(error)) => return Err(error),
            }
        }
        Ok(None)
    }
    /// Exclusively create a fresh private domain at an absent absolute path.
    /// The existing parent must be owned and not writable by others. A regular
    /// file at the legacy v1 name fences old clients before readiness is written.
    /// Failure leaves the partial domain unavailable; it is never repaired or
    /// adopted automatically. This API does not migrate a machine's global pool.
    pub fn create_private(path: &Path, slots: NonZeroU32) -> io::Result<Self> {
        if !path.is_absolute() || slots.get() > MAX_SLOTS {
            return Err(invalid("invalid retained CPU pool path or slot count"));
        }
        let parent_path =
            path.parent().ok_or_else(|| invalid("retained CPU pool has no parent"))?;
        let leaf = path
            .file_name()
            .and_then(|leaf| leaf.to_str())
            .ok_or_else(|| invalid("invalid retained CPU pool leaf"))?;
        let parent = open_parent(parent_path)?;
        mkdir_exclusive(&parent, leaf)?;
        let root = open_at(&parent, leaf, libc::O_RDONLY | libc::O_DIRECTORY, false)?;
        check_private(&root, true)?;
        // This MUST precede backend initialization. A racing legacy mkdir can
        // win, but then O_EXCL fails and this constructor never publishes.
        let mut fence = open_at(&root, DIRECTORY_NAME, libc::O_RDWR | libc::O_EXCL, true)?;
        check_private(&fence, false)?;
        fence.sync_all()?;
        root.sync_all()?;
        mkdir_exclusive(&root, RETAINED_DIRECTORY_NAME)?;
        let directory =
            open_at(&root, RETAINED_DIRECTORY_NAME, libc::O_RDONLY | libc::O_DIRECTORY, false)?;
        check_private(&directory, true)?;
        let seal = Seal {
            root: Identity::of(&root)?,
            fence: Identity::of(&fence)?,
            backend: Identity::of(&directory)?,
        };
        let mut identities = Vec::with_capacity(slots.get() as usize);
        for slot in 0..slots.get() {
            let mut file =
                open_at(&directory, &slot_name(slot), libc::O_RDWR | libc::O_EXCL, true)?;
            check_private(&file, false)?;
            write_record(&mut file, &State::Free.encode(slot))?;
            identities.push(Identity::of(&file)?);
        }
        let mut manifest = open_at(&directory, "pool", libc::O_RDWR | libc::O_EXCL, true)?;
        check_private(&manifest, false)?;
        manifest.write_all(encode_manifest(seal, &identities).as_bytes())?;
        manifest.sync_all()?;
        let manifest_identity = Identity::of(&manifest)?;
        directory.sync_all()?;
        // Commit both directory links before another opener can see a complete
        // readiness seal. An incomplete fence after a crash remains unavailable.
        root.sync_all()?;
        parent.sync_all()?;
        // Readiness is the complete fence, which pins the manifest inode. An
        // empty/partial fence cannot be opened as a usable retained pool.
        fence.write_all(encode_fence(seal, manifest_identity).as_bytes())?;
        fence.sync_all()?;
        let pool = Self::from_parts(
            parent,
            root,
            directory,
            path.to_owned(),
            seal,
            manifest_identity,
            identities,
        )?;
        pool.validate()?;
        Ok(pool)
    }

    /// Open only a ready retained domain, without creating or repairing files.
    /// `None` means the root does not exist. A partial or changed domain refuses.
    pub fn open_existing(path: &Path) -> io::Result<Option<Self>> {
        if !path.is_absolute() {
            return Err(invalid("retained CPU pool path is not absolute"));
        }
        let parent_path =
            path.parent().ok_or_else(|| invalid("retained CPU pool has no parent"))?;
        let leaf = path
            .file_name()
            .and_then(|leaf| leaf.to_str())
            .ok_or_else(|| invalid("invalid retained CPU pool leaf"))?;
        let parent = match open_parent(parent_path) {
            Err(error) if error.kind() == io::ErrorKind::NotFound => return Ok(None),
            result => result?,
        };
        let root = match open_at(&parent, leaf, libc::O_RDONLY | libc::O_DIRECTORY, false) {
            Err(error) if error.kind() == io::ErrorKind::NotFound => return Ok(None),
            result => result?,
        };
        check_private(&root, true)?;
        let mut fence = open_at(&root, DIRECTORY_NAME, libc::O_RDONLY, false)?;
        check_private(&fence, false)?;
        let (seal, manifest_identity) = parse_fence(&read_text(&mut fence, FENCE_MAX)?)?;
        if Identity::of(&root)? != seal.root || Identity::of(&fence)? != seal.fence {
            return Err(invalid("retained CPU root or fence identity changed"));
        }
        let directory =
            open_at(&root, RETAINED_DIRECTORY_NAME, libc::O_RDONLY | libc::O_DIRECTORY, false)?;
        check_private(&directory, true)?;
        if Identity::of(&directory)? != seal.backend {
            return Err(invalid("retained CPU backend identity changed"));
        }
        let mut manifest = open_at(&directory, "pool", libc::O_RDONLY, false)?;
        check_private(&manifest, false)?;
        if Identity::of(&manifest)? != manifest_identity {
            return Err(invalid("retained CPU manifest identity changed"));
        }
        let identities = parse_manifest(&read_text(&mut manifest, MANIFEST_MAX)?, seal)?;
        let pool = Self::from_parts(
            parent,
            root,
            directory,
            path.to_owned(),
            seal,
            manifest_identity,
            identities,
        )?;
        pool.validate()?;
        // Ready-open validates every unlocked record. A live holder may be in
        // the middle of a write, so snapshot keeps that unit unavailable
        // without treating partial held metadata as free or as corruption.
        pool.snapshot()?;
        Ok(Some(pool))
    }

    fn from_parts(
        parent: File,
        root: File,
        directory: File,
        path: PathBuf,
        seal: Seal,
        manifest: Identity,
        identities: Vec<Identity>,
    ) -> io::Result<Self> {
        let slots = NonZeroU32::new(identities.len() as u32)
            .ok_or_else(|| invalid("retained CPU pool has no slots"))?;
        let pool = Self(Arc::new(Inner {
            parent,
            root,
            directory,
            path,
            seal,
            manifest,
            identities,
            slots,
            next: AtomicU32::new(0),
        }));
        for slot in 0..slots.get() {
            pool.open_slot(slot, false)?;
        }
        Ok(pool)
    }

    /// Private domain location for diagnostics. Paths confer no release authority.
    #[must_use]
    pub fn path(&self) -> &Path {
        &self.0.path
    }

    /// Capacity of this explicit private domain.
    #[must_use]
    pub fn slots(&self) -> NonZeroU32 {
        self.0.slots
    }

    /// Acquire one free slot, durably retaining its debt before returning.
    /// A stale retained record remains unavailable even without a kernel holder.
    /// Unknown or damaged state is an error, never silently free capacity.
    pub fn try_acquire(&self, owner: Owner) -> io::Result<Option<RetainedLease>> {
        self.try_acquire_prepared(owner, new_nonce()?)
    }

    pub(crate) fn try_acquire_prepared(
        &self,
        owner: Owner,
        nonce: [u8; 16],
    ) -> io::Result<Option<RetainedLease>> {
        self.acquire_with(owner, nonce, |_| None)
    }

    fn acquire_with(
        &self,
        owner: Owner,
        nonce: [u8; 16],
        commitment: impl Fn(u32) -> Option<[u8; 32]>,
    ) -> io::Result<Option<RetainedLease>> {
        self.validate()?;
        if owner.pid == 0 {
            return Err(invalid("CPU owner pid is zero"));
        }
        let width = self.0.slots.get();
        let start = self.0.next.fetch_add(1, Ordering::Relaxed) % width;
        for offset in 0..width {
            let slot = (start + offset) % width;
            let mut candidate = match Candidate::lock(self.open_slot(slot, true)?) {
                Ok(candidate) => candidate,
                Err(error) if error.kind() == io::ErrorKind::WouldBlock => continue,
                Err(error) => return Err(error),
            };
            // Damaged records, refused claims and retained debt all leave
            // through the candidate's unlock; only the lease keeps the lock.
            match read_record(candidate.file()?, slot)? {
                State::Free => {
                    let recovery = commitment(slot);
                    write_record(
                        candidate.file()?,
                        &State::Retained { owner, nonce, recovery }.encode(slot),
                    )?;
                    self.validate()?;
                    return Ok(Some(RetainedLease {
                        pool: self.clone(),
                        slot,
                        owner,
                        nonce,
                        recovery,
                        file: candidate.take()?,
                        settlement_attempted: false,
                        rekey: None,
                    }));
                }
                State::Retained { .. } => {}
            }
        }
        Ok(None)
    }

    /// Observe free, held, and unlocked retained debt without waiting or repair.
    pub fn snapshot(&self) -> io::Result<Vec<RetainedSlotState>> {
        self.validate()?;
        let mut states = Vec::with_capacity(self.0.slots.get() as usize);
        for slot in 0..self.0.slots.get() {
            let mut probe = Probe(self.open_slot(slot, false)?);
            let state = match probe.0.try_lock_shared() {
                Ok(()) => match read_record(&mut probe.0, slot)? {
                    State::Free => RetainedSlotState::Available { slot },
                    State::Retained { owner, .. } => {
                        RetainedSlotState::Retained { slot, reported_owner: owner }
                    }
                },
                Err(std::fs::TryLockError::WouldBlock) => RetainedSlotState::Held {
                    slot,
                    reported_owner: read_record(&mut probe.0, slot).ok().and_then(|state| {
                        match state {
                            State::Retained { owner, .. } => Some(owner),
                            State::Free => None,
                        }
                    }),
                },
                Err(std::fs::TryLockError::Error(error)) => return Err(error),
            };
            states.push(state);
        }
        Ok(states)
    }

    fn validate(&self) -> io::Result<()> {
        let parent_path =
            self.0.path.parent().ok_or_else(|| invalid("retained CPU pool has no parent"))?;
        let parent = open_parent(parent_path)?;
        if Identity::of(&parent)? != Identity::of(&self.0.parent)? {
            return Err(invalid("retained CPU parent identity changed"));
        }
        let path = std::fs::symlink_metadata(&self.0.path)?;
        if !path.is_dir() || (Identity { dev: path.dev(), ino: path.ino() }) != self.0.seal.root {
            return Err(invalid("retained CPU root identity changed"));
        }
        check_private(&self.0.root, true)?;
        let mut fence = open_at(&self.0.root, DIRECTORY_NAME, libc::O_RDONLY, false)?;
        check_private(&fence, false)?;
        if Identity::of(&fence)? != self.0.seal.fence
            || parse_fence(&read_text(&mut fence, FENCE_MAX)?)? != (self.0.seal, self.0.manifest)
        {
            return Err(invalid("retained CPU fence changed"));
        }
        let backend = open_at(
            &self.0.root,
            RETAINED_DIRECTORY_NAME,
            libc::O_RDONLY | libc::O_DIRECTORY,
            false,
        )?;
        check_private(&backend, true)?;
        check_private(&self.0.directory, true)?;
        if Identity::of(&backend)? != self.0.seal.backend {
            return Err(invalid("retained CPU backend identity changed"));
        }
        let mut manifest = open_at(&self.0.directory, "pool", libc::O_RDONLY, false)?;
        check_private(&manifest, false)?;
        if Identity::of(&manifest)? != self.0.manifest
            || parse_manifest(&read_text(&mut manifest, MANIFEST_MAX)?, self.0.seal)?
                != self.0.identities
        {
            return Err(invalid("retained CPU manifest changed"));
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
            return Err(invalid("retained CPU slot identity changed"));
        }
        Ok(file)
    }
}

/// A slot locked to be examined or claimed. Every outcome except a handed-out
/// capability unlocks it before close: any concurrent spawn, posix_spawn as
/// well as fork, holds a copy of every descriptor until its exec, and a lock
/// released only by the final close stays held that long, so a damaged or
/// refused slot would read as live work. Only a validated original capability
/// takes the file without this unlock.
struct Candidate(Option<File>);
impl Candidate {
    fn lock(file: File) -> io::Result<Self> {
        file.try_lock().map_err(|error| match error {
            std::fs::TryLockError::WouldBlock => io::Error::from(io::ErrorKind::WouldBlock),
            std::fs::TryLockError::Error(error) => error,
        })?;
        let candidate = Self(Some(file));
        // Tests copy the locked slot here, as a concurrent spawn can, before
        // any record is read: every refusal after this point must unlock.
        #[cfg(test)]
        candidate_tests::locked();
        Ok(candidate)
    }
    fn file(&mut self) -> io::Result<&mut File> {
        self.0.as_mut().ok_or_else(|| invalid("missing retained CPU candidate"))
    }
    fn take(&mut self) -> io::Result<File> {
        self.0.take().ok_or_else(|| invalid("missing retained CPU candidate"))
    }
}
impl Drop for Candidate {
    fn drop(&mut self) {
        if let Some(file) = &self.0 {
            let _ = file.unlock();
        }
    }
}

/// The API's settlement capability for one durable retained claim.
/// It cannot be cloned, decoded from a record, or reopened from a path. Dropping
/// it closes the lock but leaves debt; process death has the same behavior.
#[derive(Debug)]
pub struct RetainedLease {
    pool: RetainedPool,
    slot: u32,
    owner: Owner,
    nonce: [u8; 16],
    recovery: Option<[u8; 32]>,
    file: File,
    settlement_attempted: bool,
    rekey: Option<rekey::Pending>,
}

/// Original unpublished acquisition custody. Neither a fresh key nor a record
/// can recreate the held slot after an uncertain write. Drop keeps debt.
pub(crate) struct PendingRecoveryAcquisition {
    held: Option<RetainedLease>,
    domain: [u8; 32],
    context: [u8; 32],
    write_started: bool,
}
impl PendingRecoveryAcquisition {
    pub(crate) fn check_original(&self, prepared: &crate::PreparedRecovery) -> io::Result<()> {
        prepared.validate(self.domain)?;
        let held =
            self.held.as_ref().ok_or_else(|| invalid("pending acquisition already completed"))?;
        if prepared.owner() != held.owner
            || prepared.width().get() != 1
            || prepared.context() != self.context
            || prepared.nonces()?.as_slice() != [held.nonce]
        {
            return Err(invalid("pending acquisition must retain its exact original key"));
        }
        held.pool.validate()?;
        if Identity::of(&held.pool.open_slot(held.slot, false)?)? != Identity::of(&held.file)? {
            return Err(invalid("pending acquisition original slot was replaced"));
        }
        Ok(())
    }
    pub(crate) fn original_description(&self) -> io::Result<std::os::fd::BorrowedFd<'_>> {
        use std::os::fd::AsFd as _;
        Ok(self
            .held
            .as_ref()
            .ok_or_else(|| invalid("pending acquisition already completed"))?
            .file
            .as_fd())
    }
    pub(crate) fn original_slot(&self) -> io::Result<u32> {
        Ok(self.held.as_ref().ok_or_else(|| invalid("pending acquisition already completed"))?.slot)
    }
    pub(crate) fn original_nonce(&self) -> io::Result<[u8; 16]> {
        Ok(self
            .held
            .as_ref()
            .ok_or_else(|| invalid("pending acquisition already completed"))?
            .nonce)
    }
    pub(crate) fn finish(
        &mut self,
        prepared: &crate::PreparedRecovery,
    ) -> io::Result<RetainedLease> {
        self.finish_with(prepared, write_record)
    }

    pub(crate) fn finish_with(
        &mut self,
        prepared: &crate::PreparedRecovery,
        mut write: impl FnMut(&mut File, &str) -> io::Result<()>,
    ) -> io::Result<RetainedLease> {
        self.check_original(prepared)?;
        let held =
            self.held.as_mut().ok_or_else(|| invalid("pending acquisition already completed"))?;
        let next =
            State::Retained { owner: held.owner, nonce: held.nonce, recovery: held.recovery };
        match read_record(&mut held.file, held.slot) {
            Ok(State::Free) => {}
            Ok(state) if self.write_started && state == next => {}
            Err(error) if self.write_started && error.kind() == io::ErrorKind::InvalidData => {}
            _ => return Err(invalid("pending acquisition original generation differs")),
        }
        self.write_started = true;
        write(&mut held.file, &next.encode(held.slot))?;
        held.pool.validate()?;
        self.held.take().ok_or_else(|| invalid("pending acquisition original missing"))
    }
}

/// Persistable identity of one original retained debt generation.
///
/// These fields are observations, not a settlement or recovery capability.
/// Reconstructing them cannot prove cohort closure, reclaim a lock, or release
/// debt. A recovery transaction must validate its original durable binding.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct RetainedLeaseIdentity {
    /// Device and inode of the original retained pool manifest.
    pub manifest: (u64, u64),
    /// Slot index within that exact pool.
    pub slot: u32,
    /// Device and inode of the original slot file.
    pub file: (u64, u64),
    /// One-use debt generation, distinct even when the same slot is reused.
    pub nonce: [u8; 16],
    /// Original diagnostic owner; PID/birth alone authorizes no recovery.
    pub owner: Owner,
}

impl RetainedLease {
    pub(crate) fn original_description(&self) -> io::Result<std::os::fd::BorrowedFd<'_>> {
        use std::os::fd::AsFd as _;
        self.identity()?;
        Ok(self.file.as_fd())
    }
    /// Capture identity while this original capability is still owned.
    /// This neither creates a recovery grant nor closes the reserve-to-bind
    /// crash gap: unbound debt must remain conservative after that gap.
    pub fn identity(&self) -> io::Result<RetainedLeaseIdentity> {
        if self.rekey.is_some() {
            return Err(invalid("retained CPU recovery transfer remains uncertain"));
        }
        self.pool.validate()?;
        check_private(&self.file, false)?;
        let identity = Identity::of(&self.file)?;
        let mut current = self.pool.open_slot(self.slot, false)?;
        if identity != Identity::of(&current)? {
            return Err(invalid("retained CPU identity no longer names the original slot"));
        }
        match read_record(&mut current, self.slot)? {
            State::Retained { owner, nonce, recovery }
                if owner == self.owner && nonce == self.nonce && recovery == self.recovery => {}
            _ => {
                return Err(invalid("retained CPU identity no longer matches its debt generation"));
            }
        }
        Ok(RetainedLeaseIdentity {
            manifest: (self.pool.0.manifest.dev, self.pool.0.manifest.ino),
            slot: self.slot,
            file: (identity.dev, identity.ino),
            nonce: self.nonce,
            owner: self.owner,
        })
    }

    /// Slot whose debt this capability controls.
    #[must_use]
    pub fn slot(&self) -> u32 {
        self.slot
    }

    /// Diagnostic owner reported when acquiring the claim.
    #[must_use]
    pub fn owner(&self) -> Owner {
        self.owner
    }

    /// Settle after the caller conclusively establishes that all work using
    /// this credit has ended. This leaf cannot establish descendant closure.
    /// Possession of this capability alone is not evidence of work completion.
    ///
    /// The original lock remains held while identities and nonce are checked
    /// and the explicit free record is written and synced. Success commits
    /// settlement. An I/O error after the free write has begun is uncertain:
    /// the slot can already be free, or remain debt/damaged state. The caller
    /// must therefore establish closure BEFORE calling, including on errors.
    pub fn settle(mut self) -> io::Result<()> {
        self.settle_held()
    }
    /// Retry using the SAME still-held original capability after an uncertain
    /// own settlement write. No record/path can construct this capability and
    /// its lock prevents any replacement generation while retry is possible.
    /// The caller must establish actual scope closure before the FIRST call.
    pub(crate) fn settle_held(&mut self) -> io::Result<()> {
        if self.rekey.is_some() {
            return Err(invalid("retained CPU recovery transfer must finish before settlement"));
        }
        self.pool.validate()?;
        let current = self.pool.open_slot(self.slot, false)?;
        if Identity::of(&self.file)? != Identity::of(&current)? {
            return Err(invalid("retained CPU capability identity changed"));
        }
        check_private(&self.file, false)?;
        match read_record(&mut self.file, self.slot) {
            Ok(State::Retained { owner, nonce, recovery })
                if owner == self.owner && nonce == self.nonce && recovery == self.recovery => {}
            Ok(State::Free) if self.settlement_attempted => {}
            Err(error)
                if self.settlement_attempted && error.kind() == io::ErrorKind::InvalidData => {}
            _ => return Err(invalid("retained CPU claim does not match settlement capability")),
        }
        self.settlement_attempted = true;
        write_record(&mut self.file, &State::Free.encode(self.slot))
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum State {
    Free,
    Retained { owner: Owner, nonce: [u8; 16], recovery: Option<[u8; 32]> },
}

impl State {
    fn encode(self, slot: u32) -> String {
        match self {
            Self::Free => format!("{VERSION} slot={slot} free=1\n"),
            Self::Retained { owner, nonce, recovery } => {
                let birth = owner.birth.map_or_else(|| "-".into(), |value| value.to_string());
                let nonce: String = nonce.iter().map(|byte| format!("{byte:02x}")).collect();
                match recovery {
                    None => format!(
                        "{VERSION} slot={slot} pid={} birth={birth} nonce={nonce} retained=1\n",
                        owner.pid
                    ),
                    Some(commitment) => {
                        let commitment: String =
                            commitment.iter().map(|byte| format!("{byte:02x}")).collect();
                        format!(
                            "{RECOVERABLE_VERSION} slot={slot} pid={} birth={birth} nonce={nonce} commitment={commitment} retained=1\n",
                            owner.pid
                        )
                    }
                }
            }
        }
    }
}

fn read_record(file: &mut File, slot: u32) -> io::Result<State> {
    file.seek(SeekFrom::Start(0))?;
    let text = read_text(file, MAX_RECORD_BYTES)?;
    if text == State::Free.encode(slot) {
        return Ok(State::Free);
    }
    let words: Vec<_> = text
        .strip_suffix('\n')
        .ok_or_else(|| invalid("unterminated retained CPU record"))?
        .split(' ')
        .collect();
    let recoverable = words.first() == Some(&RECOVERABLE_VERSION);
    if words.len() != if recoverable { 7 } else { 6 }
        || words[0] != if recoverable { RECOVERABLE_VERSION } else { VERSION }
        || words[1] != format!("slot={slot}")
        || words.last() != Some(&"retained=1")
    {
        return Err(invalid("invalid retained CPU record"));
    }
    let pid = u32::try_from(number(words[2], "pid=")?)
        .map_err(|_| invalid("retained CPU pid overflow"))?;
    if pid == 0 {
        return Err(invalid("retained CPU pid is zero"));
    }
    let birth = if words[3] == "birth=-" { None } else { Some(number(words[3], "birth=")?) };
    let hex = words[4]
        .strip_prefix("nonce=")
        .filter(|hex| hex.len() == 32 && hex.bytes().all(|byte| byte.is_ascii_hexdigit()))
        .ok_or_else(|| invalid("invalid retained CPU nonce"))?;
    let mut nonce = [0; 16];
    for (index, byte) in nonce.iter_mut().enumerate() {
        *byte = u8::from_str_radix(&hex[index * 2..index * 2 + 2], 16)
            .map_err(|_| invalid("invalid retained CPU nonce"))?;
    }
    let recovery = if recoverable {
        let text = words[5]
            .strip_prefix("commitment=")
            .filter(|text| text.len() == 64 && text.bytes().all(|byte| byte.is_ascii_hexdigit()))
            .ok_or_else(|| invalid("invalid recovery commitment"))?;
        let mut commitment = [0; 32];
        for (index, byte) in commitment.iter_mut().enumerate() {
            *byte = u8::from_str_radix(&text[2 * index..2 * index + 2], 16)
                .map_err(|_| invalid("invalid recovery commitment"))?;
        }
        Some(commitment)
    } else {
        None
    };
    let state = State::Retained { owner: Owner { pid, birth }, nonce, recovery };
    if state.encode(slot) != text {
        return Err(invalid("non-canonical retained CPU record"));
    }
    Ok(state)
}

fn write_record(file: &mut File, text: &str) -> io::Result<()> {
    file.set_len(0)?;
    file.seek(SeekFrom::Start(0))?;
    file.write_all(text.as_bytes())?;
    file.sync_all()
}

fn new_nonce() -> io::Result<[u8; 16]> {
    let mut nonce = [0; 16];
    #[cfg(any(target_os = "macos", target_os = "linux"))]
    {
        // SAFETY: the live buffer is writable for 16 bytes, below getentropy's
        // 256-byte maximum. Failure refuses issuance, with no weak fallback.
        if unsafe { libc::getentropy(nonce.as_mut_ptr().cast(), nonce.len()) } != 0 {
            return Err(io::Error::last_os_error());
        }
    }
    #[cfg(not(any(target_os = "macos", target_os = "linux")))]
    {
        // Unix portability fallback. No path or PID-derived entropy is used.
        File::open("/dev/urandom")?.read_exact(&mut nonce)?;
    }
    Ok(nonce)
}

fn mkdir_exclusive(parent: &File, leaf: &str) -> io::Result<()> {
    if leaf.is_empty() || leaf.contains('/') || leaf == "." || leaf == ".." {
        return Err(invalid("invalid retained CPU directory leaf"));
    }
    let leaf = CString::new(leaf).map_err(|_| invalid("retained CPU directory contains NUL"))?;
    // SAFETY: live directory fd and checked single NUL-terminated leaf.
    if unsafe { libc::mkdirat(parent.as_raw_fd(), leaf.as_ptr(), 0o700) } < 0 {
        return Err(io::Error::last_os_error());
    }
    Ok(())
}

fn number(word: &str, prefix: &str) -> io::Result<u64> {
    let digits = word
        .strip_prefix(prefix)
        .filter(|digits| !digits.is_empty() && digits.bytes().all(|byte| byte.is_ascii_digit()))
        .ok_or_else(|| invalid("invalid retained CPU number"))?;
    digits.parse().map_err(|_| invalid("retained CPU number overflow"))
}

fn encode_fence(seal: Seal, manifest: Identity) -> String {
    format!(
        "{VERSION} ready=1 root-dev={} root-ino={} fence-dev={} fence-ino={} backend-dev={} backend-ino={} manifest-dev={} manifest-ino={}\n",
        seal.root.dev,
        seal.root.ino,
        seal.fence.dev,
        seal.fence.ino,
        seal.backend.dev,
        seal.backend.ino,
        manifest.dev,
        manifest.ino
    )
}

fn parse_fence(text: &str) -> io::Result<(Seal, Identity)> {
    let words: Vec<_> = text
        .strip_suffix('\n')
        .ok_or_else(|| invalid("incomplete retained CPU fence"))?
        .split(' ')
        .collect();
    if words.len() != 10 || words[0] != VERSION || words[1] != "ready=1" {
        return Err(invalid("invalid retained CPU fence"));
    }
    let seal = Seal {
        root: Identity { dev: number(words[2], "root-dev=")?, ino: number(words[3], "root-ino=")? },
        fence: Identity {
            dev: number(words[4], "fence-dev=")?,
            ino: number(words[5], "fence-ino=")?,
        },
        backend: Identity {
            dev: number(words[6], "backend-dev=")?,
            ino: number(words[7], "backend-ino=")?,
        },
    };
    let manifest = Identity {
        dev: number(words[8], "manifest-dev=")?,
        ino: number(words[9], "manifest-ino=")?,
    };
    if encode_fence(seal, manifest) != text {
        return Err(invalid("non-canonical retained CPU fence"));
    }
    Ok((seal, manifest))
}

fn encode_manifest(seal: Seal, identities: &[Identity]) -> String {
    use std::fmt::Write as _;
    let mut text = format!(
        "{VERSION} slots={} root-dev={} root-ino={} fence-dev={} fence-ino={} backend-dev={} backend-ino={}\n",
        identities.len(),
        seal.root.dev,
        seal.root.ino,
        seal.fence.dev,
        seal.fence.ino,
        seal.backend.dev,
        seal.backend.ino
    );
    for (slot, identity) in identities.iter().enumerate() {
        writeln!(text, "slot={slot} dev={} ino={}", identity.dev, identity.ino)
            .expect("writing to String");
    }
    text
}

fn parse_manifest(text: &str, seal: Seal) -> io::Result<Vec<Identity>> {
    let mut lines = text.lines();
    let words: Vec<_> =
        lines.next().ok_or_else(|| invalid("empty retained CPU manifest"))?.split(' ').collect();
    if words.len() != 8 || words[0] != VERSION {
        return Err(invalid("invalid retained CPU manifest"));
    }
    let count = number(words[1], "slots=")?;
    if count == 0 || count > u64::from(MAX_SLOTS) {
        return Err(invalid("invalid retained CPU capacity"));
    }
    let mut identities = Vec::with_capacity(count as usize);
    for (slot, line) in lines.enumerate() {
        let fields: Vec<_> = line.split(' ').collect();
        if slot >= count as usize || fields.len() != 3 || fields[0] != format!("slot={slot}") {
            return Err(invalid("invalid retained CPU manifest slot"));
        }
        identities
            .push(Identity { dev: number(fields[1], "dev=")?, ino: number(fields[2], "ino=")? });
    }
    if identities.len() != count as usize || encode_manifest(seal, &identities) != text {
        return Err(invalid("incomplete or changed retained CPU manifest"));
    }
    Ok(identities)
}

#[path = "retained_recovery.rs"]
mod recovery;
pub use recovery::{RecoveredReservation, RecoveryCandidate};

#[cfg(test)]
mod candidate_tests {
    use std::cell::RefCell;
    use std::fs::OpenOptions;
    use std::os::unix::fs::OpenOptionsExt;

    use super::*;
    use crate::recovery_material::{RecoveryAuthority, RecoveryMaterial};
    use crate::tests::descriptor_copy::{Unexecuted, relockable};

    /// The copies made for one claim. `copies` is declared first, so every
    /// copy is killed and reaped before the kernel fixture is released.
    struct Armed {
        copies: Vec<Unexecuted>,
        fixture: crate::tests::KernelFixture,
    }

    thread_local! {
        static ARMED: RefCell<Option<Armed>> = const { RefCell::new(None) };
    }

    /// `Candidate::lock`'s hook: on a thread that `while_copied` armed, copy
    /// the descriptor table while the new candidate holds its slot.
    pub(super) fn locked() {
        ARMED.with_borrow_mut(|armed| {
            if let Some(armed) = armed {
                let copy = Unexecuted::copy(&armed.fixture);
                armed.copies.push(copy);
            }
        });
    }

    /// Runs `claim` with every candidate lock it takes copied into an
    /// unexecuted fork, then `observe` while each copy still lives. Every copy
    /// is killed and reaped, and the fixture released, before this returns or
    /// unwinds, so a failed assertion leaves no copy holding other tests'
    /// descriptors. Returns both results and the number of locks copied.
    fn while_copied<T, O>(
        fixture: crate::tests::KernelFixture,
        claim: impl FnOnce() -> T,
        observe: impl FnOnce() -> O,
    ) -> (T, O, usize) {
        struct Disarm;
        impl Drop for Disarm {
            fn drop(&mut self) {
                drop(ARMED.with_borrow_mut(Option::take));
            }
        }
        ARMED.with_borrow_mut(|armed| *armed = Some(Armed { copies: Vec::new(), fixture }));
        let disarm = Disarm;
        let claimed = claim();
        // Stop copying, but keep the copies alive while observing.
        let armed = ARMED.with_borrow_mut(Option::take);
        drop(disarm);
        let observed = observe();
        let copies = armed.as_ref().map_or(0, |armed| armed.copies.len());
        drop(armed);
        (claimed, observed, copies)
    }

    fn only_slot(pool: &RetainedPool) -> PathBuf {
        slot_path(pool, 0)
    }

    fn slot_path(pool: &RetainedPool, slot: u32) -> PathBuf {
        pool.path().join(RETAINED_DIRECTORY_NAME).join(slot_name(slot))
    }

    /// A torn intent record, written in place so the slot keeps its identity.
    const TORN: &[u8] = b"trust-build-cpu-retained-v1 slot=0 pid=";

    fn tear(slot: &Path) {
        let mut file = OpenOptions::new().write(true).truncate(true).open(slot).unwrap();
        file.write_all(TORN).unwrap();
        file.sync_all().unwrap();
    }

    #[test]
    fn a_refused_claim_unlocks_its_slot_while_a_spawn_holds_a_copy() {
        // Each copy holds every open description: own the descriptor table.
        let fixture = crate::tests::kernel_fixture();
        let directory = crate::tests::private_tempdir();
        let root = directory.path().join("retained");
        let pool = RetainedPool::create_private(&root, NonZeroU32::MIN).unwrap();
        let fence = root.join(DIRECTORY_NAME);
        let slot = only_slot(&pool);
        let (claim, relocked, copies) = while_copied(
            fixture,
            || {
                pool.acquire_with(Owner::current(None), [7; 16], |_| {
                    // The candidate read a free record. Make the claim's final
                    // validation refuse: the readiness fence is replaced by an
                    // equal new file.
                    let bytes = std::fs::read(&fence).unwrap();
                    std::fs::rename(&fence, root.join("former-fence")).unwrap();
                    let mut replacement = OpenOptions::new()
                        .write(true)
                        .create_new(true)
                        .mode(0o600)
                        .open(&fence)
                        .unwrap();
                    replacement.write_all(&bytes).unwrap();
                    None
                })
            },
            || relockable(&slot),
        );
        assert_eq!(copies, 1, "the claim did not lock its one candidate");
        assert!(claim.is_err(), "a replaced readiness fence must refuse the claim");
        assert!(relocked, "a refused claim kept its slot locked through a spawn's copy");
    }

    #[test]
    fn a_damaged_record_unlocks_its_slot_while_a_spawn_holds_a_copy() {
        let fixture = crate::tests::kernel_fixture();
        let directory = crate::tests::private_tempdir();
        let root = directory.path().join("retained");
        let pool = RetainedPool::create_private(&root, NonZeroU32::MIN).unwrap();
        let slot = only_slot(&pool);
        tear(&slot);
        let (claim, (relocked, snapshot), copies) = while_copied(
            fixture,
            || pool.try_acquire(Owner::current(None)),
            || (relockable(&slot), pool.snapshot()),
        );
        assert_eq!(copies, 1, "the claim did not lock its one candidate");
        assert_eq!(claim.err().map(|error| error.kind()), Some(io::ErrorKind::InvalidData));
        assert!(relocked, "a damaged record kept its slot locked through a spawn's copy");
        assert!(snapshot.is_err(), "a damaged record was observed as held work, not as damage");
        assert_eq!(std::fs::read(&slot).unwrap(), TORN, "a refused claim rewrote the record");
    }

    #[test]
    fn a_damaged_record_unlocks_its_slot_during_restoration_while_a_spawn_holds_a_copy() {
        let fixture = crate::tests::kernel_fixture();
        let directory = crate::tests::private_tempdir();
        let root = directory.path().join("retained");
        let pool = RetainedPool::create_private(&root, NonZeroU32::MIN).unwrap();
        let store = directory.path().join("authority");
        crate::tests::private_dir(&store);
        let store = store.canonicalize().unwrap();
        let material =
            RecoveryMaterial::mint([1; 32], Owner::current(None), NonZeroU32::MIN, [2; 32])
                .unwrap();
        drop(material.persist(&store, "grant").unwrap());
        let authority = RecoveryAuthority::open(&store, "grant").unwrap();
        let slot = only_slot(&pool);
        tear(&slot);
        let (restored, relocked, copies) =
            while_copied(fixture, || pool.restore_original(authority), || relockable(&slot));
        assert_eq!(copies, 1, "restoration did not lock its one candidate");
        assert_eq!(restored.err().map(|error| error.kind()), Some(io::ErrorKind::InvalidData));
        assert!(relocked, "a damaged record kept its slot locked through a spawn's copy");
        assert_eq!(std::fs::read(&slot).unwrap(), TORN, "restoration rewrote the record");
    }

    #[test]
    fn a_later_refusal_unlocks_every_restored_slot_while_a_spawn_holds_a_copy() {
        let fixture = crate::tests::kernel_fixture();
        let directory = crate::tests::private_tempdir();
        let root = directory.path().join("retained");
        let width = NonZeroU32::new(2).unwrap();
        let pool = RetainedPool::create_private(&root, width).unwrap();
        let store = directory.path().join("authority");
        crate::tests::private_dir(&store);
        let store = store.canonicalize().unwrap();
        let material =
            RecoveryMaterial::mint([1; 32], Owner::current(None), width, [2; 32]).unwrap();
        drop(material.persist(&store, "grant").unwrap());
        let authority = RecoveryAuthority::open(&store, "grant").unwrap();
        // Slot 0 holds the authority's first original unit, as an issued
        // bundle leaves it once its lease has closed: restorable debt.
        let issued = pool
            .try_acquire_recoverable(
                authority.owner(),
                authority.width(),
                &authority.domain(),
                &authority.context(),
                &authority.units()[0],
            )
            .unwrap()
            .expect("the first free slot is claimed");
        assert_eq!(issued.slot(), 0, "the first claim took another slot");
        drop(issued);
        let (first, second) = (slot_path(&pool, 0), slot_path(&pool, 1));
        let restorable = std::fs::read(&first).unwrap();
        // Restoration validates slot 0 into a lease, then refuses at slot 1.
        tear(&second);
        let (restored, relocked, copies) =
            while_copied(fixture, || pool.restore_original(authority), || relockable(&first));
        assert_eq!(copies, 2, "restoration did not lock both slots");
        assert_eq!(restored.err().map(|error| error.kind()), Some(io::ErrorKind::InvalidData));
        assert!(relocked, "a later refusal kept a restored slot locked through a spawn's copy");
        assert_eq!(std::fs::read(&first).unwrap(), restorable, "a refused restoration settled");
        // Slot 0 was restored before the refusal: with slot 1 repaired, the
        // same material restores it.
        let mut repaired = OpenOptions::new().write(true).open(&second).unwrap();
        write_record(&mut repaired, &State::Free.encode(1)).unwrap();
        let reopened = RecoveryAuthority::open(&store, "grant").unwrap();
        assert_eq!(pool.restore_original(reopened).unwrap().retained_units(), 1);
    }

    #[test]
    fn a_refused_restoration_unlocks_its_material_while_a_spawn_holds_a_copy() {
        let fixture = crate::tests::kernel_fixture();
        let directory = crate::tests::private_tempdir();
        let root = directory.path().join("retained");
        let pool = RetainedPool::create_private(&root, NonZeroU32::MIN).unwrap();
        let store = directory.path().join("authority");
        crate::tests::private_dir(&store);
        let store = store.canonicalize().unwrap();
        let material =
            RecoveryMaterial::mint([1; 32], Owner::current(None), NonZeroU32::MIN, [2; 32])
                .unwrap();
        drop(material.persist(&store, "grant").unwrap());
        let authority = RecoveryAuthority::open(&store, "grant").unwrap();
        tear(&only_slot(&pool));
        let (restored, reopened, copies) = while_copied(
            fixture,
            || pool.restore_original(authority),
            || RecoveryAuthority::open(&store, "grant").map(drop).map_err(|error| error.kind()),
        );
        assert_eq!(copies, 1, "restoration did not lock its one candidate");
        assert_eq!(restored.err().map(|error| error.kind()), Some(io::ErrorKind::InvalidData));
        assert_eq!(reopened, Ok(()), "a refused restoration kept its material locked");
    }
}
