// SPDX-License-Identifier: MIT OR Apache-2.0
// Copyright 2026 Andrew Yates

//! Inactive migration boundary excluding raw pre-v3 native CPU clients.
//!
//! Permission barriers do not prove descendant closure. A different kernel boot
//! after BOTH barriers is mandatory before a new domain can be published. No
//! constructor is invoked automatically by ordinary Pool callers. Unknown old
//! pool leaves, including previously activated external-debt sidecars, refuse
//! migration; they are never discarded or interpreted as empty. An unbound new
//! pool after a publication crash likewise requires explicit recovery.

use std::fs::{self, File, OpenOptions, Permissions};
use std::io::{self, Write};
use std::num::NonZeroU32;
use std::os::fd::AsRawFd;
use std::os::unix::fs::{DirBuilderExt, MetadataExt, OpenOptionsExt, PermissionsExt};
use std::path::{Path, PathBuf};

use sha2::{Digest, Sha256};

use crate::unix::{Probe, check_private, open_at, open_parent, read_text, slot_name};
use crate::{DIRECTORY_NAME, ExternalDebt, LegacyRetirement, MAX_SLOTS, Pool, invalid};

const VERSION: &str = "trust-native-domain-v1";
const STATE: &str = "native-retirement";

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Id(u64, u64);
impl Id {
    fn of(meta: &fs::Metadata) -> Self {
        Self(meta.dev(), meta.ino())
    }
    fn text(self) -> String {
        format!("{}:{}", self.0, self.1)
    }
    fn parse(text: &str) -> io::Result<Self> {
        let (a, b) = text.split_once(':').ok_or_else(|| invalid("invalid domain identity"))?;
        let id = Self(
            a.parse().map_err(|_| invalid("invalid device"))?,
            b.parse().map_err(|_| invalid("invalid inode"))?,
        );
        if id.text() != text {
            return Err(invalid("noncanonical domain identity"));
        }
        Ok(id)
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct Record {
    phase: u8, // 0 prepared, 1 barrier complete, 2 new pool published
    width: u32,
    old_capacity: Id,
    old_pool: Id,
    manifest: Id,
    slots: String,
    legacy: Id,
    legacy_width: u32,
    new_capacity: Id,
    boot: String,
    new_pool: Option<(Id, Id)>,
    debt_root: Option<Id>,
}
impl Record {
    fn encode(&self) -> String {
        let (pool, manifest) =
            self.new_pool.map_or(("-".into(), "-".into()), |(a, b)| (a.text(), b.text()));
        let debt = self.debt_root.map_or(String::new(), |id| format!(" {}", id.text()));
        format!(
            "{VERSION} {} {} {} {} {} {} {} {} {} {} {pool} {manifest}{debt}\n",
            self.phase,
            self.width,
            self.old_capacity.text(),
            self.old_pool.text(),
            self.manifest.text(),
            self.slots,
            self.legacy.text(),
            self.legacy_width,
            self.new_capacity.text(),
            self.boot
        )
    }
    fn parse(text: &str) -> io::Result<Self> {
        let w: Vec<_> = text.trim_end_matches('\n').split(' ').collect();
        if !(13..=14).contains(&w.len()) || w[0] != VERSION {
            return Err(invalid("invalid native retirement record"));
        }
        let phase: u8 = w[1].parse().map_err(|_| invalid("invalid domain phase"))?;
        let width: u32 = w[2].parse().map_err(|_| invalid("invalid native width"))?;
        let legacy_width: u32 = w[8].parse().map_err(|_| invalid("invalid legacy width"))?;
        if phase > 2
            || width == 0
            || width > MAX_SLOTS
            || legacy_width != (width / 6).max(1)
            || w[6].len() != 64
            || !w[6].bytes().all(|b| b.is_ascii_hexdigit() && !b.is_ascii_uppercase())
            || (phase == 0 && w[10] != "-")
            || (phase != 0 && !valid_boot(w[10]))
        {
            return Err(invalid("invalid native retirement fields"));
        }
        let new_pool = match (phase, w[11], w[12]) {
            (2, a, b) => Some((Id::parse(a)?, Id::parse(b)?)),
            (_, "-", "-") => None,
            _ => return Err(invalid("invalid published native identities")),
        };
        // Exact re-encoding rejects extra newlines and decimal aliases.
        let value = Self {
            phase,
            width,
            old_capacity: Id::parse(w[3])?,
            old_pool: Id::parse(w[4])?,
            manifest: Id::parse(w[5])?,
            slots: w[6].into(),
            legacy: Id::parse(w[7])?,
            legacy_width,
            new_capacity: Id::parse(w[9])?,
            boot: w[10].into(),
            new_pool,
            debt_root: match (phase, w.get(13)) {
                (2, Some(id)) => Some(Id::parse(id)?),
                (_, None) => None,
                _ => return Err(invalid("unexpected retained debt identity")),
            },
        };
        if value.encode() != text {
            return Err(invalid("noncanonical native retirement record"));
        }
        Ok(value)
    }
}

fn valid_boot(value: &str) -> bool {
    crate::legacy_retirement::parse_kernel_boot(value).is_ok_and(|canonical| canonical == value)
}

/// Validated new CPU domain, unavailable until a later boot after retirement.
/// This proves exclusion of old clients, not memory or execution entitlement.
pub struct NativeDomain {
    layout: Layout,
    record: Record,
    pool: Pool,
    legacy: LegacyRetirement,
    debt: ExternalDebt,
}

/// Read-only migration observations, never admission or barrier authority.
/// Even `Published` requires `open_canonical` before any resource use.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum NativeMigrationStatus {
    NotStarted,
    Prepared,
    AwaitingLaterBoot,
    ReadyToResume,
    Published,
}

#[derive(Clone)]
struct Layout {
    old: PathBuf,
    new: PathBuf,
    legacy: PathBuf,
}
impl Layout {
    fn canonical() -> io::Result<Self> {
        let old = crate::capacity_dir()?;
        let new = old.with_file_name("capacity-v3");
        Ok(Self { old, new, legacy: crate::unix::account_home()?.join(".cache/build-slot") })
    }
    fn old_pool(&self) -> PathBuf {
        self.old.join(DIRECTORY_NAME)
    }
}

impl NativeDomain {
    /// Observe canonical durable intent without creating files, probing write
    /// permissions, retiring launchers, repairing records or publishing a pool.
    pub fn migration_status_canonical() -> io::Result<NativeMigrationStatus> {
        let layout = Layout::canonical()?;
        require_canonical_env(&layout)?;
        Self::migration_status(&layout)
    }

    /// Explicit postboot maintenance only. Never starts a missing migration
    /// or repairs a prepared/same-boot barrier. Observation grants nothing:
    /// the existing retire owner still authenticates every accepting input.
    pub fn resume_canonical() -> io::Result<Self> {
        let layout = Layout::canonical()?;
        require_canonical_env(&layout)?;
        Self::resume(layout)
    }

    fn resume(layout: Layout) -> io::Result<Self> {
        match Self::migration_status(&layout)? {
            NativeMigrationStatus::ReadyToResume | NativeMigrationStatus::Published => {
                Self::retire(layout)
            }
            _ => Err(io::ErrorKind::WouldBlock.into()),
        }
    }

    fn migration_status(layout: &Layout) -> io::Result<NativeMigrationStatus> {
        non_root()?;
        match fs::symlink_metadata(&layout.new) {
            Err(error) if error.kind() == io::ErrorKind::NotFound => {
                return Ok(NativeMigrationStatus::NotStarted);
            }
            Err(error) => return Err(error),
            Ok(_) => {}
        }
        let new = open_parent(&layout.new)?;
        check_private(&new, true)?;
        let Some(record) = read_record(&new)? else {
            match fs::symlink_metadata(layout.new.join(DIRECTORY_NAME)) {
                Err(error) if error.kind() == io::ErrorKind::NotFound => {
                    return Ok(NativeMigrationStatus::NotStarted);
                }
                Err(error) => return Err(error),
                Ok(_) => return Err(invalid("unbound new native pool requires explicit recovery")),
            }
        };
        if Id::of(&metadata(&layout.old, true)?) != record.old_capacity
            || Id::of(&new.metadata()?) != record.new_capacity
        {
            return Err(invalid("capacity identity changed"));
        }
        inspect_files(layout, &record, record.phase != 0)?;
        // These are record observations, deliberately not validate_old/open:
        // those owners perform write-denial probes and bind live authority.
        match record.phase {
            0 => Ok(NativeMigrationStatus::Prepared),
            1 if record.boot == crate::legacy_retirement::kernel_boot()? => {
                Ok(NativeMigrationStatus::AwaitingLaterBoot)
            }
            1 => Ok(NativeMigrationStatus::ReadyToResume),
            2 => Ok(NativeMigrationStatus::Published),
            _ => Err(invalid("invalid native domain phase")),
        }
    }

    /// Durably retire old canonical launchers. First completion returns
    /// WouldBlock; only a subsequent kernel boot permits publishing the pool.
    /// Root and custom legacy namespaces are refused. No automatic activation.
    pub fn retire_canonical() -> io::Result<Self> {
        let layout = Layout::canonical()?;
        require_canonical_env(&layout)?;
        Self::retire(layout)
    }
    /// Read-only lookup. Never creates, repairs, retires or adopts a pool.
    pub fn open_canonical() -> io::Result<Self> {
        let layout = Layout::canonical()?;
        require_canonical_env(&layout)?;
        Self::open(layout)
    }
    /// Physical pool identity and observation. Admission uses the shared debt owner.
    pub fn pool(&self) -> &Pool {
        &self.pool
    }
    /// Shared admission ledger for fixed reservations and native worker credits.
    pub fn debt(&self) -> &ExternalDebt {
        &self.debt
    }
    /// Retired canonical build-slot domain bound to this migration.
    pub fn legacy(&self) -> &LegacyRetirement {
        &self.legacy
    }
    /// Recheck durable barriers, prior boot, and original new-pool identities.
    pub fn validate(&self) -> io::Result<()> {
        let current = Self::open(self.layout.clone())?;
        if current.record != self.record {
            return Err(invalid("native domain changed"));
        }
        Ok(())
    }
    fn open(layout: Layout) -> io::Result<Self> {
        non_root()?;
        let new = open_parent(&layout.new)?;
        check_private(&new, true)?;
        let record = read_record(&new)?.ok_or_else(|| invalid("native retirement missing"))?;
        if record.phase != 2 {
            return Err(io::Error::from(io::ErrorKind::WouldBlock));
        }
        validate_old(&layout, &record)?;
        let legacy = bound_legacy(&layout, &record)?;
        prior_boot(&record.boot)?;
        legacy.ensure_prior_boot()?;
        let pool =
            Pool::open_existing(&layout.new)?.ok_or_else(|| invalid("published pool missing"))?;
        if pool.slots().get() != record.width || Some(pool_ids(&pool)?) != record.new_pool {
            return Err(invalid("published native pool replaced"));
        }
        let debt = ExternalDebt::open(&pool, &legacy)?
            .ok_or_else(|| invalid("published native domain lacks a debt ledger"))?;
        let (device, inode) = debt.retained_identity();
        if record.debt_root != Some(Id(device, inode)) {
            return Err(invalid("published debt ledger replaced or unbound"));
        }
        // Retry durability after an earlier rename succeeded but directory
        // flush failed. This does not create or repair any namespace entry.
        new.sync_all()?;
        Ok(Self { layout, record, pool, legacy, debt })
    }
    fn retire(layout: Layout) -> io::Result<Self> {
        non_root()?;
        let parent =
            open_parent(layout.new.parent().ok_or_else(|| invalid("new domain lacks parent"))?)?;
        match fs::DirBuilder::new().mode(0o700).create(&layout.new) {
            Ok(()) => parent.sync_all()?,
            Err(e) if e.kind() == io::ErrorKind::AlreadyExists => {}
            Err(e) => return Err(e),
        }
        let new = open_parent(&layout.new)?;
        check_private(&new, true)?;
        let lock = open_at(&new, "native-retirement.lock", libc::O_RDWR, true)?;
        check_private(&lock, false)?;
        let _lock = exclusive(lock)?;
        let previous = read_record(&new)?;
        if let Some(record) = &previous {
            if record.phase == 2 {
                return Self::open(layout);
            }
            if record.phase == 1 {
                validate_old(&layout, record)?;
                let legacy = bound_legacy(&layout, record)?;
                prior_boot(&record.boot)?;
                legacy.ensure_prior_boot()?;
                // An unbound pool could have served work after a publication
                // crash. Never silently adopt it, including a partial init.
                if fs::symlink_metadata(layout.new.join(DIRECTORY_NAME)).is_ok() {
                    return Err(invalid("unbound new native pool requires explicit recovery"));
                }
                let staging = layout.new.join("native-pool-staging");
                fs::DirBuilder::new().mode(0o700).create(&staging)?;
                new.sync_all()?;
                let pool = Pool::open_in(
                    &staging,
                    NonZeroU32::new(record.width).ok_or_else(|| invalid("zero width"))?,
                )?;
                let debt = ExternalDebt::activate(&pool, &legacy)?;
                let (device, inode) = debt.retained_identity();
                let ids = pool_ids(&pool)?;
                let staged = open_parent(&staging)?;
                fs::rename(staging.join(DIRECTORY_NAME), layout.new.join(DIRECTORY_NAME))?;
                staged.sync_all()?;
                new.sync_all()?;
                let mut ready = record.clone();
                ready.phase = 2;
                ready.new_pool = Some(ids);
                ready.debt_root = Some(Id(device, inode));
                write_record(&new, &ready)?;
                return Self::open(layout);
            }
        }
        let old = open_parent(&layout.old)?;
        check_private(&old, true)?;
        let directory = open_parent(&layout.old_pool())?;
        check_private(&directory, true)?;
        let (width, legacy) = if let Some(record) = &previous {
            if Id::of(&old.metadata()?) != record.old_capacity
                || Id::of(&directory.metadata()?) != record.old_pool
                || Id::of(&new.metadata()?) != record.new_capacity
            {
                return Err(invalid("prepared native domain replaced"));
            }
            inspect_files(&layout, record, false)?;
            let legacy = bound_legacy(&layout, record)?;
            restore(&directory, "pool")?;
            (record.width, legacy)
        } else {
            let pool = Pool::open_existing(&layout.old)?
                .ok_or_else(|| invalid("old native pool missing"))?;
            let width = pool.slots().get();
            let legacy = LegacyRetirement::retire(&layout.legacy, (width / 6).max(1))?;
            (width, legacy)
        };
        let manifest = exclusive(open_at(&directory, "pool", libc::O_RDWR, false)?)?;
        let mut guards = vec![manifest];
        for slot in 0..width {
            let name = slot_name(slot);
            if previous.is_some() {
                restore(&directory, &name)?;
            }
            let file = open_at(&directory, &name, libc::O_RDWR, false)?;
            check_private(&file, false)?;
            guards.push(exclusive(file)?);
        }
        // Authenticate the unchanged original manifest against every slot via
        // the ordinary Pool reader, while all admission/slot locks are held.
        let original =
            Pool::open_existing(&layout.old)?.ok_or_else(|| invalid("old native pool vanished"))?;
        if original.slots().get() != width {
            return Err(invalid("native width changed"));
        }
        let mut record = Record {
            phase: 0,
            width,
            old_capacity: Id::of(&old.metadata()?),
            old_pool: Id::of(&directory.metadata()?),
            manifest: Id::of(&guards[0].0.metadata()?),
            slots: slot_digest(&layout.old_pool(), width, false)?,
            legacy: Id(legacy.directory_identity().0, legacy.directory_identity().1),
            legacy_width: (width / 6).max(1),
            new_capacity: Id::of(&new.metadata()?),
            boot: "-".into(),
            new_pool: None,
            debt_root: None,
        };
        if let Some(previous) = previous
            && record != previous
        {
            return Err(invalid("prepared native contents changed"));
        }
        write_record(&new, &record)?;
        for guard in &guards {
            guard.0.set_permissions(Permissions::from_mode(0o000))?;
            guard.0.sync_all()?;
        }
        directory.set_permissions(Permissions::from_mode(0o500))?;
        directory.sync_all()?;
        validate_old(&layout, &record)?;
        legacy.validate()?;
        record.boot = crate::legacy_retirement::kernel_boot()?;
        record.phase = 1;
        write_record(&new, &record)?;
        Err(io::Error::from(io::ErrorKind::WouldBlock))
    }
}

fn bound_legacy(layout: &Layout, record: &Record) -> io::Result<LegacyRetirement> {
    let value = LegacyRetirement::open(&layout.legacy)?;
    if value.directory_identity() != (record.legacy.0, record.legacy.1)
        || value.nominal_width() != record.legacy_width
    {
        return Err(invalid("legacy/native retirement binding changed"));
    }
    value.validate()?;
    Ok(value)
}
fn prior_boot(boot: &str) -> io::Result<()> {
    if boot == crate::legacy_retirement::kernel_boot()? {
        return Err(io::Error::from(io::ErrorKind::WouldBlock));
    }
    Ok(())
}
fn require_canonical_env(layout: &Layout) -> io::Result<()> {
    if std::env::var_os("BUILD_SLOT_DIR").is_some_and(|v| Path::new(&v) != layout.legacy) {
        return Err(invalid("custom legacy domain cannot select machine authority"));
    }
    Ok(())
}
fn non_root() -> io::Result<()> {
    // SAFETY: geteuid reads the effective process identity.
    if unsafe { libc::geteuid() } == 0 {
        return Err(invalid("native permission retirement unavailable to root"));
    }
    Ok(())
}
fn exclusive(file: File) -> io::Result<Probe> {
    check_private(&file, false)?;
    file.try_lock().map_err(|e| match e {
        fs::TryLockError::WouldBlock => io::Error::from(io::ErrorKind::WouldBlock),
        fs::TryLockError::Error(e) => e,
    })?;
    Ok(Probe(file))
}
fn restore(dir: &File, name: &str) -> io::Result<()> {
    let name = std::ffi::CString::new(name).map_err(|_| invalid("invalid native leaf"))?;
    // SAFETY: retained directory FD and NUL-terminated leaf; NOFOLLOW prevents
    // a replaced symlink from chmodding any target outside the old domain.
    if unsafe { libc::fchmodat(dir.as_raw_fd(), name.as_ptr(), 0o600, libc::AT_SYMLINK_NOFOLLOW) }
        != 0
    {
        return Err(io::Error::last_os_error());
    }
    Ok(())
}
fn metadata(path: &Path, directory: bool) -> io::Result<fs::Metadata> {
    let m = fs::symlink_metadata(path)?;
    // SAFETY: geteuid only observes the effective account identity.
    if m.uid() != unsafe { libc::geteuid() }
        || m.mode() & 0o022 != 0
        || (directory && !m.is_dir())
        || (!directory && (!m.is_file() || m.nlink() != 1))
    {
        return Err(invalid("unsafe native domain object"));
    }
    Ok(m)
}
fn slot_digest(path: &Path, width: u32, retired: bool) -> io::Result<String> {
    let mut digest = Sha256::new();
    digest.update(b"trust-native-retired-slots-v1\0");
    for slot in 0..width {
        let m = metadata(&path.join(slot_name(slot)), false)?;
        if retired && m.mode() & 0o777 != 0 {
            return Err(invalid("native slot permissions restored"));
        }
        digest.update(slot.to_be_bytes());
        digest.update(m.dev().to_be_bytes());
        digest.update(m.ino().to_be_bytes());
    }
    for entry in fs::read_dir(path)? {
        let name = entry?.file_name();
        let name = name.to_str().ok_or_else(|| invalid("nonUTF8 native leaf"))?;
        if !matches!(name, "pool" | "init.lock")
            && !name
                .strip_prefix("slot-")
                .and_then(|s| u32::from_str_radix(s, 16).ok())
                .is_some_and(|i| i < width && slot_name(i) == name)
        {
            return Err(invalid("unknown native pool leaf"));
        }
    }
    Ok(format!("{:x}", digest.finalize()))
}
fn inspect_files(layout: &Layout, r: &Record, retired: bool) -> io::Result<()> {
    let dir = metadata(&layout.old_pool(), true)?;
    let m = metadata(&layout.old_pool().join("pool"), false)?;
    if Id::of(&dir) != r.old_pool
        || Id::of(&m) != r.manifest
        || slot_digest(&layout.old_pool(), r.width, retired)? != r.slots
        || (retired && (dir.mode() & 0o777 != 0o500 || m.mode() & 0o777 != 0))
    {
        return Err(invalid("old native domain changed"));
    }
    Ok(())
}
fn validate_old(layout: &Layout, r: &Record) -> io::Result<()> {
    non_root()?;
    if Id::of(&metadata(&layout.old, true)?) != r.old_capacity
        || Id::of(&metadata(&layout.new, true)?) != r.new_capacity
    {
        return Err(invalid("capacity identity changed"));
    }
    inspect_files(layout, r, true)?;
    for name in std::iter::once("pool".into()).chain((0..r.width).map(slot_name)) {
        for write in [false, true] {
            match OpenOptions::new()
                .read(true)
                .write(write)
                .custom_flags(libc::O_NOFOLLOW | libc::O_CLOEXEC | libc::O_NONBLOCK)
                .open(layout.old_pool().join(&name))
            {
                Err(e) if e.kind() == io::ErrorKind::PermissionDenied => {}
                Err(e) => return Err(e),
                Ok(_) => return Err(invalid("old native ACL permits access")),
            }
        }
    }
    let path = layout.old_pool().join("native-retirement-create-probe");
    match OpenOptions::new()
        .write(true)
        .create_new(true)
        .mode(0o600)
        .custom_flags(libc::O_NOFOLLOW | libc::O_CLOEXEC)
        .open(&path)
    {
        Err(e) if e.kind() == io::ErrorKind::PermissionDenied => Ok(()),
        Err(e) => Err(e),
        Ok(f) => {
            drop(f);
            fs::remove_file(path)?;
            Err(invalid("old native ACL permits creation"))
        }
    }
}
fn pool_ids(pool: &Pool) -> io::Result<(Id, Id)> {
    Ok((
        Id::of(&metadata(pool.path(), true)?),
        Id::of(&metadata(&pool.path().join("pool"), false)?),
    ))
}
fn read_record(dir: &File) -> io::Result<Option<Record>> {
    let mut file = match open_at(dir, STATE, libc::O_RDONLY, false) {
        Ok(f) => f,
        Err(e) if e.kind() == io::ErrorKind::NotFound => return Ok(None),
        Err(e) => return Err(e),
    };
    check_private(&file, false)?;
    Record::parse(&read_text(&mut file, 2048)?).map(Some)
}
fn write_record(dir: &File, r: &Record) -> io::Result<()> {
    // A stale next file is not authoritative. Reusing it never truncates an
    // unrelated object: private, single-link original is checked before write.
    let mut file = open_at(dir, "native-retirement.next", libc::O_RDWR, true)?;
    check_private(&file, false)?;
    file.set_len(0)?;
    file.write_all(r.encode().as_bytes())?;
    file.sync_all()?;
    // SAFETY: retained directory descriptor and constant NUL-terminated leaves.
    if unsafe {
        libc::renameat(
            dir.as_raw_fd(),
            c"native-retirement.next".as_ptr(),
            dir.as_raw_fd(),
            c"native-retirement".as_ptr(),
        )
    } != 0
    {
        return Err(io::Error::last_os_error());
    }
    dir.sync_all()
}

/// Native-only read of committed metadata: deliberately does not call legacy
/// canonical_layout, avoiding recursion after old manifest access is denied.
pub(crate) fn canonical_legacy_width() -> io::Result<u32> {
    let layout = Layout::canonical()?;
    let dir = open_parent(&layout.new)?;
    check_private(&dir, true)?;
    let record = read_record(&dir)?.ok_or_else(|| invalid("native retirement absent"))?;
    if record.phase == 0 {
        return Err(invalid("native retirement incomplete"));
    }
    validate_old(&layout, &record)?;
    Ok(record.legacy_width)
}

#[cfg(test)]
mod tests;
