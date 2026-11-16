// SPDX-License-Identifier: MIT OR Apache-2.0
// Copyright 2026 Andrew Yates

//! Durable retirement of cooperative legacy build-slot launchers.
//!
//! A committed retirement removes their filesystem permissions. Unlike a
//! supervisor-held flock, the exclusion survives every supervisor's death.
//! This is not a security boundary against an owner deliberately changing the
//! permissions, and is unavailable to root, which bypasses discretionary access.

use std::collections::BTreeMap;
use std::ffi::CString;
use std::fs::{self, File, OpenOptions, Permissions};
use std::io::{self, Write};
use std::os::fd::AsRawFd;
use std::os::unix::fs::{DirBuilderExt, MetadataExt, OpenOptionsExt, PermissionsExt};
use std::path::{Path, PathBuf};

use crate::invalid;
use crate::unix::{Probe, check_private, open_at, open_parent, read_text};

mod boot;

const VERSION: &str = "trust-legacy-retirement-v2";
const MAX_FILES: usize = 127;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Identity(u64, u64);
impl Identity {
    fn of(metadata: &fs::Metadata) -> Self {
        Self(metadata.dev(), metadata.ino())
    }
}

#[derive(Clone, Debug)]
struct Record {
    committed: bool,
    retired_boot: String,
    width: u32,
    directory: Identity,
    files: BTreeMap<String, Identity>,
}

/// A checked, already committed legacy namespace retirement. It grants no CPU
/// capacity and cannot settle retained work. Consumers revalidate it at launch.
#[derive(Clone, Debug)]
pub struct LegacyRetirement {
    directory: PathBuf,
    anchor: PathBuf,
    record: Record,
}

pub(crate) fn kernel_boot() -> io::Result<String> {
    boot::current()
}

pub(crate) fn parse_kernel_boot(value: &str) -> io::Result<String> {
    boot::parse(value)
}

fn nominal_width(pool: Option<&crate::Pool>) -> io::Result<u32> {
    let pool = pool
        .ok_or_else(|| invalid("canonical native host pool must exist before legacy retirement"))?;
    Ok((pool.slots().get() / 6).max(1))
}

impl LegacyRetirement {
    pub(crate) fn nominal_width(&self) -> u32 {
        self.record.width
    }

    /// Account-owned default namespace of supported legacy build-slot versions.
    /// Neither a scratch HOME nor a caller's custom namespace selects authority.
    pub fn canonical_layout() -> io::Result<(PathBuf, u32)> {
        let path = crate::unix::account_home()?.join(".cache/build-slot");
        // The sealed host pool is global across callers. In particular,
        // available_parallelism can reflect a Linux caller's affinity/quota,
        // which must never change the canonical retirement's identity.
        let width = match crate::Pool::open_existing(&crate::capacity_dir()?) {
            Ok(pool) => nominal_width(pool.as_ref())?,
            Err(error) if error.kind() == io::ErrorKind::PermissionDenied => {
                crate::native_domain::canonical_legacy_width()?
            }
            Err(error) => return Err(error),
        };
        Ok((path, width))
    }

    /// Open only the canonical machine retirement, never a request-provided path.
    pub fn open_canonical() -> io::Result<Self> {
        let (path, width) = Self::canonical_layout()?;
        require_default_namespace(&path, std::env::var_os("BUILD_SLOT_DIR").as_deref())?;
        let value = Self::open(&path)?;
        if value.record.width != width {
            return Err(invalid("canonical legacy width changed"));
        }
        Ok(value)
    }

    /// Migrate the canonical namespace after draining old participants. Custom
    /// BUILD_SLOT_DIR is an isolated scope, not permission for a machine grant.
    pub fn retire_canonical() -> io::Result<Self> {
        require_non_root()?;
        let (path, width) = Self::canonical_layout()?;
        require_default_namespace(&path, std::env::var_os("BUILD_SLOT_DIR").as_deref())?;
        let parent = path.parent().ok_or_else(|| invalid("legacy namespace has no parent"))?;
        let parent = open_created_parent(parent)?;
        match fs::DirBuilder::new().mode(0o700).create(&path) {
            Ok(()) => parent.sync_all()?,
            Err(error) if error.kind() == io::ErrorKind::AlreadyExists => {}
            Err(error) => return Err(error),
        }
        Self::retire(&path, width)
    }

    /// Retire only after taking exclusive locks on the admission file and every
    /// canonical/historical slot. Busy legacy/native-v2 epochs return WouldBlock.
    /// A prepared crash may resume; committed retirement is never rolled back.
    pub fn retire(directory: &Path, width: u32) -> io::Result<Self> {
        require_non_root()?;
        if width == 0 || width as usize >= MAX_FILES || !directory.is_absolute() {
            return Err(invalid("invalid legacy retirement namespace or width"));
        }
        let directory = fs::canonicalize(directory)?;
        let dir = open_parent(&directory)?;
        let leaf = directory
            .file_name()
            .and_then(|s| s.to_str())
            .ok_or_else(|| invalid("legacy directory has no UTF-8 name"))?;
        let anchor = directory.with_file_name(format!("{leaf}.retired-v3"));
        let anchor_dir = open_anchor(&anchor)?;
        let lock = open_file(&anchor.join("lock"), true)?;
        check_private(&lock, false)?;
        let _anchor_lock = exclusive(lock)?;
        let previous = read_record(&anchor)?;
        if let Some(record) = &previous {
            if record.width != width || record.directory != Identity::of(&dir.metadata()?) {
                return Err(invalid("legacy retirement identity or width changed"));
            }
            if record.committed {
                let retirement = Self { directory, anchor, record: record.clone() };
                retirement.validate()?;
                return Ok(retirement);
            }
            validate_files(&directory, record, false)?;
            // Prepared is not a grant: no v3 job may launch before commit. A
            // waiting old launcher may run during recovery, but the exclusive
            // locks below must observe its completion before commit succeeds.
            restore_prepared_file(&dir, "admission.lock")?;
        } else if dir.metadata()?.mode() & 0o200 == 0 {
            return Err(invalid("read-only legacy namespace has no retirement record"));
        }
        let admission = open_at(&dir, "admission.lock", libc::O_RDWR, previous.is_none())?;
        validate_old_file(&admission)?;
        let admission = exclusive(admission)?;
        let mut files = BTreeMap::new();
        for slot in 0..width {
            files.insert(format!("slot-{slot}"), ());
        }
        for entry in fs::read_dir(&directory)? {
            let name = entry?.file_name();
            if let Some(name) = name.to_str().filter(|name| slot_name(name)) {
                files.insert(name.to_owned(), ());
            }
        }
        if files.len() + 1 > MAX_FILES {
            return Err(invalid("too many historical legacy slots"));
        }
        let mut guards = vec![admission];
        let mut identities = BTreeMap::new();
        identities.insert("admission.lock".into(), Identity::of(&guards[0].0.metadata()?));
        for (name, ()) in files {
            if previous.is_some() {
                restore_prepared_file(&dir, &name)?;
            }
            let file = open_at(&dir, &name, libc::O_RDWR, previous.is_none())?;
            validate_old_file(&file)?;
            identities.insert(name, Identity::of(&file.metadata()?));
            guards.push(exclusive(file)?);
        }
        if let Some(previous) = &previous {
            for (name, identity) in &previous.files {
                if identities.get(name) != Some(identity) {
                    return Err(invalid("prepared legacy slot identity changed"));
                }
            }
        }
        let mut record = Record {
            committed: false,
            retired_boot: boot::current()?,
            width,
            directory: Identity::of(&dir.metadata()?),
            files: identities,
        };
        write_record(&anchor, &anchor_dir, &record)?;
        // Keep the kernel exclusion until the durable permission boundary and
        // committed record are both on disk. Existing waiters holding an old
        // admission FD can later lock it, but cannot open any slot or create one.
        for guard in &guards {
            guard.0.set_permissions(Permissions::from_mode(0o000))?;
            guard.0.sync_all()?;
        }
        dir.set_permissions(Permissions::from_mode(0o500))?;
        dir.sync_all()?;
        validate_files(&directory, &record, true)?;
        deny_legacy_access(&directory, &record)?;
        // Bind the boot of the COMPLETED barrier, including prepared recovery.
        // A barrier finished after reboot must wait for a subsequent boot.
        record.retired_boot = boot::current()?;
        record.committed = true;
        write_record(&anchor, &anchor_dir, &record)?;
        let retirement = Self { directory, anchor, record };
        retirement.validate()?;
        Ok(retirement)
    }

    /// Reopen committed authority. A prepared, malformed or missing record
    /// never permits v3 activation or clears retained external debt.
    pub fn open(directory: &Path) -> io::Result<Self> {
        require_non_root()?;
        let directory = fs::canonicalize(directory)?;
        let leaf = directory
            .file_name()
            .and_then(|s| s.to_str())
            .ok_or_else(|| invalid("legacy directory has no UTF-8 name"))?;
        let anchor = directory.with_file_name(format!("{leaf}.retired-v3"));
        let record = read_record(&anchor)?.ok_or_else(|| invalid("legacy retirement is absent"))?;
        if !record.committed {
            return Err(invalid("legacy retirement is not committed"));
        }
        let retirement = Self { directory, anchor, record };
        retirement.validate()?;
        Ok(retirement)
    }

    /// Boot in which the complete permission boundary was durably committed.
    /// This is exclusion history, not a claim that old descendants ended.
    pub fn retired_boot_id(&self) -> &str {
        &self.record.retired_boot
    }

    /// A later boot proves that pre-barrier descendants cannot still exist.
    /// Same-boot descriptor drain alone never grants this stronger readiness.
    pub fn ensure_prior_boot(&self) -> io::Result<()> {
        self.validate()?;
        if boot::current()? == self.record.retired_boot {
            return Err(io::Error::new(
                io::ErrorKind::WouldBlock,
                "legacy barrier has no later-boot quiescence receipt",
            ));
        }
        Ok(())
    }

    pub(crate) fn directory_identity(&self) -> (u64, u64) {
        (self.record.directory.0, self.record.directory.1)
    }

    /// Validate immediately before an external/native v3 launch. Permissions
    /// or inode replacement revokes readiness, never silently repairs it.
    pub fn validate(&self) -> io::Result<()> {
        require_non_root()?;
        let dir = open_parent(&self.directory)?;
        if Identity::of(&dir.metadata()?) != self.record.directory
            || dir.metadata()?.mode() & 0o777 != 0o500
        {
            return Err(invalid("retired legacy directory changed"));
        }
        let anchor_dir = open_parent(&self.anchor)?;
        check_private(&anchor_dir, true)?;
        let current =
            read_record(&self.anchor)?.ok_or_else(|| invalid("retirement record lost"))?;
        if current.encode() != self.record.encode() || !current.committed {
            return Err(invalid("retirement readiness changed"));
        }
        validate_files(&self.directory, &self.record, true)?;
        deny_legacy_access(&self.directory, &self.record)
    }
}

fn require_default_namespace(
    expected: &Path,
    configured: Option<&std::ffi::OsStr>,
) -> io::Result<()> {
    if configured.is_some_and(|path| Path::new(path) != expected) {
        return Err(invalid("custom BUILD_SLOT_DIR is not machine-wide v3 authority"));
    }
    Ok(())
}

fn restore_prepared_file(directory: &File, name: &str) -> io::Result<()> {
    let name = CString::new(name).map_err(|_| invalid("invalid legacy component"))?;
    // SAFETY: the retained directory FD is live; name is one validated component
    // with a NUL terminator. NOFOLLOW prevents changing any symlink's target.
    let result = unsafe {
        libc::fchmodat(directory.as_raw_fd(), name.as_ptr(), 0o600, libc::AT_SYMLINK_NOFOLLOW)
    };
    if result != 0 {
        return Err(io::Error::last_os_error());
    }
    Ok(())
}

/// Creates `parent` and each missing ancestor 0700, then opens it as the
/// checked capacity parent. `fs::create_dir_all` asks for 0777 less the umask,
/// which is 0775 under 002, a Linux login default (user private groups), and
/// `open_parent` refuses a group-writable directory, so it refused the parent
/// it had just made.
fn open_created_parent(parent: &Path) -> io::Result<File> {
    fs::DirBuilder::new().recursive(true).mode(0o700).create(parent)?;
    open_parent(&fs::canonicalize(parent)?)
}

fn require_non_root() -> io::Result<()> {
    // SAFETY: geteuid has no arguments and only reads process identity.
    if unsafe { libc::geteuid() } == 0 {
        return Err(invalid("permission retirement is unavailable to root"));
    }
    Ok(())
}

fn open_anchor(path: &Path) -> io::Result<File> {
    let parent = open_parent(path.parent().ok_or_else(|| invalid("anchor has no parent"))?)?;
    match fs::DirBuilder::new().mode(0o700).create(path) {
        Ok(()) => parent.sync_all()?,
        Err(error) if error.kind() == io::ErrorKind::AlreadyExists => {}
        Err(error) => return Err(error),
    }
    let directory = open_parent(path)?;
    check_private(&directory, true)?;
    Ok(directory)
}

fn open_file(path: &Path, create: bool) -> io::Result<File> {
    OpenOptions::new()
        .read(true)
        .write(true)
        .create(create)
        .mode(0o600)
        .custom_flags(libc::O_NOFOLLOW | libc::O_CLOEXEC | libc::O_NONBLOCK)
        .open(path)
}

fn exclusive(file: File) -> io::Result<Probe> {
    file.try_lock().map_err(|error| match error {
        fs::TryLockError::WouldBlock => io::Error::from(io::ErrorKind::WouldBlock),
        fs::TryLockError::Error(error) => error,
    })?;
    Ok(Probe(file))
}

fn validate_old_file(file: &File) -> io::Result<()> {
    validate_old_metadata(&file.metadata()?)
}

fn validate_old_metadata(metadata: &fs::Metadata) -> io::Result<()> {
    // SAFETY: geteuid only reads the current effective identity.
    if !metadata.is_file()
        || metadata.nlink() != 1
        || metadata.mode() & 0o022 != 0
        || metadata.uid() != unsafe { libc::geteuid() }
    {
        return Err(invalid("unsafe legacy slot"));
    }
    Ok(())
}

fn validate_files(directory: &Path, record: &Record, retired: bool) -> io::Result<()> {
    for (name, identity) in &record.files {
        let metadata = fs::symlink_metadata(directory.join(name))?;
        validate_old_metadata(&metadata)?;
        if Identity::of(&metadata) != *identity || (retired && metadata.mode() & 0o777 != 0) {
            return Err(invalid("legacy slot identity or retired permissions changed"));
        }
    }
    for entry in fs::read_dir(directory)? {
        let name = entry?.file_name();
        if let Some(name) = name.to_str().filter(|name| slot_name(name))
            && !record.files.contains_key(name)
        {
            return Err(invalid("unbound legacy slot appeared"));
        }
    }
    Ok(())
}

fn deny_legacy_access(directory: &Path, record: &Record) -> io::Result<()> {
    // ACL entries can grant access despite mode000. Test the ordinary opens
    // actually used by legacy fixed jobs and native-v2 fence readers.
    for name in record.files.keys() {
        for write in [false, true] {
            match OpenOptions::new()
                .read(true)
                .write(write)
                .custom_flags(libc::O_NOFOLLOW | libc::O_CLOEXEC | libc::O_NONBLOCK)
                .open(directory.join(name))
            {
                Err(error) if error.kind() == io::ErrorKind::PermissionDenied => {}
                Err(error) => return Err(error),
                Ok(_) => return Err(invalid("legacy file ACL still grants access")),
            }
        }
    }
    let name = (0..=MAX_FILES)
        .map(|offset| format!("slot-{}", u32::MAX - offset as u32))
        .find(|name| !record.files.contains_key(name))
        .ok_or_else(|| invalid("legacy write probe namespace exhausted"))?;
    let probe = directory.join(name);
    match OpenOptions::new()
        .write(true)
        .create_new(true)
        .mode(0o600)
        .custom_flags(libc::O_NOFOLLOW | libc::O_CLOEXEC | libc::O_NONBLOCK)
        .open(&probe)
    {
        Err(error) if error.kind() == io::ErrorKind::PermissionDenied => Ok(()),
        Err(error) => Err(error),
        Ok(file) => {
            drop(file);
            // This private, newly created probe has never backed execution.
            // A failed cleanup remains an unbound slot and blocks readiness.
            fs::remove_file(probe)?;
            Err(invalid("legacy directory ACL still permits new slots"))
        }
    }
}

fn slot_name(name: &str) -> bool {
    name.strip_prefix("slot-").is_some_and(|tail| {
        !tail.is_empty() && tail.len() <= 10 && tail.bytes().all(|byte| byte.is_ascii_digit())
    })
}

fn read_record(anchor: &Path) -> io::Result<Option<Record>> {
    let mut file = match OpenOptions::new()
        .read(true)
        .custom_flags(libc::O_NOFOLLOW | libc::O_CLOEXEC | libc::O_NONBLOCK)
        .open(anchor.join("state"))
    {
        Ok(file) => file,
        Err(error) if error.kind() == io::ErrorKind::NotFound => return Ok(None),
        Err(error) => return Err(error),
    };
    check_private(&file, false)?;
    Record::parse(&read_text(&mut file, 16 * 1024)?).map(Some)
}

fn write_record(anchor: &Path, directory: &File, record: &Record) -> io::Result<()> {
    let next = anchor.join("next");
    if next.exists() {
        let file = open_file(&next, false)?;
        check_private(&file, false)?;
        fs::remove_file(&next)?;
    }
    let mut file = OpenOptions::new()
        .write(true)
        .create_new(true)
        .mode(0o600)
        .custom_flags(libc::O_NOFOLLOW | libc::O_CLOEXEC)
        .open(&next)?;
    file.write_all(record.encode().as_bytes())?;
    file.sync_all()?;
    fs::rename(next, anchor.join("state"))?;
    directory.sync_all()
}

impl Record {
    fn encode(&self) -> String {
        let phase = if self.committed { "committed" } else { "prepared" };
        let mut text = format!(
            "{VERSION} {phase} {} {} {} {}\n",
            self.width, self.directory.0, self.directory.1, self.retired_boot
        );
        for (name, identity) in &self.files {
            text.push_str(&format!("{name} {} {}\n", identity.0, identity.1));
        }
        text
    }

    fn parse(text: &str) -> io::Result<Self> {
        let mut lines = text.lines();
        let header: Vec<_> = lines.next().unwrap_or_default().split(' ').collect();
        if header.len() != 6 || header[0] != VERSION {
            return Err(invalid("invalid legacy retirement record"));
        }
        let committed = match header[1] {
            "committed" => true,
            "prepared" => false,
            _ => return Err(invalid("invalid retirement phase")),
        };
        let width = header[2].parse::<u32>().map_err(|_| invalid("invalid retirement width"))?;
        if width == 0 || width as usize >= MAX_FILES {
            return Err(invalid("retirement width out of bounds"));
        }
        let number = |s: &str| s.parse::<u64>().map_err(|_| invalid("invalid retirement identity"));
        let directory = Identity(number(header[3])?, number(header[4])?);
        let retired_boot = boot::parse(header[5])?;
        let mut files = BTreeMap::new();
        for line in lines {
            let words: Vec<_> = line.split(' ').collect();
            if words.len() != 3
                || !(words[0] == "admission.lock" || slot_name(words[0]))
                || files
                    .insert(words[0].to_owned(), Identity(number(words[1])?, number(words[2])?))
                    .is_some()
            {
                return Err(invalid("invalid or duplicate retired slot"));
            }
        }
        if files.len() > MAX_FILES
            || !files.contains_key("admission.lock")
            || (0..width).any(|slot| !files.contains_key(&format!("slot-{slot}")))
        {
            return Err(invalid("retirement record omits canonical slots"));
        }
        Ok(Self { committed, retired_boot, width, directory, files })
    }
}

#[cfg(test)]
mod tests;
