//! Native FIFO coordination in the existing build-slot admission namespace.
//!
//! Tickets are priority observations, not CPU, memory, SDK or execution grants.
//! The real resource owner must acquire its complete claim under this queue's
//! transaction. Unknown live requirements are barriers, never permission to pass.

use std::fs::{self, File, OpenOptions};
#[cfg(any(feature = "machine-admission", test))]
use std::io::Read;
use std::io::{self, Write};
#[cfg(feature = "machine-admission")]
use std::io::{Seek, SeekFrom};
use std::os::fd::{AsRawFd, FromRawFd};
use std::os::unix::ffi::{OsStrExt, OsStringExt};
use std::os::unix::fs::{FileExt, MetadataExt, OpenOptionsExt};
use std::path::{Component, Path, PathBuf};

use serde_derive::{Deserialize, Serialize};

const MAX_RECORD: u64 = 65_536;
const MAX_TICKETS: usize = 65_536;
const MAX_PATH: usize = 32_768;
const GIB: f64 = 1_073_741_824.0;

mod adopted;
#[cfg(feature = "machine-admission")]
pub mod budget;
#[cfg(all(feature = "native-exec", target_os = "macos", target_arch = "aarch64"))]
pub mod cache_probe;
mod resources;
#[cfg(feature = "machine-admission")]
pub mod status;
#[cfg(feature = "machine-admission")]
pub use resources::{Adoption, AdoptionError, AdoptionObservation, AdoptionOutcome, Publication};
pub use resources::{Coordinator, Reservation};
#[cfg(feature = "machine-admission")]
pub use resources::{
    EarlyFixedClaim, FIXED_HANDOFF_ENV, FixedClaim, FixedCommandAdmission, FixedCommandSignal,
    FixedCpuRequest, InheritedFixedClaim, PreparedFixedCommand, RunningFixedCommand,
    RunningFixedGroup, WorkerEpoch, WorkerEpochAdmission,
};
#[cfg(all(feature = "native-exec", target_os = "macos", target_arch = "aarch64"))]
pub use resources::{PreparedNestedFixedCommand, RunningNestedFixedCommand};
#[cfg(feature = "native-exec")]
pub use resources::{RuntimeClaimCurrency, RuntimeFixedClaim};

fn invalid(message: &'static str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, message)
}

/// Exact requirements supplied by the native resource coordinator.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Requirements {
    worktree: Option<PathBuf>,
    slots: u32,
    needed: u32,
    exclusive: bool,
    minimum_memory_bytes: u64,
}

impl Requirements {
    /// Validate before registering a ticket or opening any resource claim.
    pub fn new(
        worktree: Option<PathBuf>,
        slots: u32,
        needed: u32,
        exclusive: bool,
        minimum_memory_bytes: u64,
    ) -> io::Result<Self> {
        if slots == 0 || slots > 65_536 || needed == 0 || needed > slots {
            return Err(invalid("invalid admission slot requirements"));
        }
        if let Some(path) = &worktree {
            validate_path(path)?;
        }
        Ok(Self { worktree, slots, needed, exclusive, minimum_memory_bytes })
    }
    pub fn worktree(&self) -> Option<&Path> {
        self.worktree.as_deref()
    }
    pub fn slots(&self) -> u32 {
        self.slots
    }
    pub fn needed(&self) -> u32 {
        self.needed
    }
    pub fn exclusive(&self) -> bool {
        self.exclusive
    }
    pub fn minimum_memory_bytes(&self) -> u64 {
        self.minimum_memory_bytes
    }
}

fn validate_path(path: &Path) -> io::Result<()> {
    if !path.is_absolute()
        || path.as_os_str().as_bytes().len() > MAX_PATH
        || path.as_os_str().as_bytes().contains(&0)
        || !path.components().all(|part| matches!(part, Component::RootDir | Component::Normal(_)))
    {
        return Err(invalid("admission worktree lock requires a bounded absolute path"));
    }
    Ok(())
}

#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct NativeRecord {
    native_admission_version: u32,
    pid: u32,
    requires: NativeRequirements,
}
#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct NativeRequirements {
    worktree_bytes: Option<Vec<u8>>,
    slots: u32,
    needed: u32,
    exclusive: bool,
    minimum_memory_bytes: u64,
}

impl NativeRecord {
    fn new(required: &Requirements) -> Self {
        Self {
            native_admission_version: 1,
            pid: std::process::id(),
            requires: NativeRequirements {
                worktree_bytes: required
                    .worktree
                    .as_ref()
                    .map(|path| path.as_os_str().as_bytes().to_vec()),
                slots: required.slots,
                needed: required.needed,
                exclusive: required.exclusive,
                minimum_memory_bytes: required.minimum_memory_bytes,
            },
        }
    }
    fn required(self) -> io::Result<Requirements> {
        if self.native_admission_version != 1 || self.pid == 0 {
            return Err(invalid("unsupported native admission record"));
        }
        let worktree = self
            .requires
            .worktree_bytes
            .map(|bytes| PathBuf::from(std::ffi::OsString::from_vec(bytes)));
        Requirements::new(
            worktree,
            self.requires.slots,
            self.requires.needed,
            self.requires.exclusive,
            self.requires.minimum_memory_bytes,
        )
    }
}

// Existing Python tickets remain live kernel-held facts during migration.
// Unknown/unrepresentable records remain priority barriers. Native byte paths
// have no UTF-8 restriction and are never normalized through display text.
#[derive(Deserialize)]
struct LegacyRecord {
    requires: LegacyRequirements,
}
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct LegacyRequirements {
    worktree: Option<PathBuf>,
    slots: u32,
    memory: f64,
    exclusive: bool,
    #[serde(default = "one")]
    needed: u32,
}
fn one() -> u32 {
    1
}
fn memory_bytes(gib: f64) -> io::Result<u64> {
    let bytes = (gib * GIB).ceil();
    if !gib.is_finite() || gib < 0.0 || !bytes.is_finite() || bytes >= u64::MAX as f64 {
        return Err(invalid("invalid admission memory requirement"));
    }
    Ok(bytes as u64)
}

fn read_record(file: &File) -> io::Result<Vec<u8>> {
    let mut bytes = Vec::new();
    let mut chunk = [0; 4096];
    loop {
        let remaining = (MAX_RECORD + 1 - bytes.len() as u64) as usize;
        if remaining == 0 {
            break;
        }
        let count = file.read_at(&mut chunk[..remaining.min(4096)], bytes.len() as u64)?;
        if count == 0 {
            break;
        }
        bytes.extend_from_slice(&chunk[..count]);
    }
    if bytes.len() as u64 > MAX_RECORD {
        return Err(invalid("admission ticket exceeds its bound"));
    }
    Ok(bytes)
}

fn read_requirements(file: &File) -> io::Result<Requirements> {
    let bytes = read_record(file)?;
    requirements_from_bytes(&bytes)
}

// The original launcher reserves FIFO order before some memory waits, when
// no live ticket exists. A native arrival must sort after those reservations.
fn legacy_sequence(directory: &Directory) -> io::Result<u128> {
    let file = match directory.open_file("sequence", false) {
        Ok(file) => file,
        Err(error) if error.kind() == io::ErrorKind::NotFound => return Ok(0),
        Err(error) => return Err(error),
    };
    if file.metadata()?.len() > 64 {
        return Err(invalid("legacy admission sequence exceeds its bound"));
    }
    let bytes = read_record(&file)?;
    directory.check_file("sequence", &file)?;
    let number = bytes.trim_ascii();
    if number.is_empty() || number.len() > 39 || !number.iter().all(u8::is_ascii_digit) {
        return Err(invalid("invalid legacy admission sequence"));
    }
    std::str::from_utf8(number).map_err(io::Error::other)?.parse().map_err(io::Error::other)
}

fn requirements_from_bytes(bytes: &[u8]) -> io::Result<Requirements> {
    let discriminator: serde_json::Value =
        serde_json::from_slice(bytes).map_err(io::Error::other)?;
    if discriminator.as_object().is_some_and(|row| row.contains_key("native_admission_version")) {
        let record: NativeRecord = serde_json::from_slice(bytes).map_err(io::Error::other)?;
        return record.required();
    }
    let old: LegacyRecord = serde_json::from_slice(bytes).map_err(io::Error::other)?;
    Requirements::new(
        old.requires.worktree,
        old.requires.slots,
        old.requires.needed,
        old.requires.exclusive,
        memory_bytes(old.requires.memory)?,
    )
}

struct Directory {
    path: PathBuf,
    file: File,
}
impl Directory {
    fn open(path: &Path) -> io::Result<Self> {
        let file = OpenOptions::new()
            .read(true)
            .custom_flags(libc::O_DIRECTORY | libc::O_NOFOLLOW | libc::O_CLOEXEC)
            .open(path)?;
        let directory = Self { path: path.to_owned(), file };
        directory.check()?;
        Ok(directory)
    }
    fn check(&self) -> io::Result<()> {
        let held = self.file.metadata()?;
        let named = fs::symlink_metadata(&self.path)?;
        if !held.is_dir()
            || !named.is_dir()
            || held.uid() != unsafe { libc::geteuid() }
            || (held.dev(), held.ino()) != (named.dev(), named.ino())
        {
            return Err(invalid("admission directory identity or ownership changed"));
        }
        if held.mode() & 0o022 != 0 {
            // Refused, since another account could change its entries. Under
            // umask 002 git makes `<git-dir>`, the worktree lease's parent,
            // 0775. A namespace an older scripts/build-slot made with
            // os.makedirs is 0755 under umask 022 and 0775 under 002; the
            // current one makes each missing component 0700 and never changes
            // an existing directory, so a 0775 namespace stays until its owner
            // repairs it. This owned directory is therefore named with its
            // mode and the recovery, its path quoted so the command can be
            // pasted into a shell.
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                format!(
                    "admission directory {} is group or other writable (mode {:04o}); \
                     check that no other account changed its entries, then run `chmod go-w {}`",
                    self.path.display(),
                    held.mode() & 0o7777,
                    crate::shell_word::quoted(&self.path)
                ),
            ));
        }
        Ok(())
    }
    fn open_file(&self, name: impl AsRef<std::ffi::OsStr>, create: bool) -> io::Result<File> {
        self.create_file(name, create, false)
    }
    fn create_file(
        &self,
        name: impl AsRef<std::ffi::OsStr>,
        create: bool,
        exclusive: bool,
    ) -> io::Result<File> {
        self.check()?;
        let name = name.as_ref();
        let name_c = std::ffi::CString::new(name.as_bytes()).map_err(io::Error::other)?;
        let flags = libc::O_RDWR
            | libc::O_NOFOLLOW
            | libc::O_NONBLOCK
            | libc::O_CLOEXEC
            | if create { libc::O_CREAT } else { 0 }
            | if exclusive { libc::O_EXCL } else { 0 };
        // The operation stays relative to the SAME retained original directory.
        let raw = unsafe { libc::openat(self.file.as_raw_fd(), name_c.as_ptr(), flags, 0o600) };
        if raw < 0 {
            return Err(io::Error::last_os_error());
        }
        // SAFETY: successful openat returned this one newly owned descriptor.
        let file = unsafe { File::from_raw_fd(raw) };
        self.check_file(name, &file)?;
        Ok(file)
    }
    fn remove(&self, name: &str, file: &File) -> io::Result<()> {
        self.check_file(name, file)?;
        let name = std::ffi::CString::new(name).map_err(io::Error::other)?;
        // Cooperating namespace writers hold the same registry transaction.
        if unsafe { libc::unlinkat(self.file.as_raw_fd(), name.as_ptr(), 0) } != 0 {
            return Err(io::Error::last_os_error());
        }
        self.check()
    }
    fn entries(&self) -> io::Result<Vec<std::ffi::OsString>> {
        self.check()?;
        let duplicate = self.file.try_clone()?;
        // SAFETY: duplicate is an owned readable directory descriptor. DIR
        // takes that exact duplicate only when fdopendir succeeds.
        let stream = unsafe { libc::fdopendir(duplicate.as_raw_fd()) };
        if stream.is_null() {
            return Err(io::Error::last_os_error());
        }
        std::mem::forget(duplicate);
        struct Stream(*mut libc::DIR);
        impl Drop for Stream {
            fn drop(&mut self) {
                unsafe {
                    libc::closedir(self.0);
                }
            }
        }
        let stream = Stream(stream);
        // Duplicates share the original directory cursor; reset it for EACH
        // bounded enumeration, never rely on a prior scan's ending offset.
        unsafe {
            libc::rewinddir(stream.0);
        }
        let mut names = Vec::new();
        loop {
            #[cfg(target_os = "macos")]
            let errno = unsafe { libc::__error() };
            #[cfg(target_os = "linux")]
            let errno = unsafe { libc::__errno_location() };
            unsafe {
                *errno = 0;
            }
            let entry = unsafe { libc::readdir(stream.0) };
            if entry.is_null() {
                let error = unsafe { *errno };
                if error != 0 {
                    return Err(io::Error::from_raw_os_error(error));
                }
                break;
            }
            // SAFETY: the entry's NUL-terminated name remains live until the
            // next readdir; copy its original bytes before advancing.
            let name = unsafe { std::ffi::CStr::from_ptr((*entry).d_name.as_ptr()) }.to_bytes();
            if name == b"." || name == b".." {
                continue;
            }
            if names.len() > MAX_TICKETS {
                return Err(invalid("admission directory exceeds its entry bound"));
            }
            names.push(std::ffi::OsString::from_vec(name.to_vec()));
        }
        self.check()?;
        Ok(names)
    }
    fn check_file(&self, name: impl AsRef<std::ffi::OsStr>, file: &File) -> io::Result<()> {
        let name = name.as_ref();
        self.check()?;
        let held = file.metadata()?;
        let named = fs::symlink_metadata(self.path.join(name))?;
        if !held.is_file()
            || !named.is_file()
            || held.uid() != unsafe { libc::geteuid() }
            || held.nlink() != 1
            || held.mode() & 0o022 != 0
            || (held.dev(), held.ino()) != (named.dev(), named.ino())
        {
            return Err(invalid("admission file identity or ownership changed"));
        }
        Ok(())
    }
}

fn try_exclusive(file: &File) -> io::Result<bool> {
    match file.try_lock() {
        Ok(()) => Ok(true),
        Err(std::fs::TryLockError::WouldBlock) => Ok(false),
        Err(std::fs::TryLockError::Error(error)) => Err(error),
    }
}

/// One live priority ticket in the ORIGINAL existing admission directory.
/// This value never owns or manufactures a CPU or resource permission.
pub struct Ticket {
    directory: Directory,
    owner: u32,
    original: Option<(u128, String, File, Vec<u8>)>,
    required: Requirements,
}

/// A specific observed reason why no actual resource claim was returned.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Waiting {
    MemoryUnavailable,
    RegistryBusy,
    EarlierEligible {
        ticket: u128,
    },
    ResourcesBusy,
    #[cfg(feature = "machine-admission")]
    NativeCpu(trust_build_cpu::LegacyFixedRoom),
}

/// Structured coordination result. Queue priority itself grants no resources.
#[derive(Debug, PartialEq, Eq)]
pub enum Attempt<T> {
    Admitted(T),
    Waiting(Waiting),
}
impl<T> Attempt<T> {
    pub fn into_claim(self) -> Option<T> {
        match self {
            Self::Admitted(claim) => Some(claim),
            Self::Waiting(_) => None,
        }
    }
}

impl Ticket {
    /// Open only an existing coordinator namespace; create its queue metadata.
    /// Callers select the canonical namespace before invoking this constructor.
    pub fn open(namespace: &Path, required: Requirements) -> io::Result<Self> {
        validate_path(namespace)?;
        let parent = Directory::open(namespace)?;
        let path = namespace.join("admission");
        let name = std::ffi::CString::new("admission").unwrap();
        // Create metadata in the retained original namespace, never an alias
        // substituted at the caller's spelling after that namespace was opened.
        if unsafe { libc::mkdirat(parent.file.as_raw_fd(), name.as_ptr(), 0o700) } != 0 {
            let error = io::Error::last_os_error();
            if error.kind() != io::ErrorKind::AlreadyExists {
                return Err(error);
            }
        }
        parent.check()?;
        Ok(Self {
            directory: Directory::open(&path)?,
            owner: std::process::id(),
            original: None,
            required,
        })
    }

    /// Atomically register, judge older live requirements and try the complete
    /// actual resource claim. The native backend callbacks must be bounded and
    /// nonblocking; they must not reenter this queue. A returned `T` is supplied
    /// by that real backend, not created by queue position or ticket metadata.
    /// Acquisition returns an unlaunched resource claim; callbacks must never
    /// start work. Launch belongs after successful original-ticket retirement.
    pub fn attempt<T>(
        &mut self,
        available_memory: Option<u64>,
        mut worktree_available: impl FnMut(&Path) -> io::Result<bool>,
        mut slots_available: impl FnMut(u32, u32) -> io::Result<bool>,
        acquire: impl FnOnce(&Requirements) -> io::Result<Option<T>>,
    ) -> io::Result<Attempt<T>> {
        if self.owner != std::process::id() {
            return Err(invalid("forked admission ticket has no owner authority"));
        }
        if available_memory.map_or(self.required.minimum_memory_bytes != 0, |available| {
            available < self.required.minimum_memory_bytes
        }) {
            return Ok(Attempt::Waiting(Waiting::MemoryUnavailable));
        }
        let registry = self.directory.open_file("registry.lock", true)?;
        if !try_exclusive(&registry)? {
            return Ok(Attempt::Waiting(Waiting::RegistryBusy));
        }
        let mut live = Vec::new();
        for name in self.directory.entries()? {
            let Some(name) = name.to_str() else { continue };
            let Some(order) = name.strip_prefix("wait-") else { continue };
            if order.is_empty() || !order.bytes().all(|byte| byte.is_ascii_digit()) {
                continue;
            }
            if live.len() >= MAX_TICKETS {
                return Err(invalid("admission queue exceeds its ticket bound"));
            }
            let order: u128 =
                order.parse().map_err(|_| invalid("admission ticket order overflow"))?;
            if self.original.as_ref().is_some_and(|(_, original, _, _)| original == name) {
                continue;
            }
            let file = match self.directory.open_file(name, false) {
                Ok(file) => file,
                Err(error) if error.kind() == io::ErrorKind::NotFound => continue,
                Err(error) => return Err(error),
            };
            if try_exclusive(&file)? {
                self.directory.remove(name, &file)?;
            } else {
                live.push((order, name.to_owned(), file));
            }
        }
        if self.original.is_none() {
            let legacy = legacy_sequence(&self.directory)?;
            let order = live
                .iter()
                .map(|(order, _, _)| *order)
                .max()
                .unwrap_or(0)
                .max(legacy)
                .checked_add(1)
                .ok_or_else(|| invalid("admission order exhausted"))?;
            let name = format!("wait-{order}");
            let mut file = self.directory.create_file(&name, true, true)?;
            file.try_lock().map_err(io::Error::other)?;
            self.directory.check_file(&name, &file)?;
            let bytes =
                serde_json::to_vec(&NativeRecord::new(&self.required)).map_err(io::Error::other)?;
            if bytes.len() as u64 > MAX_RECORD {
                return Err(invalid("native admission ticket exceeds bound"));
            }
            file.write_all(&bytes)?;
            self.original = Some((order, name, file, bytes));
        }
        let (order, name, file, bytes) = self.original.as_ref().unwrap();
        self.directory.check_file(name, file)?;
        if read_record(file)? != *bytes {
            return Err(invalid("original admission record changed"));
        }
        for (prior, name, file) in &live {
            if prior >= order {
                continue;
            }
            let blocks = match read_requirements(file) {
                Err(_) => true,
                Ok(requirements)
                    if available_memory
                        .is_some_and(|available| available < requirements.minimum_memory_bytes) =>
                {
                    false
                }
                Ok(requirements) => {
                    if requirements
                        .worktree
                        .as_deref()
                        .map(&mut worktree_available)
                        .transpose()?
                        .is_some_and(|available| !available)
                    {
                        false
                    } else if requirements.exclusive {
                        // An older eligible exclusive request reserves priority
                        // while the actual resource owner drains its pool.
                        true
                    } else {
                        slots_available(requirements.slots, requirements.needed)?
                    }
                }
            };
            self.directory.check_file(name, file)?;
            if blocks {
                return Ok(Attempt::Waiting(Waiting::EarlierEligible { ticket: *prior }));
            }
        }
        let result = acquire(&self.required)?;
        match result {
            Some(claim) => {
                self.retire_locked()?;
                Ok(Attempt::Admitted(claim))
            }
            None => Ok(Attempt::Waiting(Waiting::ResourcesBusy)),
        }
    }

    fn retire_locked(&mut self) -> io::Result<()> {
        if let Some((_, name, file, bytes)) = &self.original {
            if read_record(file)? != *bytes {
                return Err(invalid("original admission record changed during retirement"));
            }
            self.directory.remove(name, file)?;
        }
        self.original = None;
        Ok(())
    }

    /// Retire only the exact original ticket, or retain it on contention/error.
    pub fn close(&mut self) -> io::Result<bool> {
        if self.owner != std::process::id() {
            return Err(invalid("forked admission ticket cannot retire original"));
        }
        if self.original.is_none() {
            return Ok(true);
        }
        let registry = self.directory.open_file("registry.lock", true)?;
        if !try_exclusive(&registry)? {
            return Ok(false);
        }
        self.retire_locked()?;
        Ok(true)
    }
}

impl Drop for Ticket {
    fn drop(&mut self) {
        if self.owner == std::process::id() {
            let _ = self.close();
        }
        // If close cannot serialize, the now-unlocked stale original is
        // retired by the next owner; a replacement path is never removed.
    }
}

#[cfg(test)]
mod tests;
