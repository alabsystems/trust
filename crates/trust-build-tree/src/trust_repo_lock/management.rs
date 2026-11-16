//! Build/measurement holder management in the original shared namespace.
//!
//! This owns policy formerly implemented by trust_build_lock.sh. It never
//! signals a writer. A surviving writer is adopted, a parent-managed holder is
//! retained until its actual outer cleanup, and unknown liveness is not death.
//! Discovery covers same-account cooperating actors; arbitrary privileged
//! writers and arbitrary source mutation remain outside this protocol.

use std::collections::BTreeMap;
use std::ffi::{OsStr, OsString};
use std::fs::{self, File, Metadata, OpenOptions};
use std::io::{self, Read, Write};
use std::os::fd::{AsRawFd, FromRawFd};
use std::os::unix::ffi::OsStrExt;
use std::os::unix::fs::{MetadataExt, OpenOptionsExt};
use std::path::Path;
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};

use super::{Root, create_holder_directory, open_directory, same_inode};
use crate::trust_build_lock::NamespaceGuard;

pub mod cli;
#[cfg(feature = "native-exec")]
pub mod exec;
mod lease;
pub(crate) mod process;
#[cfg(feature = "resident-inputs")]
pub use lease::RetiredResidentInputs;
#[cfg(test)]
mod tests;

pub use lease::{
    JoinedChild, LaunchIdentity, LaunchRegistration, Lease, LeaseAcquisition, LocalJoinedScope,
    OriginalSourceOffer, OriginalSourceRoot, ProtectedWorkScope, ScopeDispatch, ScopeFailure,
    ScopeIdentity, ScopedCapture, ScopedChild, ScopedReader, ScopedThread, ScopedThreads,
    ScopedWorker, SealedWorkScope, SourceOfferData, WeakScopeDispatch, WithheldLease,
    WithholdFailure, WithholdPublication, WorkerRegistration,
};

const HOLDER: &str = ".trust-build-lock";
const SENTINEL: &str = ".trust-measurement-in-flight";
const RECORD_LIMIT: u64 = 16 * 1024;
const SEED_WAIT: Duration = Duration::from_secs(120);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Kind {
    Build,
    Measurement,
}
impl Kind {
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Build => "build",
            Self::Measurement => "measurement",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Liveness {
    Live,
    Gone,
    Unknown,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Holder {
    pub token: String,
    pub pid: u32,
    pub group: Option<u32>,
    pub kind: String,
    pub purpose: String,
    pub command: String,
    pub contract: String,
    pub parent_managed: bool,
    pub liveness: Liveness,
    fields: BTreeMap<String, String>,
}
impl Holder {
    /// Durable exclusion, not a Host custody, closure or release capability.
    pub fn is_withheld(&self) -> bool {
        self.fields.get("state").is_some_and(|state| state == "WITHHELD")
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Writer {
    pub pid: Option<u32>,
    pub kind: Kind,
    pub command: String,
    pub covered: bool,
    identity: Option<process::Process>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Status {
    pub holder: Option<Holder>,
    pub writers: Vec<Writer>,
    pub malformed_holder: bool,
}
impl Status {
    pub fn is_free(&self) -> bool {
        self.holder.is_none() && !self.malformed_holder && self.writers.is_empty()
    }
}

/// A checked acquisition request. The caller must outlive its protected work.
/// Waiting releases the namespace guard; it never releases a live holder.
pub struct Acquire {
    pub kind: Kind,
    pub owner_pid: u32,
    pub purpose: String,
    pub contract: String,
    pub wait: Duration,
    pub inherited_token: Option<String>,
    pub break_reason: Option<String>,
}

#[derive(Debug, PartialEq, Eq)]
pub enum Acquisition {
    Acquired(String),
    Borrowed(String),
    Busy(Status),
}

enum HeldAcquisition {
    Acquired(String, HeldRecord),
    Borrowed(String, HeldRecord),
    Busy(Status),
}

#[derive(Debug, PartialEq, Eq)]
pub enum Release {
    AlreadyFree,
    Released,
    HandedOver(Writer),
    ForeignHolder,
    ParentManaged,
}

/// Native management of one original physical build-tree namespace. Opening
/// does not create a holder. Operations validate its original root mapping.
pub struct Manager {
    root: Root,
}

impl Manager {
    /// Release only the original native guard's pinned holder. Borrow the real
    /// open root description; a pathname or matching token cannot reconstruct
    /// this authority. The common namespace mutex spans validation and release.
    pub(super) fn release_original(lease: &super::BuildLease) -> io::Result<Release> {
        lease.root.check_current().map_err(invalid)?;
        let manager = Self {
            root: Root {
                logical: lease.root.logical.clone(),
                physical: lease.root.physical.clone(),
                logical_identity: lease.root.logical_identity.clone(),
                identity: lease.root.identity.clone(),
                file: lease.root.file.try_clone()?,
            },
        };
        let _namespace = NamespaceGuard::acquire(&manager.root.physical)?;
        lease.check_current_locked().map_err(invalid)?;
        let fields = fields(&lease.info)?;
        let token =
            fields.get("token").ok_or_else(|| invalid("original native guard has no token"))?;
        manager.release_locked(token)
    }

    pub fn open(root: &Path) -> io::Result<Self> {
        if unsafe { libc::getuid() } != unsafe { libc::geteuid() } {
            return Err(invalid("changed-UID build-tree management is unsupported"));
        }
        Ok(Self { root: Root::open(root).map_err(invalid)? })
    }

    pub fn status(&self) -> io::Result<Status> {
        self.check()?;
        let _namespace = NamespaceGuard::acquire(&self.root.physical)?;
        self.snapshot()
    }

    /// Acquire, recover a provably stale independent holder, or adopt an
    /// unwrapped writer before refusing. Tokens alone never excuse a writer:
    /// borrowing requires the same live holder and observed process ancestry.
    pub fn acquire(&self, request: &Acquire) -> io::Result<Acquisition> {
        Ok(match self.acquire_held(request)? {
            HeldAcquisition::Acquired(token, _) => Acquisition::Acquired(token),
            HeldAcquisition::Borrowed(token, _) => Acquisition::Borrowed(token),
            HeldAcquisition::Busy(status) => Acquisition::Busy(status),
        })
    }

    fn acquire_held(&self, request: &Acquire) -> io::Result<HeldAcquisition> {
        self.check()?;
        line(&request.purpose, 2048)?;
        line(&request.contract, 2048)?;
        if let Some(reason) = &request.break_reason {
            reason_line(reason)?;
        }
        if request.owner_pid <= 1 {
            return Err(invalid("a durable owner PID greater than one is required"));
        }
        let owner = process::read(request.owner_pid)?;
        if owner.uid != unsafe { libc::geteuid() } {
            return Err(invalid("a build-tree owner must be in the current account"));
        }
        let deadline = Instant::now()
            .checked_add(request.wait)
            .ok_or_else(|| invalid("build-tree wait duration overflows"))?;
        let mut seed_deadline = None;
        // The temporary name supplies a random token, independently of stdout,
        // an external nonce program or the wall-clock start timestamp.
        let staged_token = tempfile::Builder::new()
            .prefix(".trust-build-lock.token.")
            .tempfile_in(&self.root.physical)?;
        let token = staged_token
            .path()
            .file_name()
            .unwrap()
            .to_str()
            .ok_or_else(|| invalid("non-UTF8 generated token"))?
            .to_owned();
        drop(staged_token);
        let record =
            make_record(&owner, request.kind, &token, &request.purpose, &request.contract, None)?;
        for _ in 0..10000 {
            self.check()?;
            let namespace = NamespaceGuard::acquire(&self.root.physical)?;
            self.check()?;
            if process::read(owner.pid)? != owner {
                return Err(invalid("the requested owner changed while waiting"));
            }
            match self.read_record()? {
                Some(held) => {
                    let holder = held.parse()?;
                    if holder.is_withheld() {
                        return Ok(HeldAcquisition::Busy(self.snapshot()?));
                    }
                    if request.inherited_token.as_deref() == Some(&holder.token) {
                        if holder.parent_managed {
                            return Ok(HeldAcquisition::Busy(self.snapshot()?));
                        }
                        if holder.liveness == Liveness::Live {
                            let ancestor = process::read(holder.pid)?;
                            if holder_matches(&holder, &ancestor)?
                                && process::descendant(&owner, &ancestor)?
                            {
                                return Ok(HeldAcquisition::Borrowed(holder.token, held));
                            }
                        }
                        return Ok(HeldAcquisition::Busy(self.snapshot()?));
                    }
                    if let Some(reason) = &request.break_reason {
                        self.audit("EXPLICIT-BREAK", reason, Some(&held))?;
                        self.retire(&held)?;
                        drop(namespace);
                        continue;
                    }
                    if holder.liveness == Liveness::Gone && !holder.parent_managed {
                        self.audit(
                            "STALE-TAKEOVER",
                            "recorded independent owner is provably gone",
                            Some(&held),
                        )?;
                        self.retire(&held)?;
                        drop(namespace);
                        continue;
                    }
                    let now = Instant::now();
                    let seed = holder.purpose.starts_with("stage-1 seed source ");
                    if seed && seed_deadline.is_none() {
                        seed_deadline = now.checked_add(SEED_WAIT);
                    }
                    let wait =
                        now < deadline || (seed && seed_deadline.is_some_and(|end| now < end));
                    if !wait || holder.parent_managed && holder.liveness != Liveness::Live {
                        return Ok(HeldAcquisition::Busy(self.snapshot()?));
                    }
                    drop(namespace);
                    std::thread::sleep(Duration::from_millis(100));
                }
                None => {
                    if self.holder_directory_exists()? {
                        // Every current initializer publishes while holding the
                        // same namespace guard. An empty directory can only be
                        // left by an interrupted initializer; other contents are
                        // retained for explicit recovery, never recursively erased.
                        let directory = self.root.physical.join(HOLDER);
                        if fs::read_dir(&directory)?.next().is_some() {
                            return Ok(HeldAcquisition::Busy(self.snapshot()?));
                        }
                        self.audit(
                            "STALE-TAKEOVER",
                            "empty interrupted holder initialization",
                            None,
                        )?;
                        fs::remove_dir(directory)?;
                        drop(namespace);
                        continue;
                    }
                    let writers = self.writers(None)?;
                    let conflicts: Vec<_> = writers
                        .iter()
                        .filter(|writer| {
                            !writer.identity.as_ref().is_some_and(|identity| {
                                process::descendant(identity, &owner).unwrap_or(false)
                            })
                        })
                        .collect();
                    if !conflicts.is_empty() && request.break_reason.is_none() {
                        if let Some(writer) =
                            conflicts.iter().find(|writer| writer.identity.is_some())
                        {
                            self.publish_adoption(
                                writer,
                                "found an unwrapped writer while the tree was free",
                            )?;
                        }
                        return Ok(HeldAcquisition::Busy(self.snapshot()?));
                    }
                    if !conflicts.is_empty() {
                        self.audit(
                            "EXPLICIT-BREAK",
                            request.break_reason.as_deref().unwrap(),
                            None,
                        )?;
                    }
                    self.publish_new(&record)?;
                    let held =
                        self.read_record()?.ok_or_else(|| invalid("new holder disappeared"))?;
                    // Check again after publication. A writer that became visible
                    // in the observation window must not leave a free namespace.
                    let holder = held.parse()?;
                    let extra = self.writers(Some(&holder))?;
                    let conflict = extra.iter().find(|writer| !writer.covered);
                    if let Some(writer) = conflict {
                        if request.break_reason.is_none() {
                            if writer.identity.is_some() {
                                self.replace_adoption(
                                    &held,
                                    writer,
                                    "writer appeared during holder publication",
                                )?;
                            }
                            return Ok(HeldAcquisition::Busy(self.snapshot()?));
                        }
                    }
                    self.check_record(&held)?;
                    return Ok(HeldAcquisition::Acquired(token, held));
                }
            }
        }
        Err(io::Error::new(
            io::ErrorKind::TimedOut,
            "build-tree acquisition exceeded its contention bound",
        ))
    }

    /// Release this exact token, retaining or handing over ownership when a
    /// writer survives. Native parent-managed ownership is never released by
    /// this legacy token surface, even when its process is dead.
    pub fn release(&self, token: &str) -> io::Result<Release> {
        line(token, 512)?;
        if token.is_empty() {
            return Err(invalid("release requires a token"));
        }
        self.check()?;
        let _namespace = NamespaceGuard::acquire(&self.root.physical)?;
        self.release_locked(token)
    }

    fn release_locked(&self, token: &str) -> io::Result<Release> {
        self.check()?;
        let Some(held) = self.read_record()? else {
            return if self.holder_directory_exists()? {
                Err(invalid("holder metadata is missing; retain it for explicit recovery"))
            } else {
                Ok(Release::AlreadyFree)
            };
        };
        let holder = held.parse()?;
        if holder.is_withheld() {
            return Ok(Release::ParentManaged);
        }
        if holder.token != token {
            return Ok(Release::ForeignHolder);
        }
        if holder.parent_managed {
            return Ok(Release::ParentManaged);
        }
        let writers = self.writers(None)?;
        for writer in writers {
            let Some(identity) = &writer.identity else { continue };
            // Retain every discovered writer in this exact tree, even when
            // reparenting erased ancestry or an unrelated unwrapped peer is
            // present. This arm can only retain exclusion, never grant work.
            self.audit(
                "ORPHAN-HANDOVER",
                &format!("holder {} has surviving writer {}", holder.pid, identity.pid),
                Some(&held),
            )?;
            self.replace_adoption(&held, &writer, "holder released while a writer remained alive")?;
            return Ok(Release::HandedOver(writer));
        }
        if !self.writers(None)?.is_empty() {
            return Err(invalid("a live sentinel or uncertain writer prevents release"));
        }
        self.retire(&held)?;
        Ok(Release::Released)
    }

    /// Explicit recovery. Callers must supply the person's meaningful reason;
    /// this method never invents approval from a stale PID or an environment bit.
    pub fn break_holder(&self, reason: &str) -> io::Result<bool> {
        reason_line(reason)?;
        self.check()?;
        let _namespace = NamespaceGuard::acquire(&self.root.physical)?;
        let Some(held) = self.read_record()? else {
            if !self.holder_directory_exists()? {
                return Ok(false);
            }
            let directory = self.root.physical.join(HOLDER);
            if fs::read_dir(&directory)?.next().is_some() {
                return Err(invalid(
                    "unreadable holder has unknown contents; no unchecked recursive removal",
                ));
            }
            self.audit("EXPLICIT-BREAK", reason, None)?;
            fs::remove_dir(directory)?;
            return Ok(true);
        };
        if held.parse()?.is_withheld() {
            return Err(invalid(
                "WITHHELD requires original Host closure; generic recovery is unavailable",
            ));
        }
        self.audit("EXPLICIT-BREAK", reason, Some(&held))?;
        self.retire(&held)?;
        Ok(true)
    }

    fn check(&self) -> io::Result<()> {
        self.root.check_current().map_err(invalid)
    }

    fn snapshot(&self) -> io::Result<Status> {
        self.check()?;
        let record = self.read_record()?;
        let holder = record.as_ref().map(HeldRecord::parse).transpose()?;
        let malformed_holder = holder.is_none() && self.holder_directory_exists()?;
        let writers = self.writers(holder.as_ref())?;
        self.check()?;
        Ok(Status { holder, writers, malformed_holder })
    }

    fn holder_directory_exists(&self) -> io::Result<bool> {
        let path = self.root.physical.join(HOLDER);
        match fs::symlink_metadata(&path) {
            Ok(metadata) if metadata.is_dir() && metadata.uid() == unsafe { libc::geteuid() } => {
                if metadata.mode() & 0o022 == 0 {
                    Ok(true)
                } else {
                    // Refused, since another account could have changed it. This
                    // crate made its holders 0775 under umask 002 before
                    // `create_holder_directory`, and every verb that reads the
                    // holder (acquire, release, status and break;
                    // reclaim-incremental reads none) reads it through here, so
                    // the refusal names the mode and the recovery, its path
                    // quoted so the command can be pasted into a shell. `break`
                    // has no liveness check, so the recovery names it only for
                    // a holder whose process lives on with no build under it.
                    Err(invalid(format!(
                        "holder directory {} is group or other writable (mode {:04o}); \
                         check that its info is yours and that no build still runs under \
                         the holder it names, then run `chmod go-w {}`: the next acquire \
                         takes over a holder whose process has exited, and \
                         `targo trust repo lock break --reason TEXT` retires one whose \
                         process lives on",
                        path.display(),
                        metadata.mode() & 0o7777,
                        crate::shell_word::quoted(&path)
                    )))
                }
            }
            Ok(_) => Err(invalid("holder directory must be an owned non-symlink directory")),
            Err(error) if error.kind() == io::ErrorKind::NotFound => Ok(false),
            Err(error) => Err(error),
        }
    }

    fn read_record(&self) -> io::Result<Option<HeldRecord>> {
        if !self.holder_directory_exists()? {
            return Ok(None);
        }
        let path = self.root.physical.join(HOLDER);
        let directory = open_directory(&path).map_err(invalid)?;
        let identity = directory.metadata()?;
        // SAFETY: directory is an owned live descriptor; info is NUL-terminated.
        let fd = unsafe {
            libc::openat(
                directory.as_raw_fd(),
                c"info".as_ptr(),
                libc::O_RDONLY | libc::O_NOFOLLOW | libc::O_NONBLOCK | libc::O_CLOEXEC,
            )
        };
        if fd < 0 {
            let error = io::Error::last_os_error();
            return if error.kind() == io::ErrorKind::NotFound { Ok(None) } else { Err(error) };
        }
        // SAFETY: the successful openat returned a new uniquely owned descriptor.
        let file = unsafe { File::from_raw_fd(fd) };
        let metadata = file.metadata()?;
        if !metadata.is_file()
            || metadata.uid() != unsafe { libc::geteuid() }
            || metadata.nlink() != 1
            || metadata.mode() & 0o022 != 0
            || metadata.len() > RECORD_LIMIT
        {
            return Err(invalid("holder record must be bounded, owned and singly linked"));
        }
        let mut bytes = Vec::new();
        (&file).take(RECORD_LIMIT + 1).read_to_end(&mut bytes)?;
        if bytes.len() as u64 > RECORD_LIMIT {
            return Err(invalid("holder record exceeds its bound"));
        }
        let text = String::from_utf8(bytes).map_err(|_| invalid("holder record is not UTF-8"))?;
        let held = HeldRecord { directory, identity, file, metadata, text };
        self.check_record(&held)?;
        Ok(Some(held))
    }

    fn check_record(&self, held: &HeldRecord) -> io::Result<()> {
        use std::os::unix::fs::FileExt;
        self.check()?;
        let directory = self.root.physical.join(HOLDER);
        let metadata = held.file.metadata()?;
        if !same_inode(&held.identity, Some(&held.directory.metadata()?))
            || !same_inode(&held.identity, fs::symlink_metadata(&directory).ok().as_ref())
            || !same_inode(&held.metadata, Some(&metadata))
            || !same_inode(
                &held.metadata,
                fs::symlink_metadata(directory.join("info")).ok().as_ref(),
            )
            || metadata.nlink() != 1
            || metadata.len() != held.text.len() as u64
            || metadata.uid() != unsafe { libc::geteuid() }
            || metadata.mode() & 0o022 != 0
        {
            return Err(invalid("original holder directory or record changed"));
        }
        let mut bytes = vec![0; held.text.len()];
        held.file.read_exact_at(&mut bytes, 0)?;
        if bytes != held.text.as_bytes() {
            return Err(invalid("original holder record bytes changed"));
        }
        self.check()
    }

    fn publish_new(&self, text: &str) -> io::Result<()> {
        self.check()?;
        let staged = self.stage(text)?;
        let directory = self.root.physical.join(HOLDER);
        create_holder_directory(&directory)?;
        let opened = open_directory(&directory).map_err(invalid)?;
        let identity = opened.metadata()?;
        self.check()?;
        if !same_inode(&identity, fs::symlink_metadata(&directory).ok().as_ref()) {
            return Err(invalid("holder directory changed during publication"));
        }
        staged.persist_noclobber(directory.join("info")).map_err(|error| error.error)?;
        opened.sync_all()?;
        self.check()
    }

    fn stage(&self, text: &str) -> io::Result<tempfile::NamedTempFile> {
        if text.len() as u64 > RECORD_LIMIT {
            return Err(invalid("new holder record exceeds its bound"));
        }
        let mut temporary = tempfile::Builder::new()
            .prefix(".trust-build-lock.tmp.")
            .tempfile_in(&self.root.physical)?;
        temporary.write_all(text.as_bytes())?;
        temporary.as_file().sync_all()?;
        Ok(temporary)
    }

    fn publish_adoption(&self, writer: &Writer, why: &str) -> io::Result<()> {
        let record = adoption_record(&self.root.physical, writer, why)?;
        self.publish_new(&record)
    }

    fn replace_adoption(&self, held: &HeldRecord, writer: &Writer, why: &str) -> io::Result<()> {
        let record = adoption_record(&self.root.physical, writer, why)?;
        let staged = self.stage(&record)?;
        self.check_record(held)?;
        // The original directory remains continuously present. Atomic record
        // replacement under the common namespace guard never frees the tree.
        staged
            .persist(self.root.physical.join(HOLDER).join("info"))
            .map_err(|error| error.error)?;
        held.directory.sync_all()?;
        self.check()
    }

    fn retire(&self, held: &HeldRecord) -> io::Result<()> {
        self.check_record(held)?;
        for entry in fs::read_dir(self.root.physical.join(HOLDER))? {
            if entry?.file_name() != OsStr::new("info") {
                return Err(invalid("unknown holder contents prevent retirement"));
            }
        }
        let quarantine = tempfile::Builder::new()
            .prefix(".trust-build-lock.stale.")
            .tempdir_in(&self.root.physical)?;
        let moved = quarantine.path().join("holder");
        fs::rename(self.root.physical.join(HOLDER), &moved)?;
        if !same_inode(&held.identity, fs::symlink_metadata(&moved).ok().as_ref()) {
            // Retain unknown contents; never recursively delete a replacement.
            let _ = quarantine.keep();
            return Err(invalid("holder changed at retirement; retained quarantine"));
        }
        self.check()?;
        quarantine.close()
    }

    fn audit(&self, event: &str, reason: &str, held: Option<&HeldRecord>) -> io::Result<()> {
        line(reason, 4096)?;
        self.check()?;
        let path = self.root.physical.join(".trust-build-lock.breaks");
        let mut file = OpenOptions::new()
            .append(true)
            .create(true)
            .mode(0o600)
            .custom_flags(libc::O_NOFOLLOW | libc::O_NONBLOCK | libc::O_CLOEXEC)
            .open(&path)?;
        let metadata = file.metadata()?;
        if !metadata.is_file()
            || metadata.uid() != unsafe { libc::geteuid() }
            || metadata.nlink() != 1
            || metadata.mode() & 0o022 != 0
            || !same_inode(&metadata, fs::symlink_metadata(&path).ok().as_ref())
        {
            return Err(invalid("displacement audit must be the owned regular inode"));
        }
        let now = SystemTime::now().duration_since(UNIX_EPOCH).map_err(invalid)?.as_secs();
        writeln!(file, "when={now} pid={} reason={event} ({reason})", std::process::id())?;
        if let Some(held) = held {
            for line in held.text.lines() {
                writeln!(file, "    displaced: {line}")?;
            }
        }
        writeln!(file)?;
        file.sync_all()?;
        if !same_inode(&metadata, fs::symlink_metadata(&path).ok().as_ref())
            || file.metadata()?.nlink() != 1
        {
            return Err(invalid("displacement audit inode changed before holder mutation"));
        }
        self.check()
    }

    fn writers(&self, holder: Option<&Holder>) -> io::Result<Vec<Writer>> {
        let mut writers = Vec::new();
        let owner = holder.filter(|holder| holder.liveness == Liveness::Live).and_then(|holder| {
            process::read(holder.pid)
                .ok()
                .filter(|owner| holder_matches(holder, owner).unwrap_or(false))
        });
        let pids = process::all_pids().inspect_err(|error| {
            let _ = writeln!(
                io::stderr().lock(),
                "trust build-tree lock: native writer process table: {error}"
            );
        })?;
        // One exit-wait budget for the whole census (process::CensusSettle).
        let settle = process::CensusSettle::new();
        for pid in pids {
            if pid == std::process::id() {
                continue;
            }
            let identity = match process::writer_identity(pid, &settle) {
                Ok(Some(identity)) => identity,
                Ok(None) => continue,
                Err(error) => {
                    return Err(io::Error::new(
                        error.kind(),
                        format!("native process identity {pid}: {error}"),
                    ));
                }
            };
            if identity.zombie || identity.uid != unsafe { libc::geteuid() } {
                continue;
            }
            let name = identity.name.to_string_lossy().to_ascii_lowercase();
            if !native_build_program(&name)
                && !name.starts_with("python")
                && !name.starts_with("pypy")
            {
                continue;
            }
            let args = match process::args(pid) {
                Ok(args) => args,
                Err(_) if process::census_gone(pid, &settle) => continue,
                Err(error) => {
                    return Err(io::Error::new(
                        error.kind(),
                        format!("native writer argv {pid}: {error}"),
                    ));
                }
            };
            let kind = if native_build_program(&name) {
                if native_management_request(&name, &args) {
                    continue;
                }
                Some(Kind::Build)
            } else if args.iter().any(|arg| {
                arg.as_bytes()
                    .windows(b"trust_ir_producer_scorecard.py".len())
                    .any(|part| part == b"trust_ir_producer_scorecard.py")
            }) {
                Some(Kind::Measurement)
            } else {
                None
            };
            let Some(kind) = kind else { continue };
            let cwd = match process::cwd(pid) {
                Ok(cwd) => cwd,
                Err(_) if process::census_gone(pid, &settle) => continue,
                Err(error) => {
                    return Err(io::Error::new(
                        error.kind(),
                        format!("native writer cwd {pid}: {error}"),
                    ));
                }
            };
            if !cwd.starts_with(&self.root.physical)
                && !args.iter().any(|arg| names_root(arg, &self.root.physical))
            {
                continue;
            }
            let current = process::writer_recheck(&identity, &settle).inspect_err(|error| {
                let _ = writeln!(
                    io::stderr().lock(),
                    "trust build-tree lock: native writer final identity {pid}: {error}"
                );
            })?;
            if !current {
                continue;
            }
            let covered = owner
                .as_ref()
                .is_some_and(|owner| process::descendant(&identity, owner).unwrap_or(false));
            writers.push(Writer {
                pid: Some(pid),
                kind,
                command: command_text(&args),
                covered,
                identity: Some(identity),
            });
        }
        let sentinel = self.root.physical.join(SENTINEL);
        match fs::symlink_metadata(&sentinel) {
            Ok(metadata) => {
                if !metadata.is_file()
                    || metadata.file_type().is_symlink()
                    || metadata.len() > RECORD_LIMIT
                {
                    return Err(invalid(
                        "legacy measurement sentinel is not a bounded regular file",
                    ));
                }
                let text = fs::read_to_string(&sentinel)?;
                let pid = text
                    .lines()
                    .find_map(|line| line.strip_prefix("pid="))
                    .and_then(|pid| pid.parse::<u32>().ok());
                // A bare sentinel PID has no start identity and cannot be
                // adopted. Unreadable identity keeps the tree busy.
                if pid.is_none() || process::present(pid.unwrap())? {
                    writers.push(Writer {
                        pid: None,
                        kind: Kind::Measurement,
                        command: format!(
                            "live or unclassified legacy measurement sentinel {}",
                            sentinel.display()
                        ),
                        covered: false,
                        identity: None,
                    });
                }
            }
            Err(error) if error.kind() == io::ErrorKind::NotFound => {}
            Err(error) => return Err(error),
        }
        writers.sort_by_key(|writer| writer.pid);
        Ok(writers)
    }
}

// Discovery only retains exclusion. These names cannot grant an SDK, proof,
// CPU lease or permission to execute. Actual cwd/argv root and kernel identity
// checks still apply before any process is reported as a writer.
fn native_build_program(name: &str) -> bool {
    matches!(
        name,
        "bootstrap"
            | "targo"
            | "cargo"
            | "targo-trust"
            | "cargo-trust"
            | "trustc"
            | "rustc"
            | "trustdoc"
            | "rustdoc"
            | "compiletest"
            | "clang"
            | "clang++"
            | "cc"
            | "c++"
            | "cmake"
            | "ninja"
            | "make"
            | "gmake"
            | "rust-lld"
            | "lld"
            | "ld.lld"
            | "ld64.lld"
            | "ld"
    ) || name.starts_with("clang-")
}

fn native_management_request(name: &str, args: &[OsString]) -> bool {
    let at = |index: usize| args.get(index).and_then(|arg| arg.to_str());
    match name {
        "bootstrap" => {
            matches!(at(1), Some("--trust-build-tree-lock" | "--trust-build-lock-guard"))
        }
        "targo" | "cargo" => {
            matches!((at(1), at(2), at(3)), (Some("trust"), Some("repo"), Some("lock")))
                || matches!(
                    (at(1), at(2), at(3)),
                    (Some("--unverified"), Some("resource"), Some("repo-lock-exec" | "repo-prune"))
                )
                // These exact coordinators acquire the SAME atomic Manager
                // before protected work. Their waiting outer fixed process
                // is not an independent writer to adopt during acquisition.
                || (matches!(
                    (at(1), at(2), at(3)),
                    (Some("--unverified"), Some("resource"), Some("fixed"))
                ) && matches!(
                    args.iter().position(|arg| arg == "--").and_then(|index| at(index + 1)),
                    Some("repo-lock-exec" | "repo-prune")
                ))
                || matches!(
                    at(1),
                    Some("report" | "help" | "version" | "--help" | "-h" | "--version" | "-V")
                )
        }
        "targo-trust" | "cargo-trust" => {
            matches!((at(1), at(2)), (Some("repo"), Some("lock")))
                || matches!((at(1), at(2), at(3)), (Some("trust"), Some("repo"), Some("lock")))
        }
        _ => false,
    }
}

struct HeldRecord {
    directory: File,
    identity: Metadata,
    file: File,
    metadata: Metadata,
    text: String,
}
impl HeldRecord {
    fn parse(&self) -> io::Result<Holder> {
        let fields = fields(&self.text)?;
        let pid = fields
            .get("pid")
            .and_then(|pid| pid.parse::<u32>().ok())
            .filter(|pid| *pid > 1)
            .ok_or_else(|| invalid("holder has no valid durable PID"))?;
        let token = fields
            .get("token")
            .filter(|token| !token.is_empty())
            .ok_or_else(|| invalid("holder has no token"))?
            .clone();
        let mut holder = Holder {
            token,
            pid,
            group: fields.get("pgid").and_then(|group| group.parse().ok()),
            kind: fields.get("kind").cloned().unwrap_or_default(),
            purpose: fields.get("purpose").cloned().unwrap_or_default(),
            command: fields.get("cmd").cloned().unwrap_or_default(),
            contract: fields.get("contract").cloned().unwrap_or_default(),
            parent_managed: ["release_parent_pid", "release_parent_start", "release_token"]
                .iter()
                .any(|key| fields.contains_key(*key)),
            liveness: Liveness::Unknown,
            fields,
        };
        holder.liveness = match process::present(pid) {
            Ok(false) => Liveness::Gone,
            Ok(true) => match process::read(pid) {
                Ok(current) => match holder_matches(&holder, &current) {
                    Ok(true) => Liveness::Live,
                    Ok(false) => Liveness::Gone,
                    Err(_) => Liveness::Unknown,
                },
                Err(_) => Liveness::Unknown,
            },
            Err(_) => Liveness::Unknown,
        };
        Ok(holder)
    }
}

fn fields(text: &str) -> io::Result<BTreeMap<String, String>> {
    if text.len() as u64 > RECORD_LIMIT || !text.ends_with('\n') {
        return Err(invalid("holder record is overlong or incomplete"));
    }
    let mut fields = BTreeMap::new();
    const KNOWN: [&str; 18] = [
        "token",
        "kind",
        "pid",
        "pstart",
        "pstart_utc",
        "pgid",
        "started",
        "purpose",
        "cmd",
        "contract",
        "host",
        "adopted",
        "native_birth",
        "release_parent_pid",
        "release_parent_start",
        "release_token",
        "state",
        "withheld_version",
    ];
    for row in text.strip_suffix('\n').unwrap().split('\n') {
        let (key, value) = row.split_once('=').ok_or_else(|| invalid("malformed holder field"))?;
        if !KNOWN.contains(&key)
            || !key.bytes().all(|byte| byte.is_ascii_lowercase() || byte == b'_')
            || value.chars().any(char::is_control)
            || fields.insert(key.to_owned(), value.to_owned()).is_some()
        {
            return Err(invalid("duplicate or invalid holder field"));
        }
    }
    if !matches!(fields.get("kind").map(String::as_str), Some("build" | "measurement")) {
        return Err(invalid("unknown holder kind is retained for explicit recovery"));
    }
    match (
        fields.get("state").map(String::as_str),
        fields.get("withheld_version").map(String::as_str),
    ) {
        (None, None) => {}
        (Some("WITHHELD"), Some("1"))
            if fields.get("release_parent_pid").is_some_and(String::is_empty)
                && !fields.contains_key("release_parent_start")
                && !fields.contains_key("release_token") => {}
        _ => return Err(invalid("unknown or incomplete withheld state; recovery is unavailable")),
    }
    Ok(fields)
}

fn holder_matches(holder: &Holder, current: &process::Process) -> io::Result<bool> {
    if current.pid != holder.pid {
        return Ok(false);
    }
    if let Some(birth) = holder.fields.get("native_birth") {
        let birth: u64 = birth.parse().map_err(|_| invalid("invalid native holder birth"))?;
        return Ok(birth == current.birth);
    }
    match holder.fields.get("pstart_utc").filter(|start| !start.is_empty()) {
        Some(start) => Ok(*start == process::utc_start(current.epoch_seconds)?),
        // An old locale-sensitive start or an absent/empty UTC reading does
        // not establish PID reuse. Keep the actual live PID conservatively.
        None => Err(invalid("a live PID without a zone-free start has unknown identity")),
    }
}

fn make_record(
    owner: &process::Process,
    kind: Kind,
    token: &str,
    purpose: &str,
    contract: &str,
    adopted: Option<&str>,
) -> io::Result<String> {
    let start = process::utc_start(owner.epoch_seconds)?;
    let command = command_text(&process::args(owner.pid)?);
    if process::read(owner.pid)? != *owner {
        return Err(invalid("owner changed during metadata observation"));
    }
    let now = SystemTime::now().duration_since(UNIX_EPOCH).map_err(invalid)?.as_secs();
    let mut record = format!(
        "token={token}\nkind={}\npid={}\npstart={start}\npstart_utc={start}\npgid={}\nstarted={now}\npurpose={purpose}\ncmd={command}\ncontract={contract}\nnative_birth={}\n",
        kind.as_str(),
        owner.pid,
        owner.group,
        owner.birth
    );
    if let Some(adopted) = adopted {
        record.push_str(&format!("adopted={adopted}\n"));
    }
    Ok(record)
}

fn adoption_record(root: &Path, writer: &Writer, why: &str) -> io::Result<String> {
    let owner = writer
        .identity
        .as_ref()
        .ok_or_else(|| invalid("a sentinel has no adoptable process identity"))?;
    if process::read(owner.pid)? != *owner {
        return Err(invalid("writer changed before adoption"));
    }
    let temporary = tempfile::NamedTempFile::new_in(root)?;
    let token = temporary.path().file_name().unwrap().to_string_lossy();
    make_record(
        owner,
        writer.kind,
        &token,
        &format!("ADOPTED (unwrapped writer): {why}"),
        "an unwrapped writer is rewriting this tree; wait for it or explicitly recover",
        Some(why),
    )
}

fn names_root(argument: &OsStr, root: &Path) -> bool {
    let bytes = argument.as_bytes();
    let root = root.as_os_str().as_bytes();
    if root.is_empty() {
        return false;
    }
    bytes.windows(root.len()).enumerate().any(|(at, part)| {
        part == root
            && bytes.get(at + root.len()).is_none_or(|next| matches!(next, b'/' | b' ' | b'\t'))
    })
}

fn command_text(arguments: &[OsString]) -> String {
    let text = arguments.iter().map(|arg| arg.to_string_lossy()).collect::<Vec<_>>().join(" ");
    text.chars()
        .map(|character| {
            if character.is_control() || matches!(character, '\u{2028}' | '\u{2029}') {
                ' '
            } else {
                character
            }
        })
        .take(2048)
        .collect()
}

fn line(value: &str, maximum: usize) -> io::Result<()> {
    if value.len() > maximum
        || value
            .chars()
            .any(|character| character.is_control() || matches!(character, '\u{2028}' | '\u{2029}'))
    {
        return Err(invalid("holder metadata must be a bounded single line"));
    }
    Ok(())
}
fn reason_line(reason: &str) -> io::Result<()> {
    line(reason, 4096)?;
    if reason.trim().is_empty() {
        return Err(invalid("explicit recovery requires a meaningful reason"));
    }
    Ok(())
}
fn invalid(error: impl ToString) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, error.to_string())
}

#[cfg(feature = "resident-inputs")]
pub use lease::RefusedInputRetirement;
#[cfg(all(feature = "native-exec", target_os = "macos", target_arch = "aarch64"))]
pub(crate) use lease::{MaintenanceBinding, MaintenanceLease};
