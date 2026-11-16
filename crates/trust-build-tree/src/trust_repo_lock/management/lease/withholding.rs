//! Consuming transition of original owned custody into durable exclusion.
//! No Host release/transfer authority exists in this module.

use std::ffi::CString;
use std::fs::File;
use std::io::Write as _;
use std::os::fd::{AsRawFd as _, FromRawFd as _};
use std::os::unix::fs::{FileExt as _, MetadataExt as _};
use std::sync::atomic::{AtomicU64, Ordering};
use std::{fmt, io};

use super::{HeldRecord, Lease, NamespaceGuard, invalid};
use crate::trust_repo_lock::same_inode;

/// Publication history is diagnostic data, never permission to release.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum WithholdPublication {
    NotAttempted,
    Attempted,
}

/// Retains the SAME acquired manager, root and original record descriptions,
/// plus the new record pinned after atomic replacement in the SAME directory.
/// Drop never releases. There is deliberately no release, import or
/// deserialization API: close-only source offers confer no Host closure.
#[must_use = "retain withheld original custody; dropping cannot release exclusion"]
pub struct WithheldLease {
    original: Lease,
    held: HeldRecord,
    protected_scope: std::sync::atomic::AtomicBool,
}

impl fmt::Debug for WithheldLease {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("WithheldLease").finish_non_exhaustive()
    }
}

impl WithheldLease {
    /// Checks input custody only; this grants no Host execution or release.
    pub fn check_current(&self) -> io::Result<()> {
        check_withheld(&self.original, &self.held)
    }
}

fn check_withheld(original: &Lease, held: &HeldRecord) -> io::Result<()> {
    if original.process != std::process::id() || original.borrowed {
        return Err(invalid("withheld custody belongs to its original acquiring process"));
    }
    let _namespace = NamespaceGuard::acquire(&original.manager.root.physical)?;
    if !same_inode(&original.held.identity, Some(&held.identity)) {
        return Err(invalid("withheld holder is not the original acquired directory"));
    }
    // Retain/check the old descriptions too. Its info entry was replaced,
    // so the original file may be unlinked but cannot become another file.
    check_original_description(&original.held)?;
    original.manager.check_record(held)?;
    if !held.parse()?.is_withheld() {
        return Err(invalid("original withheld record lost its closed state"));
    }
    Ok(())
}

/// Owns all retained inputs after a failed conversion. Its destructor never
/// performs ordinary release, including on ambiguous publication or unwind.
#[must_use = "retain failed custody; publication failure is not release authority"]
pub struct WithholdFailure {
    original: Box<Lease>,
    published: Option<Box<HeldRecord>>,
    error: io::Error,
    publication: WithholdPublication,
}

impl WithholdFailure {
    pub fn error(&self) -> &io::Error {
        &self.error
    }

    pub fn publication(&self) -> WithholdPublication {
        self.publication
    }

    /// Rechecks the originally acquired inputs. A successful observation does
    /// not erase publication history or establish a Host closure.
    pub fn check_original_current(&self) -> io::Result<()> {
        self.original.check_current()
    }

    /// Checks the actual retained publication when known, otherwise the exact
    /// original. Success does not make a failed transition execution-eligible.
    pub fn check_current(&self) -> io::Result<()> {
        match &self.published {
            Some(held) => check_withheld(&self.original, held),
            None => self.original.check_current(),
        }
    }

    /// Explicitly recover ordinary custody only if publication was NEVER
    /// attempted and the exact original still validates. No error kind can
    /// substitute for those checks. Failure returns this same retained owner.
    pub fn try_recover_unpublished(mut self) -> Result<Lease, Self> {
        if self.publication != WithholdPublication::NotAttempted
            || self.original.check_current().is_err()
        {
            return Err(self);
        }
        self.original.release_on_drop = true;
        Ok(*self.original)
    }
}

impl fmt::Debug for WithholdFailure {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("WithholdFailure")
            .field("publication", &self.publication)
            .field("error", &self.error)
            .finish_non_exhaustive()
    }
}

impl fmt::Display for WithholdFailure {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "withholding {:?}: {}", self.publication, self.error)
    }
}

impl std::error::Error for WithholdFailure {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        Some(&self.error)
    }
}

impl Lease {
    /// Consumes only an owned, same-process, exact original lease. No record,
    /// token, path, FD or borrowed acquisition can construct withheld custody.
    pub fn into_withheld(mut self) -> Result<WithheldLease, WithholdFailure> {
        // Disable automatic release BEFORE every fallible operation. Even an
        // unwind or post-rename IO error must not run ordinary release.
        self.release_on_drop = false;
        let mut publication = WithholdPublication::NotAttempted;
        let mut published = None;
        match self.withhold_record(&mut publication, &mut published) {
            Ok(()) => Ok(WithheldLease {
                original: self,
                held: published.expect("published record"),
                protected_scope: std::sync::atomic::AtomicBool::new(false),
            }),
            Err(error) => Err(WithholdFailure {
                original: Box::new(self),
                published: published.map(Box::new),
                error,
                publication,
            }),
        }
    }

    fn withhold_record(
        &self,
        publication: &mut WithholdPublication,
        published: &mut Option<HeldRecord>,
    ) -> io::Result<()> {
        if self.borrowed || self.process != std::process::id() {
            return Err(invalid("only an owned same-process lease can become WITHHELD"));
        }
        let _namespace = NamespaceGuard::acquire(&self.manager.root.physical)?;
        self.manager.check_record(&self.held)?;
        let holder = self.held.parse()?;
        if holder.parent_managed || holder.is_withheld() {
            return Err(invalid("existing outer custody cannot be promoted to WITHHELD"));
        }
        // Empty legacy marker is deliberately incapable of satisfying the
        // existing parent PID/start/token handoff. Its presence only refuses
        // borrowing, stale takeover and token release in older active readers.
        let text =
            format!("{}state=WITHHELD\nwithheld_version=1\nrelease_parent_pid=\n", self.held.text);
        super::super::fields(&text)?;
        // This already-held holder is the publication namespace. Staging at
        // the repository root would mutate an unrelated retained config/source
        // parent even though only this original info record is being replaced.
        let staged = StagedRecord::new(&self.held.directory, &text)?;
        let metadata = staged.file().metadata()?;
        let directory = self.held.directory.try_clone()?;
        let identity = self.held.identity.clone();
        self.manager.check_record(&self.held)?;
        staged.check_named()?;
        #[cfg(test)]
        if FAIL_BEFORE_REPLACE.with(|fault| fault.get()) {
            return Err(io::Error::other("injected failure before publication attempt"));
        }
        *publication = WithholdPublication::Attempted;
        let file = staged.publish()?;
        *published = Some(HeldRecord { directory, identity, file, metadata, text });
        #[cfg(test)]
        if FAIL_AFTER_REPLACE.with(|fault| fault.get()) {
            return Err(io::Error::other("injected sync failure after actual info replacement"));
        }
        self.held.directory.sync_all()?;
        check_original_description(&self.held)?;
        self.manager.check_record(published.as_ref().expect("published original record"))
    }
}

/// A new private record in the SAME original holder description. Names are
/// collision-refusing data, never lease/release authority. No absolute holder
/// path, reopen or symlink traversal is used for creation, publication or Drop.
struct StagedRecord<'a> {
    directory: &'a File,
    name: CString,
    file: Option<File>,
    expected: Vec<u8>,
}
impl<'a> StagedRecord<'a> {
    fn new(directory: &'a File, text: &str) -> io::Result<Self> {
        static SEQUENCE: AtomicU64 = AtomicU64::new(1);
        let mut sequence = SEQUENCE.load(Ordering::Relaxed);
        loop {
            let next = sequence
                .checked_add(1)
                .ok_or_else(|| invalid("holder staging sequence exhausted"))?;
            match SEQUENCE.compare_exchange_weak(
                sequence,
                next,
                Ordering::Relaxed,
                Ordering::Relaxed,
            ) {
                Ok(_) => break,
                Err(current) => sequence = current,
            }
        }
        let name = CString::new(format!(".withheld-info-{}-{sequence}", std::process::id()))
            .map_err(io::Error::other)?;
        Self::create(directory, name, text)
    }
    fn create(directory: &'a File, name: CString, text: &str) -> io::Result<Self> {
        if text.len() as u64 > super::super::RECORD_LIMIT {
            return Err(invalid("new holder record exceeds its bound"));
        }
        if name.as_bytes().is_empty()
            || name.as_bytes().contains(&b'/')
            || matches!(name.as_bytes(), b"." | b".." | b"info")
        {
            return Err(invalid("staged record requires a private single leaf"));
        }
        let expected = text.as_bytes().to_vec();
        // SAFETY: the original holder directory is retained; the generated
        // single leaf is NUL-terminated. O_EXCL refuses ANY existing entry.
        let fd = unsafe {
            libc::openat(
                directory.as_raw_fd(),
                name.as_ptr(),
                libc::O_RDWR
                    | libc::O_CREAT
                    | libc::O_EXCL
                    | libc::O_NOFOLLOW
                    | libc::O_NONBLOCK
                    | libc::O_CLOEXEC,
                0o600,
            )
        };
        if fd < 0 {
            return Err(io::Error::last_os_error());
        }
        // Install cleanup ownership BEFORE every fallible write or check.
        let mut staged =
            Self { directory, name, file: Some(unsafe { File::from_raw_fd(fd) }), expected };
        staged.file.as_mut().expect("original new file").write_all(text.as_bytes())?;
        staged.file().sync_all()?;
        staged.check_prepared()?;
        staged.retain_readonly()?;
        Ok(staged)
    }
    fn file(&self) -> &File {
        self.file.as_ref().expect("same unpublished record")
    }
    fn open_named(&self) -> io::Result<File> {
        // SAFETY: this opens one leaf relative to the SAME held directory;
        // no target of a symlink or different holder can be followed.
        let fd = unsafe {
            libc::openat(
                self.directory.as_raw_fd(),
                self.name.as_ptr(),
                libc::O_RDONLY | libc::O_NOFOLLOW | libc::O_NONBLOCK | libc::O_CLOEXEC,
            )
        };
        if fd < 0 {
            return Err(io::Error::last_os_error());
        }
        Ok(unsafe { File::from_raw_fd(fd) })
    }
    fn check_named(&self) -> io::Result<()> {
        let named = self.open_named()?;
        let before = self.file().metadata()?;
        let current = named.metadata()?;
        if !before.is_file()
            || !current.is_file()
            || !same_inode(&before, Some(&current))
            || before.nlink() != 1
            || current.nlink() != 1
            || before.uid() != unsafe { libc::geteuid() }
            || current.len() != before.len()
            || current.mode() != before.mode()
        {
            return Err(invalid("original staged holder record changed"));
        }
        Ok(())
    }
    fn retain_readonly(&mut self) -> io::Result<()> {
        // Attenuate only this freshly created, still-private staged record.
        // The original HeldRecord will be born readonly; an export must never
        // reopen or replace a live owner's original description.
        self.check_prepared()?;
        let readonly = self.open_named()?;
        let before = self.file().metadata()?;
        let observed = readonly.metadata()?;
        if !same_inode(&before, Some(&observed))
            || !observed.is_file()
            || observed.nlink() != 1
            || observed.uid() != unsafe { libc::geteuid() }
            || observed.mode() != before.mode()
            || observed.len() != self.expected.len() as u64
        {
            return Err(invalid("readonly staged holder record changed"));
        }
        let mut bytes = vec![0; self.expected.len()];
        readonly.read_exact_at(&mut bytes, 0)?;
        if bytes != self.expected {
            return Err(invalid("readonly staged holder record bytes changed"));
        }
        self.check_prepared()?;
        // Drop the writer before publication. All subsequent ownership,
        // checks and close-only duplicates use this exact readonly OFD.
        drop(self.file.replace(readonly));
        self.check_prepared()
    }
    fn publish(mut self) -> io::Result<File> {
        self.check_prepared()?;
        // SAFETY: both single leaves are within the SAME original held holder
        // descriptor. Root/holder path replacement cannot redirect this write.
        if unsafe {
            libc::renameat(
                self.directory.as_raw_fd(),
                self.name.as_ptr(),
                self.directory.as_raw_fd(),
                c"info".as_ptr(),
            )
        } != 0
        {
            return Err(io::Error::last_os_error());
        }
        // No stage name remains. The caller pins this exact already-synced
        // file before its fallible directory sync and original-record checks.
        Ok(self.file.take().expect("same published record"))
    }
    fn check_prepared(&self) -> io::Result<()> {
        self.check_named()?;
        if self.file().metadata()?.len() != self.expected.len() as u64 {
            return Err(invalid("staged holder record length changed"));
        }
        let mut bytes = vec![0; self.expected.len()];
        self.file().read_exact_at(&mut bytes, 0)?;
        if bytes != self.expected {
            return Err(invalid("staged holder record bytes changed"));
        }
        self.check_named()
    }
}
impl Drop for StagedRecord<'_> {
    fn drop(&mut self) {
        if self.file.is_some() && self.check_named().is_ok() {
            // Best-effort cleanup ONLY of the same newly created stage. A
            // replaced/unknown name is retained, never recursively removed.
            unsafe { libc::unlinkat(self.directory.as_raw_fd(), self.name.as_ptr(), 0) };
        }
    }
}

fn check_original_description(held: &HeldRecord) -> io::Result<()> {
    use std::os::unix::fs::FileExt;
    let before = held.file.metadata()?;
    if !same_inode(&held.identity, Some(&held.directory.metadata()?))
        || !same_inode(&held.metadata, Some(&before))
        || before.len() != held.text.len() as u64
    {
        return Err(invalid("original acquisition descriptions changed"));
    }
    let mut bytes = vec![0; held.text.len()];
    held.file.read_exact_at(&mut bytes, 0)?;
    if bytes != held.text.as_bytes() || !same_inode(&held.metadata, Some(&held.file.metadata()?)) {
        return Err(invalid("original acquisition bytes changed"));
    }
    Ok(())
}

#[cfg(test)]
thread_local! {
    static FAIL_AFTER_REPLACE: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
    static FAIL_BEFORE_REPLACE: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

#[cfg(test)]
mod tests;

mod protected_scope;
pub use protected_scope::{
    JoinedChild, LaunchIdentity, LaunchRegistration, LocalJoinedScope, OriginalSourceOffer,
    OriginalSourceRoot, ProtectedWorkScope, ScopeDispatch, ScopeFailure, ScopeIdentity,
    ScopedCapture, ScopedChild, ScopedReader, ScopedThread, ScopedThreads, ScopedWorker,
    SealedWorkScope, SourceOfferData, WeakScopeDispatch, WorkerRegistration,
};

#[cfg(all(feature = "native-exec", target_os = "macos", target_arch = "aarch64"))]
mod maintenance;
#[cfg(all(feature = "native-exec", target_os = "macos", target_arch = "aarch64"))]
pub(crate) use maintenance::{
    Binding as MaintenanceBinding, MaintenanceLease, State as MaintenanceState,
};
#[cfg(feature = "resident-inputs")]
pub use protected_scope::{RefusedInputRetirement, RetiredResidentInputs};
