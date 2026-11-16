// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

//! Selected physical input custody, not source meaning or a reader completion.
//! The real source issuer must supply and retain its original opaque owner;
//! borrowed descriptors and equality expectations cannot construct that role.

use std::collections::BTreeMap;
use std::ffi::{CString, OsStr};
use std::fs::File;
use std::io;
use std::os::fd::{AsRawFd as _, BorrowedFd, FromRawFd as _};
use std::os::unix::ffi::OsStrExt as _;
use std::os::unix::fs::{FileExt as _, MetadataExt as _};
use std::path::{Component, Path, PathBuf};
use std::sync::atomic::{AtomicBool, Ordering};
use std::time::Instant;

const MAX_DESCRIPTORS: usize = 8192;
const MAX_BYTES: usize = 512 * 1024 * 1024;
const MAX_FILE_BYTES: usize = 16 * 1024 * 1024;
const MAX_PATH_BYTES: usize = 4096;
fn invalid(why: &'static str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, why)
}

mod file_offer;
#[cfg(test)]
mod tests;
pub use file_offer::{HeldSourceFileOffer, RefusedSourceFileOffer};
fn error(e: impl std::fmt::Display) -> io::Error {
    io::Error::other(e.to_string())
}
fn time(end: Instant) -> io::Result<()> {
    if Instant::now() >= end { Err(io::ErrorKind::TimedOut.into()) } else { Ok(()) }
}
fn selected_path(path: &Path) -> io::Result<()> {
    let mut normal = PathBuf::new();
    for part in path.components() {
        let Component::Normal(part) = part else {
            return Err(invalid("selected source requires a relative normal path"));
        };
        normal.push(part);
    }
    if normal.as_os_str().is_empty()
        || normal.as_os_str() != path.as_os_str()
        || path.as_os_str().as_bytes().len() > MAX_PATH_BYTES
        || path.as_os_str().as_bytes().contains(&0)
        || path.components().count() > 128
    {
        return Err(invalid("selected source path is empty, escaping or exceeds bound"));
    }
    Ok(())
}

/// DATA read from retained physical originals under exact equality
/// expectations; the source issuer separately authenticates those expectations. These values alone never construct a read-set or source owner.
#[derive(Clone, PartialEq, Eq)]
pub enum SourceRead {
    File { mode: u16, bytes: Vec<u8> },
    Link { target: Vec<u8> },
    Directory,
    Absent,
}

/// Literal no-follow directory-entry DATA, not source or glob authority.
#[derive(Clone, PartialEq, Eq)]
pub enum SourceEntryKind {
    File,
    Directory,
    Link,
    Other,
}
#[derive(Clone, PartialEq, Eq)]
pub struct SourceDirectoryEntry {
    pub name: Vec<u8>,
    pub kind: SourceEntryKind,
}

#[derive(PartialEq, Eq)]
struct Stamp {
    dev: u64,
    ino: u64,
    mode: u32,
    uid: u32,
    gid: u32,
    links: u64,
    size: u64,
    modified: (i64, i64),
    changed: (i64, i64),
}
impl Stamp {
    fn of(m: &std::fs::Metadata) -> Self {
        Self {
            dev: m.dev(),
            ino: m.ino(),
            mode: m.mode(),
            uid: m.uid(),
            gid: m.gid(),
            links: m.nlink(),
            size: m.len(),
            modified: (m.mtime(), m.mtime_nsec()),
            changed: (m.ctime(), m.ctime_nsec()),
        }
    }
}
struct Directory {
    file: File,
    stamp: Stamp,
}
enum Leaf {
    File { file: File, stamp: Stamp, bytes: Vec<u8>, mode: u16 },
    Link { stamp: Stamp, target: Vec<u8> },
    Absent,
}

/// Actual readonly physical input/ancestor custody under one borrowed root.
/// This is not source authentication, writer exclusion, selection completeness,
/// process admission, a private Seed or SDK. Retain the real owner separately.
pub struct HeldSourceReadSet {
    root: File,
    root_stamp: Stamp,
    directories: BTreeMap<PathBuf, Directory>,
    leaves: BTreeMap<PathBuf, Leaf>,
    listings: BTreeMap<PathBuf, Vec<SourceDirectoryEntry>>,
    bytes: usize,
    creator: u32,
    deadline: Instant,
    revoked: AtomicBool,
}

fn component(path: &Path) -> io::Result<CString> {
    CString::new(path.as_os_str().as_bytes()).map_err(error)
}
fn open(parent: BorrowedFd<'_>, name: &OsStr, directory: bool) -> io::Result<File> {
    let name = CString::new(name.as_bytes()).map_err(error)?;
    let flags = libc::O_RDONLY
        | libc::O_NOFOLLOW
        | libc::O_NONBLOCK
        | libc::O_CLOEXEC
        | if directory { libc::O_DIRECTORY } else { 0 };
    let fd = unsafe { libc::openat(parent.as_raw_fd(), name.as_ptr(), flags) };
    if fd < 0 {
        return Err(io::Error::last_os_error());
    }
    Ok(unsafe { File::from_raw_fd(fd) })
}
fn protected(file: &File, directory: bool) -> io::Result<Stamp> {
    let m = file.metadata()?;
    if m.is_dir() != directory
        || (!directory && (!m.is_file() || m.nlink() != 1))
        || m.uid() != unsafe { libc::geteuid() }
        || m.mode() & 0o022 != 0
    {
        return Err(invalid("selected source is not a protected original"));
    }
    crate::require_no_acl_grants(file)?;
    Ok(Stamp::of(&m))
}
fn bytes(file: &File, stamp: &Stamp, end: Instant) -> io::Result<Vec<u8>> {
    time(end)?;
    if Stamp::of(&file.metadata()?) != *stamp || stamp.size > MAX_FILE_BYTES as u64 {
        return Err(invalid("selected source changed or exceeds bound"));
    }
    let mut raw = vec![0; stamp.size as usize + 1];
    let mut at = 0;
    while at < raw.len() {
        time(end)?;
        match file.read_at(&mut raw[at..], at as u64) {
            Ok(0) => break,
            Ok(n) => at += n,
            Err(e) if e.kind() == io::ErrorKind::Interrupted => {}
            Err(e) => return Err(e),
        }
    }
    if at != stamp.size as usize || Stamp::of(&file.metadata()?) != *stamp {
        return Err(invalid("selected source changed during positional read"));
    }
    raw.truncate(at);
    time(end)?;
    Ok(raw)
}
fn link(parent: BorrowedFd<'_>, name: &OsStr, end: Instant) -> io::Result<(Stamp, Vec<u8>)> {
    time(end)?;
    let name = CString::new(name.as_bytes()).map_err(error)?;
    let stat = || -> io::Result<libc::stat> {
        let mut m = std::mem::MaybeUninit::uninit();
        if unsafe {
            libc::fstatat(
                parent.as_raw_fd(),
                name.as_ptr(),
                m.as_mut_ptr(),
                libc::AT_SYMLINK_NOFOLLOW,
            )
        } != 0
        {
            return Err(io::Error::last_os_error());
        }
        Ok(unsafe { m.assume_init() })
    };
    let before = stat()?;
    if before.st_mode & libc::S_IFMT != libc::S_IFLNK
        || before.st_uid != unsafe { libc::geteuid() }
        || before.st_nlink != 1
    {
        return Err(invalid("selected source literal link changed kind or owner"));
    }
    let mut target = vec![0u8; MAX_PATH_BYTES + 1];
    let n = unsafe {
        libc::readlinkat(
            parent.as_raw_fd(),
            name.as_ptr(),
            target.as_mut_ptr().cast(),
            target.len(),
        )
    };
    if n < 0 {
        return Err(io::Error::last_os_error());
    }
    let after = stat()?;
    if n as usize > MAX_PATH_BYTES
        || before.st_dev != after.st_dev
        || before.st_ino != after.st_ino
        || before.st_mode != after.st_mode
        || before.st_uid != after.st_uid
        || before.st_gid != after.st_gid
        || before.st_nlink != after.st_nlink
        || before.st_size != after.st_size
        || before.st_mtime != after.st_mtime
        || before.st_mtime_nsec != after.st_mtime_nsec
        || before.st_ctime != after.st_ctime
        || before.st_ctime_nsec != after.st_ctime_nsec
    {
        return Err(invalid("selected source literal link changed during read"));
    }
    target.truncate(n as usize);
    time(end)?;
    Ok((native_stamp(before), target))
}

#[allow(
    clippy::unnecessary_cast,
    clippy::useless_conversion,
    reason = "Trust: normalize the native stat ABI widths on macOS and Linux"
)]
fn native_stamp(m: libc::stat) -> Stamp {
    Stamp {
        dev: m.st_dev as u64,
        ino: m.st_ino as u64,
        mode: m.st_mode as u32,
        uid: m.st_uid,
        gid: m.st_gid,
        links: m.st_nlink as u64,
        size: m.st_size as u64,
        modified: (m.st_mtime.into(), m.st_mtime_nsec.into()),
        changed: (m.st_ctime.into(), m.st_ctime_nsec.into()),
    }
}

impl HeldSourceReadSet {
    /// Capture an actual initial listing, retaining its SAME directory and
    /// parents in this shared population. `.` selects only the original root.
    /// The native source issuer and unchanged glob evaluator separately judge
    /// membership meaning. Names/kinds and caller paths create no completion.
    pub fn directory_entries(
        &mut self,
        root: BorrowedFd<'_>,
        path: &Path,
    ) -> io::Result<Vec<SourceDirectoryEntry>> {
        let captured = (|| {
            self.check_current(root)?;
            if path != Path::new(".") {
                selected_path(path)?;
                self.parent(root, &path.join(".selected-listing"), 0)?;
            }
            let file =
                if path == Path::new(".") { &self.root } else { &self.directories[path].file };
            let actual = directory_entries(file, self.deadline)?;
            if let Some(original) = self.listings.get(path) {
                if original != &actual {
                    return Err(invalid("original source listing changed"));
                }
            } else {
                let additional = actual.iter().try_fold(0usize, |total, entry| {
                    total
                        .checked_add(entry.name.capacity() + 128)
                        .ok_or_else(|| invalid("source listing byte accounting overflow"))
                })?;
                self.bytes = self
                    .bytes
                    .checked_add(additional)
                    .filter(|total| *total <= MAX_BYTES)
                    .ok_or_else(|| invalid("source listing retained bytes exceed bound"))?;
                self.listings.insert(path.to_owned(), actual.clone());
            }
            self.check_current(root)?;
            Ok(actual)
        })();
        if captured.is_err() {
            self.revoked.store(true, Ordering::Release);
        }
        captured
    }
    pub const fn original_deadline(&self) -> Instant {
        self.deadline
    }

    /// Count DATA only, never native descriptor admission or semantic coverage.
    pub fn selected_population(&self) -> usize {
        self.directories.len() + self.leaves.len() + 1
    }

    /// One bounded physical capture batch with complete original bookends.
    /// No caller-selected callback, recipe evaluation or success role occurs.
    /// Failure retains the same already captured originals and is terminal.
    pub fn observe_batch(
        &mut self,
        root: BorrowedFd<'_>,
        selected: &[(PathBuf, SourceRead)],
    ) -> io::Result<Vec<SourceRead>> {
        let result = (|| {
            if selected.len() > MAX_DESCRIPTORS {
                return Err(invalid("selected source batch exceeds bound"));
            }
            self.check_current(root)?;
            let mut observed = Vec::with_capacity(selected.len());
            for (path, expected) in selected {
                selected_path(path)?;
                observed.push(self.observe_inner(root, path, expected.clone())?);
            }
            self.check_current(root)?;
            Ok(observed)
        })();
        if result.is_err() {
            self.revoked.store(true, Ordering::Release);
        }
        result
    }

    pub fn capture(root: BorrowedFd<'_>, deadline: Instant) -> io::Result<Self> {
        time(deadline)?;
        let flags = unsafe { libc::fcntl(root.as_raw_fd(), libc::F_GETFL) };
        if flags < 0 {
            return Err(io::Error::last_os_error());
        }
        if flags & libc::O_ACCMODE != libc::O_RDONLY {
            return Err(invalid("selected source root is not readonly"));
        }
        let root = File::from(root.try_clone_to_owned()?);
        let root_stamp = protected(&root, true)?;
        Ok(Self {
            root,
            root_stamp,
            directories: BTreeMap::new(),
            leaves: BTreeMap::new(),
            listings: BTreeMap::new(),
            bytes: 0,
            creator: std::process::id(),
            deadline,
            revoked: AtomicBool::new(false),
        })
    }
    fn room(&self, additional: usize) -> io::Result<()> {
        if self
            .directories
            .len()
            .saturating_add(self.leaves.len())
            .saturating_add(additional)
            .saturating_add(1)
            > MAX_DESCRIPTORS
        {
            return Err(invalid("selected source descriptor population exceeds bound"));
        }
        Ok(())
    }
    fn parent<'a>(
        &'a mut self,
        root: BorrowedFd<'a>,
        relative: &Path,
        pending_leaf: usize,
    ) -> io::Result<BorrowedFd<'a>> {
        use std::os::fd::AsFd as _;
        let parent = relative.parent().unwrap();
        let mut current = PathBuf::new();
        for part in parent.components() {
            current.push(part);
            if !self.directories.contains_key(&current) {
                // Reserve the still-pending leaf while every new parent is
                // acquired. An ancestor cannot consume its final slot.
                self.room(1 + pending_leaf)?;
                let previous = current.parent().unwrap();
                let fd = if previous.as_os_str().is_empty() {
                    root
                } else {
                    self.directories[previous].file.as_fd()
                };
                let file = open(fd, current.file_name().unwrap(), true)?;
                let stamp = protected(&file, true)?;
                self.directories.insert(current.clone(), Directory { file, stamp });
            }
        }
        Ok(if parent.as_os_str().is_empty() { root } else { self.directories[parent].file.as_fd() })
    }
    /// Retain actual readonly physical originals. Expectations restrict these
    /// bytes only; they authenticate no source, selection, Seed or SDK role.
    pub fn observe(
        &mut self,
        root: BorrowedFd<'_>,
        path: &Path,
        expected: SourceRead,
    ) -> io::Result<SourceRead> {
        let result = (|| {
            selected_path(path)?;
            self.check_current(root)?;
            let value = self.observe_inner(root, path, expected)?;
            self.check_current(root)?;
            Ok(value)
        })();
        if result.is_err() {
            self.revoked.store(true, Ordering::Release);
        }
        result
    }
    fn observe_inner(
        &mut self,
        root: BorrowedFd<'_>,
        path: &Path,
        expected: SourceRead,
    ) -> io::Result<SourceRead> {
        time(self.deadline)?;
        if self.leaves.contains_key(path) {
            let current = self.read(root, path)?;
            if current != expected {
                return Err(invalid("selected source observation changed kind or bytes"));
            }
            return Ok(current);
        }
        self.room(1)?;
        let end = self.deadline;
        let leaf = match &expected {
            SourceRead::File { mode, bytes: wanted } => {
                if self.bytes.checked_add(wanted.len()).is_none_or(|n| n > MAX_BYTES) {
                    return Err(invalid("selected source retained bytes exceed bound"));
                }
                let parent = self.parent(root, path, 1)?;
                let file = open(parent, path.file_name().unwrap(), false)?;
                let stamp = protected(&file, false)?;
                if stamp.mode & 0o7777 != u32::from(*mode & 0o777)
                    || bytes(&file, &stamp, end)? != *wanted
                {
                    return Err(invalid(
                        "physical selected source differs from committed blob/mode",
                    ));
                }
                Leaf::File { file, stamp, bytes: wanted.clone(), mode: *mode }
            }
            SourceRead::Link { target } => {
                let (stamp, actual) =
                    link(self.parent(root, path, 1)?, path.file_name().unwrap(), end)?;
                if &actual != target {
                    return Err(invalid("physical source link differs from committed literal"));
                }
                Leaf::Link { stamp, target: target.clone() }
            }
            SourceRead::Directory => {
                // Include the selected directory itself, not merely ancestors:
                // subsequent additions/removals must invalidate glob inputs.
                self.parent(root, &path.join(".selected-membership"), 0)?;
                return Ok(SourceRead::Directory);
            }
            SourceRead::Absent => {
                // Anchor the FIRST missing component. A missing .cargo/config
                // cannot become TRUE merely because its .cargo parent was not
                // retained. Existing parents are all held before returning.
                let mut prefix = PathBuf::new();
                for part in path.components() {
                    prefix.push(part);
                    let parent = self.parent(root, &prefix, 1)?;
                    match open(parent, prefix.file_name().unwrap(), true) {
                        Ok(_) if prefix == path => {
                            return Err(invalid("uncommitted source input is physically present"));
                        }
                        Ok(_) => {}
                        Err(e) if e.kind() == io::ErrorKind::NotFound => {
                            self.leaves.insert(prefix, Leaf::Absent);
                            return Ok(SourceRead::Absent);
                        }
                        Err(e) => return Err(e),
                    }
                }
                return Err(invalid("negative selected source has no missing component"));
            }
        };
        if let Leaf::File { bytes, .. } = &leaf {
            self.bytes += bytes.len();
        }
        self.leaves.insert(path.into(), leaf);
        let actual = self.read(root, path)?;
        if actual != expected {
            return Err(invalid("selected source changed after capture"));
        }
        Ok(actual)
    }
    fn read(&self, root: BorrowedFd<'_>, path: &Path) -> io::Result<SourceRead> {
        use std::os::fd::AsFd as _;
        let parent = path.parent().unwrap();
        let parent = if parent.as_os_str().is_empty() {
            root
        } else {
            self.directories[parent].file.as_fd()
        };
        match &self.leaves[path] {
            Leaf::File { file, stamp, bytes: original, mode } => {
                let named = open(parent, path.file_name().unwrap(), false)?;
                if protected(&named, false)? != *stamp
                    || bytes(file, stamp, self.deadline)? != *original
                {
                    return Err(invalid("original selected source file changed"));
                }
                Ok(SourceRead::File { mode: *mode, bytes: original.clone() })
            }
            Leaf::Link { stamp, target } => {
                let (current, literal) = link(parent, path.file_name().unwrap(), self.deadline)?;
                if current != *stamp || literal != *target {
                    return Err(invalid("original selected source link changed"));
                }
                Ok(SourceRead::Link { target: target.clone() })
            }
            Leaf::Absent => {
                let name = component(path.file_name().unwrap().as_ref())?;
                let mut m = std::mem::MaybeUninit::<libc::stat>::uninit();
                let rc = unsafe {
                    libc::fstatat(
                        parent.as_raw_fd(),
                        name.as_ptr(),
                        m.as_mut_ptr(),
                        libc::AT_SYMLINK_NOFOLLOW,
                    )
                };
                if rc == 0 {
                    return Err(invalid("original absent source input appeared"));
                }
                let e = io::Error::last_os_error();
                if e.kind() != io::ErrorKind::NotFound {
                    return Err(e);
                }
                Ok(SourceRead::Absent)
            }
        }
    }
    fn check_directories(&self, root: BorrowedFd<'_>) -> io::Result<()> {
        use std::os::fd::AsFd as _;
        if protected(&self.root, true)? != self.root_stamp {
            return Err(invalid("selected source original root changed"));
        }
        let current = File::from(root.try_clone_to_owned()?);
        if protected(&current, true)? != self.root_stamp {
            return Err(invalid("selected source root was substituted"));
        }
        for (path, directory) in &self.directories {
            time(self.deadline)?;
            let parent = path.parent().unwrap();
            let parent = if parent.as_os_str().is_empty() {
                root
            } else {
                self.directories[parent].file.as_fd()
            };
            let named = open(parent, path.file_name().unwrap(), true)?;
            if protected(&directory.file, true)? != directory.stamp
                || protected(&named, true)? != directory.stamp
            {
                return Err(invalid("original selected source ancestor or membership changed"));
            }
        }
        Ok(())
    }
    pub fn check_current(&self, root: BorrowedFd<'_>) -> io::Result<()> {
        if self.creator != std::process::id() || self.revoked.load(Ordering::Acquire) {
            return Err(invalid("selected source read-set is foreign or quarantined"));
        }
        let result = (|| {
            time(self.deadline)?;
            self.room(0)?;
            self.check_directories(root)?;
            for path in self.leaves.keys() {
                self.read(root, path)?;
            }
            for (path, original) in &self.listings {
                let file =
                    if path == Path::new(".") { &self.root } else { &self.directories[path].file };
                if directory_entries(file, self.deadline)? != *original {
                    return Err(invalid("original selected directory names or kinds changed"));
                }
            }
            self.check_directories(root)?;
            time(self.deadline)
        })();
        if result.is_err() {
            self.revoked.store(true, Ordering::Release);
        }
        result
    }
}

fn directory_entries(file: &File, end: Instant) -> io::Result<Vec<SourceDirectoryEntry>> {
    time(end)?;
    let before = protected(file, true)?;
    // Reuse the shared descriptor-relative scratch listing: no original
    // cursor/flags are changed and no symlink is followed or name omitted.
    let names = super::target_sysroot::names(file, end)?;
    let mut entries = Vec::with_capacity(names.len());
    for name in names {
        time(end)?;
        let literal = CString::new(name.as_bytes()).map_err(error)?;
        let mut meta = std::mem::MaybeUninit::<libc::stat>::uninit();
        if unsafe {
            libc::fstatat(
                file.as_raw_fd(),
                literal.as_ptr(),
                meta.as_mut_ptr(),
                libc::AT_SYMLINK_NOFOLLOW,
            )
        } != 0
        {
            return Err(io::Error::last_os_error());
        }
        let kind = match unsafe { meta.assume_init() }.st_mode & libc::S_IFMT {
            libc::S_IFREG => SourceEntryKind::File,
            libc::S_IFDIR => SourceEntryKind::Directory,
            libc::S_IFLNK => SourceEntryKind::Link,
            _ => SourceEntryKind::Other,
        };
        entries.push(SourceDirectoryEntry { name: name.as_bytes().to_vec(), kind });
    }
    if protected(file, true)? != before {
        return Err(invalid("selected source directory changed during listing"));
    }
    time(end)?;
    Ok(entries)
}
