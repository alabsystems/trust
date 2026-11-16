// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

//! Passive local committed-source observations shared by native consumers.
//! The original descriptor, exact lexical root and original endpoint are kept;
//! rows/hashes/JSON never construct source, Graph, native, Seed or SDK authority.
//! The caller retains its semantic owner and joins physical reads independently.
//!
//! This separate crate is consumed by Bootstrap and native preparation hosts.
//! It must stay outside the native OpenSSL cache's dependency reach: enabling
//! Git transport in a higher consumer must not create a provenance/TLS cycle.
//! Bootstrap's original Graph/source wrapper remains its semantic owner.

#![cfg(unix)]

use std::fs::{File, OpenOptions};
use std::io;
use std::os::fd::{AsFd as _, BorrowedFd};
use std::os::unix::ffi::OsStrExt as _;
use std::os::unix::fs::{MetadataExt as _, OpenOptionsExt as _};
use std::path::Path;
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};
use std::time::Instant;

fn time(deadline: Instant) -> io::Result<()> {
    if Instant::now() >= deadline {
        return Err(io::Error::new(io::ErrorKind::TimedOut, "committed source deadline expired"));
    }
    Ok(())
}

const MAX_COMMIT_BYTES: u64 = 1024 * 1024;
// Enforce this before ordinary loose/packed object decoding, including delta
// bases. A small selected header is not an allocation bound for its bases.
pub const MAX_OBJECT_ALLOC_BYTES: usize = 16 * 1024 * 1024;
fn invalid(why: &'static str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, why)
}
fn error(error: impl std::fmt::Display) -> io::Error {
    io::Error::other(error.to_string())
}
type DirectoryStamp = (u64, u64, u32, u32, u32, u64, i64, i64);
fn stamp(file: &File) -> io::Result<DirectoryStamp> {
    let m = file.metadata()?;
    if !m.is_dir() {
        return Err(invalid("native Git source is not a directory"));
    }
    Ok((m.dev(), m.ino(), m.mode(), m.uid(), m.gid(), m.nlink(), m.ctime(), m.ctime_nsec()))
}
fn source_dir(path: &Path) -> io::Result<File> {
    OpenOptions::new()
        .read(true)
        .custom_flags(libc::O_DIRECTORY | libc::O_NOFOLLOW | libc::O_CLOEXEC)
        .open(path)
}
/// Open only isolated local Git metadata with a decoder allocation limit,
/// including delta bases. This raw DATA reader grants no original-source role.
pub fn open_repository(path: &Path) -> io::Result<gix::Repository> {
    let options = gix::open::Options::isolated()
        .config_overrides([format!("gitoxide.objects.allocLimit={MAX_OBJECT_ALLOC_BYTES}")]);
    gix::open_opts(path, options).map_err(error)
}
const MAX_ENTRIES: usize = 1_000_000;
const MAX_TREE_BYTES: u64 = MAX_OBJECT_ALLOC_BYTES as u64;
const MAX_RETAINED_BYTES: usize = 256 * 1024 * 1024;
const MAX_PATH_BYTES: usize = 4096;
const MAX_DEPTH: usize = 128;

/// Immutable Git DATA only, including directory and unresolved gitlink rows.
/// A row is not an actual physical source, source owner or negative lookup.
pub struct CommittedEntry {
    pub path: Vec<u8>,
    pub mode: u16,
    pub object: gix::ObjectId,
}

/// Lookup DATA in the authenticated repository tree. Missing descendants of
/// links/gitlinks are UNKNOWN until their original boundaries are resolved.
pub enum CommittedLookup<'a> {
    Present(&'a CommittedEntry),
    Absent,
    Unresolved(&'a CommittedEntry),
}
fn lookup_entries<'a>(
    entries: &'a [CommittedEntry],
    path: &[u8],
) -> io::Result<CommittedLookup<'a>> {
    if path.is_empty()
        || path.len() > MAX_PATH_BYTES
        || path.contains(&0)
        || path
            .split(|byte| *byte == b'/')
            .any(|part| part.is_empty() || matches!(part, b"." | b".."))
    {
        return Err(invalid("committed source lookup is not a relative byte path"));
    }
    let find = |path: &[u8]| {
        entries
            .binary_search_by(|entry| entry.path.as_slice().cmp(path))
            .ok()
            .map(|at| &entries[at])
    };
    if let Some(entry) = find(path) {
        return Ok(CommittedLookup::Present(entry));
    }
    for (at, byte) in path.iter().enumerate() {
        if *byte == b'/'
            && let Some(entry) = find(&path[..at])
            && matches!(entry.mode, 0o120000 | 0o160000)
        {
            return Ok(CommittedLookup::Unresolved(entry));
        }
    }
    Ok(CommittedLookup::Absent)
}

/// Passive, bounded observation of actual Git storage beside a retained original
/// directory description. This is DATA, not a Graph/source, native, Seed or SDK
/// owner. There is no constructor from caller rows, digests or saved packets.
pub struct CommittedRepositoryObservation {
    directory: File,
    directory_stamp: DirectoryStamp,
    root: std::path::PathBuf,
    head: gix::ObjectId,
    entries: Vec<CommittedEntry>,
    deadline: Instant,
    creator: u32,
    revoked: AtomicBool,
    // An explicitly expanded gitlink retains its exact original parent.
    parent: Option<Arc<CommittedRepositoryObservation>>,
    submodule_depth: usize,
}
impl CommittedRepositoryObservation {
    /// Capture only against this actual already-held directory description and
    /// canonical lexical root. The clone retains the SAME open file description;
    /// it does not reopen a path or change the caller's cursor/status flags.
    pub fn capture(directory: BorrowedFd<'_>, root: &Path, deadline: Instant) -> io::Result<Self> {
        time(deadline)?;
        let directory = File::from(directory.try_clone_to_owned()?);
        read_repository(directory, root, deadline)
    }

    /// Original DATA only. Currentness requires a successful bounded check.
    pub fn root(&self) -> &Path {
        &self.root
    }

    /// The retained original endpoint. It cannot be replaced or extended.
    pub fn original_deadline(&self) -> Instant {
        self.deadline
    }

    /// Original DATA only; this does not establish current source ownership.
    pub fn commit(&self) -> gix::ObjectId {
        self.head
    }

    /// Revalidate this SAME descriptor, root and HEAD under the original end.
    /// A failed observation permanently quarantines this passive observation.
    pub fn check(&self, deadline: Instant) -> io::Result<()> {
        let result = (|| {
            if self.creator != std::process::id()
                || self.revoked.load(Ordering::Acquire)
                || deadline > self.deadline
            {
                return Err(invalid("committed source has another process or extended deadline"));
            }
            time(deadline)?;
            if let Some(parent) = &self.parent {
                parent.check(deadline)?;
            }
            if self.root.canonicalize()?.as_os_str() != self.root.as_os_str()
                || stamp(&self.directory)? != self.directory_stamp
                || stamp(&source_dir(&self.root)?)? != self.directory_stamp
            {
                return Err(invalid("committed source directory changed"));
            }
            let repo = open_repository(&self.root)?;
            if repo.workdir() != Some(self.root.as_path())
                || repo.head_id().map_err(error)?.detach() != self.head
            {
                return Err(invalid("committed source HEAD changed or became unreadable"));
            }
            time(deadline)
        })();
        if result.is_err() {
            self.revoked.store(true, Ordering::Release);
        }
        result
    }

    pub fn entries(&self, deadline: Instant) -> io::Result<&[CommittedEntry]> {
        self.check(deadline)?;
        Ok(&self.entries)
    }

    pub fn lookup(&self, path: &[u8], deadline: Instant) -> io::Result<CommittedLookup<'_>> {
        let result = (|| lookup_entries(self.entries(deadline)?, path))();
        if result.is_err() {
            self.revoked.store(true, Ordering::Release);
        }
        result
    }

    /// Expand ONLY an exact original parent gitlink into its actual local
    /// repository. Missing/changed children refuse; no network or parent
    /// discovery can replace them. The child retains this SAME parent.
    pub fn submodule(self: &Arc<Self>, relative: &[u8], deadline: Instant) -> io::Result<Self> {
        let result = (|| {
            self.check(deadline)?;
            if self.submodule_depth >= 64 {
                return Err(invalid("original committed submodule depth exceeds bound"));
            }
            let CommittedLookup::Present(entry) = self.lookup(relative, deadline)? else {
                return Err(invalid("submodule is not an exact committed entry"));
            };
            if entry.mode != 0o160000 {
                return Err(invalid("submodule cannot reinterpret a file, directory or link"));
            }
            let expected = entry.object;
            let path = self.root.join(std::ffi::OsStr::from_bytes(relative));
            let directory = source_dir(&path)?;
            let mut child = Self::capture(directory.as_fd(), &path, deadline)?;
            if child.head != expected {
                return Err(invalid("submodule HEAD differs from its original parent gitlink"));
            }
            child.parent = Some(Arc::clone(self));
            child.submodule_depth = self.submodule_depth + 1;
            self.check(deadline)?;
            child.check(deadline)?;
            Ok(child)
        })();
        if result.is_err() {
            self.revoked.store(true, Ordering::Release);
        }
        result
    }

    /// Read actual bounded blob storage and recheck its kind, length and SHA1.
    /// Callers must still join these expected DATA to their physical read guard.
    pub fn blob(&self, object: gix::ObjectId, deadline: Instant) -> io::Result<Vec<u8>> {
        let result = committed_blob(self, object, deadline);
        if result.is_err() {
            self.revoked.store(true, Ordering::Release);
        }
        result
    }
}

fn read_repository(
    directory: File,
    root: &Path,
    deadline: Instant,
) -> io::Result<CommittedRepositoryObservation> {
    time(deadline)?;
    // A required exact source root cannot discover a parent's repository or
    // fall back to an absent component, saved identity, network or Git child.
    std::fs::symlink_metadata(root.join(".git"))?;
    if root.canonicalize()?.as_os_str() != root.as_os_str() {
        return Err(invalid("committed source root is not canonical"));
    }
    let directory_stamp = stamp(&directory)?;
    if stamp(&source_dir(root)?)? != directory_stamp {
        return Err(invalid("committed source descriptor differs from selected root"));
    }
    let repo = open_repository(root)?;
    if repo.workdir() != Some(root) {
        return Err(invalid("committed source Git root differs"));
    }
    let head = repo.head_id().map_err(error)?.detach();
    if head.to_string().len() != 40 {
        return Err(invalid("committed source hash format unsupported"));
    }
    let header = repo.find_header(head).map_err(error)?;
    if header.kind() != gix::objs::Kind::Commit || header.size() > MAX_COMMIT_BYTES {
        return Err(invalid("committed source HEAD is not a bounded commit"));
    }
    let commit = repo.find_commit(head).map_err(error)?;
    if commit.data.len() as u64 > MAX_COMMIT_BYTES
        || gix::objs::compute_hash(head.kind(), gix::objs::Kind::Commit, &commit.data)
            .map_err(error)?
            != head
    {
        return Err(invalid("committed source commit hash differs"));
    }
    let mut pending = vec![(Vec::<u8>::new(), commit.tree_id().map_err(error)?.detach(), 0usize)];
    let mut entries = Vec::new();
    let mut retained = 0usize;
    while let Some((prefix, object, depth)) = pending.pop() {
        time(deadline)?;
        if depth > MAX_DEPTH {
            return Err(invalid("committed source tree depth exceeds bound"));
        }
        // Repository::find_header/find_tree and FindExt::find_tree synthesize
        // the canonical empty tree. This physical-input profile requires the
        // actual ordinary ODB read even for that known object ID.
        let header = gix::odb::Header::try_header(&repo.objects, &object)
            .map_err(error)?
            .ok_or_else(|| invalid("required committed source tree is absent"))?;
        if header.kind() != gix::objs::Kind::Tree || header.size() > MAX_TREE_BYTES {
            return Err(invalid("committed source tree is absent, wrong-kind or exceeds bound"));
        }
        let mut bytes = Vec::new();
        let tree = gix::objs::Find::try_find(&repo.objects, &object, &mut bytes)
            .map_err(error)?
            .ok_or_else(|| invalid("required committed source tree became absent"))?;
        if tree.kind != gix::objs::Kind::Tree
            || tree.data.len() as u64 != header.size()
            || tree.data.len() as u64 > MAX_TREE_BYTES
            || gix::objs::compute_hash(object.kind(), gix::objs::Kind::Tree, tree.data)
                .map_err(error)?
                != object
        {
            return Err(invalid("committed source tree hash differs"));
        }
        for entry in
            gix::objs::TreeRef::from_bytes(tree.data, object.kind()).map_err(error)?.entries
        {
            time(deadline)?;
            let name: &[u8] = entry.filename.as_ref();
            let mode = entry.mode.value();
            if name.is_empty()
                || matches!(name, b"." | b"..")
                || name.contains(&b'/')
                || name.contains(&0)
                || !matches!(mode, 0o040000 | 0o100644 | 0o100755 | 0o120000 | 0o160000)
            {
                return Err(invalid("committed source contains an unsupported tree entry"));
            }
            let mut path = prefix.clone();
            if !path.is_empty() {
                path.push(b'/');
            }
            path.extend_from_slice(name);
            retained = retained
                .checked_add(path.capacity().saturating_mul(2).saturating_add(256))
                .ok_or_else(|| invalid("committed source row accounting overflow"))?;
            if entries.len() >= MAX_ENTRIES
                || path.len() > MAX_PATH_BYTES
                || retained > MAX_RETAINED_BYTES
            {
                return Err(invalid("committed source row population exceeds bound"));
            }
            let object = entry.oid.to_owned();
            if mode == 0o040000 {
                pending.push((path.clone(), object, depth + 1));
            }
            // No blob is read or a gitlink followed implicitly. Their exact
            // object IDs bind later physical byte/link checks or explicit
            // native child-repository expansion; missing is never inferred.
            entries.push(CommittedEntry { path, mode, object });
        }
    }
    entries.sort_unstable_by(|left, right| left.path.cmp(&right.path));
    if entries.windows(2).any(|pair| pair[0].path == pair[1].path) {
        return Err(invalid("committed source has repeated tree paths"));
    }
    let observed = CommittedRepositoryObservation {
        directory,
        directory_stamp,
        root: root.to_owned(),
        head,
        entries,
        deadline,
        creator: std::process::id(),
        revoked: AtomicBool::new(false),
        parent: None,
        submodule_depth: 0,
    };
    observed.check(deadline)?;
    Ok(observed)
}

fn committed_blob(
    rows: &CommittedRepositoryObservation,
    object: gix::ObjectId,
    end: Instant,
) -> io::Result<Vec<u8>> {
    rows.check(end)?;
    let repo = open_repository(&rows.root)?;
    let header = gix::odb::Header::try_header(&repo.objects, &object)
        .map_err(error)?
        .ok_or_else(|| invalid("required selected source blob is absent"))?;
    if header.kind() != gix::objs::Kind::Blob || header.size() > MAX_OBJECT_ALLOC_BYTES as u64 {
        return Err(invalid("selected source blob has wrong kind or exceeds bound"));
    }
    let mut buffer = Vec::new();
    let data = gix::objs::Find::try_find(&repo.objects, &object, &mut buffer)
        .map_err(error)?
        .ok_or_else(|| invalid("required selected source blob became absent"))?;
    if data.kind != gix::objs::Kind::Blob
        || data.data.len() as u64 != header.size()
        || gix::objs::compute_hash(object.kind(), gix::objs::Kind::Blob, data.data)
            .map_err(error)?
            != object
    {
        return Err(invalid("selected source blob hash differs"));
    }
    let result = data.data.to_vec();
    rows.check(end)?;
    Ok(result)
}

mod dependency_snapshot;
pub use dependency_snapshot::{
    CommittedDependencyRefusal, CommittedDependencySnapshot, check_committed_reads,
    encode_dependency_packet,
};
