//! Trust: native, transient cache locks and namespace bookends for source DATA.
//! No saved record can reconstruct these original handles. Unsupported locking
//! and changed/unreadable identities refuse; no best-effort lock fallback.
//! Mutation paths additionally require the original private namespace and ACL policy.

use crate::util::CargoResult;
use anyhow::{Context as _, bail, ensure};
use rustix::fs::{AtFlags, Mode, OFlags};
use std::cell::Cell;
use std::collections::BTreeMap;
use std::ffi::{OsStr, OsString};
use std::fs::{File, Metadata, OpenOptions};
use std::io::{Read as _, Seek as _, Write as _};
use std::os::fd::AsRawFd as _;
use std::os::unix::ffi::OsStringExt as _;
use std::os::unix::fs::{MetadataExt as _, OpenOptionsExt as _};
use std::path::{Path, PathBuf};

const MAX_ENTRIES: usize = 100_000;
const LOCKS: [&str; 2] = [".package-cache-mutate", ".package-cache"];

pub(super) mod snapshot;
mod view;
pub(super) use view::OwnedView;
mod recovery;
pub(in crate::sources::git) use recovery::recover_missing_database;

/// Per-invocation limit on fallback stream bytes, shared across every view.
/// This is neither allocated-space accounting nor a storage reservation.
pub(super) struct CopyBudget {
    remaining: u64,
}
impl CopyBudget {
    pub(super) fn new(limit: u64) -> CargoResult<Self> {
        ensure!(
            limit <= super::MAX_TOTAL_BYTES,
            "stream-copy budget exceeds 32 GiB"
        );
        Ok(Self { remaining: limit })
    }
    fn reserve(&mut self, bytes: u64) -> CargoResult<()> {
        self.remaining = self
            .remaining
            .checked_sub(bytes)
            .context("source object stream-copy budget exceeded")?;
        Ok(())
    }
}

#[derive(Default)]
pub(super) struct Materialized {
    pub(super) bytes: u64,
    pub(super) cloned_files: u64,
    pub(super) cloned_bytes: u64,
    pub(super) streamed_bytes: u64,
}

fn stamp(a: &Metadata, b: &Metadata) -> bool {
    a.dev() == b.dev()
        && a.ino() == b.ino()
        && a.uid() == b.uid()
        && a.gid() == b.gid()
        && a.mode() == b.mode()
        && a.nlink() == b.nlink()
        && a.len() == b.len()
        && a.mtime() == b.mtime()
        && a.mtime_nsec() == b.mtime_nsec()
        && a.ctime() == b.ctime()
        && a.ctime_nsec() == b.ctime_nsec()
}

struct Directory {
    path: PathBuf,
    file: File,
    before: Metadata,
}

impl Directory {
    fn open(path: &Path) -> CargoResult<Self> {
        let file = OpenOptions::new()
            .read(true)
            .custom_flags(libc::O_DIRECTORY | libc::O_NOFOLLOW | libc::O_NONBLOCK | libc::O_CLOEXEC)
            .open(path)?;
        let before = file.metadata()?;
        let named = std::fs::symlink_metadata(path)?;
        ensure!(
            before.is_dir() && stamp(&before, &named),
            "source directory identity changed"
        );
        Ok(Self {
            path: path.to_owned(),
            file,
            before,
        })
    }

    fn child(&self, name: &OsStr) -> CargoResult<Self> {
        let file = File::from(rustix::fs::openat(
            &self.file,
            name,
            OFlags::RDONLY
                | OFlags::DIRECTORY
                | OFlags::NOFOLLOW
                | OFlags::NONBLOCK
                | OFlags::CLOEXEC,
            Mode::empty(),
        )?);
        let before = file.metadata()?;
        Ok(Self {
            path: self.path.join(name),
            file,
            before,
        })
    }

    fn create_child(&self, name: &OsStr) -> CargoResult<Self> {
        self.private_current()?;
        rustix::fs::mkdirat(&self.file, name, Mode::from_bits_truncate(0o700))?;
        let child = self.child(name)?;
        child.private_current()?;
        Ok(child)
    }

    fn private_current(&self) -> CargoResult<()> {
        self.same_identity()?;
        let metadata = self.file.metadata()?;
        // SAFETY: reads only this process's effective account.
        ensure!(
            metadata.uid() == unsafe { libc::geteuid() } && metadata.mode() & 0o7077 == 0,
            "source-data mutation requires an owner-private directory"
        );
        trust_resource_provenance::require_no_acl_grants(&self.file)?;
        self.same_identity()
    }

    fn names(&self) -> CargoResult<Vec<OsString>> {
        let mut names = Vec::new();
        for entry in rustix::fs::Dir::read_from(&self.file)? {
            let entry = entry?;
            let name = entry.file_name().to_bytes();
            if name == b"." || name == b".." {
                continue;
            }
            ensure!(
                names.len() < MAX_ENTRIES,
                "source directory entry bound exceeded"
            );
            names.push(OsString::from_vec(name.to_vec()));
        }
        Ok(names)
    }

    fn missing_relative(&self, relative: &Path) -> CargoResult<bool> {
        let mut file = self.file.try_clone()?;
        let parts = relative.components().collect::<Vec<_>>();
        for (index, part) in parts.iter().enumerate() {
            let std::path::Component::Normal(name) = part else {
                bail!("noncanonical source control name");
            };
            if index + 1 == parts.len() {
                return match rustix::fs::statat(&file, *name, AtFlags::SYMLINK_NOFOLLOW) {
                    Err(rustix::io::Errno::NOENT) => Ok(true),
                    Err(error) => Err(error.into()),
                    Ok(_) => Ok(false),
                };
            }
            file = match rustix::fs::openat(
                &file,
                *name,
                OFlags::RDONLY
                    | OFlags::DIRECTORY
                    | OFlags::NOFOLLOW
                    | OFlags::NONBLOCK
                    | OFlags::CLOEXEC,
                Mode::empty(),
            ) {
                Ok(file) => File::from(file),
                Err(rustix::io::Errno::NOENT) => return Ok(true),
                Err(error) => return Err(error.into()),
            };
        }
        bail!("empty source control name")
    }

    fn current(&self) -> CargoResult<()> {
        ensure!(
            stamp(&self.before, &self.file.metadata()?)
                && stamp(&self.before, &std::fs::symlink_metadata(&self.path)?),
            "original source directory changed: {}",
            self.path.display()
        );
        Ok(())
    }

    fn same_identity(&self) -> CargoResult<()> {
        let named = std::fs::symlink_metadata(&self.path)?;
        let held = self.file.metadata()?;
        ensure!(
            named.is_dir() && named.dev() == held.dev() && named.ino() == held.ino(),
            "original cache directory was replaced"
        );
        Ok(())
    }
}

pub(super) struct Cache {
    home: Directory,
    locks: Vec<(File, Metadata)>,
    process: u32,
}

impl Cache {
    pub(super) fn source(path: &Path) -> CargoResult<Self> {
        Self::acquire(path, false)
    }

    fn acquire(path: &Path, create: bool) -> CargoResult<Self> {
        ensure!(
            path.is_absolute() && path.canonicalize()? == path,
            "cache input must be an absolute canonical directory"
        );
        Self::acquire_home(Directory::open(path)?, create)
    }

    fn acquire_home(home: Directory, create: bool) -> CargoResult<Self> {
        let uid = unsafe { libc::geteuid() };
        ensure!(
            home.before.uid() == uid && home.before.mode() & 0o022 == 0,
            "cache input is not an owner-controlled directory"
        );
        trust_resource_provenance::require_no_acl_grants(&home.file)?;
        require_local_filesystem(&home.file)?;
        let mut result = Self {
            home,
            locks: Vec::new(),
            process: std::process::id(),
        };
        // Match Cargo's ordering: mutate first, then download. The shared mutate
        // excludes GC; exclusive download also excludes concurrent append work.
        for (index, name) in LOCKS.iter().enumerate() {
            let mut flags = OFlags::RDWR | OFlags::NOFOLLOW | OFlags::NONBLOCK | OFlags::CLOEXEC;
            if create {
                flags |= OFlags::CREATE | OFlags::EXCL;
            }
            let file = File::from(rustix::fs::openat(
                &result.home.file,
                *name,
                flags,
                Mode::from_bits_truncate(0o600),
            )?);
            let before = file.metadata()?;
            ensure!(
                before.is_file()
                    && before.nlink() == 1
                    && before.uid() == uid
                    && before.mode() & 0o022 == 0,
                "unsafe source-cache lock"
            );
            trust_resource_provenance::require_no_acl_grants(&file)?;
            let locked = if index == 0 && !create {
                crate::util::flock::try_lock_shared(&file)
            } else {
                crate::util::flock::try_lock_exclusive(&file)
            };
            locked.map_err(|error| {
                anyhow::anyhow!("strict source-cache lock unavailable: {error}")
            })?;
            result.locks.push((file, before));
        }
        result.check_current()?;
        Ok(result)
    }

    pub(super) fn check_current(&self) -> CargoResult<()> {
        ensure!(
            self.process == std::process::id(),
            "source-cache guards belong to another process"
        );
        self.home.same_identity()?;
        trust_resource_provenance::require_no_acl_grants(&self.home.file)?;
        let metadata = self.home.file.metadata()?;
        // SAFETY: this reads the current process's effective uid.
        ensure!(
            metadata.uid() == unsafe { libc::geteuid() } && metadata.mode() & 0o022 == 0,
            "cache directory ownership changed"
        );
        for ((file, before), name) in self.locks.iter().zip(LOCKS) {
            trust_resource_provenance::require_no_acl_grants(file)?;
            ensure!(
                stamp(before, &file.metadata()?)
                    && stamp(
                        before,
                        &std::fs::symlink_metadata(self.home.path.join(name))?
                    ),
                "original source-cache lock changed"
            );
        }
        Ok(())
    }
}

impl Drop for Cache {
    fn drop(&mut self) {
        if self.process == std::process::id() {
            for (file, _) in &self.locks {
                let _ = crate::util::flock::unlock(file);
            }
        }
        // Foreign fork copies only close; they never LOCK_UN the parent's OFD.
    }
}

pub(super) struct ObjectSource {
    // Retain the same original provider root. Descendant records are
    // observation DATA, not original OFDs or another source owner.
    root: Directory,
    directories: BTreeMap<PathBuf, Metadata>,
    files: Vec<(PathBuf, Metadata)>,
    forbidden: Vec<PathBuf>,
    failed: Cell<bool>,
    depth_limit: usize,
}

impl ObjectSource {
    /// Snapshot object DATA only. No enclosing repository is opened or read;
    /// without a Cargo cache guard this grants no exclusion against Git GC.
    pub(super) fn capture_objects(objects: &Path) -> CargoResult<Self> {
        ensure!(
            objects.is_absolute() && objects.canonicalize()? == objects,
            "source object directory must be absolute and canonical"
        );
        let mut result = Self {
            root: Directory::open(objects)?,
            directories: BTreeMap::new(),
            files: Vec::new(),
            forbidden: Vec::new(),
            failed: Cell::new(false),
            depth_limit: 4,
        };
        for relative in ["info/alternates", "info/http-alternates"] {
            ensure!(
                result.root.missing_relative(Path::new(relative))?,
                "unsupported Git object indirection: {relative}"
            );
            result.forbidden.push(PathBuf::from(relative));
        }
        Self::walk(&result.root, 0, &mut result.directories, &mut result.files)?;
        result.check_current()?;
        Ok(result)
    }

    pub(super) fn capture(repository: &Path) -> CargoResult<Self> {
        ensure!(
            repository.canonicalize()? == repository,
            "source Git database must be canonical"
        );
        let mut result = Self {
            root: Directory::open(repository)?,
            directories: BTreeMap::new(),
            files: Vec::new(),
            forbidden: Vec::new(),
            failed: Cell::new(false),
            depth_limit: 4,
        };
        result
            .directories
            .insert(result.root.path.clone(), result.root.before.clone());
        for relative in [
            "shallow",
            "commondir",
            "config.worktree",
            "info/grafts",
            "refs/replace",
            "objects/info/alternates",
            "objects/info/http-alternates",
        ] {
            ensure!(
                result.root.missing_relative(Path::new(relative))?,
                "unsupported Git source indirection: {relative}"
            );
            result.forbidden.push(PathBuf::from(relative));
        }
        let config = repository.join("config");
        let file = File::from(rustix::fs::openat(
            &result.root.file,
            "config",
            OFlags::RDONLY | OFlags::NOFOLLOW | OFlags::NONBLOCK | OFlags::CLOEXEC,
            Mode::empty(),
        )?);
        let metadata = file.metadata()?;
        ensure!(
            metadata.is_file() && metadata.nlink() == 1 && metadata.len() <= 16 * 1024,
            "unsupported source Git configuration"
        );
        let mut bytes = String::new();
        file.take(16 * 1024 + 1).read_to_string(&mut bytes)?;
        // Admit only generated core metadata. Never ask Git to read donor
        // config/includes or copy it into the destination. Values are not logged.
        let mut core = false;
        for line in bytes
            .lines()
            .map(str::trim)
            .filter(|line| !line.is_empty() && !line.starts_with(['#', ';']))
        {
            if line == "[core]" {
                core = true;
                continue;
            }
            ensure!(
                core && !line.starts_with('['),
                "unsupported source Git configuration section"
            );
            let (key, value) = line
                .split_once('=')
                .context("unsupported source Git configuration")?;
            let (key, value) = (key.trim(), value.trim());
            ensure!(
                matches!(
                    (key, value),
                    ("repositoryformatversion", "0")
                        | ("bare", "true")
                        | ("autocrlf", "false")
                        | (
                            "filemode" | "ignorecase" | "precomposeunicode" | "logallrefupdates",
                            "true" | "false"
                        )
                ),
                "unsupported source Git configuration key"
            );
        }
        result.files.push((config, metadata));
        let objects = result.root.child(OsStr::new("objects"))?;
        Self::walk(&objects, 0, &mut result.directories, &mut result.files)?;
        result.check_current()?;
        Ok(result)
    }

    fn walk(
        directory: &Directory,
        depth: usize,
        directories: &mut BTreeMap<PathBuf, Metadata>,
        files: &mut Vec<(PathBuf, Metadata)>,
    ) -> CargoResult<()> {
        ensure!(depth <= 3, "unsupported source object-directory depth");
        ensure!(
            files.len() + directories.len() < MAX_ENTRIES,
            "source object namespace exceeds its bound"
        );
        directory.current()?;
        directories.insert(directory.path.clone(), directory.before.clone());
        let names = directory.names()?;
        for name in names {
            let at = rustix::fs::statat(&directory.file, &name, AtFlags::SYMLINK_NOFOLLOW)?;
            if at.st_mode & libc::S_IFMT == libc::S_IFDIR {
                let child = directory.child(&name)?;
                Self::walk(&child, depth + 1, directories, files)?;
            } else {
                let file = File::from(rustix::fs::openat(
                    &directory.file,
                    &name,
                    OFlags::RDONLY | OFlags::NOFOLLOW | OFlags::NONBLOCK | OFlags::CLOEXEC,
                    Mode::empty(),
                )?);
                let metadata = file.metadata()?;
                ensure!(
                    metadata.is_file() && metadata.nlink() >= 1,
                    "source object namespace contains a link or special file"
                );
                ensure!(
                    files.len() + directories.len() < MAX_ENTRIES,
                    "source object namespace exceeds its bound"
                );
                files.push((directory.path.join(name), metadata));
            }
        }
        directory.current()
    }

    fn observe<T>(&self, operation: impl FnOnce() -> CargoResult<T>) -> CargoResult<T> {
        let result = operation();
        if result.is_err() {
            self.failed.set(true);
        }
        result
    }

    /// Reobserve a bounded descendant path from the still-live original root.
    /// No directory descriptor is returned. Every component is opened separately
    /// with NOFOLLOW and checked on both sides of the scoped operation.
    fn with_directory(
        &self,
        path: &Path,
        operation: impl FnOnce(&Directory) -> CargoResult<()>,
    ) -> CargoResult<()> {
        ensure!(!self.failed.get(), "source object observation has failed");
        let mut components = path.strip_prefix(&self.root.path)?.components();
        // A Cargo database has one additional "objects" component.
        ensure!(
            components.clone().count() <= self.depth_limit,
            "unsupported source object-directory depth"
        );
        self.descend(&self.root, &mut components, operation)
    }

    fn descend(
        &self,
        directory: &Directory,
        components: &mut std::path::Components<'_>,
        operation: impl FnOnce(&Directory) -> CargoResult<()>,
    ) -> CargoResult<()> {
        self.observe(|| directory.current())?;
        let result = match components.next() {
            None => operation(directory),
            Some(std::path::Component::Normal(name)) => {
                let mut child = self.observe(|| {
                    directory.child(name).with_context(|| {
                        format!(
                            "cannot observe source object directory {}",
                            directory.path.join(name).display()
                        )
                    })
                })?;
                child.before = self.observe(|| {
                    self.directories
                        .get(&child.path)
                        .cloned()
                        .context("original source object directory observation unavailable")
                })?;
                self.descend(&child, components, operation)
            }
            Some(_) => self.observe(|| bail!("noncanonical source object directory component")),
        };
        let after = self.observe(|| directory.current());
        result.and(after)
    }

    #[cfg(test)]
    pub(super) fn materialize_objects(
        &self,
        root: &Path,
        destination: &Path,
        byte_budget: u64,
        copy_budget: &mut CopyBudget,
    ) -> CargoResult<Materialized> {
        let mut view = OwnedView::test_create(destination)?;
        self.materialize_view(root, &mut view, byte_budget, copy_budget)
    }

    #[cfg(test)]
    fn materialize_objects_with(
        &self,
        root: &Path,
        destination: &Path,
        byte_budget: u64,
        copy_budget: &mut CopyBudget,
        native_clone: bool,
        after_copy: impl FnOnce() -> CargoResult<()>,
    ) -> CargoResult<Materialized> {
        let mut view = OwnedView::test_create(destination)?;
        self.materialize_view_with(
            root,
            &mut view,
            byte_budget,
            copy_budget,
            native_clone,
            after_copy,
        )
    }

    pub(super) fn materialize_view(
        &self,
        root: &Path,
        view: &mut OwnedView,
        byte_budget: u64,
        copy_budget: &mut CopyBudget,
    ) -> CargoResult<Materialized> {
        self.materialize_view_with(root, view, byte_budget, copy_budget, true, || Ok(()))
    }

    fn materialize_view_with(
        &self,
        root: &Path,
        view: &mut OwnedView,
        byte_budget: u64,
        copy_budget: &mut CopyBudget,
        native_clone: bool,
        after_copy: impl FnOnce() -> CargoResult<()>,
    ) -> CargoResult<Materialized> {
        use std::os::unix::ffi::OsStrExt as _;
        ensure!(!self.failed.get(), "source object observation has failed");
        let mut bytes = 0_u64;
        let mut materialized = Materialized::default();
        for (path, before) in &self.files {
            let Ok(relative) = path.strip_prefix(root) else {
                continue;
            };
            let components = relative.components().collect::<Vec<_>>();
            let [
                std::path::Component::Normal(first),
                std::path::Component::Normal(second),
            ] = components.as_slice()
            else {
                continue;
            };
            let first = first.as_bytes();
            let second_bytes = second.as_bytes();
            let hex = |bytes: &[u8]| {
                bytes
                    .iter()
                    .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(b))
            };
            let loose =
                first.len() == 2 && hex(first) && second_bytes.len() == 38 && hex(second_bytes);
            let pack = first == b"pack"
                && second_bytes.starts_with(b"pack-")
                && matches!(second_bytes.len(), 49 | 50)
                && hex(&second_bytes[5..45])
                && matches!(&second_bytes[45..], b".pack" | b".idx");
            if !loose && !pack {
                continue;
            }
            bytes = bytes
                .checked_add(before.len())
                .context("source object-data byte overflow")?;
            ensure!(
                bytes <= byte_budget,
                "source object-data view exceeds 32 GiB transaction bound"
            );
            let parent = path
                .parent()
                .context("original object parent unavailable")?;
            self.with_directory(parent, |parent| {
                let mut input = self.observe(|| {
                    let input = File::from(
                        rustix::fs::openat(
                            &parent.file,
                            *second,
                            OFlags::RDONLY | OFlags::NOFOLLOW | OFlags::NONBLOCK | OFlags::CLOEXEC,
                            Mode::empty(),
                        )
                        .context("cannot open original source object")?,
                    );
                    ensure!(
                        stamp(before, &input.metadata()?),
                        "source object was replaced before copying"
                    );
                    Ok(input)
                })?;
                let target_parent = view.directory(OsStr::from_bytes(first))?;
                let copied = view.create_file(target_parent, second, |destination| {
                    #[cfg(target_os = "macos")]
                    {
                        let target_name = std::ffi::CString::new(second_bytes)?;
                        // SAFETY: live original input, checked private parent
                        // and valid C string. This clones DATA only.
                        if native_clone
                            && unsafe {
                                libc::fclonefileat(
                                    input.as_raw_fd(),
                                    destination.as_raw_fd(),
                                    target_name.as_ptr(),
                                    0,
                                )
                            } == 0
                        {
                            let output = File::from(rustix::fs::openat(
                                destination,
                                *second,
                                OFlags::RDONLY
                                    | OFlags::NOFOLLOW
                                    | OFlags::NONBLOCK
                                    | OFlags::CLOEXEC,
                                Mode::empty(),
                            )?);
                            materialized.cloned_files += 1;
                            materialized.cloned_bytes += before.len();
                            return Ok(output);
                        }
                    }
                    let mut output = File::from(rustix::fs::openat(
                        destination,
                        *second,
                        OFlags::WRONLY
                            | OFlags::CREATE
                            | OFlags::EXCL
                            | OFlags::NOFOLLOW
                            | OFlags::NONBLOCK
                            | OFlags::CLOEXEC,
                        Mode::from_bits_truncate(0o600),
                    )?);
                    #[cfg(target_os = "linux")]
                    // SAFETY: live original input and fresh private output.
                    // A refused reflink uses the bounded stream path.
                    let cloned = native_clone
                        && unsafe {
                            libc::ioctl(output.as_raw_fd(), libc::FICLONE, input.as_raw_fd())
                        } == 0;
                    #[cfg(target_os = "macos")]
                    let cloned = false;
                    if !cloned {
                        ensure!(
                            before.len() <= 32 * 1024 * 1024 * 1024,
                            "compressed object file exceeds bound"
                        );
                        // Charge the SAME cumulative budget before any stream
                        // write. Failed attempts do not refund reservations.
                        copy_budget.reserve(before.len())?;
                        let copied =
                            std::io::copy(&mut (&mut input).take(before.len()), &mut output)?;
                        // Do not write a sentinel beyond the charged limit.
                        let mut extra = [0];
                        self.observe(|| {
                            ensure!(
                                copied == before.len() && input.read(&mut extra)? == 0,
                                "source object changed while copying"
                            );
                            Ok(())
                        })?;
                        materialized.streamed_bytes += copied;
                    } else {
                        materialized.cloned_files += 1;
                        materialized.cloned_bytes += before.len();
                    }
                    Ok(output)
                });
                // Check even when the copy or its destination bookend failed.
                // A separate copy-budget refusal alone does not poison an
                // otherwise unchanged input observation.
                let after = self.observe(|| {
                    ensure!(
                        stamp(before, &input.metadata()?),
                        "source object changed during materialization"
                    );
                    Ok(())
                });
                copied.and(after)
            })?;
        }
        let after = after_copy();
        let current = self.check_current();
        after.and(current)?;
        view.seal()?;
        materialized.bytes = bytes;
        Ok(materialized)
    }

    pub(super) fn check_current(&self) -> CargoResult<()> {
        ensure!(!self.failed.get(), "source object observation has failed");
        self.observe(|| {
            for path in self.directories.keys() {
                self.with_directory(path, |_| Ok(()))?;
            }
            for (path, before) in &self.files {
                ensure!(
                    stamp(before, &std::fs::symlink_metadata(path)?),
                    "source object namespace changed"
                );
            }
            for path in &self.forbidden {
                ensure!(
                    self.root.missing_relative(path)?,
                    "source Git indirection appeared"
                );
            }
            self.root.current()
        })
    }
}

pub(super) struct Stage {
    ancestors: Vec<Directory>,
    container: Directory,
    views: Directory,
    marker: File,
    path: PathBuf,
    destination: PathBuf,
    parent: Directory,
    cache: Cache,
    published: bool,
    preflight_finished: bool,
}

impl Stage {
    pub(super) fn new(destination: &Path, donors: &[&Path]) -> CargoResult<Self> {
        Self::new_with(destination, donors, |_| Ok(()))
    }

    fn new_with(
        destination: &Path,
        donors: &[&Path],
        after_container: impl FnOnce(&Path) -> CargoResult<()>,
    ) -> CargoResult<Self> {
        ensure!(
            destination.is_absolute(),
            "destination Cargo home must be absolute"
        );
        let parent = destination
            .parent()
            .context("destination Cargo home has no parent")?;
        ensure!(
            parent.canonicalize()? == parent,
            "destination parent must already be canonical"
        );
        // Check every explicit input before the first mkdirat. The random
        // staging sibling is created exclusively; an existing input cannot be
        // inside it, and an ancestor input would also contain destination.
        for donor in donors {
            ensure!(
                !destination.starts_with(donor) && !donor.starts_with(destination),
                "source and destination data namespaces must be disjoint"
            );
        }
        ensure!(
            matches!(std::fs::symlink_metadata(destination), Err(error) if error.kind() == std::io::ErrorKind::NotFound),
            "local Git source import requires a fresh absent Cargo home"
        );
        let (ancestors, parent) = controlled_parent(parent)?;
        let name = format!(
            ".targo-git-source-import-{:032x}.noindex",
            rand::random::<u128>()
        );
        let container = parent.create_child(OsStr::new(&name))?;
        after_container(&container.path)?;
        let home = container.create_child(OsStr::new("home"))?;
        let path = home.path.clone();
        let cache = Cache::acquire_home(home, true)?;
        let views = container.create_child(OsStr::new("views"))?;
        let marker = File::from(rustix::fs::openat(
            &cache.home.file,
            ".targo-source-data-state",
            OFlags::RDWR
                | OFlags::CREATE
                | OFlags::EXCL
                | OFlags::NOFOLLOW
                | OFlags::NONBLOCK
                | OFlags::CLOEXEC,
            Mode::from_bits_truncate(0o600),
        )?);
        let result = Self {
            ancestors,
            container,
            views,
            marker,
            path,
            destination: destination.to_owned(),
            parent,
            cache,
            published: false,
            preflight_finished: false,
        };
        result.state(b"targo-source-data-v1\nincomplete-original-owner\n")?;
        Ok(result)
    }

    pub(super) fn path(&self) -> &Path {
        &self.path
    }

    pub(super) fn create_view(&self, ident: &str) -> CargoResult<OwnedView> {
        self.validate_namespace()?;
        OwnedView::create(&self.views, OsStr::new(ident))
    }

    /// Only the original live producer may finish an unpublished preflight.
    /// ODB destruction and final original-input bookends are the caller's prior
    /// obligation. The report is not a cleanup/restart capability.
    pub(super) fn finish_preflight(&mut self, views: &mut [OwnedView]) -> CargoResult<()> {
        self.validate_namespace()?;
        ensure!(
            !self.published && !self.preflight_finished,
            "source preflight already finished"
        );
        ensure!(
            matches!(std::fs::symlink_metadata(&self.destination), Err(error) if error.kind() == std::io::ErrorKind::NotFound),
            "destination appeared during preflight"
        );
        self.close_views(views)?;
        self.state(b"targo-source-data-v1\npreflight-observed-views-closed-no-adoption\n")?;
        self.preflight_finished = true;
        Ok(())
    }

    /// Close only the actual private views issued by this still-unpublished stage.
    /// The caller drops every actual ODB borrower before this owning cleanup.
    pub(super) fn close_views(&self, views: &mut [OwnedView]) -> CargoResult<()> {
        self.validate_namespace()?;
        ensure!(
            !self.published && !self.preflight_finished,
            "source stage already finished"
        );
        let mut expected = std::collections::BTreeSet::new();
        for view in &*views {
            ensure!(
                view.parent_is(&self.views.file)?,
                "private view belongs to another original stage"
            );
            ensure!(
                expected.insert(view.leaf().to_owned()),
                "private view repeated in preflight cleanup"
            );
        }
        ensure!(
            self.views
                .names()?
                .into_iter()
                .collect::<std::collections::BTreeSet<_>>()
                == expected,
            "preflight stage contains unexpected views"
        );
        for view in views {
            view.cleanup()
                .context("preflight view cleanup incomplete; remaining private DATA retained")?;
        }
        ensure!(
            self.views.names()?.is_empty(),
            "preflight view namespace is not empty after cleanup"
        );
        self.validate_namespace()?;
        Ok(())
    }

    pub(super) fn validate_namespace(&self) -> CargoResult<()> {
        for directory in &self.ancestors {
            ancestor_security(directory, None)?;
        }
        self.parent.private_current()?;
        self.container.private_current()?;
        self.views.private_current()?;
        self.cache.home.private_current()?;
        self.cache.check_current()
    }

    fn state(&self, bytes: &[u8]) -> CargoResult<()> {
        let metadata = self.marker.metadata()?;
        let named = rustix::fs::statat(
            &self.cache.home.file,
            ".targo-source-data-state",
            AtFlags::SYMLINK_NOFOLLOW,
        )?;
        // SAFETY: reads only the effective account.
        ensure!(
            metadata.is_file()
                && metadata.nlink() == 1
                && metadata.uid() == unsafe { libc::geteuid() }
                && metadata.mode() & 0o7077 == 0
                && named.st_dev as u64 == metadata.dev()
                && named.st_ino as u64 == metadata.ino(),
            "original source-data marker changed"
        );
        trust_resource_provenance::require_no_acl_grants(&self.marker)?;
        let mut file = &self.marker;
        file.rewind()?;
        file.set_len(0)?;
        file.write_all(bytes)?;
        file.sync_all()?;
        Ok(())
    }

    pub(super) fn publish(&mut self) -> CargoResult<()> {
        self.publish_with(|_| Ok(()))
    }

    fn publish_with(
        &mut self,
        after_rename: impl FnOnce(&Self) -> CargoResult<()>,
    ) -> CargoResult<()> {
        self.validate_namespace()?;
        self.state(b"targo-source-data-v1\ncomplete-data-not-authority\n")?;
        self.cache.check_current()?;
        self.container.same_identity()?;
        self.cache.home.file.sync_all()?;
        use std::ffi::CString;
        use std::os::unix::ffi::OsStrExt as _;
        let destination = CString::new(
            self.destination
                .file_name()
                .context("destination name unavailable")?
                .as_bytes(),
        )?;
        #[cfg(target_os = "macos")]
        let result = unsafe {
            libc::renameatx_np(
                self.container.file.as_raw_fd(),
                c"home".as_ptr(),
                self.parent.file.as_raw_fd(),
                destination.as_ptr(),
                libc::RENAME_EXCL,
            )
        };
        #[cfg(target_os = "linux")]
        let result = unsafe {
            libc::renameat2(
                self.container.file.as_raw_fd(),
                c"home".as_ptr(),
                self.parent.file.as_raw_fd(),
                destination.as_ptr(),
                libc::RENAME_NOREPLACE,
            )
        };
        ensure!(
            result == 0,
            "source-data publication refused: {}",
            std::io::Error::last_os_error()
        );
        // The kernel rename is the commit point. Later errors cannot claim the
        // home is absent, and Drop must not quarantine or roll it back.
        self.published = true;
        self.cache.home.path = self.destination.clone();
        let completion: CargoResult<()> = (|| {
            after_rename(self)?;
            self.cache.check_current()?;
            self.parent.file.sync_all()?;
            Ok(())
        })();
        completion.context("source-data home has been published; post-commit observation/durability failed, no rollback attempted")
    }
}

fn require_local_filesystem(file: &File) -> CargoResult<()> {
    let mut fs = std::mem::MaybeUninit::<libc::statfs>::uninit();
    // SAFETY: live descriptor and writable statfs; the kernel retains neither.
    ensure!(
        unsafe { libc::fstatfs(file.as_raw_fd(), fs.as_mut_ptr()) } == 0,
        "cannot identify source cache filesystem"
    );
    // SAFETY: successful fstatfs initialized the complete value.
    let fs = unsafe { fs.assume_init() };
    #[cfg(target_os = "macos")]
    let nfs = fs.f_fstypename[..4] == [b'n' as _, b'f' as _, b's' as _, 0];
    #[cfg(target_os = "linux")]
    let nfs = fs.f_type as u64 == libc::NFS_SUPER_MAGIC as u64;
    ensure!(
        !nfs,
        "strict local source-cache locks are unavailable on NFS"
    );
    Ok(())
}

fn ancestor_security(directory: &Directory, child: Option<&Directory>) -> CargoResult<()> {
    directory.same_identity()?;
    let metadata = directory.file.metadata()?;
    // SAFETY: reads only this process's effective account.
    let uid = unsafe { libc::geteuid() };
    ensure!(
        metadata.uid() == 0 || metadata.uid() == uid,
        "source-data ancestor belongs to an uncontrolled account"
    );
    trust_resource_provenance::require_no_acl_grants(&directory.file)?;
    if metadata.mode() & 0o022 != 0 {
        ensure!(
            metadata.mode() & 0o1000 != 0,
            "source-data ancestor is writable without sticky protection"
        );
        if let Some(child) = child {
            let child = child.file.metadata()?;
            ensure!(
                child.uid() == 0 || child.uid() == uid,
                "sticky ancestor does not protect the selected child"
            );
        }
    }
    Ok(())
}

fn controlled_parent(path: &Path) -> CargoResult<(Vec<Directory>, Directory)> {
    let mut ancestors = Vec::new();
    let mut directory = Directory::open(Path::new("/"))?;
    for part in path.components() {
        match part {
            std::path::Component::RootDir => {}
            std::path::Component::Normal(name) => {
                let child = directory.child(name)?;
                ancestor_security(&directory, Some(&child))?;
                ancestors.push(directory);
                directory = child;
            }
            _ => bail!("noncanonical source-data parent"),
        }
    }
    directory.private_current()?;
    Ok((ancestors, directory))
}

impl Drop for Stage {
    fn drop(&mut self) {
        if !self.published && !self.preflight_finished && self.cache.process == std::process::id() {
            let _ = self.state(b"targo-source-data-v1\nquarantined-no-adoption\n");
        }
        // Retain partial bytes for inspection. No restart/path-only adoption exists.
    }
}

#[cfg(test)]
mod tests;
