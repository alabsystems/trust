//! Native repository/commit correspondence for SAME retained package inputs.
//! This is not a repository writer, proof grade, SDK or permission to publish.
//! The native caller must hold its actual paid preparation around every call.
use std::collections::{BTreeMap, BTreeSet};
use std::ffi::{CStr, CString, OsString};
use std::fs::{File, Metadata};
use std::io;
use std::os::fd::{AsRawFd, FromRawFd};
use std::os::unix::ffi::{OsStrExt, OsStringExt};
use std::os::unix::fs::MetadataExt;
use std::path::{Component, Path, PathBuf};
use std::sync::{
    Arc, Mutex,
    atomic::{AtomicBool, Ordering},
};
use std::time::Instant;

use git2::{ObjectType, Oid, Repository, Status, StatusOptions};
use trust_resource_controller::descriptors::{
    AdmittedDirectory, AdmittedPackageSource, DescriptorBudget, OriginalInputPermit,
};

const MAX_ENTRIES: usize = 500_000;
const MAX_CHANGED: usize = 8192;
const MAX_HISTORY: usize = 4096;
const MAX_PACK_FILES: usize = 64;
const MAX_DEPTH: usize = 64;
const MAX_CONTROL_BYTES: u64 = 64 * 1024 * 1024;
const MAX_OBJECT_BYTES: usize = 512 * 1024 * 1024;
const MAX_READ_BYTES: usize = 1024 * 1024 * 1024;
const MAX_PACKAGES: usize = 64;
// Covers libgit2's serial transient descriptions and native directory scans.
// Every retained original below additionally pays its own actual FD demand.
const LIBRARY_DESCRIPTORS: usize = 128;

fn refused(reason: &'static str) -> io::Error {
    io::Error::new(io::ErrorKind::PermissionDenied, reason)
}
fn git(error: git2::Error) -> io::Error {
    io::Error::other(error)
}
fn time(deadline: Instant) -> io::Result<()> {
    if Instant::now() >= deadline {
        Err(io::ErrorKind::TimedOut.into())
    } else {
        Ok(())
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
struct Stamp {
    device: u64,
    inode: u64,
    mode: u32,
    uid: u32,
    gid: u32,
    bytes: u64,
    modified: (i64, i64),
    changed: (i64, i64),
}
impl Stamp {
    fn of(value: &Metadata) -> Self {
        Self {
            device: value.dev(),
            inode: value.ino(),
            mode: value.mode(),
            uid: value.uid(),
            gid: value.gid(),
            bytes: value.len(),
            modified: (value.mtime(), value.mtime_nsec()),
            changed: (value.ctime(), value.ctime_nsec()),
        }
    }
}
struct Original {
    file: File,
    before: Stamp,
    // LAST: the native description closes before its charge can be returned.
    _permit: OriginalInputPermit,
}
impl Original {
    fn open(
        parent: &File,
        name: &Path,
        directory: bool,
        budget: &Arc<DescriptorBudget>,
    ) -> io::Result<Self> {
        let permit = budget.reserve_original_inputs(1)?;
        let name = CString::new(name.as_os_str().as_bytes())
            .map_err(|_| refused("Git name contains NUL"))?;
        let flags = libc::O_RDONLY
            | libc::O_CLOEXEC
            | libc::O_NOFOLLOW
            | libc::O_NONBLOCK
            | if directory { libc::O_DIRECTORY } else { 0 };
        // SAFETY: actual retained directory, bounded single component and a
        // new owned descriptor; no symlink or ambient fd can replace it.
        let raw = unsafe { libc::openat(parent.as_raw_fd(), name.as_ptr(), flags) };
        if raw < 0 {
            return Err(io::Error::last_os_error());
        }
        let file = unsafe { File::from_raw_fd(raw) };
        let metadata = file.metadata()?;
        if (directory && !metadata.is_dir()) || (!directory && !metadata.is_file()) {
            return Err(refused("Git control/object original has another file type"));
        }
        let uid = unsafe { libc::geteuid() };
        if (metadata.uid() != uid && metadata.uid() != 0)
            || metadata.mode() & 0o7022 != 0
            || !directory && metadata.nlink() == 0
        {
            return Err(refused(
                "Git original has unsafe ownership or writable/special mode",
            ));
        }
        trust_resource_provenance::require_no_acl_grants(&file)?;
        Ok(Self {
            before: Stamp::of(&metadata),
            file,
            _permit: permit,
        })
    }
    fn validate(&self) -> io::Result<()> {
        if Stamp::of(&self.file.metadata()?) != self.before {
            return Err(refused("original Git control/object changed"));
        }
        Ok(())
    }
}
/// One native no-follow walk, including the original intermediate directories.
struct PathOriginal {
    root: Arc<AdmittedDirectory>,
    relative: PathBuf,
    parents: Vec<Original>,
    leaf: Option<Original>,
    // For a negative lookup, retain the first missing component and its actual
    // original parent. A later creation cannot turn it into an original.
    missing: Option<PathBuf>,
}
impl PathOriginal {
    fn capture(
        root: Arc<AdmittedDirectory>,
        relative: &Path,
        budget: &Arc<DescriptorBudget>,
        deadline: Instant,
    ) -> io::Result<Self> {
        time(deadline)?;
        let parts = relative
            .components()
            .map(|part| match part {
                Component::Normal(name) => Ok(PathBuf::from(name)),
                _ => Err(refused("Git lookup is not a canonical root-relative path")),
            })
            .collect::<io::Result<Vec<_>>>()?;
        if parts.is_empty() || parts.len() > MAX_DEPTH {
            return Err(refused("Git lookup depth is unsupported"));
        }
        let root_file = File::from(root.descriptor(deadline)?.try_clone_to_owned()?);
        let mut parents = Vec::new();
        let mut leaf = None;
        let mut missing = None;
        for (index, part) in parts.iter().enumerate() {
            let parent = parents
                .last()
                .map_or(&root_file, |held: &Original| &held.file);
            let terminal = index + 1 == parts.len();
            let opened = Original::open(parent, part, !terminal, budget);
            match opened {
                Ok(original) if terminal => {
                    leaf = Some(original);
                }
                Ok(original) => parents.push(original),
                Err(error) if error.kind() == io::ErrorKind::NotFound => {
                    missing = Some(part.clone());
                    break;
                }
                Err(error) => return Err(error),
            }
        }
        let result = Self {
            root,
            relative: relative.into(),
            parents,
            leaf,
            missing,
        };
        result.validate(budget, deadline)?;
        Ok(result)
    }
    fn validate(&self, budget: &Arc<DescriptorBudget>, deadline: Instant) -> io::Result<()> {
        self.root.validate(deadline)?;
        // This temporary walk is independently paid before cloning/opening.
        let _temporary = budget.reserve_original_inputs(MAX_DEPTH + 1)?;
        let mut current = File::from(self.root.descriptor(deadline)?.try_clone_to_owned()?);
        for (part, original) in self.relative.components().zip(&self.parents) {
            time(deadline)?;
            original.validate()?;
            let Component::Normal(part) = part else {
                return Err(refused("noncanonical original Git parent"));
            };
            let name =
                CString::new(part.as_bytes()).map_err(|_| refused("Git parent contains NUL"))?;
            let raw = unsafe {
                libc::openat(
                    current.as_raw_fd(),
                    name.as_ptr(),
                    libc::O_RDONLY | libc::O_CLOEXEC | libc::O_NOFOLLOW | libc::O_DIRECTORY,
                )
            };
            if raw < 0 {
                return Err(io::Error::last_os_error());
            }
            current = unsafe { File::from_raw_fd(raw) };
            if Stamp::of(&current.metadata()?) != original.before {
                return Err(refused("Git parent directory was replaced or mutated"));
            }
        }
        let name = self
            .missing
            .as_deref()
            .or_else(|| self.relative.file_name().map(Path::new))
            .ok_or_else(|| refused("Git original lost terminal name"))?;
        let name = CString::new(name.as_os_str().as_bytes())
            .map_err(|_| refused("Git terminal contains NUL"))?;
        let raw = unsafe {
            libc::openat(
                current.as_raw_fd(),
                name.as_ptr(),
                libc::O_RDONLY | libc::O_CLOEXEC | libc::O_NOFOLLOW,
            )
        };
        if let Some(original) = &self.leaf {
            original.validate()?;
            if raw < 0 {
                return Err(io::Error::last_os_error());
            }
            let named = unsafe { File::from_raw_fd(raw) };
            if Stamp::of(&named.metadata()?) != original.before {
                return Err(refused(
                    "original Git name no longer names its retained file",
                ));
            }
        } else {
            if raw >= 0 {
                drop(unsafe { File::from_raw_fd(raw) });
                return Err(refused("negative Git lookup was populated"));
            }
            let error = io::Error::last_os_error();
            if error.kind() != io::ErrorKind::NotFound {
                return Err(error);
            }
        }
        self.root.validate(deadline)
    }
}
struct State {
    // Close libgit2 and its object backend before native original charges.
    repository: Repository,
    roots: Vec<Arc<AdmittedDirectory>>,
    root_stamps: Vec<Stamp>,
    controls: Vec<PathOriginal>,
    objects: BTreeMap<Oid, PathOriginal>,
    observations: BTreeMap<Oid, ObjectObservation>,
    common: Arc<AdmittedDirectory>,
    packs: PackPopulation,
    budget: Arc<DescriptorBudget>,
    read_bytes: usize,
}
#[derive(Clone)]
struct ObjectObservation {
    kind: ObjectType,
    bytes: usize,
    sha256: String,
}
struct PackPopulation {
    root: Arc<AdmittedDirectory>,
    before: Stamp,
    names: Vec<OsString>,
    originals: Vec<PathOriginal>,
}
fn directory_stamp(root: &AdmittedDirectory, deadline: Instant) -> io::Result<Stamp> {
    let file = File::from(root.descriptor(deadline)?.try_clone_to_owned()?);
    Ok(Stamp::of(&file.metadata()?))
}
fn directory_names(
    root: &AdmittedDirectory,
    budget: &Arc<DescriptorBudget>,
    deadline: Instant,
) -> io::Result<Vec<OsString>> {
    time(deadline)?;
    let _temporary = budget.reserve_original_inputs(1)?;
    let original = root.descriptor(deadline)?;
    // A dup shares its directory OFD cursor and would consume the original's
    // offset. Open a fresh cursor relative to the SAME actual original instead.
    // SAFETY: fixed dot component, original admitted directory, fresh owned FD.
    let raw = unsafe {
        libc::openat(
            original.as_raw_fd(),
            c".".as_ptr(),
            libc::O_RDONLY | libc::O_DIRECTORY | libc::O_CLOEXEC | libc::O_NOFOLLOW,
        )
    };
    if raw < 0 {
        return Err(io::Error::last_os_error());
    }
    // SAFETY: ownership of this new cursor is transferred to fdopendir.
    let pointer = unsafe { libc::fdopendir(raw) };
    if pointer.is_null() {
        let error = io::Error::last_os_error();
        unsafe {
            libc::close(raw);
        };
        return Err(error);
    }
    struct Directory(*mut libc::DIR);
    impl Drop for Directory {
        fn drop(&mut self) {
            unsafe {
                libc::closedir(self.0);
            }
        }
    }
    let directory = Directory(pointer);
    let mut names = Vec::new();
    loop {
        time(deadline)?;
        #[cfg(target_os = "macos")]
        unsafe {
            *libc::__error() = 0;
        }
        #[cfg(target_os = "linux")]
        unsafe {
            *libc::__errno_location() = 0;
        }
        let entry = unsafe { libc::readdir(directory.0) };
        if entry.is_null() {
            let error = io::Error::last_os_error();
            if error.raw_os_error() != Some(0) {
                return Err(error);
            }
            break;
        }
        let name = unsafe { CStr::from_ptr((*entry).d_name.as_ptr()) }.to_bytes();
        if name == b"." || name == b".." {
            continue;
        }
        if names.len() >= MAX_PACK_FILES || name.len() > 128 || name.contains(&b'/') {
            return Err(refused("Git pack namespace exceeds native bound"));
        }
        names.push(OsString::from_vec(name.to_vec()));
    }
    names.sort();
    if names.windows(2).any(|pair| pair[0] == pair[1]) {
        return Err(refused("Git directory returned duplicate entries"));
    }
    root.validate(deadline)?;
    Ok(names)
}
impl PackPopulation {
    fn capture(
        common: &Path,
        budget: &Arc<DescriptorBudget>,
        deadline: Instant,
    ) -> io::Result<Self> {
        let root = budget.capture_directory(&common.join("objects/pack"), deadline)?;
        let before = directory_stamp(&root, deadline)?;
        let names = directory_names(&root, budget, deadline)?;
        let mut originals = Vec::new();
        for name in &names {
            let bytes = name.as_bytes();
            if bytes != b"multi-pack-index"
                && ![b".pack".as_slice(), b".idx", b".rev", b".bitmap", b".keep"]
                    .iter()
                    .any(|suffix| bytes.ends_with(suffix))
            {
                return Err(refused("Git pack namespace contains an unsupported input"));
            }
            let original = PathOriginal::capture(root.clone(), Path::new(name), budget, deadline)?;
            if original.leaf.is_none() {
                return Err(refused("Git pack population changed during capture"));
            }
            originals.push(original);
        }
        let result = Self {
            root,
            before,
            names,
            originals,
        };
        result.validate(budget, deadline)?;
        Ok(result)
    }
    fn validate(&self, budget: &Arc<DescriptorBudget>, deadline: Instant) -> io::Result<()> {
        if directory_stamp(&self.root, deadline)? != self.before {
            return Err(refused("original Git pack directory changed"));
        }
        if directory_names(&self.root, budget, deadline)? != self.names {
            return Err(refused("original Git pack membership changed"));
        }
        for original in &self.originals {
            original.validate(budget, deadline)?;
        }
        Ok(())
    }
}

/// Holds the actual repository/control directories and package originals. No
/// deserializer, arbitrary Git runner, receipt or public field constructs it.
pub struct RepositorySources {
    state: Mutex<State>,
    sources: Vec<Arc<AdmittedPackageSource>>,
    workdir: PathBuf,
    prefixes: Vec<PathBuf>,
    commit: Oid,
    tree: Oid,
    invalid: AtomicBool,
    // LAST: includes libgit2's actual serial descriptor envelope.
    _library: OriginalInputPermit,
}

/// Changed paths grouped by the unique pair of retained package originals.
/// Indices refer to the exact populations passed to `capture`. This is DATA,
/// not evidence that any affected owner passed its ordinary development gate.
pub struct PackageChange {
    pub baseline: usize,
    pub candidate: usize,
    pub paths: Vec<PathBuf>,
}
pub struct SourceDelta {
    pub paths: Vec<PathBuf>,
    pub affected: Vec<PackageChange>,
}

impl RepositorySources {
    pub fn capture(
        sources: Vec<Arc<AdmittedPackageSource>>,
        budget: Arc<DescriptorBudget>,
        deadline: Instant,
    ) -> io::Result<Self> {
        if sources.is_empty() || sources.len() > MAX_PACKAGES {
            return Err(refused(
                "native repository package population is unsupported",
            ));
        }
        // Reject a foreign process before a Git library or inherited mutex.
        for source in &sources {
            source.validate(deadline)?;
        }
        let library = budget.reserve_original_inputs(LIBRARY_DESCRIPTORS)?;
        let repository = Repository::discover(sources[0].path()).map_err(git)?;
        if repository.is_bare() || repository.is_shallow() {
            return Err(refused(
                "native landing requires a complete non-bare repository",
            ));
        }
        let workdir = repository
            .workdir()
            .ok_or_else(|| refused("Git worktree is unavailable"))?
            .canonicalize()?;
        if std::fs::symlink_metadata(workdir.join(".git"))?
            .file_type()
            .is_symlink()
        {
            return Err(refused("Git worktree control cannot be a symlink"));
        }
        let mut prefixes: Vec<PathBuf> = Vec::with_capacity(sources.len());
        let mut identities = BTreeSet::new();
        for source in &sources {
            let prefix = source
                .path()
                .strip_prefix(&workdir)
                .map_err(|_| refused("held source is outside the actual Git worktree"))?
                .to_path_buf();
            if prefix.as_os_str().is_empty()
                || prefix
                    .components()
                    .any(|part| !matches!(part, Component::Normal(_)))
            {
                return Err(refused(
                    "selected package cannot include its mutable Git control directory",
                ));
            }
            if prefixes
                .iter()
                .any(|held| prefix.starts_with(held) || held.starts_with(&prefix))
            {
                return Err(refused(
                    "duplicate or overlapping native repository package owners",
                ));
            }
            let identity = source.original_root_identity(deadline)?;
            if !identities.insert((identity.device, identity.inode)) {
                return Err(refused(
                    "native repository package owners alias the same original",
                ));
            }
            // A nested repository is another control/object owner, even when
            // its files happen to match a directory in this commit.
            let selected = Repository::discover(source.path()).map_err(git)?;
            if selected.path().canonicalize()? != repository.path().canonicalize()? {
                return Err(refused(
                    "package population crosses actual repository controls",
                ));
            }
            prefixes.push(prefix);
        }
        let git_dir = repository.path().canonicalize()?;
        let common_dir = repository.commondir().canonicalize()?;
        let root = budget.capture_directory(&workdir, deadline)?;
        let control = budget.capture_directory(&git_dir, deadline)?;
        let common = budget.capture_directory(&common_dir, deadline)?;
        let roots = vec![root.clone(), control.clone(), common.clone()];
        let root_stamps = roots
            .iter()
            .map(|root| directory_stamp(root, deadline))
            .collect::<io::Result<Vec<_>>>()?;
        let packs = PackPopulation::capture(&common_dir, &budget, deadline)?;
        let mut state = State {
            repository,
            roots,
            root_stamps,
            controls: Vec::new(),
            objects: BTreeMap::new(),
            observations: BTreeMap::new(),
            common,
            packs,
            budget,
            read_bytes: 0,
        };
        // Strictly retain actual worktree/HEAD/index/config control originals.
        // A linked worktree's real common directory remains independently held.
        if workdir.join(".git").is_file() {
            state.control(root, Path::new(".git"), deadline)?;
        }
        for name in ["HEAD", "index", "commondir", "config.worktree", "gitdir"] {
            state.control(control.clone(), Path::new(name), deadline)?;
        }
        for name in ["config", "packed-refs", "index"] {
            state.control(state.common.clone(), Path::new(name), deadline)?;
        }
        for name in [
            "shallow",
            "info/grafts",
            "objects/info/alternates",
            "objects/info/http-alternates",
        ] {
            if state.control(state.common.clone(), Path::new(name), deadline)? {
                return Err(refused(
                    "shallow, grafted or alternate Git object stores are unsupported",
                ));
            }
        }
        let (commit, head_name) = {
            let head = state.repository.head().map_err(git)?;
            (
                head.target()
                    .ok_or_else(|| refused("unborn or unresolved Git HEAD"))?,
                PathBuf::from(head.name().map_err(git)?),
            )
        };
        state.control(control.clone(), &head_name, deadline)?;
        state.control(state.common.clone(), &head_name, deadline)?;
        let tree = state.commit(commit, deadline)?.0;
        state.clean(deadline)?;
        let result = Self {
            state: Mutex::new(state),
            sources,
            workdir,
            prefixes,
            commit,
            tree,
            invalid: AtomicBool::new(false),
            _library: library,
        };
        result.check(
            |state| {
                for (prefix, source) in result.prefixes.iter().zip(&result.sources) {
                    state.matches_source(result.tree, prefix, source, deadline)?;
                }
                Ok(())
            },
            deadline,
        )?;
        Ok(result)
    }
    pub fn repository_root(&self) -> &Path {
        &self.workdir
    }
    pub fn commit(&self) -> String {
        self.commit.to_string()
    }
    pub fn sources(&self) -> &[Arc<AdmittedPackageSource>] {
        &self.sources
    }
    pub fn validate(&self, deadline: Instant) -> io::Result<()> {
        self.check(|_| Ok(()), deadline)
    }
    fn check<T>(
        &self,
        operation: impl FnOnce(&mut State) -> io::Result<T>,
        deadline: Instant,
    ) -> io::Result<T> {
        if self.invalid.load(Ordering::Acquire) {
            return Err(refused("repository source has an earlier failed bookend"));
        }
        let result = (|| {
            time(deadline)?;
            // Controller originals reject a foreign process before touching
            // any inherited repository/Git mutex. A fork may have copied a
            // permanently held mutex; matching paths/FDs cannot adopt it.
            for source in &self.sources {
                source.validate(deadline)?;
            }
            let mut state = self
                .state
                .lock()
                .map_err(|_| refused("repository owner poisoned"))?;
            state.validate(deadline)?;
            if state.repository.head().map_err(git)?.target() != Some(self.commit) {
                return Err(refused("original source HEAD changed"));
            }
            state.clean(deadline)?;
            let value = operation(&mut state)?;
            state.validate(deadline)?;
            for source in &self.sources {
                source.validate(deadline)?;
            }
            time(deadline)?;
            Ok(value)
        })();
        if result.is_err() {
            self.invalid.store(true, Ordering::Release);
        }
        if result.is_ok() && self.invalid.load(Ordering::Acquire) {
            return Err(refused("repository source failed a concurrent bookend"));
        }
        result
    }
    /// Independently validate the complete commit delta against BOTH actual
    /// source owners. No unvalidated sibling changes disappear from the delta.
    pub fn require_candidate_of(
        &self,
        baseline: &Self,
        deadline: Instant,
    ) -> io::Result<SourceDelta> {
        let result = (|| {
            let before: BTreeMap<_, _> = baseline
                .prefixes
                .iter()
                .enumerate()
                .map(|(i, p)| (p, i))
                .collect();
            let after: BTreeMap<_, _> = self
                .prefixes
                .iter()
                .enumerate()
                .map(|(i, p)| (p, i))
                .collect();
            if self.commit == baseline.commit || before.keys().ne(after.keys()) {
                return Err(refused(
                    "native repair must change the same complete selected package population",
                ));
            }
            baseline.validate(deadline)?;
            let before_identity =
                baseline.check(|state| state.common.original_identity(deadline), deadline)?;
            let delta = self.check(
                |state| {
                    if state.common.original_identity(deadline)? != before_identity {
                        return Err(refused("candidate replaced the original common repository"));
                    }
                    state.require_ancestor(baseline.commit, self.commit, deadline)?;
                    let changed =
                        state.delta(baseline.tree, self.tree, &self.prefixes, deadline)?;
                    if changed.is_empty() {
                        return Err(refused(
                            "native repair changed no selected committed source",
                        ));
                    }
                    let mut affected = Vec::new();
                    for (prefix, candidate) in &after {
                        let paths: Vec<_> = changed
                            .iter()
                            .filter(|path| path.starts_with(prefix))
                            .cloned()
                            .collect();
                        if !paths.is_empty() {
                            affected.push(PackageChange {
                                baseline: before[prefix],
                                candidate: *candidate,
                                paths,
                            });
                        }
                    }
                    Ok(SourceDelta {
                        paths: changed,
                        affected,
                    })
                },
                deadline,
            )?;
            baseline.validate(deadline)?;
            self.validate(deadline)?;
            Ok(delta)
        })();
        if result.is_err() {
            self.invalid.store(true, Ordering::Release);
        }
        result
    }
}

/// The original finite single-package profile remains a separate type. Its
/// constructor cannot silently acquire a different source population.
pub struct RepositorySource {
    inner: RepositorySources,
}
impl RepositorySource {
    pub fn capture(
        source: Arc<AdmittedPackageSource>,
        budget: Arc<DescriptorBudget>,
        deadline: Instant,
    ) -> io::Result<Self> {
        Ok(Self {
            inner: RepositorySources::capture(vec![source], budget, deadline)?,
        })
    }
    pub fn repository_root(&self) -> &Path {
        self.inner.repository_root()
    }
    pub fn commit(&self) -> String {
        self.inner.commit()
    }
    pub fn source(&self) -> &Arc<AdmittedPackageSource> {
        &self.inner.sources[0]
    }
    pub fn validate(&self, deadline: Instant) -> io::Result<()> {
        self.inner.validate(deadline)
    }
    pub fn require_candidate_of(
        &self,
        baseline: &Self,
        deadline: Instant,
    ) -> io::Result<Vec<PathBuf>> {
        Ok(self
            .inner
            .require_candidate_of(&baseline.inner, deadline)?
            .paths)
    }
}

impl State {
    fn control(
        &mut self,
        root: Arc<AdmittedDirectory>,
        relative: &Path,
        deadline: Instant,
    ) -> io::Result<bool> {
        let original = PathOriginal::capture(root, relative, &self.budget, deadline)?;
        let present = original.leaf.is_some();
        if original
            .leaf
            .as_ref()
            .is_some_and(|file| file.before.bytes > MAX_CONTROL_BYTES)
        {
            return Err(refused("Git control file exceeds native bound"));
        }
        self.controls.push(original);
        Ok(present)
    }
    fn validate(&self, deadline: Instant) -> io::Result<()> {
        for (root, before) in self.roots.iter().zip(&self.root_stamps) {
            root.validate(deadline)?;
            if directory_stamp(root, deadline)? != *before {
                return Err(refused("original repository/control directory changed"));
            }
        }
        self.packs.validate(&self.budget, deadline)?;
        for original in self.controls.iter().chain(self.objects.values()) {
            original.validate(&self.budget, deadline)?;
        }
        Ok(())
    }
    fn clean(&self, deadline: Instant) -> io::Result<()> {
        time(deadline)?;
        let index = self.repository.index().map_err(git)?;
        if index.len() > MAX_ENTRIES || index.has_conflicts() {
            return Err(refused(
                "native repository index is conflicted or exceeds bound",
            ));
        }
        for entry in index.iter() {
            if entry.flags & 0x8000 != 0 || entry.flags_extended & 0x6000 != 0 {
                return Err(refused(
                    "hidden, sparse or intent-to-add index scope is unsupported",
                ));
            }
        }
        let mut options = StatusOptions::new();
        options
            .include_untracked(true)
            .recurse_untracked_dirs(true)
            .include_ignored(true)
            .recurse_ignored_dirs(true)
            .exclude_submodules(false)
            .update_index(false);
        let statuses = self.repository.statuses(Some(&mut options)).map_err(git)?;
        if statuses.len() > MAX_ENTRIES
            || statuses
                .iter()
                .any(|entry| entry.status() != Status::CURRENT)
        {
            return Err(refused(
                "native source repository has dirty or unknown paths",
            ));
        }
        time(deadline)
    }
    fn object(
        &mut self,
        oid: Oid,
        kind: ObjectType,
        deadline: Instant,
    ) -> io::Result<ObjectObservation> {
        time(deadline)?;
        if let Some(original) = self.observations.get(&oid) {
            if original.kind != kind {
                return Err(refused("cached original Git object changed type"));
            }
            return Ok(original.clone());
        }
        if !self.objects.contains_key(&oid) {
            if self.objects.len() > MAX_ENTRIES {
                return Err(refused("native object population exceeds bound"));
            }
            let text = oid.to_string();
            let relative = PathBuf::from("objects").join(&text[..2]).join(&text[2..]);
            let original =
                PathOriginal::capture(self.common.clone(), &relative, &self.budget, deadline)?;
            self.objects.insert(oid, original);
        }
        // The actual native ODB validates type, size and content-addressed
        // bytes; original package SHA256 independently binds source content.
        let odb = self.repository.odb().map_err(git)?;
        let (size, actual) = odb.read_header(oid).map_err(git)?;
        if actual != kind || size > MAX_OBJECT_BYTES {
            return Err(refused("native Git object type/size is unsupported"));
        }
        self.read_bytes = self
            .read_bytes
            .checked_add(size)
            .filter(|sum| *sum <= MAX_READ_BYTES)
            .ok_or_else(|| refused("native Git object byte population exceeds bound"))?;
        let object = odb.read(oid).map_err(git)?;
        if object.kind() != kind
            || object.len() != size
            || Oid::hash_object(kind, object.data()).map_err(git)? != oid
        {
            return Err(refused("Git object bytes do not match their original ID"));
        }
        let observation = ObjectObservation {
            kind,
            bytes: object.len(),
            sha256: crate::tree::hash_bytes(object.data()),
        };
        self.observations.insert(oid, observation.clone());
        Ok(observation)
    }
    fn commit(&mut self, oid: Oid, deadline: Instant) -> io::Result<(Oid, Vec<Oid>)> {
        self.object(oid, ObjectType::Commit, deadline)?;
        let commit = self.repository.find_commit(oid).map_err(git)?;
        if commit.parent_count() > 64 {
            return Err(refused("commit parent population exceeds bound"));
        }
        Ok((commit.tree_id(), commit.parent_ids().collect()))
    }
    fn tree(&mut self, oid: Oid, deadline: Instant) -> io::Result<BTreeMap<PathBuf, (Oid, i32)>> {
        self.object(oid, ObjectType::Tree, deadline)?;
        let tree = self.repository.find_tree(oid).map_err(git)?;
        if tree.len() > MAX_ENTRIES {
            return Err(refused("Git tree population exceeds bound"));
        }
        tree.iter()
            .map(|entry| {
                let name = entry.name_bytes();
                if name.is_empty()
                    || name == b"."
                    || name == b".."
                    || name.contains(&b'/')
                    || name.contains(&0)
                {
                    return Err(refused("noncanonical Git tree name"));
                }
                Ok((
                    PathBuf::from(OsString::from_vec(name.to_vec())),
                    (entry.id(), entry.filemode()),
                ))
            })
            .collect()
    }
    fn matches_source(
        &mut self,
        mut tree: Oid,
        prefix: &Path,
        source: &AdmittedPackageSource,
        deadline: Instant,
    ) -> io::Result<()> {
        for component in prefix.components() {
            let Component::Normal(name) = component else {
                return Err(refused("source prefix is not canonical"));
            };
            let entries = self.tree(tree, deadline)?;
            let &(next, mode) = entries
                .get(Path::new(name))
                .ok_or_else(|| refused("held package is absent from candidate commit"))?;
            if mode != 0o040000 {
                return Err(refused("held package ancestor is not a Git directory"));
            }
            tree = next;
        }
        let originals = source
            .entries()
            .iter()
            .map(|entry| (entry.path.as_path(), entry))
            .collect::<BTreeMap<_, _>>();
        let mut seen = BTreeSet::new();
        let mut pending = vec![(PathBuf::new(), tree, 0usize)];
        while let Some((path, tree, depth)) = pending.pop() {
            if depth > MAX_DEPTH || seen.len() > MAX_ENTRIES {
                return Err(refused("committed package namespace exceeds bound"));
            }
            let directory = originals
                .get(path.as_path())
                .ok_or_else(|| refused("committed directory lacks the original package owner"))?;
            if !directory.directory {
                return Err(refused(
                    "committed package type differs from original source",
                ));
            }
            seen.insert(path.clone());
            for (name, (oid, mode)) in self.tree(tree, deadline)? {
                let path = path.join(name);
                if mode == 0o040000 {
                    pending.push((path, oid, depth + 1));
                    continue;
                }
                if mode != 0o100644 && mode != 0o100755 {
                    return Err(refused(
                        "symlink/submodule/special source requires another native owner",
                    ));
                }
                let original = originals
                    .get(path.as_path())
                    .ok_or_else(|| refused("commit has an unowned package file"))?;
                if original.directory || (original.mode & 0o111 != 0) != (mode == 0o100755) {
                    return Err(refused(
                        "committed executable mode differs from original package",
                    ));
                }
                let object = self.object(oid, ObjectType::Blob, deadline)?;
                if object.bytes as u64 != original.bytes
                    || original.sha256.as_deref() != Some(object.sha256.as_str())
                {
                    return Err(refused(
                        "candidate commit blob differs from SAME held source bytes",
                    ));
                }
                seen.insert(path);
            }
        }
        if seen.len() != originals.len() {
            return Err(refused(
                "held package has dirty, unknown or empty-directory scope outside its commit",
            ));
        }
        source.validate(deadline)
    }
    fn require_ancestor(&mut self, before: Oid, after: Oid, deadline: Instant) -> io::Result<()> {
        let mut pending = vec![after];
        let mut seen = BTreeSet::new();
        while let Some(oid) = pending.pop() {
            if oid == before {
                return Ok(());
            }
            if seen.insert(oid) {
                if seen.len() > MAX_HISTORY {
                    return Err(refused("native fast-forward ancestry exceeds bound"));
                }
                pending.extend(self.commit(oid, deadline)?.1);
            }
        }
        Err(refused(
            "candidate is not an ordinary fast-forward of original baseline",
        ))
    }
    fn delta(
        &mut self,
        before: Oid,
        after: Oid,
        prefixes: &[PathBuf],
        deadline: Instant,
    ) -> io::Result<Vec<PathBuf>> {
        let mut pending = vec![(PathBuf::new(), Some(before), Some(after), 0usize)];
        let mut changed = Vec::new();
        let mut visited = 0usize;
        while let Some((parent, before, after, depth)) = pending.pop() {
            if depth > MAX_DEPTH || visited > MAX_ENTRIES {
                return Err(refused("native commit delta exceeds namespace bound"));
            }
            if before == after {
                continue;
            }
            let left = before
                .map(|oid| self.tree(oid, deadline))
                .transpose()?
                .unwrap_or_default();
            let right = after
                .map(|oid| self.tree(oid, deadline))
                .transpose()?
                .unwrap_or_default();
            for name in left.keys().chain(right.keys()).collect::<BTreeSet<_>>() {
                visited += 1;
                let a = left.get(name).copied();
                let b = right.get(name).copied();
                if a == b {
                    continue;
                }
                let path = parent.join(name);
                if !prefixes
                    .iter()
                    .any(|prefix| path.starts_with(prefix) || prefix.starts_with(&path))
                {
                    return Err(refused(
                        "candidate commit contains changes outside validated package scope",
                    ));
                }
                let tree = |entry: Option<(Oid, i32)>| {
                    entry
                        .filter(|(_, mode)| *mode == 0o040000)
                        .map(|(oid, _)| oid)
                };
                let x = tree(a);
                let y = tree(b);
                if x.is_some() || y.is_some() {
                    if a.is_some() && x.is_none() || b.is_some() && y.is_none() {
                        return Err(refused(
                            "native repair replaces a directory with another input family",
                        ));
                    }
                    pending.push((path, x, y, depth + 1));
                } else {
                    if !prefixes.iter().any(|prefix| path.starts_with(prefix)) {
                        return Err(refused("candidate changes an unvalidated package ancestor"));
                    }
                    changed.push(path);
                    if changed.len() > MAX_CHANGED {
                        return Err(refused("native changed-file population exceeds bound"));
                    }
                }
            }
        }
        changed.sort();
        Ok(changed)
    }
}

#[cfg(all(test, target_os = "macos", target_arch = "aarch64"))]
mod tests;
