use std::collections::{BTreeMap, BTreeSet};
use std::ffi::CString;
use std::fs::{File, Metadata};
use std::os::fd::{AsRawFd, BorrowedFd, FromRawFd};
use std::os::unix::ffi::OsStrExt;
use std::os::unix::fs::{FileExt, MetadataExt};
use std::path::{Component, Path, PathBuf};
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};
use std::time::Instant;

use build_helper::trust_repo_lock::management::OriginalSourceRoot;
use sha2::{Digest, Sha256};

use super::{CapturedInputs, Comparison, GraphError, InputObservation, InputPair};
use crate::engine::Outcome;

const MAX_FILES: usize = 256;
const MAX_BYTES: u64 = 64 * 1024 * 1024;

// Trust: complete finite source-subtree custody shares the existing real task
// executor; it is never a detached inventory or a reconstructed source owner.
#[path = "tree.rs"]
pub(super) mod tree;

#[derive(PartialEq, Eq)]
struct Stamp {
    dev: u64,
    ino: u64,
    bytes: u64,
    mode: u32,
    uid: u32,
    links: u64,
    modified: (i64, i64),
    changed: (i64, i64),
}
impl Stamp {
    fn of(meta: &Metadata) -> Self {
        Self {
            dev: meta.dev(),
            ino: meta.ino(),
            bytes: meta.len(),
            mode: meta.mode(),
            uid: meta.uid(),
            links: meta.nlink(),
            modified: (meta.mtime(), meta.mtime_nsec()),
            changed: (meta.ctime(), meta.ctime_nsec()),
        }
    }
}
struct Input {
    path: PathBuf,
    file: File,
    stamp: Stamp,
}
struct Parent {
    path: PathBuf,
    file: File,
    stamp: Stamp,
}
pub(super) struct Inputs {
    root: Arc<OriginalSourceRoot>,
    root_stamp: Stamp,
    entries: Vec<Input>,
    parents: BTreeMap<PathBuf, Parent>,
    invalid: AtomicBool,
    tree: Option<tree::Membership>,
}

fn before(deadline: Instant) -> Result<(), GraphError> {
    if Instant::now() >= deadline {
        Err(GraphError::Io(std::io::ErrorKind::TimedOut.into()))
    } else {
        Ok(())
    }
}

pub(super) fn check_owner(owner: &Outcome) -> Result<(), GraphError> {
    owner
        .protected
        .as_ref()
        .ok_or_else(|| GraphError::OriginalOwner("open scope absent".into()))?
        .native_graph_owner()
        .map_err(GraphError::OriginalOwner)?
        .check()
        .map_err(GraphError::OriginalOwner)?;
    if owner.completed.is_some() {
        owner.check_completed_runtime().map_err(GraphError::OriginalOwner)?;
    }
    Ok(())
}

pub(super) fn run<F, T>(owner: &Outcome, deadline: Instant, work: F) -> Result<T, GraphError>
where
    F: FnOnce(Instant) -> Result<T, GraphError> + Send,
    T: Send,
{
    before(deadline)?;
    check_owner(owner)?;
    let original = owner
        .protected
        .as_ref()
        .unwrap()
        .native_graph_owner()
        .map_err(GraphError::OriginalOwner)?;
    let result =
        crate::utils::metadata_scheduler::run_native_worker(original.identity(), deadline, work)?;
    check_owner(owner)?;
    before(deadline)?;
    result
}

fn normalized(path: &Path) -> Result<(), GraphError> {
    let mut normal = PathBuf::new();
    let mut count = 0;
    for part in path.components() {
        let Component::Normal(part) = part else {
            return Err(GraphError::InvalidReadSet("relative regular paths only"));
        };
        normal.push(part);
        count += 1;
    }
    if count == 0
        || count > 32
        || path.as_os_str().as_bytes().len() > 4096
        || normal.as_os_str().as_bytes() != path.as_os_str().as_bytes()
    {
        return Err(GraphError::InvalidReadSet("input path is empty or unnormalized"));
    }
    Ok(())
}

fn open(root: BorrowedFd<'_>, path: &Path) -> Result<File, GraphError> {
    open_pinned(root, path).map(|(file, _)| file)
}

fn open_pinned(root: BorrowedFd<'_>, path: &Path) -> Result<(File, Vec<Parent>), GraphError> {
    normalized(path)?;
    let mut directories = Vec::<Parent>::new();
    let mut relative = PathBuf::new();
    let parts = path.components().collect::<Vec<_>>();
    for (index, part) in parts.iter().enumerate() {
        let Component::Normal(part) = part else { unreachable!() };
        let name = CString::new(part.as_bytes())
            .map_err(|_| GraphError::InvalidReadSet("NUL in input path"))?;
        let parent = directories.last().map_or(root.as_raw_fd(), |entry| entry.file.as_raw_fd());
        let flags = libc::O_RDONLY
            | libc::O_CLOEXEC
            | libc::O_NOFOLLOW
            | libc::O_NONBLOCK
            | if index + 1 < parts.len() { libc::O_DIRECTORY } else { 0 };
        // SAFETY: bounded component, original retained directory, no mutation.
        let raw = unsafe { libc::openat(parent, name.as_ptr(), flags) };
        if raw < 0 {
            return Err(std::io::Error::last_os_error().into());
        }
        let file = unsafe { File::from_raw_fd(raw) };
        if index + 1 == parts.len() {
            return Ok((file, directories));
        }
        relative.push(part);
        let metadata = file.metadata()?;
        if !metadata.is_dir()
            || metadata.uid() != unsafe { libc::geteuid() }
            || metadata.mode() & 0o022 != 0
        {
            return Err(GraphError::InvalidReadSet("input ancestor is not protected original"));
        }
        directories.push(Parent { path: relative.clone(), stamp: Stamp::of(&metadata), file });
    }
    unreachable!()
}

fn valid(meta: &Metadata) -> bool {
    meta.is_file()
        && meta.nlink() == 1
        && meta.uid() == unsafe { libc::geteuid() }
        && meta.mode() & 0o022 == 0
}

fn digest(
    file: &File,
    stamp: &Stamp,
    path: &Path,
    deadline: Instant,
) -> Result<[u8; 32], GraphError> {
    before(deadline)?;
    let first = file.metadata()?;
    if !valid(&first) || Stamp::of(&first) != *stamp {
        return Err(GraphError::InputChanged(path.to_owned()));
    }
    let mut hash = Sha256::new();
    let mut offset = 0;
    let mut chunk = [0; 65536];
    while offset < stamp.bytes {
        before(deadline)?;
        let limit = (stamp.bytes - offset).min(chunk.len() as u64) as usize;
        let count = match file.read_at(&mut chunk[..limit], offset) {
            Err(error) if error.kind() == std::io::ErrorKind::Interrupted => continue,
            result => result?,
        };
        if count == 0 {
            return Err(GraphError::InputChanged(path.to_owned()));
        }
        hash.update(&chunk[..count]);
        offset += count as u64;
    }
    let mut extra = [0];
    if file.read_at(&mut extra, offset)? != 0 || Stamp::of(&file.metadata()?) != *stamp {
        return Err(GraphError::InputChanged(path.to_owned()));
    }
    before(deadline)?;
    Ok(hash.finalize().into())
}

fn root_matches(owner: &Outcome, root: &Arc<OriginalSourceRoot>) -> Result<(), GraphError> {
    let original = owner
        .protected
        .as_ref()
        .unwrap()
        .native_graph_owner()
        .map_err(GraphError::OriginalOwner)?;
    if !Arc::ptr_eq(original.source_root(), root) {
        return Err(GraphError::OriginalOwner(
            "source belongs to another original scope owner".into(),
        ));
    }
    root.check_current()?;
    Ok(())
}

pub(super) fn capture<'owner>(
    owner: &'owner Outcome,
    paths: &[PathBuf],
    deadline: Instant,
) -> Result<CapturedInputs<'owner>, GraphError> {
    if paths.is_empty() || paths.len() > MAX_FILES {
        return Err(GraphError::InvalidReadSet("nonempty bounded selection required"));
    }
    let mut selected = BTreeSet::new();
    for path in paths {
        normalized(path)?;
        if !selected.insert(path) {
            return Err(GraphError::InvalidReadSet("duplicate selected input"));
        }
    }
    run(owner, deadline, |deadline| {
        let original = owner
            .protected
            .as_ref()
            .unwrap()
            .native_graph_owner()
            .map_err(GraphError::OriginalOwner)?;
        // Extend the SAME source owner captured before enrollment. No path
        // reopen, duplicate directory File or data-to-owner constructor.
        let root = Arc::clone(original.source_root());
        root_matches(owner, &root)?;
        let root_stamp = Stamp::of(&root.metadata()?);
        let mut entries = Vec::with_capacity(paths.len());
        let mut parents = BTreeMap::<PathBuf, Parent>::new();
        let mut observations = Vec::with_capacity(paths.len());
        let mut total = 0_u64;
        for path in paths {
            before(deadline)?;
            let (file, original_parents) = open_pinned(root.directory()?, path)?;
            for parent in original_parents {
                if let Some(original) = parents.get(&parent.path) {
                    if parent.stamp != original.stamp
                        || Stamp::of(&original.file.metadata()?) != original.stamp
                    {
                        return Err(GraphError::InputChanged(parent.path));
                    }
                } else {
                    parents.insert(parent.path.clone(), parent);
                }
            }
            let meta = file.metadata()?;
            if !valid(&meta) {
                return Err(GraphError::InvalidReadSet(
                    "selected input is not protected regular original",
                ));
            }
            total = total
                .checked_add(meta.len())
                .filter(|bytes| *bytes <= MAX_BYTES)
                .ok_or(GraphError::InvalidReadSet("selected input bytes exceed bound"))?;
            let stamp = Stamp::of(&meta);
            let sha256 = digest(&file, &stamp, path, deadline)?;
            if Stamp::of(&open(root.directory()?, path)?.metadata()?) != stamp {
                return Err(GraphError::InputChanged(path.clone()));
            }
            observations.push(InputObservation { path: path.clone(), bytes: stamp.bytes, sha256 });
            entries.push(Input { path: path.clone(), file, stamp });
        }
        root_matches(owner, &root)?;
        let captured = CapturedInputs {
            owner,
            observations,
            native: Inputs {
                root,
                root_stamp,
                entries,
                parents,
                invalid: AtomicBool::new(false),
                tree: None,
            },
        };
        validate(owner, &captured, deadline)?;
        Ok(captured)
    })
}

pub(super) fn validate(
    owner: &Outcome,
    inputs: &CapturedInputs<'_>,
    deadline: Instant,
) -> Result<(), GraphError> {
    if inputs.native.invalid.load(Ordering::Acquire) {
        // Trust: a complete finite subtree may contain empty directories only.
        // Its failure is still terminal even without a selected regular file.
        return Err(GraphError::InputChanged(
            inputs
                .observations
                .first()
                .map_or_else(|| inputs.native.root.path().to_owned(), |entry| entry.path.clone()),
        ));
    }
    let result = (|| {
        root_matches(owner, &inputs.native.root)?;
        check_parents(inputs, deadline)?;
        tree::validate_membership(inputs, deadline)?;
        for (entry, observed) in inputs.native.entries.iter().zip(&inputs.observations) {
            before(deadline)?;
            if Stamp::of(&open(inputs.native.root.directory()?, &entry.path)?.metadata()?)
                != entry.stamp
                || digest(&entry.file, &entry.stamp, &entry.path, deadline)? != observed.sha256
                || Stamp::of(&open(inputs.native.root.directory()?, &entry.path)?.metadata()?)
                    != entry.stamp
            {
                return Err(GraphError::InputChanged(entry.path.clone()));
            }
        }
        tree::validate_membership(inputs, deadline)?;
        check_parents(inputs, deadline)?;
        root_matches(owner, &inputs.native.root)
    })();
    if result.is_err() {
        inputs.native.invalid.store(true, Ordering::Release);
    }
    result
}

fn check_parents(inputs: &CapturedInputs<'_>, deadline: Instant) -> Result<(), GraphError> {
    before(deadline)?;
    if Stamp::of(&inputs.native.root.metadata()?) != inputs.native.root_stamp {
        return Err(GraphError::InputChanged(inputs.native.root.path().to_owned()));
    }
    for parent in inputs.native.parents.values() {
        before(deadline)?;
        if Stamp::of(&parent.file.metadata()?) != parent.stamp
            || Stamp::of(&open(inputs.native.root.directory()?, &parent.path)?.metadata()?)
                != parent.stamp
            || Stamp::of(&parent.file.metadata()?) != parent.stamp
        {
            return Err(GraphError::InputChanged(parent.path.clone()));
        }
    }
    Ok(())
}

pub(super) fn read_input(
    inputs: &CapturedInputs<'_>,
    index: usize,
    deadline: Instant,
) -> Result<Vec<u8>, GraphError> {
    validate(inputs.owner, inputs, deadline)?;
    let entry = inputs
        .native
        .entries
        .get(index)
        .ok_or(GraphError::InvalidReadSet("task input index exceeds original selection"))?;
    let observed = &inputs.observations[index];
    let result = (|| {
        let length = usize::try_from(entry.stamp.bytes)
            .map_err(|_| GraphError::InvalidReadSet("input length exceeds address space"))?;
        let mut bytes = vec![0; length];
        let mut offset = 0;
        while offset < bytes.len() {
            before(deadline)?;
            let count = match entry.file.read_at(&mut bytes[offset..], offset as u64) {
                Err(error) if error.kind() == std::io::ErrorKind::Interrupted => continue,
                result => result?,
            };
            if count == 0 {
                return Err(GraphError::InputChanged(entry.path.clone()));
            }
            offset += count;
        }
        let actual: [u8; 32] = Sha256::digest(&bytes).into();
        if actual != observed.sha256 || Stamp::of(&entry.file.metadata()?) != entry.stamp {
            return Err(GraphError::InputChanged(entry.path.clone()));
        }
        validate(inputs.owner, inputs, deadline)?;
        Ok(bytes)
    })();
    if result.is_err() {
        inputs.native.invalid.store(true, Ordering::Release);
    }
    result
}

#[cfg(test)]
#[path = "tests.rs"]
mod tests;

pub(super) fn revalidate(
    owner: &Outcome,
    inputs: &CapturedInputs<'_>,
    deadline: Instant,
) -> Result<(), GraphError> {
    run(owner, deadline, |deadline| validate(owner, inputs, deadline))
}

pub(super) fn compare(
    owner: &Outcome,
    left: &CapturedInputs<'_>,
    right: &CapturedInputs<'_>,
    deadline: Instant,
) -> Result<Comparison, GraphError> {
    if left.observations.len() != right.observations.len() || left.observations.is_empty() {
        return Err(GraphError::InvalidReadSet(
            "nonempty paired selections must have equal populations",
        ));
    }
    run(owner, deadline, |deadline| {
        validate(owner, left, deadline)?;
        validate(owner, right, deadline)?;
        let pairs = left
            .observations
            .iter()
            .zip(&right.observations)
            .map(|(left, right)| InputPair {
                left: left.clone(),
                right: right.clone(),
                same_digest: left.bytes == right.bytes && left.sha256 == right.sha256,
            })
            .collect::<Vec<_>>();
        Ok(Comparison { all_digests_match: pairs.iter().all(|pair| pair.same_digest), pairs })
    })
}
