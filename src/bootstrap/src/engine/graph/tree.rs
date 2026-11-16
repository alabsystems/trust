//! Trust: complete finite package namespace custody for actual native tasks.
//! No hidden exclusions, source mutation, SDK freeze or completion constructor.

use std::ffi::{CStr, CString, OsString};
use std::os::fd::IntoRawFd as _;
use std::os::unix::ffi::OsStringExt as _;
use std::ptr::NonNull;

use super::*;

// Includes the original source directory and EVERY retained file/ancestor/empty
// directory, not merely file count. Keep traversal/listing scratch headroom at
// NOFILE=256; ordinary OS exhaustion still refuses rather than dropping owners.
const MAX_DESCRIPTORS: usize = 96;
const SCRATCH_RESERVE: u64 = 66;

pub(super) struct Membership {
    directories: BTreeMap<PathBuf, Vec<OsString>>,
}

fn descriptor_budget() -> Result<usize, GraphError> {
    let mut limit = std::mem::MaybeUninit::<libc::rlimit>::uninit();
    if unsafe { libc::getrlimit(libc::RLIMIT_NOFILE, limit.as_mut_ptr()) } != 0 {
        return Err(std::io::Error::last_os_error().into());
    }
    #[allow(
        clippy::unnecessary_cast,
        reason = "Trust: libc rlim_t can be 32-bit c_ulong on Linux; normalize before the existing u64 reserve arithmetic"
    )]
    let limit = unsafe { limit.assume_init() }.rlim_cur as u64;
    Ok(limit.saturating_sub(SCRATCH_RESERVE).min(MAX_DESCRIPTORS as u64) as usize)
}
fn room(parents: usize, files: usize, budget: usize) -> Result<(), GraphError> {
    if parents.checked_add(files).and_then(|n| n.checked_add(2)).is_none_or(|n| n > budget) {
        return Err(GraphError::InvalidReadSet("complete tree descriptor budget exceeded"));
    }
    Ok(())
}
fn directory_valid(meta: &Metadata) -> bool {
    meta.is_dir() && meta.uid() == unsafe { libc::geteuid() } && meta.mode() & 0o022 == 0
}
fn named(parent: i32, name: &CStr) -> Result<libc::stat, GraphError> {
    let mut stat = std::mem::MaybeUninit::<libc::stat>::uninit();
    if unsafe { libc::fstatat(parent, name.as_ptr(), stat.as_mut_ptr(), libc::AT_SYMLINK_NOFOLLOW) }
        != 0
    {
        return Err(std::io::Error::last_os_error().into());
    }
    Ok(unsafe { stat.assume_init() })
}
#[allow(
    clippy::unnecessary_cast,
    clippy::useless_conversion,
    reason = "Trust: this ABI-only mapping normalizes libc stat widths to Stamp; ino_t and signed time fields can be 32-bit on Linux, while macOS already has the destination widths"
)]
fn native_stamp(stat: libc::stat) -> Stamp {
    Stamp {
        dev: stat.st_dev as u64,
        ino: stat.st_ino as u64,
        bytes: stat.st_size as u64,
        mode: stat.st_mode as u32,
        uid: stat.st_uid,
        links: stat.st_nlink as u64,
        modified: (stat.st_mtime.into(), stat.st_mtime_nsec.into()),
        changed: (stat.st_ctime.into(), stat.st_ctime_nsec.into()),
    }
}

struct Listing(Option<NonNull<libc::DIR>>);
impl Listing {
    fn close(mut self) -> Result<(), GraphError> {
        let directory = self.0.take().unwrap();
        if unsafe { libc::closedir(directory.as_ptr()) } != 0 {
            return Err(std::io::Error::last_os_error().into());
        }
        Ok(())
    }
}
impl Drop for Listing {
    fn drop(&mut self) {
        if let Some(directory) = self.0.take() {
            // Only this listing's newly opened description, never an original.
            unsafe { libc::closedir(directory.as_ptr()) };
        }
    }
}
unsafe fn errno() -> *mut libc::c_int {
    #[cfg(target_os = "macos")]
    unsafe {
        libc::__error()
    }
    #[cfg(target_os = "linux")]
    unsafe {
        libc::__errno_location()
    }
}
fn names(parent: &Parent, deadline: Instant) -> Result<Vec<OsString>, GraphError> {
    before(deadline)?;
    if Stamp::of(&parent.file.metadata()?) != parent.stamp {
        return Err(GraphError::InputChanged(parent.path.clone()));
    }
    // A separate listing description leaves the actual retained directory's
    // cursor/flags untouched. It is never substituted for the original owner.
    let raw = unsafe {
        libc::openat(
            parent.file.as_raw_fd(),
            c".".as_ptr(),
            libc::O_RDONLY | libc::O_DIRECTORY | libc::O_NOFOLLOW | libc::O_CLOEXEC,
        )
    };
    if raw < 0 {
        return Err(std::io::Error::last_os_error().into());
    }
    let file = unsafe { File::from_raw_fd(raw) };
    if Stamp::of(&file.metadata()?) != parent.stamp {
        return Err(GraphError::InputChanged(parent.path.clone()));
    }
    let raw = file.into_raw_fd();
    let directory = unsafe { libc::fdopendir(raw) };
    let Some(directory) = NonNull::new(directory) else {
        let error = std::io::Error::last_os_error();
        unsafe { libc::close(raw) };
        return Err(error.into());
    };
    let listing = Listing(Some(directory));
    let mut result = Vec::new();
    loop {
        before(deadline)?;
        unsafe { *errno() = 0 };
        let entry = unsafe { libc::readdir(directory.as_ptr()) };
        if entry.is_null() {
            if unsafe { *errno() } != 0 {
                return Err(std::io::Error::last_os_error().into());
            }
            break;
        }
        let name = unsafe { CStr::from_ptr((*entry).d_name.as_ptr()) }.to_bytes();
        if name == b"." || name == b".." {
            continue;
        }
        if name.is_empty() || result.len() >= MAX_DESCRIPTORS {
            return Err(GraphError::InvalidReadSet(
                "complete tree directory population exceeds bound",
            ));
        }
        result.push(OsString::from_vec(name.to_vec()));
    }
    listing.close()?;
    if Stamp::of(&parent.file.metadata()?) != parent.stamp {
        return Err(GraphError::InputChanged(parent.path.clone()));
    }
    result.sort();
    if result.windows(2).any(|pair| pair[0] == pair[1]) {
        return Err(GraphError::InputChanged(parent.path.clone()));
    }
    Ok(result)
}

pub(in crate::engine::graph) fn capture<'owner>(
    owner: &'owner Outcome,
    subtree: &Path,
    deadline: Instant,
) -> Result<CapturedInputs<'owner>, GraphError> {
    capture_with(owner, subtree, deadline, |_| {})
}

// The production caller has no hook. Tests synchronize actual namespace races
// here rather than treating elapsed sleeps or fabricated observations as proof.
pub(super) fn capture_with<'owner>(
    owner: &'owner Outcome,
    subtree: &Path,
    deadline: Instant,
    mut after_listing: impl FnMut(&Path) + Send,
) -> Result<CapturedInputs<'owner>, GraphError> {
    normalized(subtree)?;
    run(owner, deadline, |deadline| {
        let original = owner
            .protected
            .as_ref()
            .unwrap()
            .native_graph_owner()
            .map_err(GraphError::OriginalOwner)?;
        let root = Arc::clone(original.source_root());
        root_matches(owner, &root)?;
        let root_stamp = Stamp::of(&root.metadata()?);
        let physical = root.path().join(subtree);
        original
            .source_directory_disjoint(&physical, (root_stamp.dev, root_stamp.ino))
            .map_err(GraphError::OriginalOwner)?;
        let budget = descriptor_budget()?;
        // Count the selected directory and every intermediate component before
        // opening that chain; low descriptor limits cannot bypass this budget.
        room(subtree.components().count() - 1, 0, budget)?;
        let (file, ancestors) = open_pinned(root.directory()?, subtree)?;
        room(ancestors.len(), 0, budget)?;
        let meta = file.metadata()?;
        if !directory_valid(&meta) {
            return Err(GraphError::InvalidReadSet(
                "source subtree is not a protected original directory",
            ));
        }
        let mut parents =
            ancestors.into_iter().map(|p| (p.path.clone(), p)).collect::<BTreeMap<_, _>>();
        parents.insert(
            subtree.to_owned(),
            Parent { path: subtree.to_owned(), file, stamp: Stamp::of(&meta) },
        );
        let mut directory_ids =
            parents.values().map(|p| (p.stamp.dev, p.stamp.ino)).collect::<BTreeSet<_>>();
        if directory_ids.len() != parents.len()
            || !directory_ids.insert((root_stamp.dev, root_stamp.ino))
        {
            return Err(GraphError::InvalidReadSet("source tree directory alias"));
        }
        for parent in parents.values() {
            original
                .source_directory_disjoint(&physical, (parent.stamp.dev, parent.stamp.ino))
                .map_err(GraphError::OriginalOwner)?;
        }
        let mut pending = vec![subtree.to_owned()];
        let mut membership = BTreeMap::new();
        let mut files = BTreeMap::new();
        let mut total = 0_u64;
        while let Some(path) = pending.pop() {
            before(deadline)?;
            let parent = &parents[&path];
            original
                .source_directory_disjoint(&physical, (parent.stamp.dev, parent.stamp.ino))
                .map_err(GraphError::OriginalOwner)?;
            let children = names(parent, deadline)?;
            after_listing(&path);
            // The map retains every original File throughout insertion/walking.
            let parent_fd = parent.file.as_raw_fd();
            for name in &children {
                before(deadline)?;
                let path = path.join(name);
                normalized(&path)?;
                let name = CString::new(name.as_bytes())
                    .map_err(|_| GraphError::InvalidReadSet("NUL in tree entry"))?;
                let selected = named(parent_fd, &name)?;
                let kind = selected.st_mode & libc::S_IFMT;
                if kind != libc::S_IFDIR && kind != libc::S_IFREG {
                    return Err(GraphError::InvalidReadSet(
                        "complete tree refuses symlink or special entry",
                    ));
                }
                room(parents.len(), files.len(), budget)?;
                let flags = libc::O_RDONLY
                    | libc::O_NOFOLLOW
                    | libc::O_NONBLOCK
                    | libc::O_CLOEXEC
                    | if kind == libc::S_IFDIR { libc::O_DIRECTORY } else { 0 };
                let raw = unsafe { libc::openat(parent_fd, name.as_ptr(), flags) };
                if raw < 0 {
                    return Err(std::io::Error::last_os_error().into());
                }
                let file = unsafe { File::from_raw_fd(raw) };
                let metadata = file.metadata()?;
                let stamp = Stamp::of(&metadata);
                if stamp != native_stamp(selected) {
                    return Err(GraphError::InputChanged(path));
                }
                if kind == libc::S_IFDIR {
                    if !directory_valid(&metadata) || !directory_ids.insert((stamp.dev, stamp.ino))
                    {
                        return Err(GraphError::InvalidReadSet(
                            "tree directory is unprotected or aliased",
                        ));
                    }
                    original
                        .source_directory_disjoint(&physical, (stamp.dev, stamp.ino))
                        .map_err(GraphError::OriginalOwner)?;
                    pending.push(path.clone());
                    parents.insert(path.clone(), Parent { path, file, stamp });
                } else {
                    if !valid(&metadata) || files.len() >= MAX_FILES {
                        return Err(GraphError::InvalidReadSet(
                            "tree file is not protected regular original",
                        ));
                    }
                    total = total
                        .checked_add(metadata.len())
                        .filter(|bytes| *bytes <= MAX_BYTES)
                        .ok_or(GraphError::InvalidReadSet(
                        "complete tree bytes exceed bound",
                    ))?;
                    let sha256 = digest(&file, &stamp, &path, deadline)?;
                    let observed =
                        InputObservation { path: path.clone(), bytes: stamp.bytes, sha256 };
                    files.insert(path.clone(), (Input { path, file, stamp }, observed));
                }
            }
            membership.insert(path, children);
        }
        let (entries, observations) = files.into_values().unzip();
        let captured = CapturedInputs {
            owner,
            observations,
            native: Inputs {
                root,
                root_stamp,
                entries,
                parents,
                invalid: AtomicBool::new(false),
                tree: Some(Membership { directories: membership }),
            },
        };
        validate(owner, &captured, deadline)?;
        Ok(captured)
    })
}

pub(super) fn validate_membership(
    inputs: &CapturedInputs<'_>,
    deadline: Instant,
) -> Result<(), GraphError> {
    if let Some(tree) = &inputs.native.tree {
        for (path, expected) in &tree.directories {
            if names(&inputs.native.parents[path], deadline)? != *expected {
                return Err(GraphError::InputChanged(path.clone()));
            }
        }
    }
    Ok(())
}
