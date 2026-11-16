// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

//! Complete bounded current-target input custody, separate from loader images.
//! This is neither a functional SDK verdict nor writer exclusion, admission,
//! Ready, source finalization or proof. The caller retains its real SDK/Root
//! owners and this shared guard through actual retirement. Same-UID namespace
//! writers and the system runtime have the same explicit TCB as HeldProgram.

use std::collections::BTreeSet;
use std::ffi::CStr;
use std::os::fd::IntoRawFd as _;
use std::os::unix::ffi::OsStringExt as _;
#[cfg(not(all(target_os = "macos", target_arch = "aarch64")))]
use std::os::unix::fs::FileExt as _;
use std::ptr::NonNull;
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};

#[cfg(not(all(target_os = "macos", target_arch = "aarch64")))]
use sha2::Digest as _;
use sha2::{NativeSha256, Sha256};

use super::*;

const TARGET: &str = "aarch64-apple-darwin";
const MAX_DESCRIPTORS: usize = 2048;
const MAX_DEPTH: usize = 32;
const MAX_FILE_BYTES: u64 = 8 * 1024 * 1024 * 1024;
const MAX_BYTES: u64 = 32 * 1024 * 1024 * 1024;
const SCRATCH_RESERVE: u64 = 64;

struct Directory {
    file: File,
    before: Metadata,
    names: Option<Vec<OsString>>,
}
pub(super) struct Namespace {
    directories: BTreeMap<PathBuf, Directory>,
    files: BTreeMap<PathBuf, HeldFile>,
    root_before: Metadata,
    // Retain the selection made by the SAME descriptor-relative plan.
    selected_path: PathBuf,
    profile: NamespaceProfile,
    package_digest: Option<[u8; 32]>,
    invalid: AtomicBool,
}

pub(super) struct NamespacePlan {
    directories: BTreeMap<PathBuf, Directory>,
    planned: BTreeMap<PathBuf, Metadata>,
    root_before: Metadata,
    root_path: PathBuf,
    selected: PathBuf,
    profile: NamespaceProfile,
    deadline: Instant,
    invalid: AtomicBool,
}

// Both owners use the same descriptor-relative namespace machinery. The SDK
// profile and bounds stay unchanged; package custody has its own explicit scope.
#[derive(Clone, Copy)]
struct NamespaceProfile {
    descriptors: usize,
    file_bytes: u64,
    total_bytes: u64,
    depth: usize,
    root_selected: bool,
    reject_backend: bool,
    package_digest: bool,
    // Package custody belongs to one original graph. A mature shared sysroot
    // instead admits separately bounded consumers of the same held identity.
    timeout_is_terminal: bool,
}
const TARGET_PROFILE: NamespaceProfile = NamespaceProfile {
    descriptors: MAX_DESCRIPTORS,
    file_bytes: MAX_FILE_BYTES,
    total_bytes: MAX_BYTES,
    depth: MAX_DEPTH,
    root_selected: true,
    reject_backend: true,
    package_digest: false,
    timeout_is_terminal: false,
};
const PACKAGE_PROFILE: NamespaceProfile = NamespaceProfile {
    descriptors: 8192,
    file_bytes: 512 * 1024 * 1024,
    total_bytes: 512 * 1024 * 1024,
    depth: 64,
    root_selected: false,
    reject_backend: false,
    package_digest: true,
    timeout_is_terminal: true,
};

/// Live original-directory plan, consumed exactly once after native descriptor
/// admission. Its demand is data, never capacity, SDK or execution authority.
/// Original compiler/SDK directories and membership remain held; no manifest
/// can reconstruct this value or renew its original preparation deadline.
pub struct RustTargetSysrootPlan {
    compiler: Arc<HeldProgram>,
    namespace: NamespacePlan,
}

/// Original read-only files, complete directory membership and negative lookups
/// for ONE current target beneath the SAME held program's original SDK root.
/// Shared with Arc across units: capture/hash once, validate original backing at
/// each bookend. It does not cover other targets, external -L/extern inputs,
/// dynamic backend/plugin families or a whole Rust dependency closure.
/// No observations, saved manifests or hashes can reconstruct this owner.
pub struct HeldRustTargetSysroot {
    compiler: Arc<HeldProgram>,
    namespace: Namespace,
}

pub(super) fn package_budget() -> io::Result<usize> {
    Ok(native_budget()?.min(PACKAGE_PROFILE.descriptors))
}
fn budget() -> io::Result<usize> {
    Ok(native_budget()?.min(MAX_DESCRIPTORS))
}
fn native_budget() -> io::Result<usize> {
    let mut limit = std::mem::MaybeUninit::<libc::rlimit>::uninit();
    // SAFETY: one correctly sized output, no limit mutation.
    if unsafe { libc::getrlimit(libc::RLIMIT_NOFILE, limit.as_mut_ptr()) } != 0 {
        return Err(io::Error::last_os_error());
    }
    #[allow(
        clippy::unnecessary_cast,
        reason = "libc rlim_t is 32-bit on some Unix targets; reserve arithmetic uses u64"
    )]
    let available =
        (unsafe { limit.assume_init() }.rlim_cur as u64).saturating_sub(SCRATCH_RESERVE);
    // This preflight is not an assertion about unobserved current FD use. An
    // actual EMFILE/ENFILE always refuses too; never raise the process limit.
    Ok(usize::try_from(available).unwrap_or(usize::MAX))
}
fn room(directories: usize, files: usize, budget: usize) -> io::Result<()> {
    if directories.checked_add(files).and_then(|n| n.checked_add(1)).is_none_or(|n| n > budget) {
        return Err(refused("complete target sysroot descriptor capacity unavailable"));
    }
    Ok(())
}

pub(super) fn directory_entry(parent: &File, name: &OsStr) -> io::Result<bool> {
    let name = CString::new(name.as_bytes()).map_err(|_| refused("target name contains NUL"))?;
    let mut meta = std::mem::MaybeUninit::<libc::stat>::uninit();
    // SAFETY: original held parent, one bounded component and sized output;
    // no-follow kind admission refuses known special files before opening.
    if unsafe {
        libc::fstatat(
            parent.as_raw_fd(),
            name.as_ptr(),
            meta.as_mut_ptr(),
            libc::AT_SYMLINK_NOFOLLOW,
        )
    } != 0
    {
        return Err(io::Error::last_os_error());
    }
    let kind = unsafe { meta.assume_init() }.st_mode & libc::S_IFMT;
    if kind == libc::S_IFDIR {
        Ok(true)
    } else if kind == libc::S_IFREG {
        Ok(false)
    } else {
        Err(refused("target namespace contains a symlink or special file"))
    }
}

struct Listing(Option<NonNull<libc::DIR>>);
impl Listing {
    fn close(mut self) -> io::Result<()> {
        let pointer = self.0.take().unwrap();
        // SAFETY: this listing owns this fdopendir handle exactly once.
        if unsafe { libc::closedir(pointer.as_ptr()) } != 0 {
            return Err(io::Error::last_os_error());
        }
        Ok(())
    }
}
impl Drop for Listing {
    fn drop(&mut self) {
        if let Some(pointer) = self.0.take() {
            // SAFETY: only this scratch listing, never an original input FD.
            unsafe { libc::closedir(pointer.as_ptr()) };
        }
    }
}
#[cfg(any(target_os = "macos", target_os = "linux"))]
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
#[cfg(not(any(target_os = "macos", target_os = "linux")))]
pub(super) fn names(_: &File, _: Instant) -> io::Result<Vec<OsString>> {
    Err(io::ErrorKind::Unsupported.into())
}
#[cfg(any(target_os = "macos", target_os = "linux"))]
pub(super) fn names(file: &File, deadline: Instant) -> io::Result<Vec<OsString>> {
    time(deadline)?;
    let before = owned(file, true, false)?;
    // A fresh descriptor-relative listing never changes the original cursor.
    let scratch = openat(file.as_raw_fd(), OsStr::new("."), true)?;
    if stamp(&before) != stamp(&scratch.metadata()?) {
        return Err(refused("target directory changed before listing"));
    }
    let fd = scratch.into_raw_fd();
    // SAFETY: fd is a new owned directory description transferred on success.
    let raw = unsafe { libc::fdopendir(fd) };
    let Some(raw) = NonNull::new(raw) else {
        let error = io::Error::last_os_error();
        unsafe { libc::close(fd) };
        return Err(error);
    };
    let listing = Listing(Some(raw));
    let mut result = Vec::new();
    loop {
        time(deadline)?;
        // SAFETY: supported Unix errno slot and live listing; d_name is used
        // only until the next readdir and copied before that next call.
        unsafe { *errno() = 0 };
        #[cfg(target_os = "macos")]
        let entry = unsafe { libc::readdir(raw.as_ptr()) };
        #[cfg(target_os = "linux")]
        let entry = unsafe { libc::readdir64(raw.as_ptr()) };
        if entry.is_null() {
            if unsafe { *errno() } != 0 {
                return Err(io::Error::last_os_error());
            }
            break;
        }
        let name = unsafe { CStr::from_ptr((*entry).d_name.as_ptr()) }.to_bytes();
        if name == b"." || name == b".." {
            continue;
        }
        if name.is_empty() || name.contains(&b'/') || result.len() >= PACKAGE_PROFILE.descriptors {
            return Err(refused("target directory membership exceeds bound"));
        }
        result.push(OsString::from_vec(name.to_vec()));
    }
    listing.close()?;
    result.sort();
    if result.windows(2).any(|pair| pair[0] == pair[1])
        || stamp(&before) != stamp(&file.metadata()?)
    {
        return Err(refused("target directory changed while listing"));
    }
    Ok(result)
}

// Preserve the existing Targo v1 selected/canonical source digest while
// feeding original file bytes to both hashes during ONE positional read.
fn package_field(hash: &mut Sha256, bytes: &[u8]) {
    hash.update((bytes.len() as u64).to_le_bytes());
    hash.update(bytes);
}
fn package_header(
    hash: &mut Sha256,
    path: &Path,
    selected: &Path,
    metadata: &Metadata,
    directory: bool,
) -> io::Result<()> {
    let relative = path
        .strip_prefix(selected)
        .map_err(|_| refused("package digest entry escaped selected root"))?;
    package_field(hash, relative.as_os_str().as_bytes());
    package_field(hash, if directory { b"directory" } else { b"file" });
    for permission in [metadata.mode(), metadata.uid(), metadata.gid()] {
        hash.update(permission.to_le_bytes());
    }
    if !directory {
        hash.update(metadata.len().to_le_bytes());
    }
    Ok(())
}

impl NamespacePlan {
    fn capture(
        root: &File,
        root_path: &Path,
        deadline: Instant,
        capacity: usize,
        after_listing: impl FnMut(&Path),
    ) -> io::Result<Self> {
        Self::capture_selected(
            root,
            root_path,
            PathBuf::from("lib/rustlib").join(TARGET),
            TARGET_PROFILE,
            deadline,
            capacity,
            after_listing,
        )
    }
    #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
    pub(super) fn capture_package(
        root: &File,
        root_path: &Path,
        selected: PathBuf,
        deadline: Instant,
        capacity: usize,
    ) -> io::Result<Self> {
        Self::capture_selected(
            root,
            root_path,
            selected,
            PACKAGE_PROFILE,
            deadline,
            capacity,
            |_| {},
        )
    }
    fn capture_selected(
        root: &File,
        root_path: &Path,
        target: PathBuf,
        profile: NamespaceProfile,
        deadline: Instant,
        capacity: usize,
        mut after_listing: impl FnMut(&Path),
    ) -> io::Result<Self> {
        let root_before = owned(root, true, false)?;
        let mut directories: BTreeMap<PathBuf, Directory> = BTreeMap::new();
        let mut current = PathBuf::new();
        for component in target.components() {
            let Component::Normal(name) = component else {
                return Err(refused("invalid target component"));
            };
            time(deadline)?;
            room(directories.len() + 1, 0, capacity)?;
            let parent = if current.as_os_str().is_empty() {
                root
            } else {
                &directories.get(&current).ok_or_else(|| refused("target parent missing"))?.file
            };
            let file = openat(parent.as_raw_fd(), name, true)?;
            let before = owned(&file, true, false)?;
            current.push(name);
            directories.insert(current.clone(), Directory { file, before, names: None });
        }
        let mut pending = vec![target.clone()];
        let mut planned = BTreeMap::new();
        let mut identities = directories
            .values()
            .map(|dir| (dir.before.dev(), dir.before.ino()))
            .collect::<BTreeSet<_>>();
        if identities.len() != directories.len()
            || !identities.insert((root_before.dev(), root_before.ino()))
        {
            return Err(refused("target ancestors alias an original directory"));
        }
        let mut total = 0u64;
        while let Some(path) = pending.pop() {
            time(deadline)?;
            let members = names(&directories[&path].file, deadline)?;
            after_listing(&path);
            // The default built-in backend remains part of HeldProgram. A
            // directory of dynamically loaded backends needs its OWN closure;
            // mere recursive file ownership cannot establish that closure.
            if members.len() > profile.descriptors {
                return Err(refused("selected input directory population exceeds bound"));
            }
            if profile.reject_backend
                && path == target
                && members.iter().any(|name| name == "codegen-backends")
            {
                return Err(io::Error::new(
                    io::ErrorKind::Unsupported,
                    "dynamic target codegen backends are not owned by the supported profile",
                ));
            }
            for name in &members {
                time(deadline)?;
                let selected = path.join(name);
                if selected.components().count() > profile.depth
                    || selected.as_os_str().len() > MAX_PATH
                {
                    return Err(refused("target namespace depth/path exceeds bound"));
                }
                let is_directory = directory_entry(&directories[&path].file, name)?;
                let file = openat(directories[&path].file.as_raw_fd(), name, is_directory)?;
                let before = owned(&file, is_directory, false)?;
                if before.is_dir() {
                    room(directories.len() + 1, 0, capacity)?;
                    if !identities.insert((before.dev(), before.ino())) {
                        return Err(refused("target directory aliases an original directory"));
                    }
                    directories.insert(selected.clone(), Directory { file, before, names: None });
                    pending.push(selected);
                } else {
                    if before.len() > profile.file_bytes {
                        return Err(refused("target file size exceeds bound"));
                    }
                    total = total
                        .checked_add(before.len())
                        .ok_or_else(|| refused("target byte count overflow"))?;
                    if total > profile.total_bytes || planned.len() >= profile.descriptors {
                        return Err(refused("complete target population exceeds bound"));
                    }
                    planned.insert(selected, before);
                }
            }
            directories.get_mut(&path).unwrap().names = Some(members);
        }
        room(directories.len(), planned.len(), profile.descriptors)?;
        let result = Self {
            directories,
            planned,
            root_before,
            root_path: root_path.to_owned(),
            selected: target,
            profile,
            deadline,
            invalid: AtomicBool::new(false),
        };
        result.validate(root, deadline)?;
        Ok(result)
    }
    pub(super) fn checked(&self, operation: impl FnOnce() -> io::Result<()>) -> io::Result<()> {
        if self.invalid.load(Ordering::Acquire) {
            return Err(refused("original target plan is permanently invalid"));
        }
        let result = operation();
        if result.is_err() {
            self.invalid.store(true, Ordering::Release);
        }
        if result.is_ok() && self.invalid.load(Ordering::Acquire) {
            return Err(refused("original target plan failed a concurrent bookend"));
        }
        result
    }
    pub(super) fn validate(&self, root: &File, deadline: Instant) -> io::Result<()> {
        self.checked(|| {
            let deadline = deadline.min(self.deadline);
            time(deadline)?;
            if !same_directory(
                &self.root_before,
                &owned(root, true, false)?,
                self.profile.root_selected,
            ) {
                return Err(refused("original SDK plan root changed"));
            }
            for (path, held) in &self.directories {
                time(deadline)?;
                let parent = if path.parent().unwrap().as_os_str().is_empty() {
                    root
                } else {
                    &self.directories[path.parent().unwrap()].file
                };
                let named = openat(parent.as_raw_fd(), path.file_name().unwrap(), true)?;
                if stamp(&owned(&held.file, true, false)?) != stamp(&held.before)
                    || stamp(&owned(&named, true, false)?) != stamp(&held.before)
                {
                    return Err(refused("original target plan directory changed"));
                }
                if let Some(expected) = &held.names
                    && names(&held.file, deadline)? != *expected
                {
                    return Err(refused("original target plan membership changed"));
                }
            }
            for (path, before) in &self.planned {
                time(deadline)?;
                let selected = openat(
                    self.directories[path.parent().unwrap()].file.as_raw_fd(),
                    path.file_name().unwrap(),
                    false,
                )?;
                if stamp(&owned(&selected, false, false)?) != stamp(before) {
                    return Err(refused("original target plan file changed"));
                }
            }
            time(deadline)
        })
    }
    pub(super) fn materialize(
        self,
        root: &File,
        deadline: Instant,
        capacity: usize,
    ) -> io::Result<Namespace> {
        let deadline = deadline.min(self.deadline);
        self.validate(root, deadline)?;
        let Self { directories, planned, root_before, root_path, selected, profile, .. } = self;
        // Every target entry is counted BEFORE keeping every data-file FD.
        // At NOFILE=256 a 507-file SDK refuses; it is never truncated to128/96.
        room(directories.len(), planned.len(), capacity)?;
        let mut files = BTreeMap::new();
        let mut package_hash = profile.package_digest.then(Sha256::new);
        if let Some(hash) = package_hash.as_mut() {
            let root = root_path.join(&selected);
            package_field(hash, b"targo-read-only-source-tree-v1");
            package_field(hash, root.as_os_str().as_bytes());
            package_field(hash, root.as_os_str().as_bytes());
        }
        let mut directory_headers = directories.iter().peekable();
        for (path, before) in planned {
            time(deadline)?;
            let parent = &directories[path.parent().unwrap()].file;
            let file = openat(parent.as_raw_fd(), path.file_name().unwrap(), false)?;
            if stamp(&owned(&file, false, false)?) != stamp(&before) {
                return Err(refused("target input replaced during capture"));
            }
            if let Some(hash) = package_hash.as_mut() {
                while directory_headers.peek().is_some_and(|(name, _)| *name < &path) {
                    time(deadline)?;
                    let (name, directory) = directory_headers.next().unwrap();
                    package_header(hash, name, &selected, &directory.before, true)?;
                }
                package_header(hash, &path, &selected, &before, false)?;
            }
            // The same SHA-256 digest as the portable package aggregate. Use the
            // existing native compression for complete target file observations,
            // as HeldProgram already does for the compiler/runtime images.
            let mut hash = NativeSha256::new();
            let mut offset = 0u64;
            let mut buffer = [0u8; 65536];
            while offset < before.len() {
                time(deadline)?;
                let wanted = (before.len() - offset).min(buffer.len() as u64) as usize;
                let count = file.read_at(&mut buffer[..wanted], offset)?;
                if count == 0 {
                    return Err(refused("target input shortened during capture"));
                }
                hash.update(&buffer[..count]);
                if let Some(package) = package_hash.as_mut() {
                    package.update(&buffer[..count]);
                }
                offset += count as u64;
            }
            if file.read_at(&mut buffer[..1], offset)? != 0
                || stamp(&file.metadata()?) != stamp(&before)
            {
                return Err(refused("target input changed while reading original bytes"));
            }
            let observation = FileObservation {
                path: root_path.join(&path),
                sha256: crate::schema::hex(&hash.finalize()),
                bytes: before.len(),
                device: before.dev(),
                inode: before.ino(),
            };
            files.insert(path, HeldFile { file, before, observation });
        }
        if let Some(hash) = package_hash.as_mut() {
            for (name, directory) in directory_headers {
                time(deadline)?;
                package_header(hash, name, &selected, &directory.before, true)?;
            }
        }
        let package_digest: Option<[u8; 32]> = package_hash.map(|hash| hash.finalize().into());
        let result = Namespace {
            directories,
            files,
            root_before,
            selected_path: root_path.join(&selected),
            profile,
            package_digest,
            invalid: AtomicBool::new(false),
        };
        result.validate(root, deadline)?;
        Ok(result)
    }
}

impl Namespace {
    pub(super) fn original_directory_identity(&self, path: &Path) -> io::Result<(u64, u64)> {
        let held = self
            .directories
            .get(path)
            .ok_or_else(|| refused("original selected namespace directory absent"))?;
        Ok((held.before.dev(), held.before.ino()))
    }
    fn selected_directory(&self, root: &File, deadline: Instant) -> io::Result<PathBuf> {
        self.validate(root, deadline)?;
        Ok(self.selected_path.clone())
    }
    #[cfg(test)]
    fn capture(
        root: &File,
        root_path: &Path,
        deadline: Instant,
        capacity: usize,
        after_listing: impl FnMut(&Path),
    ) -> io::Result<Self> {
        NamespacePlan::capture(root, root_path, deadline, capacity, after_listing)?
            .materialize(root, deadline, capacity)
    }
    pub(super) fn checked(&self, operation: impl FnOnce() -> io::Result<()>) -> io::Result<()> {
        if self.invalid.load(Ordering::Acquire) {
            return Err(refused("original target sysroot is permanently invalid"));
        }
        let result = operation();
        // A shared sysroot's expired consumer did not change its identity;
        // later admitted consumers still perform every original bookend.
        // Package custody is graph-bound: observed deadline/unknown failures
        // remain terminal, even if a later caller supplies more time.
        if result.as_ref().is_err_and(|error| {
            self.profile.timeout_is_terminal || error.kind() != io::ErrorKind::TimedOut
        }) {
            self.invalid.store(true, Ordering::Release);
        }
        // A simultaneous failed bookend cannot be cleared by this success.
        if result.is_ok() && self.invalid.load(Ordering::Acquire) {
            return Err(refused("original target sysroot failed a concurrent bookend"));
        }
        result
    }
    pub(super) fn validate(&self, root: &File, deadline: Instant) -> io::Result<()> {
        self.checked(|| {
            time(deadline)?;
            if !same_directory(
                &self.root_before,
                &owned(root, true, false)?,
                self.profile.root_selected,
            ) {
                return Err(refused("original SDK directory changed"));
            }
            for (path, held) in &self.directories {
                time(deadline)?;
                let parent = if path.parent().unwrap().as_os_str().is_empty() {
                    root
                } else {
                    &self.directories[path.parent().unwrap()].file
                };
                let named = openat(parent.as_raw_fd(), path.file_name().unwrap(), true)?;
                if stamp(&owned(&held.file, true, false)?) != stamp(&held.before)
                    || stamp(&owned(&named, true, false)?) != stamp(&held.before)
                {
                    return Err(refused("original target directory changed"));
                }
                if let Some(expected) = &held.names
                    && names(&held.file, deadline)? != *expected
                {
                    return Err(refused("original target membership changed"));
                }
            }
            for (path, held) in &self.files {
                time(deadline)?;
                let current = openat(
                    self.directories[path.parent().unwrap()].file.as_raw_fd(),
                    path.file_name().unwrap(),
                    false,
                )?;
                if stamp(&owned(&held.file, false, false)?) != stamp(&held.before)
                    || stamp(&owned(&current, false, false)?) != stamp(&held.before)
                {
                    return Err(refused("original target file bytes/backing changed"));
                }
            }
            time(deadline)
        })
    }
}

impl NamespacePlan {
    pub(super) fn original_deadline(&self) -> Instant {
        self.deadline
    }
    pub(super) fn additional_descriptors(&self) -> usize {
        self.planned.len()
    }
}
impl Namespace {
    pub(super) fn package_entries(
        &self,
        selected: &Path,
    ) -> Vec<super::package_source::PackageEntry> {
        let mut entries = self
            .directories
            .iter()
            .map(|(path, d)| {
                super::package_source::PackageEntry::from_metadata(
                    path.strip_prefix(selected).unwrap(),
                    &d.before,
                    None,
                )
            })
            .chain(self.files.iter().map(|(path, f)| {
                super::package_source::PackageEntry::from_metadata(
                    path.strip_prefix(selected).unwrap(),
                    &f.before,
                    Some(&f.observation.sha256),
                )
            }))
            .collect::<Vec<_>>();
        entries.sort_by(|a, b| a.path.cmp(&b.path));
        entries
    }
    pub(super) fn package_digest(&self) -> io::Result<[u8; 32]> {
        self.package_digest.ok_or_else(|| refused("namespace has no package content scope"))
    }
    pub(super) fn read_package_file(&self, path: &Path, deadline: Instant) -> io::Result<Vec<u8>> {
        let held =
            self.files.get(path).ok_or_else(|| refused("unselected original package file"))?;
        let length = usize::try_from(held.before.len())
            .map_err(|_| refused("package input length overflow"))?;
        let mut bytes = vec![0; length];
        let mut at = 0;
        while at < bytes.len() {
            time(deadline)?;
            let count = held.file.read_at(&mut bytes[at..], at as u64)?;
            if count == 0 {
                return Err(refused("original package input shortened"));
            }
            at += count;
        }
        Ok(bytes)
    }
}

impl HeldRustTargetSysroot {
    /// Capture through the original HeldProgram root FD, in the caller's actual
    /// paid preparation. Current platform only; no fallback to another SDK.
    pub fn capture(compiler: Arc<HeldProgram>, deadline: Instant) -> io::Result<Self> {
        Self::plan(compiler, deadline)?.materialize(deadline)
    }
    /// Inspect complete membership while holding original directories, before
    /// materializing all data-file descriptions. The caller admits the live
    /// plan's actual demand in its existing paid Root/SDK preparation.
    pub fn plan(
        compiler: Arc<HeldProgram>,
        deadline: Instant,
    ) -> io::Result<RustTargetSysrootPlan> {
        if !cfg!(all(target_os = "macos", target_arch = "aarch64")) {
            return Err(io::ErrorKind::Unsupported.into());
        }
        compiler.validate(deadline)?;
        let root = &compiler
            .directories
            .get(compiler.root())
            .ok_or_else(|| refused("original SDK directory absent"))?
            .file;
        let namespace = NamespacePlan::capture(root, compiler.root(), deadline, budget()?, |_| {})?;
        compiler.validate(deadline)?;
        Ok(RustTargetSysrootPlan { compiler, namespace })
    }
    /// Captured byte observations only, not current validity or SDK authority.
    pub fn file_observations(&self) -> impl Iterator<Item = &FileObservation> {
        self.namespace.files.values().map(|held| &held.observation)
    }
    /// Path DATA for the complete namespace actually retained by this owner,
    /// after current original bookends. This excludes other SDK siblings and
    /// grants no read/write/SDK authority independently of this live owner.
    pub fn selected_directory(&self, deadline: Instant) -> io::Result<PathBuf> {
        self.validate(deadline)?;
        let root = &self
            .compiler
            .directories
            .get(self.compiler.root())
            .ok_or_else(|| refused("original SDK directory absent"))?
            .file;
        self.namespace.selected_directory(root, deadline)
    }
    pub fn validate(&self, deadline: Instant) -> io::Result<()> {
        self.namespace.checked(|| {
            self.compiler.validate(deadline)?;
            let root = &self
                .compiler
                .directories
                .get(self.compiler.root())
                .ok_or_else(|| refused("original SDK directory absent"))?
                .file;
            self.namespace.validate(root, deadline)
        })
    }
    /// Bind actual FINAL compiler argv and EFFECTIVE environment. No wrappers,
    /// argfiles, alternate targets/sysroots or dynamic backend/plugin loading
    /// are covered. External crate/search/source ownership remains separate.
    pub fn validate_invocation(
        &self,
        compiler: &Arc<HeldProgram>,
        program: &[u8],
        arg0: Option<&[u8]>,
        args: &[Vec<u8>],
        environment: &[(Vec<u8>, Vec<u8>)],
        deadline: Instant,
    ) -> io::Result<()> {
        self.namespace.checked(|| {
            self.validate(deadline)?;
            if !Arc::ptr_eq(compiler, &self.compiler)
                || program != self.compiler.program().as_os_str().as_bytes()
                || arg0.is_some_and(|value| value != program)
            {
                return Err(refused(
                    "target inputs do not belong to the SAME original SDK/compiler",
                ));
            }
            if environment.iter().any(|(name, value)| {
                matches!(name.as_slice(), b"RUSTC" | b"CARGO_BUILD_RUSTC")
                    && value.as_slice() != program
            }) {
                return Err(refused("effective environment selects another SDK compiler"));
            }
            let explicit = selection(self.compiler.root(), args, environment)?;
            // filesearch::default_sysroot derives this from the actual driver
            // dylib unless argv0 names a symlink (which exact no-follow image
            // custody forbids). Only these two supported driver locations
            // yield this SAME root. Explicit selection covers static/data
            // fixtures without pretending they are a usable Rust compiler.
            let default_bound = self.compiler.observation().runtime.iter().any(|image| {
                image.path.file_name().is_some_and(|name| {
                    name.as_bytes().starts_with(b"librustc_driver-")
                        && name.as_bytes().ends_with(b".dylib")
                }) && [
                    self.compiler.root().join("lib"),
                    self.compiler.root().join("lib/rustlib").join(TARGET).join("lib"),
                ]
                .iter()
                .any(|parent| image.path.parent() == Some(parent.as_path()))
            });
            if !explicit && !default_bound {
                return Err(refused("implicit sysroot is not bound to the original SDK driver"));
            }
            self.validate(deadline)
        })
    }
}

impl RustTargetSysrootPlan {
    /// Additional file FDs, derived from this live original namespace. Already
    /// held directories/runtime inputs must be included in native process
    /// occupancy; this number itself grants no capacity or ownership.
    pub fn additional_descriptors(&self) -> usize {
        self.namespace.planned.len()
    }
    /// Recheck original live inputs and original preparation deadline before
    /// native admission derives its demand. This reports data, never capacity.
    pub fn descriptor_demand(&self, deadline: Instant) -> io::Result<usize> {
        self.namespace.checked(|| {
            let deadline = deadline.min(self.namespace.deadline);
            self.compiler.validate(deadline)?;
            let root = &self
                .compiler
                .directories
                .get(self.compiler.root())
                .ok_or_else(|| refused("original SDK directory absent"))?
                .file;
            self.namespace.validate(root, deadline)?;
            self.compiler.validate(deadline)
        })?;
        Ok(self.additional_descriptors())
    }
    /// Consume this SAME live plan after admission. Actual current OS limits,
    /// original bytes/membership and original preparation deadline still apply.
    /// This method never changes process limits or creates execution authority.
    pub fn materialize(self, deadline: Instant) -> io::Result<HeldRustTargetSysroot> {
        let deadline = deadline.min(self.namespace.deadline);
        self.compiler.validate(deadline)?;
        let root = &self
            .compiler
            .directories
            .get(self.compiler.root())
            .ok_or_else(|| refused("original SDK directory absent"))?
            .file;
        let namespace = self.namespace.materialize(root, deadline, budget()?)?;
        self.compiler.validate(deadline)?;
        Ok(HeldRustTargetSysroot { compiler: self.compiler, namespace })
    }
}

fn selection(
    root: &Path,
    args: &[Vec<u8>],
    environment: &[(Vec<u8>, Vec<u8>)],
) -> io::Result<bool> {
    let mut target = false;
    let mut sysroot = false;
    let bytes = args
        .iter()
        .try_fold(0usize, |total, arg| total.checked_add(arg.len()))
        .ok_or_else(|| refused("target command size overflow"))?;
    if bytes > 16 * 1024 * 1024
        || args.len() > 16384
        || args.iter().any(|arg| arg.first() == Some(&b'@') || arg == b"--")
    {
        return Err(refused("target command has unsupported argfile/opaque syntax or size"));
    }
    let mut at = 0;
    while at < args.len() {
        let arg = args[at].as_slice();
        let mut option = |name: &[u8]| -> io::Result<Option<&[u8]>> {
            if arg == name {
                at += 1;
                return args
                    .get(at)
                    .map(|value| Some(value.as_slice()))
                    .ok_or_else(|| refused("target selection option has no value"));
            }
            Ok(arg.strip_prefix(name).and_then(|rest| rest.strip_prefix(b"=")))
        };
        if let Some(value) = option(b"--sysroot")? {
            if sysroot || value != root.as_os_str().as_bytes() {
                return Err(refused("compiler selects another or ambiguous sysroot"));
            }
            sysroot = true;
        } else if let Some(value) = option(b"--target")? {
            if target || value != TARGET.as_bytes() {
                return Err(io::Error::new(
                    io::ErrorKind::Unsupported,
                    "compiler target is outside original current-target custody",
                ));
            }
            target = true;
        } else {
            let value = if arg == b"-Z" || arg == b"-C" || arg == b"--codegen" {
                at += 1;
                Some(
                    args.get(at).ok_or_else(|| refused("compiler option has no value"))?.as_slice(),
                )
            } else if let Some(value) = arg.strip_prefix(b"--codegen=") {
                Some(value)
            } else if arg.starts_with(b"-Z") || arg.starts_with(b"-C") {
                Some(&arg[2..])
            } else {
                None
            };
            let unowned = if let Some(value) = value {
                let name = value.split(|byte| *byte == b'=').next().unwrap_or_default();
                if name.is_empty() {
                    return Err(refused("compiler option has no name"));
                }
                let normalized = name
                    .iter()
                    .map(|byte| if *byte == b'_' { b'-' } else { *byte })
                    .collect::<Vec<_>>();
                matches!(normalized.as_slice(), b"codegen-backend" | b"llvm-plugins" | b"llvm-args")
            } else {
                false
            };
            if unowned || arg.starts_with(b"--codegen-backend") {
                return Err(io::Error::new(
                    io::ErrorKind::Unsupported,
                    "dynamic backend/plugin selection requires its original native closure",
                ));
            }
        }
        at += 1;
    }
    for (name, value) in environment {
        if matches!(
            name.as_slice(),
            b"SYSROOT"
                | b"RUST_SYSROOT"
                | b"RUSTC_SYSROOT"
                | b"TRUST_SYSROOT"
                | b"RUST_TARGET_PATH"
                | b"RUSTC_CODEGEN_BACKEND"
                | b"RUSTC_WRAPPER"
                | b"RUSTC_WORKSPACE_WRAPPER"
        ) && !value.is_empty()
        {
            return Err(refused(
                "effective environment can replace target/sysroot/backend selection",
            ));
        }
    }
    Ok(sysroot)
}

#[cfg(test)]
mod tests;

#[cfg(test)]
#[path = "target_sysroot/native_hash_tests.rs"]
mod native_hash_tests;
