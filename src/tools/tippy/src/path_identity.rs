//! Shared pathname identity guards for branded Tippy processes.
//!
//! These guards deliberately do not claim stable-handle execution. They keep
//! exact executable and directory handles live, revalidate before and after a
//! guarded operation, and reject results after detectable mutation. The
//! operation still opens resources by pathname, so a raced process can perform
//! side effects before the post-check rejects its result.
//!
//! # What an ancestor directory is checked FOR
//!
//! The selected toolchain directory is held to its exact metadata: anything
//! that moves there moved the toolchain out from under the run. Its ANCESTORS
//! are held only to their AUTHORITY — identity (`device`/`inode`, or the
//! Windows volume/file id) plus the permission bits that decide who may
//! rewrite the chain (`mode`/`uid`/`gid`, or the Windows file attributes).
//!
//! That distinction is the whole point. The threat an ancestor check exists to
//! catch is a directory in the chain being REPLACED or REDIRECTED so the same
//! pathname resolves somewhere else; that necessarily changes its identity, and
//! a widened `mode` is caught for the same reason. What it must NOT catch is
//! ordinary churn — `len`, `mtime` and `ctime` on a directory move whenever ANY
//! unrelated entry is created or removed inside it, and the chain reaches all
//! the way to `/`. Comparing those made every guarded run a hostage to the
//! busiest shared directory on the machine: a file appearing in the user's home
//! directory, from any unrelated process, aborted an in-flight compile with
//! "changed identity or contents" — a failure with no relation to toolchain
//! integrity, and no action the user could take except "hold the machine still".

use std::fs;
use std::path::{Path, PathBuf};

pub(crate) const MAX_AUTHENTICATED_EXECUTABLE_BYTES: u64 = 1024 * 1024 * 1024;

/// Whether pathname metadata can own a Trust executable identity.
///
/// `FileType::is_symlink` does not cover every Windows reparse-point kind.
/// Reject the complete reparse class so a redirecting executable path cannot
/// grant its containing directory authority over selected toolchain siblings.
pub(crate) fn metadata_is_plain_file(metadata: &fs::Metadata) -> bool {
    if metadata.file_type().is_symlink() || !metadata.file_type().is_file() {
        return false;
    }

    #[cfg(windows)]
    {
        use std::os::windows::fs::MetadataExt as _;

        windows_file_attributes_are_plain(metadata.file_attributes())
    }
    #[cfg(not(windows))]
    {
        true
    }
}

#[cfg(windows)]
fn windows_file_attributes_are_plain(attributes: u32) -> bool {
    const FILE_ATTRIBUTE_REPARSE_POINT: u32 = 0x0000_0400;

    attributes & FILE_ATTRIBUTE_REPARSE_POINT == 0
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct PathSnapshot {
    pub(crate) len: u64,
    #[cfg(unix)]
    device: u64,
    #[cfg(unix)]
    inode: u64,
    #[cfg(unix)]
    mode: u32,
    #[cfg(unix)]
    links: u64,
    #[cfg(unix)]
    uid: u32,
    #[cfg(unix)]
    gid: u32,
    #[cfg(unix)]
    modified_seconds: i64,
    #[cfg(unix)]
    modified_nanoseconds: i64,
    #[cfg(unix)]
    changed_seconds: i64,
    #[cfg(unix)]
    changed_nanoseconds: i64,
    #[cfg(windows)]
    volume_serial_number: Option<u64>,
    #[cfg(windows)]
    file_id: Option<[u8; 16]>,
    #[cfg(windows)]
    file_attributes: u32,
    #[cfg(windows)]
    creation_time: u64,
    #[cfg(windows)]
    last_write_time: u64,
    #[cfg(windows)]
    change_time: Option<i64>,
    #[cfg(windows)]
    links: Option<u32>,
}

impl PathSnapshot {
    #[cfg(unix)]
    fn from_metadata(
        metadata: &fs::Metadata,
        _opened: Option<&fs::File>,
        _path: &Path,
        _subject: &str,
    ) -> Result<Self, String> {
        use std::os::unix::fs::MetadataExt as _;

        Ok(Self {
            len: metadata.len(),
            device: metadata.dev(),
            inode: metadata.ino(),
            mode: metadata.mode(),
            links: metadata.nlink(),
            uid: metadata.uid(),
            gid: metadata.gid(),
            modified_seconds: metadata.mtime(),
            modified_nanoseconds: metadata.mtime_nsec(),
            changed_seconds: metadata.ctime(),
            changed_nanoseconds: metadata.ctime_nsec(),
        })
    }

    #[cfg(windows)]
    fn from_metadata(
        metadata: &fs::Metadata,
        opened: Option<&fs::File>,
        path: &Path,
        subject: &str,
    ) -> Result<Self, String> {
        use std::os::windows::fs::MetadataExt as _;

        let identity = opened
            .map(windows_file_identity)
            .transpose()
            .map_err(|error| format!("cannot identify opened {subject} `{}`: {error}", path.display()))?;
        Ok(Self {
            len: metadata.len(),
            volume_serial_number: identity.as_ref().map(|identity| identity.volume_serial_number),
            file_id: identity.as_ref().map(|identity| identity.file_id),
            file_attributes: metadata.file_attributes(),
            creation_time: metadata.creation_time(),
            last_write_time: metadata.last_write_time(),
            change_time: identity.as_ref().map(|identity| identity.change_time),
            links: identity.map(|identity| identity.links),
        })
    }

    #[cfg(not(any(unix, windows)))]
    fn from_metadata(
        _metadata: &fs::Metadata,
        _opened: Option<&fs::File>,
        path: &Path,
        subject: &str,
    ) -> Result<Self, String> {
        Err(format!(
            "cannot authenticate {subject} `{}` because this platform has no supported stable file-identity API",
            path.display()
        ))
    }

    pub(crate) fn same_file(&self, other: &Self) -> bool {
        #[cfg(unix)]
        {
            self.device == other.device && self.inode == other.inode
        }
        #[cfg(windows)]
        {
            self.volume_serial_number.is_some()
                && self.volume_serial_number == other.volume_serial_number
                && self.file_id.is_some()
                && self.file_id == other.file_id
        }
        #[cfg(not(any(unix, windows)))]
        {
            let _ = other;
            false
        }
    }

    /// Whether the LATER snapshot `other` of an ANCESTOR directory carries a
    /// metadata-tamper signature relative to `self`: its change time advanced
    /// while its modification time did not. On a directory the two move
    /// TOGETHER for entry churn (create/remove touches contents), but a
    /// RENAME — the redirect-and-restore race, where the ancestor is moved
    /// aside, a substitute serves pathname resolution, and the original is
    /// put back before revalidation — touches metadata only: ctime advances,
    /// mtime stands still. So this ordering-aware test is what lets the chain
    /// tolerate churn without tolerating the race
    /// (`compiler_guard_rejects_ancestor_redirect_restore_after_raced_child_runs`
    /// pins the race; `ancestor_churn_tests` pin the tolerance).
    ///
    /// Honest residual, matching the module's own "detectable mutation"
    /// framing: an attacker who can BOTH rename the ancestor AND write inside
    /// it can advance mtime to mask the signature — but writing inside every
    /// chain ancestor is same-uid authority, at which point the toolchain
    /// binaries themselves are writable and no directory guard can matter.
    pub(crate) fn metadata_tampered_since(&self, other: &Self) -> bool {
        #[cfg(unix)]
        {
            let ctime_advanced = (other.changed_seconds, other.changed_nanoseconds)
                > (self.changed_seconds, self.changed_nanoseconds);
            let mtime_advanced = (other.modified_seconds, other.modified_nanoseconds)
                > (self.modified_seconds, self.modified_nanoseconds);
            ctime_advanced && !mtime_advanced
        }
        #[cfg(windows)]
        {
            match (self.change_time, other.change_time) {
                (Some(before), Some(after)) => {
                    after > before && other.last_write_time <= self.last_write_time
                }
                // Without a change-time reading there is no signature to
                // examine; identity + attributes remain the authority checks.
                _ => false,
            }
        }
        #[cfg(not(any(unix, windows)))]
        {
            let _ = other;
            false
        }
    }

    /// Whether two snapshots of an ANCESTOR directory carry the same authority
    /// over the chain: the same directory object, with the same permission
    /// bits. Deliberately blind to `len`/`mtime` (and `links`, which counts
    /// subdirectories) — see the module docs: those move on unrelated entry
    /// churn, while a replaced or redirected directory cannot keep its
    /// identity, and a widened `mode`/changed owner cannot hide here. The
    /// rename-shaped `ctime` movement is NOT ignored — see
    /// [`Self::metadata_tampered_since`], which callers pair with this.
    pub(crate) fn same_directory_authority(&self, other: &Self) -> bool {
        if !self.same_file(other) {
            return false;
        }
        #[cfg(unix)]
        {
            self.mode == other.mode && self.uid == other.uid && self.gid == other.gid
        }
        #[cfg(windows)]
        {
            self.file_attributes == other.file_attributes
        }
        #[cfg(not(any(unix, windows)))]
        {
            false
        }
    }

    fn same_path_metadata(&self, other: &Self) -> bool {
        #[cfg(windows)]
        {
            self.len == other.len
                && self.file_attributes == other.file_attributes
                && self.creation_time == other.creation_time
                && self.last_write_time == other.last_write_time
        }
        #[cfg(not(windows))]
        {
            self == other
        }
    }
}

#[cfg(windows)]
struct WindowsFileIdentity {
    volume_serial_number: u64,
    file_id: [u8; 16],
    change_time: i64,
    links: u32,
}

#[cfg(windows)]
#[repr(C)]
#[derive(Clone, Copy)]
struct WindowsFileId128 {
    identifier: [u8; 16],
}

#[cfg(windows)]
#[repr(C)]
struct WindowsFileIdInformation {
    volume_serial_number: u64,
    file_id: WindowsFileId128,
}

#[cfg(windows)]
#[repr(C)]
struct WindowsFileBasicInformation {
    creation_time: i64,
    last_access_time: i64,
    last_write_time: i64,
    change_time: i64,
    file_attributes: u32,
    _padding: u32,
}

#[cfg(windows)]
#[repr(C)]
struct WindowsFileStandardInformation {
    allocation_size: i64,
    end_of_file: i64,
    links: u32,
    delete_pending: u8,
    directory: u8,
}

#[cfg(windows)]
const _: () = {
    // These are Win32 ABI structures written directly by
    // GetFileInformationByHandleEx. Keep their manually declared layouts
    // pinned even on Windows targets where this module is only cross-checked.
    assert!(std::mem::size_of::<WindowsFileId128>() == 16);
    assert!(std::mem::size_of::<WindowsFileIdInformation>() == 24);
    assert!(std::mem::size_of::<WindowsFileBasicInformation>() == 40);
    assert!(std::mem::size_of::<WindowsFileStandardInformation>() == 24);
};

#[cfg(windows)]
#[link(name = "kernel32")]
unsafe extern "system" {
    #[link_name = "GetFileInformationByHandleEx"]
    fn get_file_information_by_handle_ex(
        file: std::os::windows::io::RawHandle,
        information_class: i32,
        information: *mut std::ffi::c_void,
        information_size: u32,
    ) -> i32;
}

#[cfg(windows)]
fn windows_file_identity(file: &fs::File) -> std::io::Result<WindowsFileIdentity> {
    use std::mem::{MaybeUninit, size_of};
    use std::os::windows::io::AsRawHandle as _;

    let mut identity = MaybeUninit::<WindowsFileIdInformation>::uninit();
    const FILE_ID_INFO: i32 = 18;
    // SAFETY: `identity` is correctly sized/aligned output storage for
    // FILE_ID_INFO and `file` owns a live handle for the complete call.
    if unsafe {
        get_file_information_by_handle_ex(
            file.as_raw_handle(),
            FILE_ID_INFO,
            identity.as_mut_ptr().cast(),
            size_of::<WindowsFileIdInformation>() as u32,
        )
    } == 0
    {
        return Err(std::io::Error::last_os_error());
    }
    // SAFETY: a successful API call initialized the complete output structure.
    let identity = unsafe { identity.assume_init() };

    let mut basic = MaybeUninit::<WindowsFileBasicInformation>::uninit();
    const FILE_BASIC_INFO: i32 = 0;
    // SAFETY: `basic` is correctly sized/aligned output storage and the live
    // file handle is valid for the duration of the call.
    if unsafe {
        get_file_information_by_handle_ex(
            file.as_raw_handle(),
            FILE_BASIC_INFO,
            basic.as_mut_ptr().cast(),
            size_of::<WindowsFileBasicInformation>() as u32,
        )
    } == 0
    {
        return Err(std::io::Error::last_os_error());
    }
    // SAFETY: a successful API call initialized the complete output structure.
    let basic = unsafe { basic.assume_init() };

    let mut standard = MaybeUninit::<WindowsFileStandardInformation>::uninit();
    const FILE_STANDARD_INFO: i32 = 1;
    // SAFETY: `standard` is correctly sized/aligned output storage for
    // FILE_STANDARD_INFO and the live file handle remains valid.
    if unsafe {
        get_file_information_by_handle_ex(
            file.as_raw_handle(),
            FILE_STANDARD_INFO,
            standard.as_mut_ptr().cast(),
            size_of::<WindowsFileStandardInformation>() as u32,
        )
    } == 0
    {
        return Err(std::io::Error::last_os_error());
    }
    // SAFETY: a successful API call initialized the complete output structure.
    let standard = unsafe { standard.assume_init() };

    Ok(WindowsFileIdentity {
        volume_serial_number: identity.volume_serial_number,
        file_id: identity.file_id.identifier,
        change_time: basic.change_time,
        links: standard.links,
    })
}

pub(crate) struct OpenedExecutable {
    pub(crate) path: PathBuf,
    pub(crate) file: fs::File,
    pub(crate) snapshot: PathSnapshot,
}

impl OpenedExecutable {
    pub(crate) fn open(path: PathBuf, subject: &str) -> Result<Self, String> {
        let before = fs::symlink_metadata(&path)
            .map_err(|error| format!("required {subject} `{}` is unavailable: {error}", path.display()))?;
        let before_snapshot = checked_executable_snapshot(&path, subject, &before, None)?;
        let file = open_executable(&path)
            .map_err(|error| format!("could not open {subject} `{}`: {error}", path.display()))?;
        let opened = file
            .metadata()
            .map_err(|error| format!("could not inspect opened {subject} `{}`: {error}", path.display()))?;
        let snapshot = checked_executable_snapshot(&path, subject, &opened, Some(&file))?;
        let after = fs::symlink_metadata(&path)
            .map_err(|error| format!("could not re-inspect {subject} path `{}`: {error}", path.display()))?;
        let after_snapshot = checked_executable_snapshot(&path, subject, &after, None)?;
        let path_file = open_executable(&path)
            .map_err(|error| format!("could not reopen {subject} `{}`: {error}", path.display()))?;
        let path_metadata = path_file
            .metadata()
            .map_err(|error| format!("could not inspect reopened {subject} `{}`: {error}", path.display()))?;
        let path_snapshot = checked_executable_snapshot(&path, subject, &path_metadata, Some(&path_file))?;
        if !before_snapshot.same_path_metadata(&snapshot)
            || !snapshot.same_path_metadata(&after_snapshot)
            || snapshot != path_snapshot
        {
            return Err(format!(
                "{subject} `{}` changed identity, metadata, or length while it was opened",
                path.display()
            ));
        }
        Ok(Self { path, file, snapshot })
    }

    pub(crate) fn confirm_stable(&self, subject: &str) -> Result<(), String> {
        let opened = self.file.metadata().map_err(|error| {
            format!(
                "could not re-inspect opened {subject} `{}`: {error}",
                self.path.display()
            )
        })?;
        let opened_snapshot = checked_executable_snapshot(&self.path, subject, &opened, Some(&self.file))?;
        let after = fs::symlink_metadata(&self.path)
            .map_err(|error| format!("could not re-inspect {subject} path `{}`: {error}", self.path.display()))?;
        let after_snapshot = checked_executable_snapshot(&self.path, subject, &after, None)?;
        let path_file = open_executable(&self.path)
            .map_err(|error| format!("could not reopen {subject} `{}`: {error}", self.path.display()))?;
        let path_metadata = path_file.metadata().map_err(|error| {
            format!(
                "could not inspect reopened {subject} `{}`: {error}",
                self.path.display()
            )
        })?;
        let path_snapshot = checked_executable_snapshot(&self.path, subject, &path_metadata, Some(&path_file))?;
        if self.snapshot != opened_snapshot
            || !self.snapshot.same_path_metadata(&after_snapshot)
            || self.snapshot != path_snapshot
        {
            return Err(format!(
                "{subject} `{}` changed identity, length, or contents while it was authenticated",
                self.path.display()
            ));
        }
        Ok(())
    }
}

fn checked_executable_snapshot(
    path: &Path,
    subject: &str,
    metadata: &fs::Metadata,
    opened: Option<&fs::File>,
) -> Result<PathSnapshot, String> {
    if !metadata_is_plain_file(metadata) {
        return Err(format!(
            "{subject} `{}` is not a regular file or is a symlink/reparse point; selected Trust toolchain executables require a plain file",
            path.display()
        ));
    }
    if !metadata_is_executable(metadata) {
        return Err(format!("{subject} `{}` is not executable", path.display()));
    }
    let len = metadata.len();
    if len == 0 || len > MAX_AUTHENTICATED_EXECUTABLE_BYTES {
        return Err(format!(
            "{subject} `{}` size {len} is outside the required 1..={MAX_AUTHENTICATED_EXECUTABLE_BYTES} byte bound",
            path.display()
        ));
    }
    PathSnapshot::from_metadata(metadata, opened, path, subject)
}

#[derive(Debug)]
pub(crate) struct AuthenticatedExecutable {
    path: PathBuf,
    role: &'static str,
    snapshot: PathSnapshot,
    // On Windows this handle uses read-only sharing and therefore prevents a
    // same-length rewrite or replacement from being hidden by restoring the
    // writable creation/last-write timestamps before the next revalidation.
    _selected: fs::File,
}

impl AuthenticatedExecutable {
    pub(crate) fn capture(path: PathBuf, role: &'static str) -> Result<Self, String> {
        let subject = format!("toolchain executable {role}");
        let executable = OpenedExecutable::open(path.clone(), &subject)?;
        executable.confirm_stable(&subject)?;
        Ok(Self {
            path,
            role,
            snapshot: executable.snapshot,
            _selected: executable.file,
        })
    }

    pub(crate) fn run_guarded_for<T>(&self, operation_label: &str, operation: impl FnOnce() -> T) -> Result<T, String> {
        let guard = self
            .revalidate()
            .map_err(|error| format!("{} authentication failed before {operation_label}: {error}", self.role))?;
        let result = operation();
        let _post_guard = self.revalidate().map_err(|error| {
            format!(
                "{} identity changed while {operation_label} was running: {error}",
                self.role
            )
        })?;
        drop(guard);
        Ok(result)
    }

    fn revalidate(&self) -> Result<fs::File, String> {
        let subject = format!("toolchain executable {}", self.role);
        let executable = OpenedExecutable::open(self.path.clone(), &subject)?;
        executable.confirm_stable(&subject)?;
        if !executable.snapshot.same_file(&self.snapshot) || executable.snapshot != self.snapshot {
            return Err(format!(
                "selected {subject} `{}` changed identity, length, or contents",
                self.path.display()
            ));
        }
        Ok(executable.file)
    }
}

#[derive(Debug)]
pub(crate) struct AuthenticatedDirectoryChain {
    root: PathBuf,
    canonical_root: PathBuf,
    directories: Vec<AuthenticatedDirectory>,
    // Retain the selected directory objects from initial authentication until
    // the complete guarded operation finishes. Windows opens these without
    // FILE_SHARE_DELETE, preventing an otherwise timestamp-restorable
    // rename/redirect between capture and the latest pre-launch check.
    _selected_handles: DirectoryChainGuard,
}

/// What a directory in the chain is trusted for, and therefore how strictly it
/// is re-checked. See the module docs.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum DirectoryRole {
    /// The selected toolchain directory itself: exact metadata, no slack. A
    /// changed `mtime` here means the toolchain moved mid-run.
    Selected,
    /// A directory the selected one merely lives under (up to `/`): checked for
    /// authority only, because its content churn is other people's business.
    Ancestor,
}

#[derive(Debug)]
struct AuthenticatedDirectory {
    path: PathBuf,
    snapshot: PathSnapshot,
    role: DirectoryRole,
}

impl AuthenticatedDirectory {
    /// Whether `observed` still authenticates this directory, at the strictness
    /// its role demands.
    fn still_authentic(&self, observed: &PathSnapshot) -> bool {
        match self.role {
            DirectoryRole::Selected => &self.snapshot == observed,
            DirectoryRole::Ancestor => {
                self.snapshot.same_directory_authority(observed)
                    && !self.snapshot.metadata_tampered_since(observed)
            }
        }
    }
}

impl AuthenticatedDirectoryChain {
    pub(crate) fn capture(root: &Path) -> Result<Self, String> {
        if !root.is_absolute() {
            return Err(format!(
                "selected Trust toolchain directory `{}` is not absolute",
                root.display()
            ));
        }
        let canonical = root.canonicalize().map_err(|error| {
            format!(
                "could not canonicalize selected Trust toolchain directory `{}`: {error}",
                root.display()
            )
        })?;
        #[cfg(unix)]
        if canonical != root {
            return Err(format!(
                "selected Trust toolchain directory `{}` traverses a symlink or non-canonical path to `{}`",
                root.display(),
                canonical.display()
            ));
        }

        let paths = launch_and_canonical_ancestors(root, &canonical);
        let (directories, selected_handles) = capture_directory_chain(&paths, root, &canonical)?;
        let chain = Self {
            root: root.to_owned(),
            canonical_root: canonical,
            directories,
            _selected_handles: selected_handles,
        };
        chain.confirm_canonical_root()?;
        chain.confirm_stable_with_guard(&chain._selected_handles)?;
        let _ = chain.revalidate()?;
        Ok(chain)
    }

    pub(crate) fn revalidate(&self) -> Result<DirectoryChainGuard, String> {
        self.confirm_canonical_root()?;
        let mut handles = Vec::with_capacity(self.directories.len());
        for expected in &self.directories {
            let (snapshot, handle) = checked_directory(&expected.path, expected.role)?;
            if !expected.still_authentic(&snapshot) {
                return Err(format!(
                    "selected Trust toolchain directory ancestor `{}` changed identity or contents",
                    expected.path.display()
                ));
            }
            handles.push(handle);
        }
        let guard = DirectoryChainGuard { handles };
        self.confirm_stable_with_guard(&guard)?;
        self.confirm_canonical_root()?;
        Ok(guard)
    }

    fn confirm_canonical_root(&self) -> Result<(), String> {
        let canonical = self.root.canonicalize().map_err(|error| {
            format!(
                "could not re-canonicalize selected Trust toolchain directory `{}`: {error}",
                self.root.display()
            )
        })?;
        if canonical != self.canonical_root {
            return Err(format!(
                "selected Trust toolchain directory `{}` changed canonical target from `{}` to `{}`",
                self.root.display(),
                self.canonical_root.display(),
                canonical.display()
            ));
        }
        Ok(())
    }

    pub(crate) fn confirm_stable_with_guard(&self, guard: &DirectoryChainGuard) -> Result<(), String> {
        if guard.handles.len() != self.directories.len() {
            return Err(format!(
                "selected Trust toolchain directory chain `{}` lost an opened ancestor handle",
                self.root.display()
            ));
        }
        for (expected, handle) in self.directories.iter().zip(&guard.handles) {
            let opened = handle.metadata().map_err(|error| {
                format!(
                    "could not inspect opened Trust toolchain directory ancestor `{}`: {error}",
                    expected.path.display()
                )
            })?;
            let opened_snapshot = checked_directory_snapshot(&expected.path, &opened, Some(handle))?;
            if !expected.still_authentic(&opened_snapshot) {
                return Err(format!(
                    "selected Trust toolchain directory ancestor `{}` changed while it was opened",
                    expected.path.display()
                ));
            }
            let after = fs::symlink_metadata(&expected.path).map_err(|error| {
                format!(
                    "could not re-inspect Trust toolchain directory ancestor `{}`: {error}",
                    expected.path.display()
                )
            })?;
            let after_snapshot = checked_directory_snapshot(&expected.path, &after, None)?;
            let path_handle = open_directory(&expected.path, &after)?;
            let path_metadata = path_handle.metadata().map_err(|error| {
                format!(
                    "could not inspect reopened Trust toolchain directory ancestor `{}`: {error}",
                    expected.path.display()
                )
            })?;
            let path_snapshot = checked_directory_snapshot(&expected.path, &path_metadata, Some(&path_handle))?;
            if !expected.still_authentic(&after_snapshot) || !expected.still_authentic(&path_snapshot) {
                return Err(format!(
                    "selected Trust toolchain directory ancestor `{}` changed while process identity was checked",
                    expected.path.display()
                ));
            }
        }
        Ok(())
    }

    // This source module is compiled separately into both Tippy binaries. The
    // frontend uses explicit compiler-chain nesting; only the driver binary
    // needs this generic operation wrapper.
    #[allow(dead_code)]
    pub(crate) fn run_guarded_for<T>(&self, operation_label: &str, operation: impl FnOnce() -> T) -> Result<T, String> {
        let guard = self
            .revalidate()
            .map_err(|error| format!("directory-chain authentication failed before {operation_label}: {error}"))?;
        let result = operation();
        let _post_guard = self.revalidate().map_err(|error| {
            format!("directory-chain identity changed while {operation_label} was running: {error}")
        })?;
        drop(guard);
        Ok(result)
    }
}

#[derive(Debug)]
pub(crate) struct DirectoryChainGuard {
    handles: Vec<fs::File>,
}

fn launch_and_canonical_ancestors(launch: &Path, canonical: &Path) -> Vec<PathBuf> {
    let mut paths = Vec::new();
    for ancestor in launch.ancestors().chain(canonical.ancestors()) {
        if !paths.iter().any(|path| path == ancestor) {
            paths.push(ancestor.to_owned());
        }
    }
    paths
}

fn capture_directory_chain(
    paths: &[PathBuf],
    root: &Path,
    canonical_root: &Path,
) -> Result<(Vec<AuthenticatedDirectory>, DirectoryChainGuard), String> {
    let mut directories = Vec::with_capacity(paths.len());
    let mut handles = Vec::with_capacity(paths.len());
    for path in paths {
        // Both spellings of the selected directory are the selected directory;
        // on unix `capture` has already proven them equal, but Windows reaches
        // here with a canonical form that may differ from the launch path.
        let role = if path == root || path == canonical_root {
            DirectoryRole::Selected
        } else {
            DirectoryRole::Ancestor
        };
        let (snapshot, handle) = checked_directory(path, role)?;
        directories.push(AuthenticatedDirectory {
            path: path.clone(),
            snapshot,
            role,
        });
        handles.push(handle);
    }
    Ok((directories, DirectoryChainGuard { handles }))
}

fn checked_directory(path: &Path, role: DirectoryRole) -> Result<(PathSnapshot, fs::File), String> {
    let before = fs::symlink_metadata(path).map_err(|error| {
        format!(
            "selected Trust toolchain directory ancestor `{}` is unavailable: {error}",
            path.display()
        )
    })?;
    let before_snapshot = checked_directory_snapshot(path, &before, None)?;
    let handle = open_directory(path, &before)?;
    let opened = handle.metadata().map_err(|error| {
        format!(
            "could not inspect opened Trust toolchain directory ancestor `{}`: {error}",
            path.display()
        )
    })?;
    let snapshot = checked_directory_snapshot(path, &opened, Some(&handle))?;
    let after = fs::symlink_metadata(path).map_err(|error| {
        format!(
            "could not re-inspect Trust toolchain directory ancestor `{}`: {error}",
            path.display()
        )
    })?;
    let after_snapshot = checked_directory_snapshot(path, &after, None)?;
    let path_handle = open_directory(path, &after)?;
    let path_metadata = path_handle.metadata().map_err(|error| {
        format!(
            "could not inspect reopened Trust toolchain directory ancestor `{}`: {error}",
            path.display()
        )
    })?;
    let path_snapshot = checked_directory_snapshot(path, &path_metadata, Some(&path_handle))?;
    // The three re-reads above bracket the open. For the SELECTED directory
    // they must agree exactly; for an ancestor they need only agree on
    // authority, or an unrelated entry appearing between two `stat`s
    // microseconds apart would fail the capture (the very race that made this
    // guard fire on `$HOME`).
    // The rename-shaped tamper signature applies here exactly as it does in
    // `still_authentic`: `left` is always the EARLIER reading.
    let agrees = |left: &PathSnapshot, right: &PathSnapshot| match role {
        DirectoryRole::Selected => left.same_path_metadata(right),
        DirectoryRole::Ancestor => {
            left.same_directory_authority(right) && !left.metadata_tampered_since(right)
        }
    };
    let identical = |left: &PathSnapshot, right: &PathSnapshot| match role {
        DirectoryRole::Selected => left == right,
        DirectoryRole::Ancestor => {
            left.same_directory_authority(right) && !left.metadata_tampered_since(right)
        }
    };
    if !agrees(&before_snapshot, &snapshot)
        || !agrees(&snapshot, &after_snapshot)
        || !identical(&snapshot, &path_snapshot)
    {
        return Err(format!(
            "selected Trust toolchain directory ancestor `{}` changed while its identity was captured",
            path.display()
        ));
    }
    Ok((snapshot, handle))
}

fn checked_directory_snapshot(
    path: &Path,
    metadata: &fs::Metadata,
    opened: Option<&fs::File>,
) -> Result<PathSnapshot, String> {
    #[cfg(not(windows))]
    if metadata.file_type().is_symlink() {
        return Err(format!(
            "selected Trust toolchain directory ancestor `{}` is a symlink",
            path.display()
        ));
    }

    #[cfg(windows)]
    let is_directory = {
        use std::os::windows::fs::MetadataExt as _;

        const FILE_ATTRIBUTE_DIRECTORY: u32 = 0x0000_0010;
        metadata.file_attributes() & FILE_ATTRIBUTE_DIRECTORY != 0
    };
    #[cfg(not(windows))]
    let is_directory = metadata.file_type().is_dir();

    if !is_directory {
        return Err(format!(
            "selected Trust toolchain directory ancestor `{}` is not a directory",
            path.display()
        ));
    }
    PathSnapshot::from_metadata(metadata, opened, path, "Trust toolchain directory ancestor")
}

#[cfg(unix)]
fn open_directory(path: &Path, _metadata: &fs::Metadata) -> Result<fs::File, String> {
    fs::File::open(path).map_err(|error| {
        format!(
            "could not open selected Trust toolchain directory ancestor `{}`: {error}",
            path.display()
        )
    })
}

#[cfg(windows)]
fn open_directory(path: &Path, metadata: &fs::Metadata) -> Result<fs::File, String> {
    use std::os::windows::fs::OpenOptionsExt as _;

    use std::os::windows::fs::MetadataExt as _;

    const FILE_SHARE_READ: u32 = 0x0000_0001;
    const FILE_SHARE_WRITE: u32 = 0x0000_0002;
    const FILE_ATTRIBUTE_REPARSE_POINT: u32 = 0x0000_0400;
    const FILE_FLAG_BACKUP_SEMANTICS: u32 = 0x0200_0000;
    const FILE_FLAG_OPEN_REPARSE_POINT: u32 = 0x0020_0000;
    // Ordinary directories may still be traversed and written beneath while
    // selected. The directory object itself cannot be renamed or deleted.
    // A junction/symlink target is mutable data on the reparse object, so deny
    // write sharing there as well as delete sharing.
    let share_mode = if metadata.file_attributes() & FILE_ATTRIBUTE_REPARSE_POINT != 0 {
        FILE_SHARE_READ
    } else {
        FILE_SHARE_READ | FILE_SHARE_WRITE
    };
    fs::OpenOptions::new()
        .access_mode(0)
        .share_mode(share_mode)
        .custom_flags(FILE_FLAG_BACKUP_SEMANTICS | FILE_FLAG_OPEN_REPARSE_POINT)
        .open(path)
        .map_err(|error| {
            format!(
                "could not open selected Trust toolchain directory ancestor `{}`: {error}",
                path.display()
            )
        })
}

#[cfg(not(any(unix, windows)))]
fn open_directory(path: &Path, _metadata: &fs::Metadata) -> Result<fs::File, String> {
    Err(format!(
        "cannot open selected Trust toolchain directory ancestor `{}` because this platform has no supported directory-handle API",
        path.display()
    ))
}

#[cfg(not(windows))]
fn open_executable(path: &Path) -> std::io::Result<fs::File> {
    fs::File::open(path)
}

#[cfg(windows)]
fn open_executable(path: &Path) -> std::io::Result<fs::File> {
    use std::os::windows::fs::OpenOptionsExt as _;

    const FILE_SHARE_READ: u32 = 0x0000_0001;
    fs::OpenOptions::new()
        .read(true)
        // Deny write and delete sharing for the lifetime of every selected,
        // pre-operation, and post-operation executable handle.
        .share_mode(FILE_SHARE_READ)
        .open(path)
}

#[cfg(unix)]
fn metadata_is_executable(metadata: &fs::Metadata) -> bool {
    use std::os::unix::fs::PermissionsExt as _;

    metadata.permissions().mode() & 0o111 != 0
}

#[cfg(not(unix))]
fn metadata_is_executable(_metadata: &fs::Metadata) -> bool {
    true
}

#[cfg(all(test, windows))]
mod windows_tests {
    use super::{PathSnapshot, windows_file_attributes_are_plain};

    fn snapshot(volume_serial_number: u64, file_id: [u8; 16]) -> PathSnapshot {
        PathSnapshot {
            len: 1,
            volume_serial_number: Some(volume_serial_number),
            file_id: Some(file_id),
            file_attributes: 0,
            creation_time: 0,
            last_write_time: 0,
            change_time: Some(0),
            links: Some(1),
        }
    }

    #[test]
    fn full_volume_and_128_bit_file_id_are_identity_authority() {
        let base = snapshot(7, [0; 16]);
        assert!(base.same_file(&snapshot(7, [0; 16])));

        let mut colliding_legacy_id = [0; 16];
        colliding_legacy_id[15] = 1;
        assert!(
            !base.same_file(&snapshot(7, colliding_legacy_id)),
            "file IDs that agree in only 64 bits must remain distinct"
        );
        assert!(
            !base.same_file(&snapshot((1_u64 << 32) | 7, [0; 16])),
            "the complete 64-bit volume serial must participate in identity"
        );
    }

    #[test]
    fn every_windows_reparse_point_is_excluded_from_plain_file_authority() {
        const FILE_ATTRIBUTE_ARCHIVE: u32 = 0x0000_0020;
        const FILE_ATTRIBUTE_REPARSE_POINT: u32 = 0x0000_0400;

        assert!(windows_file_attributes_are_plain(FILE_ATTRIBUTE_ARCHIVE));
        assert!(!windows_file_attributes_are_plain(FILE_ATTRIBUTE_REPARSE_POINT));
        assert!(!windows_file_attributes_are_plain(
            FILE_ATTRIBUTE_ARCHIVE | FILE_ATTRIBUTE_REPARSE_POINT
        ));
    }
}

/// THE ANCESTOR-CHURN CONTRACT. A guarded run must survive an unrelated file
/// appearing in a directory it merely lives under, and must still refuse a
/// toolchain that actually moved. Both halves are pinned here because relaxing
/// the first is only safe while the second still holds.
#[cfg(all(test, unix))]
mod ancestor_churn_tests {
    use std::sync::atomic::{AtomicU64, Ordering};
    use std::time::{SystemTime, UNIX_EPOCH};
    use std::{env, fs};

    use super::AuthenticatedDirectoryChain;

    static NEXT_FIXTURE: AtomicU64 = AtomicU64::new(0);

    /// `<temp>/<unique>/ancestor/selected` — a private two-level chain, so the
    /// "ancestor" this test mutates is one this test owns. Canonicalized
    /// because `capture` refuses a path that traverses a symlink, and macOS
    /// hands out `/var/folders/...` behind one.
    fn fixture(label: &str) -> std::path::PathBuf {
        let nanos = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .expect("system clock after Unix epoch")
            .as_nanos();
        let sequence = NEXT_FIXTURE.fetch_add(1, Ordering::Relaxed);
        let temp = env::temp_dir().canonicalize().unwrap_or_else(|_| env::temp_dir());
        let root = temp.join(format!(
            "tippy-ancestor-churn-{label}-{}-{nanos}-{sequence}",
            std::process::id()
        ));
        fs::create_dir_all(root.join("ancestor").join("selected")).expect("create fixture chain");
        root
    }

    /// THE BUG THIS FIXES: a file appearing in a directory the toolchain merely
    /// lives under used to abort the run with "changed identity or contents".
    /// On a real machine that ancestor chain reaches `$HOME` and `/`, so any
    /// unrelated process could kill an in-flight compile.
    #[test]
    fn unrelated_entry_churn_in_an_ancestor_keeps_the_chain_authentic() {
        let root = fixture("churn");
        let ancestor = root.join("ancestor");
        let selected = ancestor.join("selected");
        let chain = AuthenticatedDirectoryChain::capture(&selected).expect("capture chain");

        // Exactly what an unrelated process does: create, then remove, an entry
        // in a shared ancestor. Both move the directory's len/mtime/ctime.
        fs::write(ancestor.join("unrelated.tmp"), b"noise").expect("write unrelated entry");
        chain.revalidate().expect("ancestor entry churn must not break authentication");
        fs::remove_file(ancestor.join("unrelated.tmp")).expect("remove unrelated entry");
        chain.revalidate().expect("removing an unrelated entry must not break it either");

        // A whole unrelated subdirectory also bumps the ancestor's link count.
        fs::create_dir(ancestor.join("unrelated-dir")).expect("create unrelated subdir");
        chain
            .revalidate()
            .expect("an unrelated subdirectory must not break authentication");

        let _ = fs::remove_dir_all(&root);
    }

    /// THE HALF THAT MUST NOT RELAX: the selected toolchain directory is still
    /// held to its exact metadata, so a binary appearing beside the compiler
    /// mid-run is still caught.
    #[test]
    fn content_change_in_the_selected_directory_is_still_rejected() {
        let root = fixture("selected");
        let selected = root.join("ancestor").join("selected");
        let chain = AuthenticatedDirectoryChain::capture(&selected).expect("capture chain");

        fs::write(selected.join("planted"), b"tamper").expect("write into selected directory");
        let verdict = chain.revalidate();
        assert!(
            verdict.is_err(),
            "a changed selected toolchain directory must still be refused",
        );

        let _ = fs::remove_dir_all(&root);
    }

    /// THE RACE THAT MUST STAY CAUGHT: renaming an ancestor aside and putting
    /// it back restores identity and permissions, but the rename leaves a
    /// metadata-only trail — ctime advances, mtime does not — and that
    /// signature is rejected. This is the redirect-and-restore scenario the
    /// compiler-fixture test pins end to end
    /// (`compiler_guard_rejects_ancestor_redirect_restore_after_raced_child_runs`);
    /// pinned here too so the property survives without the heavier fixture.
    #[test]
    fn a_renamed_and_restored_ancestor_is_still_rejected() {
        let root = fixture("redirect");
        let ancestor = root.join("ancestor");
        let parked = root.join("ancestor-parked");
        let selected = ancestor.join("selected");
        let chain = AuthenticatedDirectoryChain::capture(&selected).expect("capture chain");

        fs::rename(&ancestor, &parked).expect("rename ancestor aside");
        fs::rename(&parked, &ancestor).expect("restore ancestor");

        assert!(
            chain.revalidate().is_err(),
            "a redirect-and-restore must be refused even though identity is back",
        );

        let _ = fs::remove_dir_all(&root);
    }

    /// AUTHORITY IS STILL CHECKED: identity is not the only thing that matters
    /// about an ancestor — widening its permissions changes who may rewrite the
    /// chain, and that must still be refused.
    #[test]
    fn a_widened_ancestor_permission_is_still_rejected() {
        use std::os::unix::fs::PermissionsExt as _;

        let root = fixture("perm");
        let ancestor = root.join("ancestor");
        let selected = ancestor.join("selected");
        let chain = AuthenticatedDirectoryChain::capture(&selected).expect("capture chain");

        let original = fs::metadata(&ancestor).expect("ancestor metadata").permissions();
        let mut widened = original.clone();
        widened.set_mode(0o777);
        fs::set_permissions(&ancestor, widened).expect("widen ancestor permissions");

        let verdict = chain.revalidate();
        let _ = fs::set_permissions(&ancestor, original);
        assert!(
            verdict.is_err(),
            "a world-writable ancestor is a changed authority and must be refused",
        );

        let _ = fs::remove_dir_all(&root);
    }
}
