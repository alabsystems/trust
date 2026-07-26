//! Shared pathname identity guards for branded Tippy processes.
//!
//! These guards deliberately do not claim stable-handle execution. They keep
//! exact executable and directory handles live, revalidate before and after a
//! guarded operation, and reject results after detectable mutation. The
//! operation still opens resources by pathname, so a raced process can perform
//! side effects before the post-check rejects its result.
//! Conservatively recording ancestor contents also means unrelated direct-entry
//! churn in a shared writable ancestor can reject an otherwise valid result.

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

#[derive(Debug)]
struct AuthenticatedDirectory {
    path: PathBuf,
    snapshot: PathSnapshot,
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
        let (directories, selected_handles) = capture_directory_chain(&paths)?;
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
            let (snapshot, handle) = checked_directory(&expected.path)?;
            if snapshot != expected.snapshot {
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
            if opened_snapshot != expected.snapshot {
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
            if !expected.snapshot.same_path_metadata(&after_snapshot) || expected.snapshot != path_snapshot {
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

fn capture_directory_chain(paths: &[PathBuf]) -> Result<(Vec<AuthenticatedDirectory>, DirectoryChainGuard), String> {
    let mut directories = Vec::with_capacity(paths.len());
    let mut handles = Vec::with_capacity(paths.len());
    for path in paths {
        let (snapshot, handle) = checked_directory(path)?;
        directories.push(AuthenticatedDirectory {
            path: path.clone(),
            snapshot,
        });
        handles.push(handle);
    }
    Ok((directories, DirectoryChainGuard { handles }))
}

fn checked_directory(path: &Path) -> Result<(PathSnapshot, fs::File), String> {
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
    if !before_snapshot.same_path_metadata(&snapshot)
        || !snapshot.same_path_metadata(&after_snapshot)
        || snapshot != path_snapshot
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
