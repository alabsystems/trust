//! Full-width opened-handle identities for security-sensitive tool paths.
//!
//! Trust: Trust-authored, no upstream counterpart. Cargo checks tool paths by
//! name and `is_file()`, which is a time-of-check/time-of-use answer: the file
//! that was inspected and the file that is executed need not be the same
//! object. The toolchain-identity guards need an identity that survives being
//! re-read, so it is derived from an open handle and includes the platform
//! fields (device/inode, or the Windows volume/file index) that a rename or a
//! reparse point cannot preserve.

use std::fs;
use std::path::Path;

/// Whether pathname metadata can own a protected Trust executable identity.
///
/// Windows has non-symlink reparse-point kinds, so `FileType::is_symlink` is
/// not a complete redirect check there.
pub fn metadata_is_plain_file(metadata: &fs::Metadata) -> bool {
    metadata.file_type().is_file() && metadata_has_no_redirect(metadata)
}

/// Whether pathname metadata names a directory object without redirection.
pub fn metadata_is_plain_directory(metadata: &fs::Metadata) -> bool {
    metadata.file_type().is_dir() && metadata_has_no_redirect(metadata)
}

#[cfg(windows)]
fn metadata_has_no_redirect(metadata: &fs::Metadata) -> bool {
    use std::os::windows::fs::MetadataExt as _;

    !metadata.file_type().is_symlink()
        && windows_file_attributes_are_plain(metadata.file_attributes())
}

#[cfg(not(windows))]
fn metadata_has_no_redirect(metadata: &fs::Metadata) -> bool {
    !metadata.file_type().is_symlink()
}

#[cfg(windows)]
fn windows_file_attributes_are_plain(attributes: u32) -> bool {
    const FILE_ATTRIBUTE_REPARSE_POINT: u32 = 0x0000_0400;

    attributes & FILE_ATTRIBUTE_REPARSE_POINT == 0
}

/// Stable identity and continuity metadata captured from one live file handle.
///
/// On Windows this deliberately uses `FileIdInfo` rather than the legacy
/// 64-bit file index, which is not unique on ReFS.
///
/// Elsewhere the identity is the full `(st_dev, st_ino)` pair read by `fstat`
/// from the open handle, and the handle itself is retained so that pair cannot
/// be recycled for another object while this identity is alive. Equality
/// compares the pair only. (Trust: std's `MetadataExt` in place of the
/// `same-file` crate, whose Unix `Handle` is exactly this, so the compiler
/// graph that reaches this crate carries no extra dependency for it.)
#[cfg(not(windows))]
#[derive(Debug)]
pub struct OpenedFileIdentity {
    _handle: fs::File,
    device: u64,
    inode: u64,
}

#[cfg(not(windows))]
impl PartialEq for OpenedFileIdentity {
    fn eq(&self, other: &Self) -> bool {
        (self.device, self.inode) == (other.device, other.inode)
    }
}

#[cfg(not(windows))]
impl Eq for OpenedFileIdentity {}

/// Stable identity and continuity metadata captured from one live file handle.
///
/// On Windows this deliberately uses `FileIdInfo` rather than the legacy
/// 64-bit file index, which is not unique on ReFS.
#[cfg(windows)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct OpenedFileIdentity {
    volume_serial_number: u64,
    file_id: [u8; 16],
    change_time: i64,
    links: u32,
}

impl OpenedFileIdentity {
    /// Whether both live handles name the same filesystem object, excluding
    /// continuity metadata that can move while that object remains selected.
    ///
    /// Windows `change_time` and `links` are intentionally absent here: they
    /// detect mutation for callers that compare the complete identity, but a
    /// directory's ordinary entry churn changes them. Path-chain guards pair
    /// this stable identity with their own role-specific metadata policy.
    pub fn same_file(&self, other: &Self) -> bool {
        #[cfg(not(windows))]
        {
            self == other
        }
        #[cfg(windows)]
        {
            self.volume_serial_number == other.volume_serial_number && self.file_id == other.file_id
        }
    }
}

/// Capture the authoritative identity of an already-open file or directory.
#[cfg(unix)]
pub fn opened_file_identity(file: &fs::File) -> std::io::Result<OpenedFileIdentity> {
    use std::os::unix::fs::MetadataExt as _;

    let handle = file.try_clone()?;
    let metadata = handle.metadata()?;
    Ok(OpenedFileIdentity {
        device: metadata.dev(),
        inode: metadata.ino(),
        _handle: handle,
    })
}

/// Capture the authoritative identity of an already-open file or directory.
///
/// No full-width handle identity is implemented for this platform, so every
/// caller's identity check fails closed.
#[cfg(not(any(unix, windows)))]
pub fn opened_file_identity(_file: &fs::File) -> std::io::Result<OpenedFileIdentity> {
    Err(std::io::Error::new(
        std::io::ErrorKind::Unsupported,
        "opened-handle file identity is not implemented on this platform",
    ))
}

/// Capture the authoritative identity of an already-open file or directory.
#[cfg(windows)]
pub fn opened_file_identity(file: &fs::File) -> std::io::Result<OpenedFileIdentity> {
    use std::mem::{MaybeUninit, size_of};
    use std::os::windows::io::AsRawHandle as _;

    use windows_sys::Win32::Storage::FileSystem::{
        FILE_BASIC_INFO, FILE_ID_INFO, FILE_STANDARD_INFO, FileBasicInfo, FileIdInfo,
        FileStandardInfo, GetFileInformationByHandleEx,
    };

    let handle = file.as_raw_handle();
    let mut identity = MaybeUninit::<FILE_ID_INFO>::uninit();
    // SAFETY: `identity` is correctly sized/aligned output storage for
    // FILE_ID_INFO and `file` keeps `handle` live for the complete call.
    if unsafe {
        GetFileInformationByHandleEx(
            handle,
            FileIdInfo,
            identity.as_mut_ptr().cast(),
            size_of::<FILE_ID_INFO>() as u32,
        )
    } == 0
    {
        return Err(std::io::Error::last_os_error());
    }
    // SAFETY: a successful API call initialized the complete output structure.
    let identity = unsafe { identity.assume_init() };

    let mut basic = MaybeUninit::<FILE_BASIC_INFO>::uninit();
    // SAFETY: `basic` is correctly sized/aligned output storage for
    // FILE_BASIC_INFO and the live handle remains valid.
    if unsafe {
        GetFileInformationByHandleEx(
            handle,
            FileBasicInfo,
            basic.as_mut_ptr().cast(),
            size_of::<FILE_BASIC_INFO>() as u32,
        )
    } == 0
    {
        return Err(std::io::Error::last_os_error());
    }
    // SAFETY: a successful API call initialized the complete output structure.
    let basic = unsafe { basic.assume_init() };

    let mut standard = MaybeUninit::<FILE_STANDARD_INFO>::uninit();
    // SAFETY: `standard` is correctly sized/aligned output storage for
    // FILE_STANDARD_INFO and the live handle remains valid.
    if unsafe {
        GetFileInformationByHandleEx(
            handle,
            FileStandardInfo,
            standard.as_mut_ptr().cast(),
            size_of::<FILE_STANDARD_INFO>() as u32,
        )
    } == 0
    {
        return Err(std::io::Error::last_os_error());
    }
    // SAFETY: a successful API call initialized the complete output structure.
    let standard = unsafe { standard.assume_init() };

    Ok(OpenedFileIdentity {
        volume_serial_number: identity.VolumeSerialNumber,
        file_id: identity.FileId.Identifier,
        change_time: basic.ChangeTime,
        links: standard.NumberOfLinks,
    })
}

/// Compare two executable paths using identities captured while both handles
/// remain live. Failure to obtain full authority is returned to the caller so
/// authentication sites can fail closed.
pub fn paths_refer_to_same_file(left: &Path, right: &Path) -> std::io::Result<bool> {
    let left = open_for_identity(left)?;
    let right = open_for_identity(right)?;
    Ok(opened_file_identity(&left)?.same_file(&opened_file_identity(&right)?))
}

/// The path the kernel reports for the executable image process `pid` is running.
///
/// Trust: the kernel's answer, not the path the process was started by. Linux's
/// `/proc/<pid>/exe` and macOS's `proc_pidpath` both name the file behind the image
/// itself, so a symlink that was executed is reported as the file it resolved to at
/// exec. Used to authenticate a live Targo parent (the `targo fix` proxy) and, through
/// [`running_executable_image`], to bind a resolved frontend symlink to the file that is
/// actually running (plan T13d).
#[cfg(target_os = "linux")]
pub fn process_executable_path(pid: u32) -> std::io::Result<std::path::PathBuf> {
    fs::read_link(format!("/proc/{pid}/exe"))
}

/// The path the kernel reports for the executable image process `pid` is running.
///
/// Trust: the kernel's answer, not the path the process was started by. Linux's
/// `/proc/<pid>/exe` and macOS's `proc_pidpath` both name the file behind the image
/// itself, so a symlink that was executed is reported as the file it resolved to at
/// exec. Used to authenticate a live Targo parent (the `targo fix` proxy) and, through
/// [`running_executable_image`], to bind a resolved frontend symlink to the file that is
/// actually running (plan T13d).
#[cfg(target_os = "macos")]
pub fn process_executable_path(pid: u32) -> std::io::Result<std::path::PathBuf> {
    use std::os::unix::ffi::OsStringExt as _;

    const PROC_PIDPATHINFO_MAXSIZE: usize = 4096;
    let pid = libc::c_int::try_from(pid).map_err(|_| {
        std::io::Error::new(
            std::io::ErrorKind::InvalidInput,
            format!("pid {pid} is out of range"),
        )
    })?;
    let mut buffer = vec![0_u8; PROC_PIDPATHINFO_MAXSIZE];
    // SAFETY: `buffer` is writable for its whole length, which is the size passed.
    let length =
        unsafe { libc::proc_pidpath(pid, buffer.as_mut_ptr().cast(), buffer.len() as u32) };
    if length <= 0 {
        return Err(std::io::Error::last_os_error());
    }
    buffer.truncate(length as usize);
    while buffer.last() == Some(&0) {
        buffer.pop();
    }
    if buffer.is_empty() {
        return Err(std::io::Error::new(
            std::io::ErrorKind::InvalidData,
            format!("the kernel reported an empty executable path for pid {pid}"),
        ));
    }
    Ok(std::path::PathBuf::from(std::ffi::OsString::from_vec(
        buffer,
    )))
}

/// The path the kernel reports for the executable image process `pid` is running.
#[cfg(not(any(target_os = "linux", target_os = "macos")))]
pub fn process_executable_path(_pid: u32) -> std::io::Result<std::path::PathBuf> {
    Err(std::io::Error::new(
        std::io::ErrorKind::Unsupported,
        "the kernel's executable path for a process is not implemented on this platform",
    ))
}

/// A path whose file IS this process's running executable image, for comparison with
/// [`paths_refer_to_same_file`].
///
/// Trust (plan T13d): on Linux, `/proc/self/exe` itself, which opens the image's own
/// file even after its path was replaced or removed. On macOS, the kernel's path for the
/// image ([`process_executable_path`]): it names the file the image was loaded from, at
/// a path that is replaced only if that file is renamed over or removed after exec, and
/// then it names another file or none, which fails a comparison closed. Elsewhere there
/// is no such answer, and the caller must not assume one.
#[cfg(target_os = "linux")]
pub fn running_executable_image() -> std::io::Result<std::path::PathBuf> {
    Ok(std::path::PathBuf::from("/proc/self/exe"))
}

/// A path whose file IS this process's running executable image (see the Linux twin).
#[cfg(not(target_os = "linux"))]
pub fn running_executable_image() -> std::io::Result<std::path::PathBuf> {
    process_executable_path(std::process::id())
}

#[cfg(not(windows))]
fn open_for_identity(path: &Path) -> std::io::Result<fs::File> {
    fs::File::open(path)
}

#[cfg(windows)]
fn open_for_identity(path: &Path) -> std::io::Result<fs::File> {
    use std::os::windows::fs::{MetadataExt as _, OpenOptionsExt as _};

    const FILE_SHARE_READ: u32 = 0x0000_0001;
    const FILE_SHARE_WRITE: u32 = 0x0000_0002;
    const FILE_SHARE_DELETE: u32 = 0x0000_0004;
    const FILE_ATTRIBUTE_DIRECTORY: u32 = 0x0000_0010;
    const FILE_FLAG_BACKUP_SEMANTICS: u32 = 0x0200_0000;
    const FILE_FLAG_OPEN_REPARSE_POINT: u32 = 0x0020_0000;

    let metadata = fs::symlink_metadata(path)?;
    if metadata.file_attributes() & FILE_ATTRIBUTE_DIRECTORY == 0 {
        return fs::File::open(path);
    }

    // Windows requires BACKUP_SEMANTICS to obtain a directory handle. Open the
    // pathname object itself so a junction/reparse point cannot compare equal
    // to its target, and share ordinary access because this short-lived handle
    // is an identity snapshot rather than a lifetime guard.
    fs::OpenOptions::new()
        .access_mode(0)
        .share_mode(FILE_SHARE_READ | FILE_SHARE_WRITE | FILE_SHARE_DELETE)
        .custom_flags(FILE_FLAG_BACKUP_SEMANTICS | FILE_FLAG_OPEN_REPARSE_POINT)
        .open(path)
}

#[cfg(all(test, windows))]
mod windows_tests {
    use super::{OpenedFileIdentity, paths_refer_to_same_file, windows_file_attributes_are_plain};

    #[test]
    fn directory_identity_uses_a_directory_capable_handle() {
        let directory =
            std::env::temp_dir().join(format!("targo-directory-identity-{}", std::process::id()));
        std::fs::create_dir_all(&directory).expect("create directory identity fixture");
        assert!(
            paths_refer_to_same_file(&directory, &directory)
                .expect("open Windows directory identity handles")
        );
        let _ = std::fs::remove_dir_all(directory);
    }

    #[test]
    fn full_volume_and_128_bit_file_id_are_identity_authority() {
        let base = OpenedFileIdentity {
            volume_serial_number: 7,
            file_id: [0; 16],
            change_time: 11,
            links: 1,
        };
        let mut colliding_legacy_id = base.clone();
        colliding_legacy_id.file_id[15] = 1;
        assert_ne!(
            base, colliding_legacy_id,
            "file IDs that agree in only 64 bits must remain distinct"
        );

        let mut extended_volume = base.clone();
        extended_volume.volume_serial_number |= 1_u64 << 32;
        assert_ne!(
            base, extended_volume,
            "the complete 64-bit volume serial must participate in identity"
        );

        let mut ordinary_directory_churn = base.clone();
        ordinary_directory_churn.change_time += 1;
        ordinary_directory_churn.links += 1;
        assert_ne!(
            base, ordinary_directory_churn,
            "full continuity metadata still moves"
        );
        assert!(
            base.same_file(&ordinary_directory_churn),
            "stable file identity must exclude directory-entry churn metadata"
        );
    }

    #[test]
    fn every_windows_reparse_point_is_excluded_from_plain_file_authority() {
        const FILE_ATTRIBUTE_ARCHIVE: u32 = 0x0000_0020;
        const FILE_ATTRIBUTE_REPARSE_POINT: u32 = 0x0000_0400;

        assert!(windows_file_attributes_are_plain(FILE_ATTRIBUTE_ARCHIVE));
        assert!(!windows_file_attributes_are_plain(
            FILE_ATTRIBUTE_REPARSE_POINT
        ));
        assert!(!windows_file_attributes_are_plain(
            FILE_ATTRIBUTE_ARCHIVE | FILE_ATTRIBUTE_REPARSE_POINT
        ));
    }
}

#[cfg(all(test, any(target_os = "linux", target_os = "macos")))]
mod running_image_tests {
    use super::{paths_refer_to_same_file, process_executable_path, running_executable_image};

    // T13d: the binding a symlinked frontend is checked against must name the file this
    // process is actually running, by the kernel's answer.
    #[test]
    fn the_running_image_is_the_file_this_test_runs_from() {
        let started_as = std::env::current_exe().expect("the test binary's path");
        let image = running_executable_image().expect("the kernel names the running image");
        assert!(
            paths_refer_to_same_file(&image, &started_as).expect("open both"),
            "{} is not {}",
            image.display(),
            started_as.display()
        );
        let by_pid = process_executable_path(std::process::id()).expect("the kernel's path by pid");
        assert!(by_pid.is_absolute(), "{}", by_pid.display());
        assert!(paths_refer_to_same_file(&by_pid, &started_as).expect("open both"));
    }
}
