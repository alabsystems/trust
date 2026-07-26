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

/// Whether pathname metadata names a directory object without redirection.
pub fn metadata_is_plain_directory(metadata: &fs::Metadata) -> bool {
    if metadata.file_type().is_symlink() || !metadata.file_type().is_dir() {
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

/// Stable identity and continuity metadata captured from one live file handle.
///
/// On Windows this deliberately uses `FileIdInfo` rather than the legacy
/// 64-bit file index, which is not unique on ReFS.
#[cfg(not(windows))]
#[derive(Debug, Eq, PartialEq)]
pub struct OpenedFileIdentity(same_file::Handle);

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

/// Capture the authoritative identity of an already-open file or directory.
#[cfg(not(windows))]
pub fn opened_file_identity(file: &fs::File) -> std::io::Result<OpenedFileIdentity> {
    same_file::Handle::from_file(file.try_clone()?).map(OpenedFileIdentity)
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
    Ok(opened_file_identity(&left)? == opened_file_identity(&right)?)
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
