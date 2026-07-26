#![allow(unsafe_code)]

use std::ffi::{OsStr, OsString};
use std::fs::{self, File, Metadata, OpenOptions};
use std::io;
use std::mem::MaybeUninit;
use std::os::windows::ffi::OsStrExt;
use std::os::windows::fs::OpenOptionsExt;
use std::os::windows::io::AsRawHandle;
use std::path::{Component, Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};

use windows_sys::Win32::Storage::FileSystem::{
    BY_HANDLE_FILE_INFORMATION, FILE_ATTRIBUTE_DIRECTORY, FILE_ATTRIBUTE_REPARSE_POINT,
    FILE_FLAG_BACKUP_SEMANTICS, FILE_FLAG_OPEN_REPARSE_POINT, FILE_ID_INFO, FILE_SHARE_READ,
    FILE_SHARE_WRITE, FileIdInfo, GetFileInformationByHandle, GetFileInformationByHandleEx,
    MOVEFILE_REPLACE_EXISTING, MOVEFILE_WRITE_THROUGH, MoveFileExW,
};

use crate::UnixMode;

const STABLE_SHARE_MODE: u32 = FILE_SHARE_READ | FILE_SHARE_WRITE;
static TOMBSTONE_SEQUENCE: AtomicU64 = AtomicU64::new(0);

/// Directory anchor for Windows publication operations.
///
/// Windows has no stable `openat` surface. Instead, this retains no-delete-share
/// handles for the canonical directory and every ancestor. Those handles stop
/// any pathname component from being renamed while checked relative operations
/// resolve beneath it.
#[derive(Debug)]
pub struct DirFd {
    path: PathBuf,
    identity: FileIdentity,
    // All selected-directory and ancestor handles deliberately remain live for
    // the full transaction.
    _anchors: Vec<File>,
}

impl DirFd {
    pub fn open(path: impl AsRef<Path>) -> io::Result<Self> {
        let path = fs::canonicalize(path)?;
        // Pin the selected leaf first, then its ancestors root-to-parent. A
        // final identity check detects any ancestor swap that happened between
        // those opens.
        let selected = open_directory_anchor(&path)?;
        directory_information(&selected)?;
        let identity = file_identity(&selected)?;
        let mut ancestors = path.ancestors().skip(1).map(Path::to_path_buf).collect::<Vec<_>>();
        ancestors.reverse();

        let mut anchors = Vec::with_capacity(ancestors.len() + 1);
        anchors.push(selected);
        for ancestor in ancestors {
            let anchor = open_directory_anchor(&ancestor)?;
            directory_information(&anchor)?;
            anchors.push(anchor);
        }
        let rechecked = open_directory_anchor(&path)?;
        directory_information(&rechecked)?;
        let rechecked_identity = file_identity(&rechecked)?;
        if rechecked_identity != identity {
            return Err(io::Error::new(
                io::ErrorKind::Other,
                "directory path changed while its ancestor handles were acquired",
            ));
        }
        Ok(Self { path, identity, _anchors: anchors })
    }

    pub fn open_file(&self, path: impl AsRef<Path>) -> io::Result<File> {
        open_file_at(self, path)
    }

    pub fn open_file_read_write(&self, path: impl AsRef<Path>) -> io::Result<File> {
        open_file_read_write_at(self, path)
    }

    pub fn create_file(&self, path: impl AsRef<Path>, mode: UnixMode) -> io::Result<File> {
        create_file_at(self, path, mode)
    }

    pub fn remove_file(&self, path: impl AsRef<Path>) -> io::Result<()> {
        remove_file_at(self, path)
    }

    pub fn rename_file(&self, from: impl AsRef<Path>, to: impl AsRef<Path>) -> io::Result<()> {
        rename_file_at(self, from, to)
    }

    pub fn sync_all(&self) -> io::Result<()> {
        // Windows does not expose the Unix directory-fsync primitive through
        // `std`. Every published file is flushed before its atomic rename; the
        // retained handles provide namespace stability for that sequence.
        Ok(())
    }

    pub fn metadata(&self, path: impl AsRef<Path>) -> io::Result<Metadata> {
        metadata_at(self, path)
    }

    pub fn identity(&self, path: impl AsRef<Path>) -> io::Result<FileIdentity> {
        identity_at(self, path)
    }

    pub fn directory_identity(&self) -> io::Result<FileIdentity> {
        Ok(self.identity)
    }

    pub fn file_identity(&self, file: &File) -> io::Result<FileIdentity> {
        file_identity(file)
    }

    pub fn file_link_count(&self, file: &File) -> io::Result<u64> {
        file_information(file).map(|information| u64::from(information.nNumberOfLinks))
    }

    pub fn read_dir_names(&self) -> io::Result<Vec<OsString>> {
        fs::read_dir(&self.path)?.map(|entry| entry.map(|entry| entry.file_name())).collect()
    }

    fn resolve(&self, path: &Path) -> io::Result<PathBuf> {
        let mut components = path.components();
        let Some(Component::Normal(name)) = components.next() else {
            return Err(invalid_path(path));
        };
        if components.next().is_some() {
            return Err(invalid_path(path));
        }
        Ok(self.path.join(name))
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct FileIdentity {
    volume: u64,
    identifier: [u8; 16],
}

impl FileIdentity {
    #[must_use]
    pub const fn device(self) -> u64 {
        self.volume
    }

    /// Returns the low 64 bits of the Windows file ID for compatibility with
    /// Unix-oriented diagnostics. This value alone is not authoritative on
    /// filesystems such as ReFS; compare the complete `FileIdentity` instead.
    #[must_use]
    pub const fn inode(self) -> u64 {
        u64::from_le_bytes([
            self.identifier[0],
            self.identifier[1],
            self.identifier[2],
            self.identifier[3],
            self.identifier[4],
            self.identifier[5],
            self.identifier[6],
            self.identifier[7],
        ])
    }
}

pub fn open_file_at(dir: &DirFd, path: impl AsRef<Path>) -> io::Result<File> {
    open_existing(dir, path.as_ref(), false)
}

pub fn open_file_read_write_at(dir: &DirFd, path: impl AsRef<Path>) -> io::Result<File> {
    open_existing(dir, path.as_ref(), true)
}

pub fn create_file_at(dir: &DirFd, path: impl AsRef<Path>, _mode: UnixMode) -> io::Result<File> {
    let path = dir.resolve(path.as_ref())?;
    let file = OpenOptions::new()
        .read(true)
        .write(true)
        .create_new(true)
        .share_mode(STABLE_SHARE_MODE)
        .open(path)?;
    ensure_regular(&file)?;
    Ok(file)
}

pub fn remove_file_at(dir: &DirFd, path: impl AsRef<Path>) -> io::Result<()> {
    let relative = path.as_ref();
    // Validate through a no-follow handle so every reparse tag (not only the
    // standard symlink tag surfaced by `FileType::is_symlink`) and every
    // non-regular entry fails before the namespace operation.
    drop(open_file_at(dir, relative)?);
    let path = dir.resolve(relative)?;
    // A write-through rename makes disappearance of the authenticated name
    // durable before best-effort tombstone deletion. A crash can leave only an
    // unauthenticated control file, never restore the old marker name.
    for _ in 0..16 {
        let sequence = TOMBSTONE_SEQUENCE.fetch_add(1, Ordering::Relaxed);
        let tombstone =
            dir.path.join(format!(".trust-os-delete-{}-{sequence}.tmp", std::process::id()));
        match move_file(&path, &tombstone, false) {
            Ok(()) => return fs::remove_file(tombstone),
            Err(error) if error.kind() == io::ErrorKind::AlreadyExists => continue,
            Err(error) => return Err(error),
        }
    }
    Err(io::Error::new(
        io::ErrorKind::AlreadyExists,
        "could not allocate a unique deletion tombstone",
    ))
}

pub fn rename_file_at(dir: &DirFd, from: impl AsRef<Path>, to: impl AsRef<Path>) -> io::Result<()> {
    let from = dir.resolve(from.as_ref())?;
    let to = dir.resolve(to.as_ref())?;
    move_file(&from, &to, true)
}

pub fn metadata_at(dir: &DirFd, path: impl AsRef<Path>) -> io::Result<Metadata> {
    let file = open_file_at(dir, path)?;
    file.metadata()
}

pub fn identity_at(dir: &DirFd, path: impl AsRef<Path>) -> io::Result<FileIdentity> {
    let file = open_file_at(dir, path)?;
    file_identity(&file)
}

fn open_existing(dir: &DirFd, path: &Path, write: bool) -> io::Result<File> {
    let path = dir.resolve(path)?;
    let mut options = OpenOptions::new();
    options
        .read(true)
        .write(write)
        .share_mode(STABLE_SHARE_MODE)
        .custom_flags(FILE_FLAG_OPEN_REPARSE_POINT);
    let file = options.open(path)?;
    ensure_regular(&file)?;
    Ok(file)
}

fn open_directory_anchor(path: &Path) -> io::Result<File> {
    OpenOptions::new()
        .access_mode(0)
        .share_mode(STABLE_SHARE_MODE)
        .custom_flags(FILE_FLAG_BACKUP_SEMANTICS | FILE_FLAG_OPEN_REPARSE_POINT)
        .open(path)
}

fn directory_information(file: &File) -> io::Result<BY_HANDLE_FILE_INFORMATION> {
    let information = file_information(file)?;
    if information.dwFileAttributes & FILE_ATTRIBUTE_DIRECTORY == 0
        || information.dwFileAttributes & FILE_ATTRIBUTE_REPARSE_POINT != 0
    {
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            "opened directory anchor is not a non-reparse directory",
        ));
    }
    Ok(information)
}

fn ensure_regular(file: &File) -> io::Result<()> {
    let information = file_information(file)?;
    if file.metadata()?.is_file()
        && information.dwFileAttributes & FILE_ATTRIBUTE_DIRECTORY == 0
        && information.dwFileAttributes & FILE_ATTRIBUTE_REPARSE_POINT == 0
    {
        Ok(())
    } else {
        Err(io::Error::new(io::ErrorKind::InvalidInput, "artifact entry is not a regular file"))
    }
}

fn file_identity(file: &File) -> io::Result<FileIdentity> {
    // `BY_HANDLE_FILE_INFORMATION` exposes only a 64-bit file index, which is
    // not unique on filesystems with 128-bit IDs (notably ReFS). Authority
    // checks must retain all of `FILE_ID_INFO::FileId`.
    let mut information = MaybeUninit::<FILE_ID_INFO>::uninit();
    let succeeded = unsafe {
        GetFileInformationByHandleEx(
            file.as_raw_handle(),
            FileIdInfo,
            information.as_mut_ptr().cast(),
            std::mem::size_of::<FILE_ID_INFO>() as u32,
        )
    };
    if succeeded == 0 {
        return Err(io::Error::last_os_error());
    }
    let information = unsafe { information.assume_init() };
    Ok(FileIdentity {
        volume: information.VolumeSerialNumber,
        identifier: information.FileId.Identifier,
    })
}

fn file_information(file: &File) -> io::Result<BY_HANDLE_FILE_INFORMATION> {
    let mut information = MaybeUninit::<BY_HANDLE_FILE_INFORMATION>::uninit();
    let succeeded =
        unsafe { GetFileInformationByHandle(file.as_raw_handle(), information.as_mut_ptr()) };
    if succeeded == 0 {
        return Err(io::Error::last_os_error());
    }
    Ok(unsafe { information.assume_init() })
}

fn move_file(from: &Path, to: &Path, replace: bool) -> io::Result<()> {
    let from = wide_null(from)?;
    let to = wide_null(to)?;
    let mut flags = MOVEFILE_WRITE_THROUGH;
    if replace {
        flags |= MOVEFILE_REPLACE_EXISTING;
    }
    let succeeded = unsafe { MoveFileExW(from.as_ptr(), to.as_ptr(), flags) };
    if succeeded == 0 { Err(io::Error::last_os_error()) } else { Ok(()) }
}

fn wide_null(path: &Path) -> io::Result<Vec<u16>> {
    let mut wide = path.as_os_str().encode_wide().collect::<Vec<_>>();
    if wide.contains(&0) {
        return Err(io::Error::new(io::ErrorKind::InvalidInput, "path contains a NUL"));
    }
    wide.push(0);
    Ok(wide)
}

fn invalid_path(path: &Path) -> io::Error {
    io::Error::new(
        io::ErrorKind::InvalidInput,
        format!("expected one relative path component, got `{}`", display_os(path.as_os_str())),
    )
}

fn display_os(value: &OsStr) -> String {
    value.encode_wide().map(|unit| char::from_u32(u32::from(unit)).unwrap_or('\u{fffd}')).collect()
}
