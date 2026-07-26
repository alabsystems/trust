#![allow(unsafe_code)]

use std::ffi::{CString, OsString};
use std::fs::{File, Metadata, OpenOptions};
use std::io;
use std::mem::MaybeUninit;
use std::os::fd::{AsRawFd, FromRawFd, RawFd};
use std::os::unix::ffi::OsStrExt;
use std::os::unix::ffi::OsStringExt;
use std::os::unix::fs::{MetadataExt, OpenOptionsExt};
use std::path::Path;

use crate::UnixMode;

/// Directory file descriptor anchor for dirfd-relative operations.
#[derive(Debug)]
pub struct DirFd {
    file: File,
}

impl DirFd {
    /// Opens a directory as a descriptor anchor.
    ///
    /// The final component is not followed if it is a symlink.
    pub fn open(path: impl AsRef<Path>) -> io::Result<Self> {
        let file = OpenOptions::new()
            .read(true)
            .custom_flags(libc::O_CLOEXEC | libc::O_DIRECTORY | libc::O_NOFOLLOW)
            .open(path)?;
        Ok(Self { file })
    }

    /// Opens an existing regular filesystem object relative to this directory.
    ///
    /// The path must be relative and may not contain `..`. Intermediate
    /// components are opened as directories without following symlinks, and
    /// the final component is not followed if it is a symlink.
    pub fn open_file(&self, path: impl AsRef<Path>) -> io::Result<File> {
        open_file_at(self, path)
    }

    /// Opens an existing regular filesystem object for reading and writing
    /// relative to this directory.
    pub fn open_file_read_write(&self, path: impl AsRef<Path>) -> io::Result<File> {
        open_file_read_write_at(self, path)
    }

    /// Creates a new file relative to this directory with `O_EXCL`.
    ///
    /// Intermediate components are opened as directories without following
    /// symlinks.
    pub fn create_file(&self, path: impl AsRef<Path>, mode: UnixMode) -> io::Result<File> {
        create_file_at(self, path, mode)
    }

    /// Removes a file or symlink relative to this directory.
    ///
    /// Intermediate components are opened as directories without following
    /// symlinks.
    pub fn remove_file(&self, path: impl AsRef<Path>) -> io::Result<()> {
        remove_file_at(self, path)
    }

    /// Atomically renames a file within this directory.
    pub fn rename_file(&self, from: impl AsRef<Path>, to: impl AsRef<Path>) -> io::Result<()> {
        rename_file_at(self, from, to)
    }

    /// Makes directory-entry changes durable.
    pub fn sync_all(&self) -> io::Result<()> {
        self.file.sync_all()
    }

    /// Reads metadata relative to this directory.
    ///
    /// This rejects a final symlink instead of following it. Intermediate
    /// components are opened as directories without following symlinks.
    pub fn metadata(&self, path: impl AsRef<Path>) -> io::Result<Metadata> {
        metadata_at(self, path)
    }

    /// Reads stable file identity relative to this directory.
    ///
    /// Intermediate components are opened as directories without following
    /// symlinks.
    pub fn identity(&self, path: impl AsRef<Path>) -> io::Result<FileIdentity> {
        identity_at(self, path)
    }

    /// Reads the stable identity of this directory anchor itself.
    pub fn directory_identity(&self) -> io::Result<FileIdentity> {
        self.file.metadata().map(|metadata| FileIdentity::from_metadata(&metadata))
    }

    /// Reads the stable identity of an already-open file.
    pub fn file_identity(&self, file: &File) -> io::Result<FileIdentity> {
        file.metadata().map(|metadata| FileIdentity::from_metadata(&metadata))
    }

    /// Returns the hard-link count for an already-open file.
    pub fn file_link_count(&self, file: &File) -> io::Result<u64> {
        use std::os::unix::fs::MetadataExt;

        file.metadata().map(|metadata| metadata.nlink())
    }

    /// Enumerates entry names through this directory anchor.
    pub fn read_dir_names(&self) -> io::Result<Vec<OsString>> {
        read_dir_names_at(self)
    }

    fn raw_fd(&self) -> RawFd {
        self.file.as_raw_fd()
    }
}

/// Stable Unix file identity.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct FileIdentity {
    device: u64,
    inode: u64,
}

impl FileIdentity {
    /// Builds identity from Unix metadata.
    #[must_use]
    pub fn from_metadata(metadata: &Metadata) -> Self {
        Self { device: metadata.dev(), inode: metadata.ino() }
    }

    /// Device number.
    #[must_use]
    pub const fn device(self) -> u64 {
        self.device
    }

    /// Inode number.
    #[must_use]
    pub const fn inode(self) -> u64 {
        self.inode
    }
}

/// Opens an existing file relative to `dir`.
pub fn open_file_at(dir: &DirFd, path: impl AsRef<Path>) -> io::Result<File> {
    let path = resolve_leaf(dir, path.as_ref())?;
    let fd = cvt(unsafe {
        libc::openat(
            path.parent_fd(),
            path.leaf.as_ptr(),
            libc::O_RDONLY | libc::O_CLOEXEC | libc::O_NOFOLLOW | libc::O_NONBLOCK,
        )
    })?;
    let file = unsafe { File::from_raw_fd(fd) };
    ensure_regular_file(&file)?;
    Ok(file)
}

/// Opens an existing file for reading and writing relative to `dir`.
pub fn open_file_read_write_at(dir: &DirFd, path: impl AsRef<Path>) -> io::Result<File> {
    let path = resolve_leaf(dir, path.as_ref())?;
    let fd = cvt(unsafe {
        libc::openat(
            path.parent_fd(),
            path.leaf.as_ptr(),
            libc::O_RDWR | libc::O_CLOEXEC | libc::O_NOFOLLOW | libc::O_NONBLOCK,
        )
    })?;
    let file = unsafe { File::from_raw_fd(fd) };
    ensure_regular_file(&file)?;
    Ok(file)
}

/// Creates a new file relative to `dir`.
pub fn create_file_at(dir: &DirFd, path: impl AsRef<Path>, mode: UnixMode) -> io::Result<File> {
    let path = resolve_leaf(dir, path.as_ref())?;
    let fd = cvt(unsafe {
        libc::openat(
            path.parent_fd(),
            path.leaf.as_ptr(),
            libc::O_WRONLY | libc::O_CREAT | libc::O_EXCL | libc::O_CLOEXEC | libc::O_NOFOLLOW,
            mode.bits() as libc::c_uint,
        )
    })?;
    let file = unsafe { File::from_raw_fd(fd) };
    ensure_regular_file(&file)?;
    Ok(file)
}

/// Enumerates entry names relative to `dir` without resolving its ambient path.
#[cfg(any(
    target_os = "android",
    target_os = "dragonfly",
    target_os = "freebsd",
    target_os = "ios",
    target_os = "linux",
    target_os = "macos",
    target_os = "netbsd",
    target_os = "openbsd",
    target_os = "tvos",
    target_os = "visionos",
    target_os = "watchos",
))]
pub fn read_dir_names_at(dir: &DirFd) -> io::Result<Vec<OsString>> {
    let dot = c".";
    let fd = cvt(unsafe {
        libc::openat(
            dir.raw_fd(),
            dot.as_ptr(),
            libc::O_RDONLY | libc::O_CLOEXEC | libc::O_DIRECTORY | libc::O_NOFOLLOW,
        )
    })?;
    let stream = unsafe { libc::fdopendir(fd) };
    if stream.is_null() {
        let error = io::Error::last_os_error();
        unsafe { libc::close(fd) };
        return Err(error);
    }
    struct Stream(*mut libc::DIR);
    impl Drop for Stream {
        fn drop(&mut self) {
            unsafe { libc::closedir(self.0) };
        }
    }
    let stream = Stream(stream);
    let mut names = Vec::new();
    loop {
        set_errno(0);
        let entry = unsafe { libc::readdir(stream.0) };
        if entry.is_null() {
            let errno = get_errno();
            if errno == 0 {
                return Ok(names);
            }
            return Err(io::Error::from_raw_os_error(errno));
        }
        let bytes = unsafe { (*entry).d_name.as_ptr().cast::<u8>() };
        let capacity = unsafe { (*entry).d_name.len() };
        let bytes = unsafe { std::slice::from_raw_parts(bytes, capacity) };
        let length = bytes.iter().position(|byte| *byte == 0).unwrap_or(capacity);
        let name = &bytes[..length];
        if name != b"." && name != b".." {
            names.push(OsString::from_vec(name.to_vec()));
        }
    }
}

#[cfg(not(any(
    target_os = "android",
    target_os = "dragonfly",
    target_os = "freebsd",
    target_os = "ios",
    target_os = "linux",
    target_os = "macos",
    target_os = "netbsd",
    target_os = "openbsd",
    target_os = "tvos",
    target_os = "visionos",
    target_os = "watchos",
)))]
pub fn read_dir_names_at(_dir: &DirFd) -> io::Result<Vec<OsString>> {
    Err(io::Error::new(
        io::ErrorKind::Unsupported,
        "anchored directory enumeration is unsupported on this Unix host",
    ))
}

#[cfg(any(target_os = "android", target_os = "linux"))]
fn set_errno(value: libc::c_int) {
    unsafe { *libc::__errno_location() = value };
}

#[cfg(any(target_os = "android", target_os = "linux"))]
fn get_errno() -> libc::c_int {
    unsafe { *libc::__errno_location() }
}

#[cfg(any(
    target_os = "dragonfly",
    target_os = "freebsd",
    target_os = "ios",
    target_os = "macos",
    target_os = "netbsd",
    target_os = "openbsd",
    target_os = "tvos",
    target_os = "visionos",
    target_os = "watchos",
))]
fn set_errno(value: libc::c_int) {
    unsafe { *libc::__error() = value };
}

#[cfg(any(
    target_os = "dragonfly",
    target_os = "freebsd",
    target_os = "ios",
    target_os = "macos",
    target_os = "netbsd",
    target_os = "openbsd",
    target_os = "tvos",
    target_os = "visionos",
    target_os = "watchos",
))]
fn get_errno() -> libc::c_int {
    unsafe { *libc::__error() }
}

fn ensure_regular_file(file: &File) -> io::Result<()> {
    if file.metadata()?.is_file() {
        Ok(())
    } else {
        Err(io::Error::new(io::ErrorKind::InvalidInput, "entry is not a regular file"))
    }
}

/// Removes a file or symlink relative to `dir`.
pub fn remove_file_at(dir: &DirFd, path: impl AsRef<Path>) -> io::Result<()> {
    let path = resolve_leaf(dir, path.as_ref())?;
    cvt(unsafe { libc::unlinkat(path.parent_fd(), path.leaf.as_ptr(), 0) })?;
    Ok(())
}

/// Atomically renames a file within `dir`.
pub fn rename_file_at(dir: &DirFd, from: impl AsRef<Path>, to: impl AsRef<Path>) -> io::Result<()> {
    let from = resolve_leaf(dir, from.as_ref())?;
    let to = resolve_leaf(dir, to.as_ref())?;
    cvt(unsafe {
        libc::renameat(from.parent_fd(), from.leaf.as_ptr(), to.parent_fd(), to.leaf.as_ptr())
    })?;
    Ok(())
}

/// Reads metadata relative to `dir`.
///
/// This rejects a final symlink instead of following it.
pub fn metadata_at(dir: &DirFd, path: impl AsRef<Path>) -> io::Result<Metadata> {
    let file = open_file_at(dir, path)?;
    file.metadata()
}

/// Reads stable identity relative to `dir`.
pub fn identity_at(dir: &DirFd, path: impl AsRef<Path>) -> io::Result<FileIdentity> {
    let path = resolve_leaf(dir, path.as_ref())?;
    let mut stat = MaybeUninit::<libc::stat>::uninit();
    cvt(unsafe {
        libc::fstatat(
            path.parent_fd(),
            path.leaf.as_ptr(),
            stat.as_mut_ptr(),
            libc::AT_SYMLINK_NOFOLLOW,
        )
    })?;
    let stat = unsafe { stat.assume_init() };
    Ok(FileIdentity { device: stat.st_dev as u64, inode: stat.st_ino })
}

struct ResolvedLeaf {
    parent: ParentDir,
    leaf: CString,
}

impl ResolvedLeaf {
    fn parent_fd(&self) -> RawFd {
        self.parent.raw_fd()
    }
}

enum ParentDir {
    Borrowed(RawFd),
    Owned(File),
}

impl ParentDir {
    fn raw_fd(&self) -> RawFd {
        match self {
            Self::Borrowed(fd) => *fd,
            Self::Owned(file) => file.as_raw_fd(),
        }
    }
}

fn resolve_leaf(dir: &DirFd, path: &Path) -> io::Result<ResolvedLeaf> {
    let mut components = checked_relative_components(path)?;
    let leaf = components.pop().ok_or_else(|| invalid_path("empty paths are not accepted"))?;
    let mut parent = ParentDir::Borrowed(dir.raw_fd());

    for component in components {
        let fd = cvt(unsafe {
            libc::openat(
                parent.raw_fd(),
                component.as_ptr(),
                libc::O_RDONLY | libc::O_CLOEXEC | libc::O_DIRECTORY | libc::O_NOFOLLOW,
            )
        })?;
        parent = ParentDir::Owned(unsafe { File::from_raw_fd(fd) });
    }

    Ok(ResolvedLeaf { parent, leaf })
}

fn checked_relative_components(path: &Path) -> io::Result<Vec<CString>> {
    let path = path.as_os_str().as_bytes();
    if path.is_empty() {
        return Err(invalid_path("empty paths are not accepted"));
    }

    if path[0] == b'/' {
        return Err(invalid_path("absolute paths are not accepted"));
    }

    let mut components = Vec::new();
    for component in path.split(|byte| *byte == b'/') {
        if component.is_empty() {
            continue;
        }

        if component == b".." {
            return Err(invalid_path("parent traversal is not accepted"));
        }

        components.push(
            CString::new(component)
                .map_err(|_| invalid_path("paths with NUL bytes are not accepted"))?,
        );
    }

    if path.ends_with(b"/") {
        components.push(CString::new(".").expect("literal path component has no NUL bytes"));
    }

    if components.is_empty() {
        return Err(invalid_path("empty paths are not accepted"));
    }

    Ok(components)
}

fn invalid_path(message: &'static str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidInput, message)
}

fn cvt(ret: libc::c_int) -> io::Result<libc::c_int> {
    if ret == -1 { Err(io::Error::last_os_error()) } else { Ok(ret) }
}

#[cfg(test)]
mod tests {
    use std::ffi::OsString;
    use std::fs;
    use std::io::{self, Read, Write};
    use std::os::unix::ffi::{OsStrExt, OsStringExt};
    use std::os::unix::fs::{PermissionsExt, symlink};
    use std::path::{Path, PathBuf};

    use super::*;

    #[test]
    fn create_open_identity_and_remove_relative_file() {
        let tmp = tempfile::tempdir().unwrap();
        let dir = DirFd::open(tmp.path()).unwrap();

        let mut created = dir.create_file("proof-cache.bin", UnixMode::OWNER_READ_WRITE).unwrap();
        created.write_all(b"cache").unwrap();
        drop(created);

        let identity = dir.identity("proof-cache.bin").unwrap();
        assert_ne!(identity.device(), 0);
        assert_ne!(identity.inode(), 0);

        let mut reopened = open_file_at(&dir, "proof-cache.bin").unwrap();
        let mut contents = String::new();
        reopened.read_to_string(&mut contents).unwrap();
        assert_eq!(contents, "cache");

        let mode = dir.metadata("proof-cache.bin").unwrap().permissions().mode() & 0o777;
        assert_eq!(mode, 0o600);

        remove_file_at(&dir, "proof-cache.bin").unwrap();
        assert!(dir.open_file("proof-cache.bin").is_err());
    }

    #[test]
    fn read_write_rename_sync_and_enumeration_stay_on_the_anchor() {
        let tmp = tempfile::tempdir().unwrap();
        let original = tmp.path().join("selected");
        let moved = tmp.path().join("moved");
        fs::create_dir(&original).unwrap();
        fs::write(original.join("entry"), b"before").unwrap();
        let dir = DirFd::open(&original).unwrap();

        let mut file = dir.open_file_read_write("entry").unwrap();
        file.write_all(b"!").unwrap();
        file.sync_all().unwrap();
        drop(file);
        dir.rename_file("entry", "renamed").unwrap();
        dir.sync_all().unwrap();

        fs::rename(&original, &moved).unwrap();
        fs::create_dir(&original).unwrap();
        let names = dir.read_dir_names().unwrap();
        assert!(names.iter().any(|name| name == "renamed"));
        assert!(!original.join("renamed").exists());
        assert!(moved.join("renamed").exists());
    }

    #[test]
    fn regular_file_opens_reject_directories_and_fifos_without_blocking() {
        let tmp = tempfile::tempdir().unwrap();
        fs::create_dir(tmp.path().join("directory")).unwrap();
        let fifo = tmp.path().join("fifo");
        let fifo_c = CString::new(fifo.as_os_str().as_bytes()).unwrap();
        assert_eq!(unsafe { libc::mkfifo(fifo_c.as_ptr(), 0o600) }, 0);
        let dir = DirFd::open(tmp.path()).unwrap();

        assert_eq!(dir.open_file("directory").unwrap_err().kind(), io::ErrorKind::InvalidInput);
        assert_eq!(
            dir.open_file_read_write("fifo").unwrap_err().kind(),
            io::ErrorKind::InvalidInput
        );
    }

    #[test]
    fn create_open_identity_and_remove_nested_file() {
        let tmp = tempfile::tempdir().unwrap();
        fs::create_dir(tmp.path().join("cache")).unwrap();
        let dir = DirFd::open(tmp.path()).unwrap();

        let mut created =
            dir.create_file("cache/proof-cache.bin", UnixMode::OWNER_READ_WRITE).unwrap();
        created.write_all(b"nested").unwrap();
        drop(created);

        let identity = dir.identity("cache/proof-cache.bin").unwrap();
        assert_ne!(identity.device(), 0);
        assert_ne!(identity.inode(), 0);

        let mut reopened = dir.open_file("cache/proof-cache.bin").unwrap();
        let mut contents = String::new();
        reopened.read_to_string(&mut contents).unwrap();
        assert_eq!(contents, "nested");

        let mode = dir.metadata("cache/proof-cache.bin").unwrap().permissions().mode() & 0o777;
        assert_eq!(mode, 0o600);

        dir.remove_file("cache/proof-cache.bin").unwrap();
        assert!(dir.open_file("cache/proof-cache.bin").is_err());
    }

    #[test]
    fn rejects_escape_paths() {
        let tmp = tempfile::tempdir().unwrap();
        let dir = DirFd::open(tmp.path()).unwrap();

        assert_eq!(dir.open_file("../outside").unwrap_err().kind(), io::ErrorKind::InvalidInput);
        assert_eq!(
            dir.open_file(tmp.path().join("absolute")).unwrap_err().kind(),
            io::ErrorKind::InvalidInput
        );
        assert_eq!(dir.open_file("").unwrap_err().kind(), io::ErrorKind::InvalidInput);
    }

    #[test]
    fn rejects_intermediate_symlink_escape_for_all_leaf_operations() {
        let tmp = tempfile::tempdir().unwrap();
        let outside = tempfile::tempdir().unwrap();
        let outside_existing = outside.path().join("existing.txt");
        let outside_created = outside.path().join("created.txt");

        fs::write(&outside_existing, b"outside").unwrap();
        symlink(outside.path(), tmp.path().join("escape")).unwrap();

        let dir = DirFd::open(tmp.path()).unwrap();

        assert!(dir.open_file("escape/existing.txt").is_err());
        assert!(dir.metadata("escape/existing.txt").is_err());
        assert!(dir.identity("escape/existing.txt").is_err());
        assert!(dir.create_file("escape/created.txt", UnixMode::OWNER_READ_WRITE).is_err());
        assert!(dir.remove_file("escape/existing.txt").is_err());

        assert_eq!(fs::read(&outside_existing).unwrap(), b"outside");
        assert!(!outside_created.exists());
    }

    #[test]
    fn create_is_exclusive() {
        let tmp = tempfile::tempdir().unwrap();
        let dir = DirFd::open(tmp.path()).unwrap();

        dir.create_file("once", UnixMode::OWNER_READ_WRITE).unwrap();
        assert_eq!(
            dir.create_file("once", UnixMode::OWNER_READ_WRITE).unwrap_err().kind(),
            io::ErrorKind::AlreadyExists
        );
    }

    #[test]
    fn hardlink_and_rename_preserve_file_identity() {
        let tmp = tempfile::tempdir().unwrap();
        let dir = DirFd::open(tmp.path()).unwrap();

        fs::write(tmp.path().join("original"), b"identity").unwrap();
        let original = dir.identity("original").unwrap();

        if let Err(error) = fs::hard_link(tmp.path().join("original"), tmp.path().join("alias")) {
            if !hardlink_can_be_unavailable(&error) {
                panic!("hard_link failed unexpectedly: {error}");
            }
        } else {
            let alias = dir.identity("alias").unwrap();
            assert_eq!(original, alias);
            assert_eq!(
                alias,
                FileIdentity::from_metadata(&fs::metadata(tmp.path().join("alias")).unwrap())
            );
        }

        fs::rename(tmp.path().join("original"), tmp.path().join("renamed")).unwrap();
        assert_eq!(dir.identity("renamed").unwrap(), original);
        assert_eq!(dir.identity("original").unwrap_err().kind(), io::ErrorKind::NotFound);
    }

    #[test]
    fn directory_entries_have_stable_identity_through_trailing_slash_paths() {
        let tmp = tempfile::tempdir().unwrap();
        fs::create_dir(tmp.path().join("cache")).unwrap();
        let dir = DirFd::open(tmp.path()).unwrap();

        let direct = dir.identity("cache").unwrap();
        let with_trailing_slash = dir.identity("cache/").unwrap();
        let with_dot = dir.identity("cache/.").unwrap();
        let from_metadata =
            FileIdentity::from_metadata(&fs::metadata(tmp.path().join("cache")).unwrap());

        assert_eq!(direct, from_metadata);
        assert_eq!(with_trailing_slash, direct);
        assert_eq!(with_dot, direct);
    }

    #[test]
    fn os_string_paths_preserve_file_name_bytes() {
        let tmp = tempfile::tempdir().unwrap();
        fs::create_dir(tmp.path().join("bytes")).unwrap();
        let dir = DirFd::open(tmp.path()).unwrap();

        assert_os_string_round_trip(&dir, tmp.path(), b"proof-\xe2\x98\x83.bin").unwrap();
        if let Err(error) = assert_os_string_round_trip(&dir, tmp.path(), b"proof-\xff-\xfe.bin")
            && !non_utf8_names_can_be_unavailable(&error)
        {
            panic!("non-UTF-8 file name failed unexpectedly: {error}");
        }
    }

    fn assert_os_string_round_trip(dir: &DirFd, root: &Path, name: &[u8]) -> io::Result<()> {
        let file_name = OsString::from_vec(name.to_vec());
        let relative = Path::new("bytes").join(&file_name);
        let absolute = root.join(&relative);

        let mut created = dir.create_file(&relative, UnixMode::OWNER_READ_WRITE)?;
        created.write_all(b"byte-exact")?;
        drop(created);

        let mut reopened = dir.open_file(&relative)?;
        let mut contents = Vec::new();
        reopened.read_to_end(&mut contents)?;
        assert_eq!(contents, b"byte-exact");
        assert_eq!(
            dir.identity(&relative)?,
            FileIdentity::from_metadata(&fs::metadata(&absolute)?)
        );

        let entry_names = fs::read_dir(root.join("bytes"))?
            .map(|entry| entry.unwrap().file_name())
            .collect::<Vec<_>>();
        assert!(
            entry_names
                .iter()
                .any(|name| name.as_os_str().as_bytes() == file_name.as_os_str().as_bytes())
        );

        dir.remove_file(&relative)?;
        assert!(!absolute.exists());
        Ok(())
    }

    #[test]
    fn invalid_paths_fail_before_leaf_operations() {
        let tmp = tempfile::tempdir().unwrap();
        let dir = DirFd::open(tmp.path()).unwrap();
        let bad_nul = PathBuf::from(OsString::from_vec(b"bad\0name".to_vec()));

        for path in [
            Path::new(""),
            Path::new("/absolute"),
            Path::new("../escape"),
            Path::new("cache/../escape"),
            bad_nul.as_path(),
        ] {
            assert_invalid_input(dir.open_file(path));
            assert_invalid_input(dir.metadata(path));
            assert_invalid_input(dir.identity(path));
            assert_invalid_input(dir.create_file(path, UnixMode::OWNER_READ_WRITE));
            assert_invalid_input(dir.remove_file(path));
        }
    }

    #[test]
    fn final_symlink_open_and_metadata_fail_without_following_target() {
        let tmp = tempfile::tempdir().unwrap();
        fs::write(tmp.path().join("target"), b"target").unwrap();
        symlink("target", tmp.path().join("link")).unwrap();
        let dir = DirFd::open(tmp.path()).unwrap();

        assert_eq!(dir.open_file("link").unwrap_err().raw_os_error(), Some(libc::ELOOP));
        assert_eq!(dir.metadata("link").unwrap_err().raw_os_error(), Some(libc::ELOOP));

        let target_identity = dir.identity("target").unwrap();
        let link_identity = dir.identity("link").unwrap();
        assert_ne!(link_identity, target_identity);
        assert_eq!(
            link_identity,
            FileIdentity::from_metadata(&fs::symlink_metadata(tmp.path().join("link")).unwrap())
        );

        dir.remove_file("link").unwrap();
        assert_eq!(fs::read(tmp.path().join("target")).unwrap(), b"target");
        assert!(!tmp.path().join("link").exists());
    }

    fn assert_invalid_input<T: std::fmt::Debug>(result: io::Result<T>) {
        assert_eq!(result.unwrap_err().kind(), io::ErrorKind::InvalidInput);
    }

    fn hardlink_can_be_unavailable(error: &io::Error) -> bool {
        let Some(code) = error.raw_os_error() else {
            return false;
        };
        code == libc::EOPNOTSUPP || code == libc::ENOTSUP || code == libc::EPERM
    }

    fn non_utf8_names_can_be_unavailable(error: &io::Error) -> bool {
        error.raw_os_error() == Some(libc::EILSEQ)
    }
}
