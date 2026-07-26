use std::ffi::OsString;
use std::fs::{File, Metadata};
use std::io;
use std::path::Path;

use crate::UnixMode;

/// Directory file descriptor anchor.
#[derive(Debug)]
pub struct DirFd {
    _private: (),
}

impl DirFd {
    /// Opens a directory as a descriptor anchor.
    pub fn open(_path: impl AsRef<Path>) -> io::Result<Self> {
        Err(unsupported())
    }

    /// Opens a file relative to this directory.
    pub fn open_file(&self, _path: impl AsRef<Path>) -> io::Result<File> {
        Err(unsupported())
    }

    /// Opens a file for reading and writing relative to this directory.
    pub fn open_file_read_write(&self, _path: impl AsRef<Path>) -> io::Result<File> {
        Err(unsupported())
    }

    /// Creates a new file relative to this directory.
    pub fn create_file(&self, _path: impl AsRef<Path>, _mode: UnixMode) -> io::Result<File> {
        Err(unsupported())
    }

    /// Removes a file or symlink relative to this directory.
    pub fn remove_file(&self, _path: impl AsRef<Path>) -> io::Result<()> {
        Err(unsupported())
    }

    /// Renames a file within this directory.
    pub fn rename_file(&self, _from: impl AsRef<Path>, _to: impl AsRef<Path>) -> io::Result<()> {
        Err(unsupported())
    }

    /// Makes directory-entry changes durable.
    pub fn sync_all(&self) -> io::Result<()> {
        Err(unsupported())
    }

    /// Reads symlink-aware metadata relative to this directory.
    pub fn metadata(&self, _path: impl AsRef<Path>) -> io::Result<Metadata> {
        Err(unsupported())
    }

    /// Reads stable file identity relative to this directory.
    pub fn identity(&self, _path: impl AsRef<Path>) -> io::Result<FileIdentity> {
        Err(unsupported())
    }

    /// Reads the stable identity of this directory anchor itself.
    pub fn directory_identity(&self) -> io::Result<FileIdentity> {
        Err(unsupported())
    }

    /// Reads the stable identity of an already-open file.
    pub fn file_identity(&self, _file: &File) -> io::Result<FileIdentity> {
        Err(unsupported())
    }

    /// Returns the hard-link count for an already-open file.
    pub fn file_link_count(&self, _file: &File) -> io::Result<u64> {
        Err(unsupported())
    }

    /// Enumerates entry names through this directory anchor.
    pub fn read_dir_names(&self) -> io::Result<Vec<OsString>> {
        Err(unsupported())
    }
}

/// Stable Unix file identity.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct FileIdentity {
    device: u64,
    inode: u64,
}

impl FileIdentity {
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

pub fn open_file_at(dir: &DirFd, path: impl AsRef<Path>) -> io::Result<File> {
    dir.open_file(path)
}

pub fn open_file_read_write_at(dir: &DirFd, path: impl AsRef<Path>) -> io::Result<File> {
    dir.open_file_read_write(path)
}

pub fn create_file_at(dir: &DirFd, path: impl AsRef<Path>, mode: UnixMode) -> io::Result<File> {
    dir.create_file(path, mode)
}

pub fn remove_file_at(dir: &DirFd, path: impl AsRef<Path>) -> io::Result<()> {
    dir.remove_file(path)
}

pub fn rename_file_at(dir: &DirFd, from: impl AsRef<Path>, to: impl AsRef<Path>) -> io::Result<()> {
    dir.rename_file(from, to)
}

pub fn metadata_at(dir: &DirFd, path: impl AsRef<Path>) -> io::Result<Metadata> {
    dir.metadata(path)
}

pub fn identity_at(dir: &DirFd, path: impl AsRef<Path>) -> io::Result<FileIdentity> {
    dir.identity(path)
}

fn unsupported() -> io::Error {
    io::Error::new(
        io::ErrorKind::Unsupported,
        "trust-os anchored filesystem APIs require a supported Unix or Windows host",
    )
}
