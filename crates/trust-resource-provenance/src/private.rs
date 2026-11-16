// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

//! Read-only owner-private opens. The Apple ACL policy follows maintained
//! astream-sys owner_private: an allow entry is not owner-only, deny entries
//! confer no access. Unknown ACL observations refuse instead of granting.
use std::ffi::{CString, OsStr};
use std::fs::{File, Metadata};
use std::io::{self, Read};
use std::os::fd::{AsRawFd, FromRawFd};
use std::os::unix::ffi::OsStrExt;
use std::os::unix::fs::MetadataExt;
use std::path::{Component, Path};

use crate::schema::{FileId, refused};

pub(crate) fn identity(meta: &Metadata) -> FileId {
    FileId::of_metadata(meta)
}
pub(crate) fn stamp(meta: &Metadata) -> (FileId, u64, u64, u32, u64, i64, i64, i64, i64) {
    (
        identity(meta),
        meta.len(),
        meta.nlink(),
        meta.mode(),
        u64::from(meta.uid()),
        meta.mtime(),
        meta.mtime_nsec(),
        meta.ctime(),
        meta.ctime_nsec(),
    )
}
pub(crate) fn owned(file: &File, directory: bool) -> io::Result<()> {
    let m = file.metadata()?;
    // SAFETY: geteuid reads the current effective account identity only.
    if m.uid() != unsafe { libc::geteuid() } {
        return Err(refused("provenance backing belongs to another account"));
    }
    if m.mode() & 0o7077 != 0 {
        return Err(refused("provenance backing has public or special mode bits"));
    }
    if if directory { !m.is_dir() } else { !m.is_file() || m.nlink() != 1 } {
        return Err(refused("provenance backing has wrong kind or link count"));
    }
    require_no_acl_grants(file)?;
    Ok(())
}

/// Recheck a held directory's current name without opening any replacement.
/// Every component is observed without following its final symlink. The held
/// descriptor remains the input owner; metadata at a name only vetoes reuse.
pub(crate) fn named_directory(path: &Path, held: &File) -> io::Result<()> {
    if !path.is_absolute() {
        return Err(refused("absolute provenance path required"));
    }
    let mut prefix = std::path::PathBuf::new();
    for component in path.components() {
        match component {
            Component::RootDir | Component::Normal(_) => prefix.push(component.as_os_str()),
            _ => return Err(refused("noncanonical provenance path")),
        }
        if !std::fs::symlink_metadata(&prefix)?.is_dir() {
            return Err(refused("provenance directory component changed"));
        }
    }
    owned(held, true)?;
    if identity(&std::fs::symlink_metadata(path)?) != identity(&held.metadata()?) {
        return Err(refused("provenance directory replaced"));
    }
    Ok(())
}

/// A current-name check is never an open or an import of newly selected bytes.
pub(crate) fn named_file(path: &Path, held: &File) -> io::Result<()> {
    owned(held, false)?;
    if stamp(&std::fs::symlink_metadata(path)?) != stamp(&held.metadata()?) {
        return Err(refused("provenance original file name changed"));
    }
    Ok(())
}

pub(crate) fn read_original(file: &File, max: usize) -> io::Result<Vec<u8>> {
    use std::os::unix::fs::FileExt as _;
    owned(file, false)?;
    let before = file.metadata()?;
    if before.len() > max as u64 {
        return Err(refused("oversized original private record"));
    }
    let mut bytes = vec![0; before.len() as usize];
    file.read_exact_at(&mut bytes, 0)?;
    if stamp(&before) != stamp(&file.metadata()?) {
        return Err(refused("original private record changed during read"));
    }
    Ok(bytes)
}

pub use trust_fs_acl::{require_no_acl_entries, require_no_acl_grants};

fn open_at(parent: i32, name: &OsStr, flags: i32) -> io::Result<File> {
    let name = CString::new(name.as_bytes()).map_err(|_| refused("path contains NUL"))?;
    // SAFETY: name is NUL-terminated. Read-only flags never create an entry;
    // parent is a held directory or AT_FDCWD for the absolute root.
    let fd = unsafe {
        libc::openat(
            parent,
            name.as_ptr(),
            flags | libc::O_CLOEXEC | libc::O_NOFOLLOW | libc::O_NONBLOCK,
        )
    };
    if fd < 0 {
        return Err(io::Error::last_os_error());
    }
    // SAFETY: successful openat returned this newly owned descriptor.
    Ok(unsafe { File::from_raw_fd(fd) })
}
pub(crate) fn directory(path: &Path) -> io::Result<File> {
    if !path.is_absolute() {
        return Err(refused("absolute provenance path required"));
    }
    let mut dir = open_at(libc::AT_FDCWD, OsStr::new("/"), libc::O_RDONLY | libc::O_DIRECTORY)?;
    for part in path.components() {
        match part {
            Component::RootDir => {}
            Component::Normal(name) => {
                dir = open_at(dir.as_raw_fd(), name, libc::O_RDONLY | libc::O_DIRECTORY)?
            }
            _ => return Err(refused("noncanonical provenance path")),
        }
    }
    owned(&dir, true)?;
    Ok(dir)
}
pub(crate) fn open_private(dir: &File, name: &OsStr) -> io::Result<File> {
    if name.is_empty()
        || Path::new(name).components().count() != 1
        || !matches!(Path::new(name).components().next(), Some(Component::Normal(_)))
    {
        return Err(refused("private filename must be one component"));
    }
    owned(dir, true)?;
    let file = open_at(dir.as_raw_fd(), name, libc::O_RDONLY)?;
    owned(&file, false)?;
    Ok(file)
}
pub(crate) fn read_private(dir: &File, name: &OsStr, max: usize) -> io::Result<(Vec<u8>, File)> {
    let mut file = open_private(dir, name)?;
    let before = file.metadata()?;
    if before.len() > max as u64 {
        return Err(refused("oversized private record"));
    }
    let mut bytes = Vec::new();
    (&mut file).take(max as u64 + 1).read_to_end(&mut bytes)?;
    if bytes.len() > max
        || bytes.len() as u64 != before.len()
        || stamp(&before) != stamp(&file.metadata()?)
    {
        return Err(refused("private record changed during read"));
    }
    Ok((bytes, file))
}

#[cfg(test)]
#[path = "private/tests.rs"]
mod tests;
