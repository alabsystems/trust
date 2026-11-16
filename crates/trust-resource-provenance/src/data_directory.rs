// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

//! Bounded descriptor-relative DATA filesystem mechanics. A caller must own
//! its write policy, disjointness checks and original-name bookends. Neither
//! a File nor success here grants SDK, resource, custody or proof authority.
//! Keeping these syscalls here preserves consumers' forbid(unsafe_code).
//!
//! Mutation excludes other UIDs with owner/mode/ACL admission. Root and the
//! current UID are trusted principals: POSIX permissions cannot isolate a
//! malicious same-UID process. Directory leases serialize cooperating callers;
//! callers still hold their normal exclusive build/output lifecycle lease.

use std::ffi::{CStr, CString, OsStr, OsString};
use std::fs::File;
use std::io::{self, Write};
use std::os::fd::{AsRawFd, FromRawFd, IntoRawFd};
use std::os::unix::ffi::{OsStrExt, OsStringExt};
use std::os::unix::fs::MetadataExt;
use std::ptr::NonNull;

fn refused(reason: &str) -> io::Error { io::Error::other(reason) }
fn name(value: &OsStr) -> io::Result<CString> {
    if value.is_empty() || value.as_bytes().contains(&b'/') {
        return Err(refused("non-component DATA directory name"));
    }
    CString::new(value.as_bytes()).map_err(|_| refused("NUL in DATA directory name"))
}

fn new_name(value: &OsStr) -> io::Result<CString> {
    if value == OsStr::new(".") || value == OsStr::new("..") {
        return Err(refused("DATA write name is not a new child component"));
    }
    name(value)
}

fn open_at(parent: &File, leaf: &OsStr, directory: bool) -> io::Result<File> {
    let leaf = name(leaf)?;
    let flags = libc::O_RDONLY | libc::O_CLOEXEC | libc::O_NOFOLLOW | libc::O_NONBLOCK
        | if directory { libc::O_DIRECTORY } else { 0 };
    // SAFETY: live parent descriptor, bounded NUL-terminated component and
    // read-only flags. Successful descriptor ownership transfers to File once.
    let fd = unsafe { libc::openat(parent.as_raw_fd(), leaf.as_ptr(), flags) };
    if fd < 0 { return Err(io::Error::last_os_error()); }
    let file = unsafe { File::from_raw_fd(fd) };
    let meta = file.metadata()?;
    if (directory && !meta.is_dir()) || (!directory && !meta.is_file()) {
        return Err(refused("DATA member is not an ordinary directory or file"));
    }
    Ok(file)
}

/// Open a single no-follow directory component below an actual descriptor.
/// The caller supplies any admission/ownership policy; this supplies none.
pub fn open_directory_at(parent: &File, leaf: &OsStr) -> io::Result<File> {
    open_at(parent, leaf, true)
}
/// Open a single no-follow, nonblocking ordinary read-only file component.
pub fn open_regular_at(parent: &File, leaf: &OsStr) -> io::Result<File> {
    open_at(parent, leaf, false)
}

/// Exclusively create one directory below the actual parent; no path walk.
pub fn create_directory_at(parent: &File, leaf: &OsStr) -> io::Result<()> {
    require_owner_mutation_scope(parent)?;
    let leaf = new_name(leaf)?;
    // SAFETY: actual held parent and a single live component.
    if unsafe { libc::mkdirat(parent.as_raw_fd(), leaf.as_ptr(), 0o755) } != 0 {
        return Err(io::Error::last_os_error());
    }
    Ok(())
}

pub fn effective_uid() -> u32 {
    // SAFETY: observation of this process's UID, without mutation or pointers.
    unsafe { libc::geteuid() }
}

/// Require an effective-UID-owned ordinary directory with no group/other
/// write and no extended access/default ACL entries. Do not chmod an unsafe
/// existing directory into eligibility. Unknown ACL observations refuse.
pub fn require_owner_mutation_scope(directory: &File) -> io::Result<()> {
    let before = directory.metadata()?;
    if !before.is_dir() || before.uid() != effective_uid() || before.mode() & 0o022 != 0 {
        return Err(refused("DATA mutation parent has foreign ownership or public write access"));
    }
    crate::require_no_acl_entries(directory)?;
    let after = directory.metadata()?;
    if (before.dev(), before.ino(), before.uid(), before.mode())
        != (after.dev(), after.ino(), after.uid(), after.mode())
    { return Err(refused("DATA mutation parent changed during admission")); }
    Ok(())
}

/// Advisory exclusion among cooperating stagers using the same actual
/// directory. This does not authenticate a Bootstrap/build lease, exclude a
/// malicious same UID/root, or confer resource/custody authority.
pub struct DirectoryMutationLease { file: File }
impl Drop for DirectoryMutationLease {
    fn drop(&mut self) {
        // SAFETY: unlock only this guard's original held open description.
        unsafe { libc::flock(self.file.as_raw_fd(), libc::LOCK_UN) };
    }
}
pub fn try_lock_owner_directory(directory: &File) -> io::Result<DirectoryMutationLease> {
    require_owner_mutation_scope(directory)?;
    // A fresh open description makes even a second request through the same
    // borrowed File contend rather than silently share/unlock another guard.
    let file = open_directory_at(directory, OsStr::new("."))?;
    let original = directory.metadata()?;
    let current = file.metadata()?;
    if (original.dev(), original.ino()) != (current.dev(), current.ino()) {
        return Err(refused("DATA writer lease differs from held directory"));
    }
    // SAFETY: nonblocking advisory lock on this actual held directory only.
    if unsafe { libc::flock(file.as_raw_fd(), libc::LOCK_EX | libc::LOCK_NB) } != 0 {
        return Err(io::Error::last_os_error());
    }
    let lease = DirectoryMutationLease { file };
    require_owner_mutation_scope(directory)?;
    Ok(lease)
}

struct Listing(Option<NonNull<libc::DIR>>);
impl Listing {
    fn close(mut self) -> io::Result<()> {
        let pointer = self.0.take().ok_or_else(|| refused("DATA listing already closed"))?;
        // SAFETY: this method consumes the listing's sole owned handle.
        if unsafe { libc::closedir(pointer.as_ptr()) } != 0 {
            return Err(io::Error::last_os_error());
        }
        Ok(())
    }
}
impl Drop for Listing {
    fn drop(&mut self) {
        if let Some(pointer) = self.0.take() {
            // SAFETY: this listing exclusively owns its fdopendir handle.
            unsafe { libc::closedir(pointer.as_ptr()) };
        }
    }
}
/// List through a fresh description without changing the original's cursor.
/// Membership above the caller's finite bound refuses instead of truncating.
pub fn names(directory: &File, bound: usize) -> io::Result<Vec<OsString>> {
    let fd = open_directory_at(directory, OsStr::new("."))?.into_raw_fd();
    // SAFETY: transfer a new owned directory description on success only.
    let pointer = unsafe { libc::fdopendir(fd) };
    let Some(pointer) = NonNull::new(pointer) else {
        let error = io::Error::last_os_error();
        unsafe { libc::close(fd) };
        return Err(error);
    };
    let listing = Listing(Some(pointer));
    let mut result = Vec::new();
    loop {
        // SAFETY: supported platform's thread-local errno and live listing.
        #[cfg(target_os = "macos")]
        unsafe { *libc::__error() = 0; }
        #[cfg(target_os = "linux")]
        unsafe { *libc::__errno_location() = 0; }
        let entry = unsafe { libc::readdir(pointer.as_ptr()) };
        if entry.is_null() {
            #[cfg(target_os = "macos")]
            let error = unsafe { *libc::__error() };
            #[cfg(target_os = "linux")]
            let error = unsafe { *libc::__errno_location() };
            if error != 0 { return Err(io::Error::from_raw_os_error(error)); }
            break;
        }
        // SAFETY: readdir's d_name is NUL-terminated until its next call.
        // Copy it before advancing or closing the listing.
        let bytes = unsafe { CStr::from_ptr((*entry).d_name.as_ptr()) }.to_bytes();
        if bytes == b"." || bytes == b".." { continue; }
        if bytes.is_empty() || bytes.contains(&b'/') || result.len() >= bound {
            return Err(refused("DATA directory listing exceeds bound"));
        }
        result.push(OsString::from_vec(bytes.to_vec()));
    }
    listing.close()?;
    result.sort();
    if result.windows(2).any(|pair| pair[0] == pair[1]) {
        return Err(refused("duplicate DATA directory membership"));
    }
    Ok(result)
}

/// Exclusively create and sync a new ordinary file below an actual parent.
/// Existing names and physical output aliases refuse; no overwrite fallback.
pub fn write_new_at(parent: &File, leaf: &OsStr, bytes: &[u8]) -> io::Result<()> {
    require_owner_mutation_scope(parent)?;
    let leaf = new_name(leaf)?;
    // SAFETY: one live component and exclusive no-follow creation. Transfer
    // the new descriptor to File once, never the borrowed parent's descriptor.
    let fd = unsafe { libc::openat(parent.as_raw_fd(), leaf.as_ptr(),
        libc::O_WRONLY | libc::O_CREAT | libc::O_EXCL | libc::O_NOFOLLOW | libc::O_CLOEXEC,
        0o644) };
    if fd < 0 { return Err(io::Error::last_os_error()); }
    let mut file = unsafe { File::from_raw_fd(fd) };
    if !file.metadata()?.is_file() || file.metadata()?.nlink() != 1
        || file.metadata()?.uid() != effective_uid() || file.metadata()?.mode() & 0o022 != 0
    {
        return Err(refused("DATA staging file is not a new unaliased ordinary file"));
    }
    crate::require_no_acl_entries(&file)?;
    file.write_all(bytes)?;
    file.sync_all()?;
    if file.metadata()?.nlink() != 1 || file.metadata()?.mode() & 0o022 != 0 {
        return Err(refused("DATA staging file acquired a physical alias"));
    }
    crate::require_no_acl_entries(&file)?;
    require_owner_mutation_scope(parent)?;
    Ok(())
}

/// Atomically publish a new directory without replacing ANY existing name.
/// No plain-rename fallback is allowed on an unsupported filesystem/kernel.
pub fn publish_directory_exclusive_at(
    parent: &File, temporary: &OsStr, expected_source: &File, destination: &OsStr,
) -> io::Result<()> {
    require_owner_mutation_scope(parent)?;
    require_owner_mutation_scope(expected_source)?;
    let named_source = open_directory_at(parent, temporary)?;
    let expected = expected_source.metadata()?;
    let named = named_source.metadata()?;
    if (expected.dev(), expected.ino()) != (named.dev(), named.ino()) {
        return Err(refused("DATA publication source name differs from held validated directory"));
    }
    let temporary = new_name(temporary)?;
    let destination = new_name(destination)?;
    // SAFETY: same actual parent and two live, single-component names. Both
    // platform APIs atomically refuse an existing destination.
    #[cfg(target_os = "macos")]
    let result = unsafe { libc::renameatx_np(parent.as_raw_fd(), temporary.as_ptr(),
        parent.as_raw_fd(), destination.as_ptr(), libc::RENAME_EXCL) };
    #[cfg(target_os = "linux")]
    let result = unsafe { libc::renameat2(parent.as_raw_fd(), temporary.as_ptr(),
        parent.as_raw_fd(), destination.as_ptr(), libc::RENAME_NOREPLACE) };
    if result != 0 { return Err(io::Error::last_os_error()); }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn actual_open_and_creation_refuse_symlinks_existing_files_and_traversal() {
        let temporary = tempfile::tempdir().unwrap();
        let root = File::open(temporary.path()).unwrap();
        write_new_at(&root, OsStr::new("data"), b"original").unwrap();
        assert!(write_new_at(&root, OsStr::new("data"), b"replacement").is_err());
        std::os::unix::fs::symlink("data", temporary.path().join("alias")).unwrap();
        assert!(open_regular_at(&root, OsStr::new("alias")).is_err());
        assert!(write_new_at(&root, OsStr::new("alias"), b"replacement").is_err());
        for name in [".", "..", "a/b"] {
            assert!(create_directory_at(&root, OsStr::new(name)).is_err());
            assert!(write_new_at(&root, OsStr::new(name), b"x").is_err());
        }
        assert_eq!(std::fs::read(temporary.path().join("data")).unwrap(), b"original");
    }

    #[test]
    fn actual_exclusive_publication_never_replaces_an_existing_empty_directory() {
        let temporary = tempfile::tempdir().unwrap();
        let root = File::open(temporary.path()).unwrap();
        create_directory_at(&root, OsStr::new("staging")).unwrap();
        create_directory_at(&root, OsStr::new("existing")).unwrap();
        let staging = open_directory_at(&root, OsStr::new("staging")).unwrap();
        assert!(publish_directory_exclusive_at(&root, OsStr::new("staging"), &staging, OsStr::new("existing")).is_err());
        assert!(temporary.path().join("staging").is_dir());
        assert_eq!(std::fs::read_dir(temporary.path().join("existing")).unwrap().count(), 0);
        publish_directory_exclusive_at(&root, OsStr::new("staging"), &staging, OsStr::new("published")).unwrap();
        assert!(temporary.path().join("published").is_dir());
        assert!(!temporary.path().join("staging").exists());
    }

    #[test]
    fn actual_directory_listing_refuses_overflow_instead_of_truncating() {
        let temporary = tempfile::tempdir().unwrap();
        let root = File::open(temporary.path()).unwrap();
        write_new_at(&root, OsStr::new("a"), b"a").unwrap();
        write_new_at(&root, OsStr::new("b"), b"b").unwrap();
        assert!(names(&root, 1).is_err());
        assert_eq!(names(&root, 2).unwrap(), [OsString::from("a"), OsString::from("b")]);
    }

    #[test]
    fn actual_final_source_name_swap_is_refused_before_fixed_name_publication() {
        let temporary = tempfile::tempdir().unwrap();
        let root = File::open(temporary.path()).unwrap();
        create_directory_at(&root, OsStr::new("staging")).unwrap();
        let staging = open_directory_at(&root, OsStr::new("staging")).unwrap();
        std::fs::rename(temporary.path().join("staging"), temporary.path().join("saved")).unwrap();
        std::fs::create_dir(temporary.path().join("staging")).unwrap();
        std::fs::write(temporary.path().join("staging/unvalidated"), b"must not publish").unwrap();
        assert!(publish_directory_exclusive_at(&root, OsStr::new("staging"), &staging, OsStr::new("fixed")).is_err());
        assert!(!temporary.path().join("fixed").exists());
        assert_eq!(std::fs::read(temporary.path().join("staging/unvalidated")).unwrap(), b"must not publish");
    }

    #[test]
    fn unsafe_posix_mutation_parents_refuse_without_writes_or_mode_repair() {
        use std::os::unix::fs::PermissionsExt;
        for mode in [0o775, 0o777, 0o1777] {
            let temporary = tempfile::tempdir().unwrap();
            std::fs::set_permissions(temporary.path(), std::fs::Permissions::from_mode(mode)).unwrap();
            let root = File::open(temporary.path()).unwrap();
            assert!(require_owner_mutation_scope(&root).is_err());
            assert!(create_directory_at(&root, OsStr::new("child")).is_err());
            assert!(write_new_at(&root, OsStr::new("child"), b"data").is_err());
            assert!(try_lock_owner_directory(&root).is_err());
            assert_eq!(std::fs::read_dir(temporary.path()).unwrap().count(), 0);
            assert_eq!(std::fs::metadata(temporary.path()).unwrap().mode() & 0o7777, mode);
        }
    }

    #[test]
    fn independent_cooperating_directory_writer_is_excluded_until_lease_drop() {
        let temporary = tempfile::tempdir().unwrap();
        let root = File::open(temporary.path()).unwrap();
        let other = File::open(temporary.path()).unwrap();
        let lease = try_lock_owner_directory(&root).unwrap();
        assert!(try_lock_owner_directory(&root).is_err());
        assert!(try_lock_owner_directory(&other).is_err());
        drop(lease);
        assert!(try_lock_owner_directory(&other).is_ok());
    }

    #[test]
    fn actual_extended_or_default_acl_refuses_parent_writes() {
        let temporary = tempfile::tempdir().unwrap();
        let root = File::open(temporary.path()).unwrap();
        #[cfg(target_os = "macos")]
        {
            let output = std::process::Command::new("/bin/chmod").arg("+a")
                .arg("everyone allow add_file,add_subdirectory,delete_child")
                .arg(temporary.path()).output().unwrap();
            assert!(output.status.success(), "{}", String::from_utf8_lossy(&output.stderr));
        }
        #[cfg(target_os = "linux")]
        {
            // Actual Linux POSIX default ACL xattr. Its presence does not
            // change this directory's current group mode bits; NoEntries
            // must reject it independently of the public-write mode check.
            let mut acl = 2u32.to_le_bytes().to_vec();
            for (tag, permissions) in [(1u16, 7u16), (4, 5), (32, 5)] {
                acl.extend_from_slice(&tag.to_le_bytes());
                acl.extend_from_slice(&permissions.to_le_bytes());
                acl.extend_from_slice(&u32::MAX.to_le_bytes());
            }
            // SAFETY: live held test directory, constant xattr name and
            // the complete bounded Linux POSIX ACL byte buffer above.
            assert_eq!(unsafe { libc::fsetxattr(root.as_raw_fd(), c"system.posix_acl_default".as_ptr(),
                acl.as_ptr().cast(), acl.len(), 0) }, 0, "{}", io::Error::last_os_error());
        }
        assert_eq!(root.metadata().unwrap().mode() & 0o022, 0);
        assert!(require_owner_mutation_scope(&root).is_err());
        assert!(create_directory_at(&root, OsStr::new("child")).is_err());
        assert!(!temporary.path().join("child").exists());
    }
}
