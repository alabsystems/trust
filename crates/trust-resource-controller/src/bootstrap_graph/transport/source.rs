//! Validate close-only source descriptions without opening any release owner.
use std::io;
use std::os::fd::{AsFd as _, AsRawFd as _, BorrowedFd, OwnedFd};
use std::time::Instant;

use sha2::{Digest as _, Sha256};

use super::super::{SourceAttachment, SourceRecord};
use crate::{Channel, FileIdentity};

#[derive(PartialEq, Eq)]
struct Stamp {
    identity: FileIdentity,
    mode: libc::mode_t,
    uid: libc::uid_t,
    gid: libc::gid_t,
    links: u64,
    bytes: i64,
    modified: (i64, i64),
    changed: (i64, i64),
}
fn stamp(stat: libc::stat) -> Stamp {
    Stamp {
        identity: FileIdentity { device: stat.st_dev as u64, inode: stat.st_ino },
        mode: stat.st_mode,
        uid: stat.st_uid,
        gid: stat.st_gid,
        links: stat.st_nlink as u64,
        bytes: stat.st_size,
        modified: (stat.st_mtime, stat.st_mtime_nsec),
        changed: (stat.st_ctime, stat.st_ctime_nsec),
    }
}
fn inspect(fd: BorrowedFd<'_>) -> io::Result<Stamp> {
    let mut stat = std::mem::MaybeUninit::<libc::stat>::uninit();
    // SAFETY: observations of this held description, no OFD/cursor changes.
    if unsafe { libc::fstat(fd.as_raw_fd(), stat.as_mut_ptr()) } != 0 {
        return Err(io::Error::last_os_error());
    }
    let flags = unsafe { libc::fcntl(fd.as_raw_fd(), libc::F_GETFL) };
    let local = unsafe { libc::fcntl(fd.as_raw_fd(), libc::F_GETFD) };
    if flags < 0 || local < 0 {
        return Err(io::Error::last_os_error());
    }
    if flags & libc::O_ACCMODE != libc::O_RDONLY || local & libc::FD_CLOEXEC == 0 {
        return Err(crate::wire::invalid());
    }
    Ok(stamp(unsafe { stat.assume_init() }))
}
fn named(parent: BorrowedFd<'_>, name: &std::ffi::CStr) -> io::Result<Stamp> {
    let mut stat = std::mem::MaybeUninit::<libc::stat>::uninit();
    // SAFETY: one fixed leaf at the supplied held directory; no link following.
    if unsafe {
        libc::fstatat(
            parent.as_raw_fd(),
            name.as_ptr(),
            stat.as_mut_ptr(),
            libc::AT_SYMLINK_NOFOLLOW,
        )
    } != 0
    {
        return Err(io::Error::last_os_error());
    }
    Ok(stamp(unsafe { stat.assume_init() }))
}
fn record(
    fd: BorrowedFd<'_>,
    expected: &SourceRecord,
    before: &Stamp,
    deadline: Instant,
) -> io::Result<()> {
    if before.mode & libc::S_IFMT != libc::S_IFREG
        || before.identity != expected.identity
        || before.bytes != expected.bytes as i64
    {
        return Err(crate::wire::invalid());
    }
    // Bounded private bytes; never log/parse tokens or change the shared cursor.
    let mut bytes = vec![0u8; expected.bytes as usize];
    let mut offset = 0;
    while offset < bytes.len() {
        super::time(deadline)?;
        // SAFETY: bounded positional read into a live buffer.
        let count = unsafe {
            libc::pread(
                fd.as_raw_fd(),
                bytes[offset..].as_mut_ptr().cast(),
                bytes.len() - offset,
                offset as libc::off_t,
            )
        };
        if count < 0 {
            let error = io::Error::last_os_error();
            if error.kind() == io::ErrorKind::Interrupted {
                continue;
            }
            return Err(error);
        }
        if count == 0 {
            return Err(crate::wire::invalid());
        }
        offset += count as usize;
    }
    let digest: [u8; 32] = Sha256::digest(&bytes).into();
    if digest != expected.sha256 || inspect(fd)? != *before {
        return Err(crate::wire::invalid());
    }
    super::time(deadline)
}

/// Names and bounded record DATA bind the actual supplied descriptions only.
/// Authentication/original-producer lineage and lifetime remain the caller's
/// obligation; this creates no Manager or recursively immutable source tree.
pub fn check_source(
    request: &SourceAttachment,
    fds: &[BorrowedFd<'_>; 4],
    deadline: Instant,
) -> io::Result<()> {
    super::time(deadline)?;
    request.validate()?;
    for (index, fd) in fds.iter().enumerate() {
        if fds[..index].iter().any(|other| other.as_raw_fd() == fd.as_raw_fd()) {
            return Err(crate::wire::invalid());
        }
    }
    let before = [inspect(fds[0])?, inspect(fds[1])?, inspect(fds[2])?, inspect(fds[3])?];
    if before[0].identity != request.source_directory
        || before[1].identity != request.holder_directory
        || before[0].mode & libc::S_IFMT != libc::S_IFDIR
        || before[1].mode & libc::S_IFMT != libc::S_IFDIR
        || before[0].links == 0
        || before[1].links == 0
        || before[2].links > 1
        || before[3].links != 1
        || named(fds[0], c".trust-build-lock")? != before[1]
        || named(fds[1], c"info")? != before[3]
    {
        return Err(crate::wire::invalid());
    }
    record(fds[2], &request.original_record, &before[2], deadline)?;
    record(fds[3], &request.withheld_record, &before[3], deadline)?;
    if named(fds[0], c".trust-build-lock")? != before[1] || named(fds[1], c"info")? != before[3] {
        return Err(crate::wire::invalid());
    }
    for (fd, stamp) in fds.iter().zip(&before) {
        if inspect(*fd)? != *stamp {
            return Err(crate::wire::invalid());
        }
    }
    super::time(deadline)
}
pub fn send_source(
    channel: &mut Channel,
    request: &SourceAttachment,
    fds: &[BorrowedFd<'_>; 4],
    deadline: Instant,
    mut revalidate: impl FnMut() -> io::Result<()>,
) -> io::Result<()> {
    let result = (|| {
        check_source(request, fds, deadline)?;
        revalidate()?;
        super::time(deadline)?;
        channel.send_bootstrap_source_descriptions(fds, deadline)?;
        check_source(request, fds, deadline)?;
        revalidate()?;
        super::time(deadline)
    })();
    if result.is_err() {
        channel.poison();
    }
    result
}
pub fn receive_source(
    channel: &mut Channel,
    request: &SourceAttachment,
    deadline: Instant,
    mut revalidate: impl FnMut() -> io::Result<()>,
) -> io::Result<[OwnedFd; 4]> {
    let result = (|| {
        super::time(deadline)?;
        revalidate()?;
        let fds: [OwnedFd; 4] = channel
            .receive_bootstrap_source_descriptions(deadline)?
            .try_into()
            .map_err(|_| crate::wire::invalid())?;
        check_source(request, &fds.each_ref().map(|fd| fd.as_fd()), deadline)?;
        revalidate()?;
        super::time(deadline)?;
        Ok(fds)
    })();
    if result.is_err() {
        channel.poison();
    }
    result
}

#[cfg(test)]
mod tests;
