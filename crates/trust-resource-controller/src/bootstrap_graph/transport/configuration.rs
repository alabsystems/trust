//! Bounded observations of one actually retained source/configuration pair.
//! These checks grant no original source, parser, dispatch or release authority.
use std::ffi::CString;
use std::io;
use std::os::fd::{AsFd as _, AsRawFd as _, BorrowedFd, FromRawFd as _, OwnedFd};
use std::time::Instant;

use sha2::{Digest as _, Sha256};

use crate::bootstrap_graph::configuration::{ConfigurationAttachment, Timestamp};
use crate::{Channel, FileIdentity};

#[derive(PartialEq, Eq)]
struct Stamp {
    file: FileIdentity,
    mode: libc::mode_t,
    uid: libc::uid_t,
    gid: libc::gid_t,
    links: u64,
    bytes: i64,
    modified: (i64, i64),
    changed: (i64, i64),
}

fn inspect(fd: BorrowedFd<'_>) -> io::Result<Stamp> {
    let mut stat = std::mem::MaybeUninit::<libc::stat>::uninit();
    // SAFETY: observations of this borrowed description only.
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
    let stat = unsafe { stat.assume_init() };
    Ok(Stamp {
        file: FileIdentity { device: stat.st_dev as u64, inode: stat.st_ino },
        mode: stat.st_mode,
        uid: stat.st_uid,
        gid: stat.st_gid,
        links: stat.st_nlink as u64,
        bytes: stat.st_size,
        modified: (stat.st_mtime, stat.st_mtime_nsec),
        changed: (stat.st_ctime, stat.st_ctime_nsec),
    })
}

fn opened(parent: BorrowedFd<'_>, name: &[u8], directory: bool) -> io::Result<OwnedFd> {
    let name = CString::new(name).map_err(|_| crate::wire::invalid())?;
    let flags = libc::O_RDONLY
        | libc::O_NOFOLLOW
        | libc::O_NONBLOCK
        | libc::O_CLOEXEC
        | if directory { libc::O_DIRECTORY } else { 0 };
    // SAFETY: bounded NUL-terminated single component and held parent.
    let fd = unsafe { libc::openat(parent.as_raw_fd(), name.as_ptr(), flags) };
    if fd < 0 {
        return Err(io::Error::last_os_error());
    }
    // SAFETY: successful openat returns this uniquely owned descriptor.
    Ok(unsafe { OwnedFd::from_raw_fd(fd) })
}

fn matches(value: &Stamp, request: &ConfigurationAttachment) -> bool {
    let time = |stamp: Timestamp| (stamp.seconds, i64::from(stamp.nanoseconds));
    value.mode & libc::S_IFMT == libc::S_IFREG
        && value.file == request.file
        && value.bytes == request.bytes as i64
        && value.modified == time(request.modified)
        && value.changed == time(request.changed)
}

/// Recheck the expected readonly original, its root-relative nofollow name and
/// bounded bytes without moving the shared OFD cursor. The enclosing issuer
/// must already retain the actual source and configuration owners before calling.
pub fn check_configuration(
    request: &ConfigurationAttachment,
    source: BorrowedFd<'_>,
    file: BorrowedFd<'_>,
    deadline: Instant,
) -> io::Result<()> {
    super::time(deadline)?;
    request.validate()?;
    let root = inspect(source)?;
    let before = inspect(file)?;
    if root.mode & libc::S_IFMT != libc::S_IFDIR || !matches(&before, request) {
        return Err(crate::wire::invalid());
    }
    let names: Vec<_> = request.relative.split(|byte| *byte == b'/').collect();
    let mut parents = Vec::new();
    for name in &names[..names.len() - 1] {
        super::time(deadline)?;
        let parent = parents.last().map_or(source, |(fd, _): &(OwnedFd, Stamp)| fd.as_fd());
        let fd = opened(parent, name, true)?;
        let stamp = inspect(fd.as_fd())?;
        parents.push((fd, stamp));
    }
    let parent = parents.last().map_or(source, |(fd, _)| fd.as_fd());
    let named = opened(parent, names.last().expect("validated components"), false)?;
    if inspect(named.as_fd())? != before {
        return Err(crate::wire::invalid());
    }
    let mut digest = Sha256::new();
    let mut offset = 0;
    let mut bytes = [0u8; 4096];
    while offset < request.bytes {
        super::time(deadline)?;
        let length = (request.bytes - offset).min(bytes.len() as u64) as usize;
        // SAFETY: bounded positional read; no shared cursor or flag mutation.
        let count = unsafe {
            libc::pread(file.as_raw_fd(), bytes.as_mut_ptr().cast(), length, offset as libc::off_t)
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
        digest.update(&bytes[..count as usize]);
        offset += count as u64;
    }
    let actual: [u8; 32] = digest.finalize().into();
    if actual != request.sha256 || inspect(file)? != before || inspect(source)? != root {
        return Err(crate::wire::invalid());
    }
    let mut parent = source;
    for ((fd, stamp), name) in parents.iter().zip(&names) {
        let named = opened(parent, name, true)?;
        if inspect(fd.as_fd())? != *stamp || inspect(named.as_fd())? != *stamp {
            return Err(crate::wire::invalid());
        }
        parent = fd.as_fd();
    }
    let named = opened(parent, names.last().expect("validated components"), false)?;
    if inspect(named.as_fd())? != before || inspect(file)? != before {
        return Err(crate::wire::invalid());
    }
    super::time(deadline)
}

/// Receive the actual close-only description without reading its contents.
/// The caller must install it in the original operation slot BEFORE validation,
/// so a failed postcheck cannot discard an already delivered original.
pub fn receive_configuration_description(
    channel: &mut Channel,
    deadline: Instant,
) -> io::Result<OwnedFd> {
    let result = (|| {
        super::time(deadline)?;
        let mut fds = channel.receive_bootstrap_configuration_description(deadline)?;
        fds.pop().ok_or_else(crate::wire::invalid)
    })();
    if result.is_err() {
        channel.poison();
    }
    result
}

pub fn send_configuration_description(
    channel: &mut Channel,
    file: BorrowedFd<'_>,
    deadline: Instant,
) -> io::Result<()> {
    channel.send_bootstrap_configuration_description(file, deadline)
}

#[cfg(test)]
mod tests;
