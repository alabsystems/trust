//! Two original source descriptions; no path reopening creates source custody.
//! The caller retains and rechecks the actual source owner through retirement.
use std::io;
use std::os::fd::{AsFd as _, AsRawFd as _, BorrowedFd, FromRawFd as _, OwnedFd};
use std::time::Instant;

use super::{Request, SOURCE_BYTES, SOURCE_MARKER};
use crate::{Channel, FileIdentity};

fn time(deadline: Instant) -> io::Result<()> {
    if Instant::now() >= deadline { Err(io::ErrorKind::TimedOut.into()) } else { Ok(()) }
}
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
    // SAFETY: observe an actual borrowed original without changing OFD state.
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
fn directory(parent: BorrowedFd<'_>, name: &std::ffi::CStr) -> io::Result<OwnedFd> {
    // SAFETY: held-parent relative, one literal component; never follow a link.
    let raw = unsafe {
        libc::openat(
            parent.as_raw_fd(),
            name.as_ptr(),
            libc::O_RDONLY | libc::O_DIRECTORY | libc::O_NOFOLLOW | libc::O_CLOEXEC,
        )
    };
    if raw < 0 {
        return Err(io::Error::last_os_error());
    }
    Ok(unsafe { OwnedFd::from_raw_fd(raw) })
}
fn named(parent: BorrowedFd<'_>, name: &std::ffi::CStr) -> io::Result<Stamp> {
    let mut stat = std::mem::MaybeUninit::<libc::stat>::uninit();
    // SAFETY: inspect exactly this original parent's named entry, not its target.
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

/// Checks the exact fixed source fragment against original borrowed descriptions
/// and the complete relative name chain. Equality DATA does not reconstruct an
/// OriginalSourceRoot, output guard, SDK or resource admission.
pub fn check_source(
    request: &Request,
    fds: &[BorrowedFd<'_>; 2],
    deadline: Instant,
) -> io::Result<()> {
    time(deadline)?;
    request.validate()?;
    if fds[0].as_raw_fd() == fds[1].as_raw_fd() {
        return Err(crate::wire::invalid());
    }
    let root = inspect(fds[0])?;
    let source = inspect(fds[1])?;
    if root.identity != request.source_directory
        || root.mode & libc::S_IFMT != libc::S_IFDIR
        || source.identity
            != (FileIdentity { device: request.source.device, inode: request.source.inode })
        || source.mode & libc::S_IFMT != libc::S_IFREG
        || source.links == 0
        || source.bytes != SOURCE_BYTES.len() as i64
    {
        return Err(crate::wire::invalid());
    }
    // These are temporary read-only namespace observations beneath the SAME
    // supplied root; none acquires or substitutes the actual source owner.
    let src = directory(fds[0], c"src")?;
    let src_before = inspect(src.as_fd())?;
    let bootstrap = directory(src.as_fd(), c"bootstrap")?;
    let bootstrap_before = inspect(bootstrap.as_fd())?;
    if named(fds[0], c"src")? != src_before
        || named(src.as_fd(), c"bootstrap")? != bootstrap_before
        || named(bootstrap.as_fd(), c"native_object.rs")? != source
    {
        return Err(crate::wire::invalid());
    }
    let mut bytes = [0u8; SOURCE_BYTES.len()];
    let mut offset = 0;
    while offset < bytes.len() {
        time(deadline)?;
        // SAFETY: bounded positional read changes no shared file cursor.
        let count = unsafe {
            libc::pread(
                fds[1].as_raw_fd(),
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
    if bytes.as_slice() != SOURCE_BYTES
        || inspect(fds[1])? != source
        || named(bootstrap.as_fd(), c"native_object.rs")? != source
        || inspect(bootstrap.as_fd())? != bootstrap_before
        || named(src.as_fd(), c"bootstrap")? != bootstrap_before
        || inspect(src.as_fd())? != src_before
        || named(fds[0], c"src")? != src_before
        || inspect(fds[0])? != root
    {
        return Err(crate::wire::invalid());
    }
    time(deadline)
}

/// Send once only after this operation's authenticated Prepared event. The
/// actual original source owner must outlive the operation on both sides.
pub fn send_source(
    channel: &mut Channel,
    request: &Request,
    fds: &[BorrowedFd<'_>; 2],
    deadline: Instant,
    mut revalidate: impl FnMut() -> io::Result<()>,
) -> io::Result<()> {
    let result = (|| {
        check_source(request, fds, deadline)?;
        revalidate()?;
        time(deadline)?;
        channel.send_bootstrap_descriptions(fds, SOURCE_MARKER, deadline)?;
        check_source(request, fds, deadline)?;
        revalidate()?;
        time(deadline)
    })();
    if result.is_err() {
        channel.poison();
    }
    result
}
pub fn receive_source(
    channel: &mut Channel,
    request: &Request,
    deadline: Instant,
    mut revalidate: impl FnMut() -> io::Result<()>,
) -> io::Result<[OwnedFd; 2]> {
    let result = (|| {
        time(deadline)?;
        revalidate()?;
        time(deadline)?;
        let fds: [OwnedFd; 2] = channel
            .receive_bootstrap_descriptions(SOURCE_MARKER, deadline)?
            .try_into()
            .map_err(|_| crate::wire::invalid())?;
        check_source(request, &fds.each_ref().map(|fd| fd.as_fd()), deadline)?;
        revalidate()?;
        time(deadline)?;
        Ok(fds)
    })();
    if result.is_err() {
        channel.poison();
    }
    result
}

#[cfg(test)]
mod tests;
