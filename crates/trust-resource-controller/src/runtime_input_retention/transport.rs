//! The caller owns peer authentication and original Host preparation guard.
//! No receiver creates a completion/release/SDK/resource owner from these FDs.
use std::collections::BTreeSet;
use std::io;
use std::os::fd::{AsFd, AsRawFd, BorrowedFd, OwnedFd};
use std::time::Instant;

use super::{CHUNK_INPUTS, Input, Kind, Request, Transfer};
use crate::Channel;

fn time(deadline: Instant) -> io::Result<()> {
    if Instant::now() >= deadline { Err(io::ErrorKind::TimedOut.into()) } else { Ok(()) }
}

/// Host sends its final reply then closes only this connection's write half.
/// Runtime-retention Host must independently retain the SAME socket description
/// with input custody through typed original-root settlement, preserving native
/// peer revalidation after EOF. This shutdown releases no input/lease owner.
pub fn finish_reply(channel: &mut Channel) -> io::Result<()> {
    channel.end_retained_send()
}
pub fn require_reply_eof(channel: &mut Channel, deadline: Instant) -> io::Result<()> {
    channel.require_retained_eof(deadline)
}

fn check(input: &Input, fd: BorrowedFd<'_>) -> io::Result<()> {
    let mut stat = std::mem::MaybeUninit::<libc::stat>::uninit();
    // SAFETY: observe held original/freshly received descriptors only.
    if unsafe { libc::fstat(fd.as_raw_fd(), stat.as_mut_ptr()) } != 0 {
        return Err(io::Error::last_os_error());
    }
    let stat = unsafe { stat.assume_init() };
    // ino_t is platform-dependent; normalize to the wire identity's width.
    let inode: u64 = stat.st_ino as _;
    let flags = unsafe { libc::fcntl(fd.as_raw_fd(), libc::F_GETFL) };
    let inherited = unsafe { libc::fcntl(fd.as_raw_fd(), libc::F_GETFD) };
    let mode = if input.kind == Kind::OutputLock { libc::O_RDWR } else { libc::O_RDONLY };
    let file_type = if input.kind.directory() { libc::S_IFDIR } else { libc::S_IFREG };
    if flags < 0 || inherited < 0 {
        return Err(io::Error::last_os_error());
    }
    if flags & libc::O_ACCMODE != mode
        || inherited & libc::FD_CLOEXEC == 0
        || stat.st_mode & libc::S_IFMT != file_type
        || stat.st_dev as u64 != input.backing.device
        || inode != input.backing.inode
        || stat.st_size < 0
        || input.size.is_some_and(|size| stat.st_size as u64 != size)
        || (!input.kind.directory() && stat.st_mode & 0o111 != 0) != input.executable
    {
        return Err(crate::wire::invalid());
    }
    Ok(())
}
pub fn check_inputs(request: &Request, fds: &[BorrowedFd<'_>]) -> io::Result<()> {
    request.validate()?;
    if fds.len() != request.inputs.len() {
        return Err(crate::wire::invalid());
    }
    let mut unique = BTreeSet::new();
    for (input, fd) in request.inputs.iter().zip(fds) {
        if !unique.insert(fd.as_raw_fd()) {
            return Err(crate::wire::invalid());
        }
        check(input, *fd)?;
    }
    Ok(())
}
/// Send once, after the authenticated Accepted reply. Caller retains the actual
/// complete original owners through its separately authorized handoff. Any error
/// is ambiguous delivery: never replay or release a durable withheld owner.
pub fn send_inputs(
    channel: &mut Channel,
    request: &Request,
    fds: &[BorrowedFd<'_>],
    deadline: Instant,
    mut revalidate: impl FnMut() -> io::Result<()>,
) -> io::Result<()> {
    let result = (|| {
        time(deadline)?;
        check_inputs(request, fds)?;
        for (index, chunk) in fds.chunks(CHUNK_INPUTS).enumerate() {
            revalidate()?;
            time(deadline)?;
            channel.send(
                &Transfer::Chunk {
                    key: request.key(),
                    offset: index * CHUNK_INPUTS,
                    count: chunk.len(),
                }
                .encode()?,
                deadline,
            )?;
            channel.send_retained_inputs(chunk, deadline)?;
        }
        check_inputs(request, fds)?;
        revalidate()?;
        time(deadline)?;
        channel
            .send(&Transfer::End { key: request.key(), count: fds.len() }.encode()?, deadline)?;
        channel.end_retained_send()?;
        revalidate()?;
        time(deadline)
    })();
    if result.is_err() {
        channel.poison();
    }
    result
}
/// Own every actual received prefix until complete terminal+write-half EOF.
/// The callback rechecks the SAME actual peer/original-root eligibility before
/// each chunk and after EOF. Any failure closes all accumulated descriptions.
pub fn receive_inputs(
    channel: &mut Channel,
    request: &Request,
    deadline: Instant,
    mut revalidate: impl FnMut() -> io::Result<()>,
) -> io::Result<Vec<OwnedFd>> {
    let result = (|| {
        time(deadline)?;
        request.validate()?;
        let mut actual = Vec::with_capacity(request.inputs.len());
        while actual.len() < request.inputs.len() {
            revalidate()?;
            time(deadline)?;
            let frame = Transfer::decode(&channel.receive(deadline)?)?;
            let count = (request.inputs.len() - actual.len()).min(CHUNK_INPUTS);
            if frame != (Transfer::Chunk { key: request.key(), offset: actual.len(), count }) {
                return Err(crate::wire::invalid());
            }
            let next = channel.receive_retained_inputs(count, deadline)?;
            for (input, fd) in request.inputs[actual.len()..actual.len() + count].iter().zip(&next)
            {
                check(input, fd.as_fd())?;
            }
            actual.extend(next);
        }
        if Transfer::decode(&channel.receive(deadline)?)?
            != (Transfer::End { key: request.key(), count: actual.len() })
        {
            return Err(crate::wire::invalid());
        }
        channel.require_retained_eof(deadline)?;
        revalidate()?;
        check_inputs(request, &actual.iter().map(AsFd::as_fd).collect::<Vec<_>>())?;
        time(deadline)?;
        Ok(actual)
    })();
    if result.is_err() {
        channel.poison();
    }
    result
}
