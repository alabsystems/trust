// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

//! Exact one-description liveness transport on the already authenticated host
//! stream. Read-only pipe possession is observation, never resource custody.
use std::fs::File;
use std::mem::{size_of, size_of_val};
use std::os::fd::{FromRawFd, OwnedFd};
use std::os::unix::fs::FileTypeExt;

use super::*;

fn check_read_pipe(fd: BorrowedFd<'_>) -> io::Result<()> {
    // SAFETY: F_GETFL observes a held live description only.
    let flags = unsafe { libc::fcntl(fd.as_raw_fd(), libc::F_GETFL) };
    if flags < 0 {
        return Err(io::Error::last_os_error());
    }
    let file = File::from(fd.try_clone_to_owned()?);
    if flags & libc::O_ACCMODE != libc::O_RDONLY || !file.metadata()?.file_type().is_fifo() {
        return Err(crate::wire::invalid());
    }
    Ok(())
}
impl Channel {
    /// Exactly one tag byte plus one actual read-only pipe description. Call
    /// only after the bound reply ACK; there is no descriptor on Unavailable.
    pub fn send_read_lifeline(&mut self, fd: BorrowedFd<'_>, deadline: Instant) -> io::Result<()> {
        check_read_pipe(fd)?;
        self.begin()?;
        let mut byte = *b"R";
        // SAFETY: CMSG_SPACE computes native storage for one descriptor.
        let space = unsafe { libc::CMSG_SPACE(size_of::<libc::c_int>() as _) as usize };
        let mut control = vec![0usize; space.div_ceil(size_of::<usize>())];
        let mut iovec = libc::iovec { iov_base: byte.as_mut_ptr().cast(), iov_len: 1 };
        // SAFETY: zero initializes unused pointers/counts in the native header.
        let mut message: libc::msghdr = unsafe { std::mem::zeroed() };
        message.msg_iov = &mut iovec;
        message.msg_iovlen = 1;
        message.msg_control = control.as_mut_ptr().cast();
        message.msg_controllen = space as _;
        // SAFETY: aligned buffer has native CMSG_SPACE room for this one right.
        unsafe {
            let header = libc::CMSG_FIRSTHDR(&message);
            (*header).cmsg_level = libc::SOL_SOCKET;
            (*header).cmsg_type = libc::SCM_RIGHTS;
            (*header).cmsg_len = libc::CMSG_LEN(size_of::<libc::c_int>() as _) as _;
            libc::CMSG_DATA(header).cast::<libc::c_int>().write_unaligned(fd.as_raw_fd());
        }
        loop {
            if Instant::now() >= deadline {
                return Err(io::ErrorKind::TimedOut.into());
            }
            // SAFETY: all native message storage and the held pipe/socket live.
            let count = unsafe {
                libc::sendmsg(
                    self.stream.as_raw_fd(),
                    &message,
                    libc::MSG_DONTWAIT | libc::MSG_NOSIGNAL,
                )
            };
            if count == 1 {
                self.poisoned = false;
                return Ok(());
            }
            if count >= 0 {
                return Err(crate::wire::invalid());
            }
            match io::Error::last_os_error().kind() {
                io::ErrorKind::Interrupted => {}
                io::ErrorKind::WouldBlock => self.ready(true, deadline)?,
                _ => return Err(io::Error::last_os_error()),
            }
        }
    }
    /// Receive and own every delivered right before validating exact count,
    /// tag and native read-only pipe type. Rejected rights are always closed.
    pub fn receive_read_lifeline(&mut self, deadline: Instant) -> io::Result<OwnedFd> {
        self.begin()?;
        let mut byte = [0u8];
        let mut control = [0usize; 32];
        let mut iovec = libc::iovec { iov_base: byte.as_mut_ptr().cast(), iov_len: 1 };
        loop {
            if Instant::now() >= deadline {
                return Err(io::ErrorKind::TimedOut.into());
            }
            // SAFETY: zero initializes unused native header members.
            let mut message: libc::msghdr = unsafe { std::mem::zeroed() };
            message.msg_iov = &mut iovec;
            message.msg_iovlen = 1;
            message.msg_control = control.as_mut_ptr().cast();
            message.msg_controllen = size_of_val(&control) as _;
            #[cfg(target_os = "linux")]
            let flags = libc::MSG_DONTWAIT | libc::MSG_CMSG_CLOEXEC;
            #[cfg(target_os = "macos")]
            let flags = libc::MSG_DONTWAIT;
            // SAFETY: initialized live native message/buffer storage.
            let count = unsafe { libc::recvmsg(self.stream.as_raw_fd(), &mut message, flags) };
            if count < 0 {
                match io::Error::last_os_error().kind() {
                    io::ErrorKind::Interrupted => continue,
                    io::ErrorKind::WouldBlock => {
                        self.ready(false, deadline)?;
                        continue;
                    }
                    _ => return Err(io::Error::last_os_error()),
                }
            }
            let mut rights = Vec::new();
            let mut unexpected = false;
            // SAFETY: kernel-produced ancillary headers lie in the initialized
            // control buffer; adopt all SCM_RIGHTS entries before any refusal.
            unsafe {
                let mut header = libc::CMSG_FIRSTHDR(&message);
                while !header.is_null() {
                    let base = libc::CMSG_LEN(0) as usize;
                    let length = (*header).cmsg_len as usize;
                    if length < base {
                        unexpected = true;
                        break;
                    }
                    if (*header).cmsg_level == libc::SOL_SOCKET
                        && (*header).cmsg_type == libc::SCM_RIGHTS
                    {
                        let bytes = length - base;
                        unexpected |= !bytes.is_multiple_of(size_of::<libc::c_int>());
                        for index in 0..bytes / size_of::<libc::c_int>() {
                            let raw = libc::CMSG_DATA(header)
                                .cast::<libc::c_int>()
                                .add(index)
                                .read_unaligned();
                            rights.push(OwnedFd::from_raw_fd(raw));
                        }
                    } else {
                        unexpected = true;
                    }
                    header = libc::CMSG_NXTHDR(&message, header);
                }
            }
            if count != 1
                || byte != *b"R"
                || message.msg_flags & (libc::MSG_TRUNC | libc::MSG_CTRUNC) != 0
                || unexpected
                || rights.len() != 1
            {
                return Err(crate::wire::invalid());
            }
            let fd = rights.pop().ok_or_else(crate::wire::invalid)?;
            // SAFETY: newly owned received descriptor; preserve all FD flags.
            let fd_flags = unsafe { libc::fcntl(fd.as_raw_fd(), libc::F_GETFD) };
            // SAFETY: set CLOEXEC on this receiver's newly owned descriptor only.
            if fd_flags < 0
                || unsafe {
                    libc::fcntl(fd.as_raw_fd(), libc::F_SETFD, fd_flags | libc::FD_CLOEXEC)
                } < 0
            {
                return Err(io::Error::last_os_error());
            }
            check_read_pipe(fd.as_fd())?;
            self.poisoned = false;
            return Ok(fd);
        }
    }
}

#[cfg(test)]
mod tests {
    use std::time::Duration;

    use super::*;
    #[test]
    fn lifeline_transfers_only_read_end_preserves_flags_and_reports_writer_death() {
        let (reader, writer) = std::io::pipe().unwrap();
        let (a, b) = UnixStream::pair().unwrap();
        let mut sender = Channel::new(a).unwrap();
        let mut receiver = Channel::new(b).unwrap();
        let deadline = Instant::now() + Duration::from_secs(60);
        assert!(sender.send_read_lifeline(writer.as_fd(), deadline).is_err());
        assert!(!sender.poisoned());
        // SAFETY: flag observation on the held source pipe reader only.
        let before = unsafe { libc::fcntl(reader.as_raw_fd(), libc::F_GETFL) };
        sender.send_read_lifeline(reader.as_fd(), deadline).unwrap();
        let actual = receiver.receive_read_lifeline(deadline).unwrap();
        // SAFETY: flags of the held original/received descriptions only.
        unsafe {
            assert_eq!(
                crate::tests::caller_status_flags(libc::fcntl(reader.as_raw_fd(), libc::F_GETFL)),
                crate::tests::caller_status_flags(before)
            );
            assert_ne!(libc::fcntl(actual.as_raw_fd(), libc::F_GETFD) & libc::FD_CLOEXEC, 0);
        }
        let mut event = libc::pollfd { fd: actual.as_raw_fd(), events: libc::POLLIN, revents: 0 };
        // SAFETY: zero-timeout poll observes this held actual read end only.
        assert_eq!(unsafe { libc::poll(&mut event, 1, 0) }, 0);
        drop(writer);
        // A concurrent test's fork may briefly retain the writer before exec
        // closes it. Wait for actual EOF, with a hang detector, not a latency bound.
        loop {
            let remaining =
                deadline.checked_duration_since(Instant::now()).expect("writer retired");
            let millis = remaining.as_millis().saturating_add(1).min(i32::MAX as u128) as i32;
            // SAFETY: one initialized pollfd for our held read end, with a bounded timeout.
            let ready = unsafe { libc::poll(&mut event, 1, millis) };
            if ready < 0 && io::Error::last_os_error().kind() == io::ErrorKind::Interrupted {
                continue;
            }
            assert_eq!(ready, 1, "the sole writer must retire");
            break;
        }
        let mut byte = 0u8;
        // SAFETY: one initialized byte and the held ready pipe reader.
        assert_eq!(unsafe { libc::read(actual.as_raw_fd(), (&mut byte as *mut u8).cast(), 1) }, 0);
    }
}
