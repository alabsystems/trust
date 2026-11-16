//! Native SCM custody on the same framed channel; no source status flag changes.
use std::mem::{size_of, size_of_val};
use std::os::fd::{FromRawFd, OwnedFd};

use super::*;
use crate::runtime_input_retention::{CHUNK_INPUTS, RIGHTS_MARKER};

impl Channel {
    pub(crate) fn send_bootstrap_configuration_description(
        &mut self,
        file: BorrowedFd<'_>,
        deadline: Instant,
    ) -> io::Result<()> {
        self.send_named_descriptions(
            &[file],
            crate::bootstrap_graph::configuration::RIGHTS_MARKER,
            1,
            deadline,
        )
    }
    pub(crate) fn receive_bootstrap_configuration_description(
        &mut self,
        deadline: Instant,
    ) -> io::Result<Vec<OwnedFd>> {
        self.receive_named_descriptions(
            1,
            crate::bootstrap_graph::configuration::RIGHTS_MARKER,
            1,
            deadline,
        )
    }
    pub(crate) fn send_bootstrap_source_descriptions(
        &mut self,
        fds: &[BorrowedFd<'_>; 4],
        deadline: Instant,
    ) -> io::Result<()> {
        self.send_named_descriptions(
            fds,
            crate::bootstrap_graph::source::RIGHTS_MARKER,
            crate::bootstrap_graph::source::DESCRIPTION_COUNT,
            deadline,
        )
    }
    pub(crate) fn receive_bootstrap_source_descriptions(
        &mut self,
        deadline: Instant,
    ) -> io::Result<Vec<OwnedFd>> {
        self.receive_named_descriptions(
            crate::bootstrap_graph::source::DESCRIPTION_COUNT,
            crate::bootstrap_graph::source::RIGHTS_MARKER,
            crate::bootstrap_graph::source::DESCRIPTION_COUNT,
            deadline,
        )
    }
    pub(crate) fn send_retained_inputs(
        &mut self,
        fds: &[BorrowedFd<'_>],
        deadline: Instant,
    ) -> io::Result<()> {
        self.send_named_descriptions(fds, RIGHTS_MARKER, CHUNK_INPUTS, deadline)
    }
    pub(crate) fn send_bootstrap_descriptions(
        &mut self,
        fds: &[BorrowedFd<'_>],
        marker: u8,
        deadline: Instant,
    ) -> io::Result<()> {
        self.send_named_descriptions(
            fds,
            marker,
            crate::bootstrap_graph::DESCRIPTION_COUNT,
            deadline,
        )
    }
    pub(crate) fn send_named_descriptions(
        &mut self,
        fds: &[BorrowedFd<'_>],
        marker: u8,
        bound: usize,
        deadline: Instant,
    ) -> io::Result<()> {
        if fds.is_empty() || fds.len() > bound {
            return Err(crate::wire::invalid());
        }
        self.begin()?;
        jobserver_utils::descriptor_transfer::send(&self.stream, fds, marker, deadline)?;
        self.poisoned = false;
        Ok(())
    }
    pub(crate) fn receive_retained_inputs(
        &mut self,
        count: usize,
        deadline: Instant,
    ) -> io::Result<Vec<OwnedFd>> {
        self.receive_named_descriptions(count, RIGHTS_MARKER, CHUNK_INPUTS, deadline)
    }
    pub(crate) fn receive_bootstrap_descriptions(
        &mut self,
        marker: u8,
        deadline: Instant,
    ) -> io::Result<Vec<OwnedFd>> {
        self.receive_named_descriptions(
            crate::bootstrap_graph::DESCRIPTION_COUNT,
            marker,
            crate::bootstrap_graph::DESCRIPTION_COUNT,
            deadline,
        )
    }
    pub(crate) fn receive_named_descriptions(
        &mut self,
        count: usize,
        marker: u8,
        bound: usize,
        deadline: Instant,
    ) -> io::Result<Vec<OwnedFd>> {
        self.begin()?;
        let (byte, read, valid, rights) = self.retained_message(deadline)?;
        if count == 0
            || count > bound
            || read != 1
            || byte != marker
            || !valid
            || rights.len() != count
        {
            return Err(crate::wire::invalid());
        }
        self.poisoned = false;
        Ok(rights)
    }
    pub(crate) fn end_retained_send(&mut self) -> io::Result<()> {
        self.begin()?;
        self.stream.shutdown(std::net::Shutdown::Write)?;
        self.poisoned = false;
        Ok(())
    }
    pub(crate) fn require_retained_eof(&mut self, deadline: Instant) -> io::Result<()> {
        self.begin()?;
        let (_, read, valid, rights) = self.retained_message(deadline)?;
        if read != 0 || !valid || !rights.is_empty() {
            return Err(crate::wire::invalid());
        }
        self.poisoned = false;
        Ok(())
    }
    fn retained_message(&self, deadline: Instant) -> io::Result<(u8, isize, bool, Vec<OwnedFd>)> {
        let (byte, read, valid, rights, error) = self.retained_message_custodied(deadline)?;
        if let Some(error) = error {
            return Err(error);
        }
        Ok((byte, read, valid, rights))
    }

    /// The distinct preparation receiver transfers ALL actual delivered
    /// descriptions to its native State even when marker/count/CLOEXEC fails.
    /// This is no validated output, lock owner or configured completion.
    pub(crate) fn receive_preparation_output_delivery(
        &mut self,
        deadline: Instant,
    ) -> io::Result<crate::bootstrap_graph::transport::PreparationOutputDelivery> {
        self.begin()?;
        let (byte, read, valid, rights, error) = self.retained_message_custodied(deadline)?;
        let valid = read == 1
            && valid
            && error.is_none()
            && rights.len() == 2
            && byte
                == crate::bootstrap_graph::offline_preparation::PREPARATION_OUTPUT_RIGHTS_MARKER;
        // A malformed carrier remains poisoned; its actual FD population must
        // nevertheless reach the real native quarantine before error reporting.
        self.poisoned = !valid;
        Ok(crate::bootstrap_graph::transport::PreparationOutputDelivery::received(rights, valid))
    }

    pub(crate) fn receive_preparation_cache_directory(
        &mut self,
        deadline: Instant,
    ) -> io::Result<crate::bootstrap_graph::transport::PreparationCacheDirectoryDelivery> {
        self.begin()?;
        let (byte, read, valid, rights, error) = self.retained_message_custodied(deadline)?;
        let valid = read == 1
            && valid
            && error.is_none()
            && rights.len() == 1
            && byte == crate::bootstrap_graph::transport::PREPARATION_CACHE_DIRECTORY_RIGHTS_MARKER;
        self.poisoned = !valid;
        Ok(
            crate::bootstrap_graph::transport::PreparationCacheDirectoryDelivery::received(
                rights, valid,
            ),
        )
    }

    fn retained_message_custodied(
        &self,
        deadline: Instant,
    ) -> io::Result<(u8, isize, bool, Vec<OwnedFd>, Option<io::Error>)> {
        let mut byte = [0u8];
        // Adopt every kernel-permitted rights population, even on malformed tails.
        let mut control = [0usize; 4096 / size_of::<usize>()];
        loop {
            if Instant::now() >= deadline {
                return Err(io::ErrorKind::TimedOut.into());
            }
            let mut iov = libc::iovec { iov_base: byte.as_mut_ptr().cast(), iov_len: 1 };
            // SAFETY: initialized optional fields, live bounded buffers/socket.
            let mut message: libc::msghdr = unsafe { std::mem::zeroed() };
            message.msg_iov = &mut iov;
            message.msg_iovlen = 1;
            message.msg_control = control.as_mut_ptr().cast();
            message.msg_controllen = size_of_val(&control) as _;
            #[cfg(target_os = "linux")]
            let flags = libc::MSG_DONTWAIT | libc::MSG_CMSG_CLOEXEC;
            #[cfg(target_os = "macos")]
            let flags = libc::MSG_DONTWAIT;
            // SAFETY: kernel fills the held initialized native message storage.
            let read = unsafe { libc::recvmsg(self.stream.as_raw_fd(), &mut message, flags) };
            if read < 0 {
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
            let mut valid = message.msg_flags & (libc::MSG_TRUNC | libc::MSG_CTRUNC) == 0;
            if message.msg_controllen as usize > size_of_val(&control) {
                valid = false;
                message.msg_controllen = size_of_val(&control) as _;
            }
            // SAFETY: walk only complete bounded kernel-produced headers. Own
            // ALL delivered rights before checking count/tag/semantic metadata.
            unsafe {
                let mut h = libc::CMSG_FIRSTHDR(&message);
                while !h.is_null() {
                    let base = libc::CMSG_LEN(0) as usize;
                    let remaining = message.msg_controllen as usize
                        - (h as usize - message.msg_control as usize);
                    if remaining < base || ((*h).cmsg_len as usize) < base {
                        valid = false;
                        break;
                    }
                    let length = (*h).cmsg_len as usize;
                    let payload = length.min(remaining) - base;
                    if (*h).cmsg_level == libc::SOL_SOCKET && (*h).cmsg_type == libc::SCM_RIGHTS {
                        valid &= payload.is_multiple_of(size_of::<libc::c_int>());
                        let data = libc::CMSG_DATA(h).cast::<libc::c_int>();
                        for index in 0..payload / size_of::<libc::c_int>() {
                            rights.push(OwnedFd::from_raw_fd(data.add(index).read_unaligned()));
                        }
                    } else {
                        valid = false;
                    }
                    if length > remaining {
                        valid = false;
                        break;
                    }
                    h = libc::CMSG_NXTHDR(&message, h);
                }
            }
            let mut error = None;
            for fd in &rights {
                // CLOEXEC changes only fresh receiver descriptor flags, never
                // the shared OFD's status flags or caller inheritance flags.
                let old = unsafe { libc::fcntl(fd.as_raw_fd(), libc::F_GETFD) };
                if old < 0
                    || unsafe { libc::fcntl(fd.as_raw_fd(), libc::F_SETFD, old | libc::FD_CLOEXEC) }
                        < 0
                {
                    if error.is_none() {
                        error = Some(io::Error::last_os_error());
                    }
                }
            }
            return Ok((byte[0], read, valid, rights, error));
        }
    }
}
