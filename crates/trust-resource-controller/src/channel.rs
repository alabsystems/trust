// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

use std::io;
use std::os::fd::{AsFd, AsRawFd, BorrowedFd};
use std::os::unix::net::UnixStream;
use std::time::Instant;

use crate::MAX_PAYLOAD;

/// One private framed stream. Any failed exchange poisons it: partial delivery
/// may already have happened and must never trigger replay on a new channel.
pub struct Channel {
    stream: UnixStream,
    poisoned: bool,
}
impl Channel {
    pub fn new(stream: UnixStream) -> io::Result<Self> {
        Ok(Self { stream, poisoned: false })
    }
    /// Access for native peer checks, never as a substitute for those checks.
    pub fn as_fd(&self) -> BorrowedFd<'_> {
        self.stream.as_fd()
    }
    pub fn poisoned(&self) -> bool {
        self.poisoned
    }
    /// Observe clean stream EOF between frames without consuming bytes. A
    /// partial/trailing frame remains readable and must pass receive instead.
    pub fn at_eof(&self) -> io::Result<bool> {
        if self.poisoned {
            return Err(io::ErrorKind::BrokenPipe.into());
        }
        let mut byte = 0u8;
        // SAFETY: held live socket and one initialized writable byte. Per-call
        // flags neither consume data nor change the underlying description.
        let result = unsafe {
            libc::recv(
                self.stream.as_raw_fd(),
                (&mut byte as *mut u8).cast(),
                1,
                libc::MSG_PEEK | libc::MSG_DONTWAIT,
            )
        };
        if result >= 0 {
            return Ok(result == 0);
        }
        let error = io::Error::last_os_error();
        match error.kind() {
            io::ErrorKind::WouldBlock | io::ErrorKind::Interrupted => Ok(false),
            _ => Err(error),
        }
    }
    /// Nonblocking readiness hint for an owner multiplexing target events and
    /// cancellation. HUP/error also count as ready so receive observes closure.
    /// No bytes are consumed and an idle channel is not poisoned.
    pub fn ready_to_receive(&self) -> io::Result<bool> {
        if self.poisoned {
            return Err(io::ErrorKind::BrokenPipe.into());
        }
        let mut poll =
            libc::pollfd { fd: self.stream.as_raw_fd(), events: libc::POLLIN, revents: 0 };
        // SAFETY: one initialized pollfd referencing the held live socket;
        // timeout zero never parks an event-loop owner.
        let result = unsafe { libc::poll(&mut poll, 1, 0) };
        if result < 0 {
            let error = io::Error::last_os_error();
            if error.kind() == io::ErrorKind::Interrupted {
                return Ok(false);
            }
            return Err(error);
        }
        Ok(result > 0)
    }
    pub(crate) fn send_fixed<const N: usize>(
        &mut self,
        mut bytes: [u8; N],
        deadline: Instant,
    ) -> io::Result<()> {
        self.begin()?;
        self.transfer(&mut bytes, true, deadline)?;
        self.poisoned = false;
        Ok(())
    }
    pub(crate) fn receive_fixed<const N: usize>(&mut self, deadline: Instant) -> io::Result<[u8; N]> {
        self.begin()?;
        let mut bytes = [0; N];
        self.transfer(&mut bytes, false, deadline)?;
        self.poisoned = false;
        Ok(bytes)
    }
    #[cfg(feature = "bootstrap-receiver")]
    pub(crate) fn native_peer(&self) -> io::Result<trust_resource_provenance::process::Identity> {
        trust_resource_provenance::process::connected_identity(&self.stream)
    }
    /// Send one bounded frame without SIGPIPE. A failure means unknown delivery.
    pub fn send(&mut self, payload: &[u8], deadline: Instant) -> io::Result<()> {
        self.begin()?;
        if payload.is_empty() || payload.len() > MAX_PAYLOAD {
            return Err(crate::wire::invalid());
        }
        let mut length = (payload.len() as u32).to_be_bytes();
        self.transfer(&mut length, true, deadline)?;
        // send() does not mutate the buffer; keep the caller's bytes private.
        let mut payload = payload.to_vec();
        self.transfer(&mut payload, true, deadline)?;
        self.poisoned = false;
        Ok(())
    }
    /// Receive exactly one frame; malformed/partial/late input poisons the stream.
    pub fn receive(&mut self, deadline: Instant) -> io::Result<Vec<u8>> {
        self.receive_observed(deadline, |_| {})
    }
    /// Record only bytes actually received, including a malformed/partial
    /// length frame. Observation never clears poison or grants lifecycle state.
    pub(crate) fn receive_observed(
        &mut self,
        deadline: Instant,
        mut observe: impl FnMut(&[u8]),
    ) -> io::Result<Vec<u8>> {
        self.begin()?;
        let mut length = [0; 4];
        self.transfer_observed(&mut length, false, deadline, &mut observe)?;
        let length = u32::from_be_bytes(length) as usize;
        if length == 0 || length > MAX_PAYLOAD {
            return Err(crate::wire::invalid());
        }
        let mut payload = vec![0; length];
        self.transfer_observed(&mut payload, false, deadline, &mut observe)?;
        self.poisoned = false;
        Ok(payload)
    }
    fn begin(&mut self) -> io::Result<()> {
        if self.poisoned {
            return Err(io::Error::new(
                io::ErrorKind::BrokenPipe,
                "private controller channel is unusable",
            ));
        }
        self.poisoned = true;
        Ok(())
    }
    fn transfer(&self, bytes: &mut [u8], sending: bool, deadline: Instant) -> io::Result<()> {
        self.transfer_observed(bytes, sending, deadline, &mut |_| {})
    }
    fn transfer_observed(
        &self,
        bytes: &mut [u8],
        sending: bool,
        deadline: Instant,
        observe: &mut impl FnMut(&[u8]),
    ) -> io::Result<()> {
        let mut offset = 0;
        while offset < bytes.len() {
            if Instant::now() >= deadline {
                return Err(io::ErrorKind::TimedOut.into());
            }
            let flags = libc::MSG_DONTWAIT;
            let send_flags = flags | libc::MSG_NOSIGNAL;
            // SAFETY: live socket and in-bounds buffer; per-call nonblocking I/O
            // does not change flags shared with another open description user.
            let count = unsafe {
                if sending {
                    libc::send(
                        self.stream.as_raw_fd(),
                        bytes[offset..].as_ptr().cast(),
                        bytes.len() - offset,
                        send_flags,
                    )
                } else {
                    libc::recv(
                        self.stream.as_raw_fd(),
                        bytes[offset..].as_mut_ptr().cast(),
                        bytes.len() - offset,
                        flags,
                    )
                }
            };
            if count > 0 {
                if !sending {
                    observe(&bytes[offset..offset + count as usize]);
                }
                offset += count as usize;
                continue;
            }
            if count == 0 {
                return Err(io::ErrorKind::UnexpectedEof.into());
            }
            let error = io::Error::last_os_error();
            if error.kind() == io::ErrorKind::Interrupted {
                continue;
            }
            if error.kind() != io::ErrorKind::WouldBlock {
                return Err(error);
            }
            self.ready(sending, deadline)?;
        }
        Ok(())
    }
    fn ready(&self, sending: bool, deadline: Instant) -> io::Result<()> {
        loop {
            let remaining =
                deadline.checked_duration_since(Instant::now()).ok_or(io::ErrorKind::TimedOut)?;
            let millis = remaining.as_millis().saturating_add(1).min(i32::MAX as u128) as i32;
            let mut poll = libc::pollfd {
                fd: self.stream.as_raw_fd(),
                events: if sending { libc::POLLOUT } else { libc::POLLIN },
                revents: 0,
            };
            // SAFETY: one live initialized pollfd, bounded timeout.
            let result = unsafe { libc::poll(&mut poll, 1, millis) };
            if result > 0 {
                return Ok(());
            }
            if result == 0 {
                return Err(io::ErrorKind::TimedOut.into());
            }
            let error = io::Error::last_os_error();
            if error.kind() != io::ErrorKind::Interrupted {
                return Err(error);
            }
        }
    }
}

mod lifeline;
mod retained_inputs;

impl Channel {
    pub(crate) fn poison(&mut self) { self.poisoned = true; }
}
