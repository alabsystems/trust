//! Bounded B1 byte transport on a caller-owned Unix stream.
//!
//! The caller establishes peer identity, exclusive protocol use and descriptor
//! custody, including no alias that changes the established O_NONBLOCK flag.
//! This is for parent/trusted-fixture use, not B2's protected worker descriptor.
//! DONTWAIT alone did not prevent a Darwin blocked send in the adversarial test;
//! O_NONBLOCK is required. NOSIGNAL avoids relying on a global SIGPIPE handler.
//! A would-block operation waits in poll(2) for the socket, in slices bounded
//! by the original deadline, so a call and its reply cost a wake-up each rather
//! than a timer tick each. Kernel I/O/scheduling remain opaque; no containment
//! claim is made.

use std::io;
use std::net::Shutdown;
use std::os::unix::net::UnixStream;
use std::time::{Duration, Instant};

use trust_process_isolation::{Budget, Charge, Error, frame_payload_length};

use crate::Transport;

#[allow(unsafe_code)]
mod sys {
    use std::io;
    use std::os::fd::AsRawFd;
    use std::os::unix::net::UnixStream;

    pub(super) fn nonblocking(stream: &UnixStream) -> io::Result<bool> {
        // SAFETY: the descriptor is borrowed from the live owned socket;
        // F_GETFL takes no variadic argument and returns only status flags.
        let flags = unsafe { libc::fcntl(stream.as_raw_fd(), libc::F_GETFL) };
        if flags < 0 { Err(io::Error::last_os_error()) } else { Ok(flags & libc::O_NONBLOCK != 0) }
    }

    pub(super) fn read(stream: &UnixStream, bytes: &mut [u8]) -> io::Result<usize> {
        // SAFETY: the borrowed live socket remains owned for the call; the
        // initialized writable slice is valid for exactly bytes.len() bytes.
        let n = unsafe {
            libc::recv(
                stream.as_raw_fd(),
                bytes.as_mut_ptr().cast(),
                bytes.len(),
                libc::MSG_DONTWAIT,
            )
        };
        if n < 0 { Err(io::Error::last_os_error()) } else { Ok(n as usize) }
    }
    pub(super) fn write(stream: &UnixStream, bytes: &[u8]) -> io::Result<usize> {
        // SAFETY: the borrowed live socket and initialized read-only slice
        // outlive the call. The owned endpoint retains O_NONBLOCK; DONTWAIT
        // additionally requests nonblocking behavior. NOSIGNAL suppresses
        // SIGPIPE, including for unnamed socket pairs.
        let n = unsafe {
            libc::send(
                stream.as_raw_fd(),
                bytes.as_ptr().cast(),
                bytes.len(),
                libc::MSG_DONTWAIT | libc::MSG_NOSIGNAL,
            )
        };
        if n < 0 { Err(io::Error::last_os_error()) } else { Ok(n as usize) }
    }
    /// Wait until the socket is readable (or writable), an error or hangup is
    /// pending, or `timeout_ms` passes. The result is a hint only: the caller
    /// retries its nonblocking operation and rechecks its deadline either way.
    pub(super) fn wait(stream: &UnixStream, writable: bool, timeout_ms: libc::c_int) {
        let mut descriptor = libc::pollfd {
            fd: stream.as_raw_fd(),
            events: if writable { libc::POLLOUT } else { libc::POLLIN },
            revents: 0,
        };
        // SAFETY: one initialized pollfd for the borrowed live socket, valid for
        // the call; poll neither retains it nor transfers descriptor ownership.
        let _ = unsafe { libc::poll(&mut descriptor, 1, timeout_ms) };
    }
}

pub struct UnixTransport {
    stream: Option<UnixStream>,
    budget: Budget,
}

impl UnixTransport {
    pub fn new(stream: UnixStream, budget: Budget) -> Result<Self, Error> {
        budget.check()?;
        stream
            .set_nonblocking(true)
            .map_err(|_| budget.refuse(Error::InvalidWire("worker socket nonblocking")))?;
        budget.check()?;
        // Validate the supplied descriptor is still a connected socket. Its
        // peer address is not an authentication or provenance check.
        stream.peer_addr().map_err(|_| budget.refuse(Error::InvalidWire("worker socket")))?;
        budget.check()?;
        let nonblocking = sys::nonblocking(&stream);
        budget.check()?;
        if !nonblocking.map_err(|_| budget.refuse(Error::InvalidWire("worker socket flags")))? {
            return Err(budget.refuse(Error::InvalidWire("worker socket is blocking")));
        }
        Ok(Self { stream: Some(stream), budget })
    }
    fn check(&self, budget: &Budget) -> Result<(), Error> {
        self.budget.check()?;
        if !self.budget.shares_owner(budget) {
            return Err(Error::Identity);
        }
        let stream = self.stream.as_ref().ok_or(Error::Phase)?;
        self.budget.charge(Charge { work: 1, ..Charge::default() })?;
        let nonblocking = sys::nonblocking(stream);
        self.budget.check()?;
        if !nonblocking.map_err(|_| Error::InvalidWire("worker socket flags"))? {
            return Err(Error::InvalidWire("worker socket is blocking"));
        }
        Ok(())
    }
    fn refuse(&mut self, error: Error) -> Error {
        let error = self.budget.refuse(error);
        self.close();
        error
    }
    /// The longest one wait lasts before the deadline and any cancellation are
    /// rechecked. A wake-up ends the wait early; this only bounds a silent peer.
    const WAIT_SLICE: Duration = Duration::from_millis(50);

    fn pause(&self, writable: bool) -> Result<(), Error> {
        self.budget.check()?;
        let left = self.budget.deadline().saturating_duration_since(Instant::now());
        let slice = left.min(Self::WAIT_SLICE).as_millis().max(1) as libc::c_int;
        let stream = self.stream.as_ref().ok_or(Error::Phase)?;
        sys::wait(stream, writable, slice);
        self.budget.check()
    }
    /// Give the socket back without shutting the connection down, for an owner
    /// that runs another invocation on it under a new budget. `None` after a
    /// refusal or a close: that connection is finished.
    pub fn into_stream(mut self) -> Option<UnixStream> {
        self.stream.take()
    }
    fn read_exact(&mut self, bytes: &mut [u8], allow_eof: bool) -> Result<bool, Error> {
        let mut read = 0;
        while read < bytes.len() {
            self.budget.check()?;
            let count = (bytes.len() - read).min(4096);
            self.budget.charge(Charge { work: count as u64, ..Charge::default() })?;
            let stream = self.stream.as_ref().ok_or(Error::Phase)?;
            let result = sys::read(stream, &mut bytes[read..read + count]);
            self.budget.check()?;
            match result {
                Ok(0) if read == 0 && allow_eof => return Ok(false),
                Ok(0) => return Err(Error::InvalidWire("truncated worker socket frame")),
                Ok(n) if n <= count => read += n,
                Ok(_) => return Err(Error::InvalidWire("worker socket read count")),
                Err(e) if e.kind() == io::ErrorKind::WouldBlock => self.pause(false)?,
                Err(e) if e.kind() == io::ErrorKind::Interrupted => continue,
                Err(_) => return Err(Error::InvalidWire("worker socket read")),
            }
        }
        self.budget.check()?;
        Ok(true)
    }
    fn send_inner(&mut self, frame: &[u8], budget: &Budget) -> Result<(), Error> {
        self.check(budget)?;
        let prefix: [u8; 4] = frame
            .get(..4)
            .ok_or(Error::InvalidWire("short worker frame"))?
            .try_into()
            .map_err(|_| Error::InvalidWire("worker prefix"))?;
        let n = frame_payload_length(prefix, &self.budget)?;
        if n.checked_add(4).ok_or(Error::Overflow)? != frame.len() {
            return Err(Error::InvalidWire("worker frame length"));
        }
        let mut sent = 0;
        while sent < frame.len() {
            self.budget.check()?;
            let count = (frame.len() - sent).min(4096);
            self.budget.charge(Charge { work: count as u64, ..Charge::default() })?;
            let stream = self.stream.as_ref().ok_or(Error::Phase)?;
            let result = sys::write(stream, &frame[sent..sent + count]);
            self.budget.check()?;
            match result {
                Ok(0) => return Err(Error::InvalidWire("worker socket write zero")),
                Ok(n) if n <= count => sent += n,
                Ok(_) => return Err(Error::InvalidWire("worker socket write count")),
                Err(e) if e.kind() == io::ErrorKind::WouldBlock => self.pause(true)?,
                Err(e) if e.kind() == io::ErrorKind::Interrupted => continue,
                Err(_) => return Err(Error::InvalidWire("worker socket write")),
            }
        }
        self.budget.check()
    }
    fn receive_inner(&mut self, budget: &Budget) -> Result<Option<Vec<u8>>, Error> {
        self.check(budget)?;
        let mut prefix = [0; 4];
        if !self.read_exact(&mut prefix, true)? {
            self.close();
            return Ok(None);
        }
        let n =
            frame_payload_length(prefix, &self.budget)?.checked_add(4).ok_or(Error::Overflow)?;
        self.budget.charge(Charge {
            allocation_bytes: n as u64,
            work: n as u64,
            ..Charge::default()
        })?;
        let mut frame = Vec::new();
        frame.try_reserve_exact(n).map_err(|_| Error::Allocation)?;
        self.budget.charge(Charge {
            allocation_bytes: frame.capacity().saturating_sub(n) as u64,
            ..Charge::default()
        })?;
        self.budget.check()?;
        frame.resize(n, 0);
        frame[..4].copy_from_slice(&prefix);
        self.read_exact(&mut frame[4..], false)?;
        Ok(Some(frame))
    }
    /// Receive exactly one frame. Clean EOF before a prefix is distinct from
    /// truncation, allowing an owner to require EOF after terminal Finish.
    /// This reserves raw storage; B1 decoding charges the actual wire bytes.
    pub fn receive_frame(&mut self, budget: &Budget) -> Result<Option<Vec<u8>>, Error> {
        let result = self.receive_inner(budget);
        result.map_err(|e| self.refuse(e))
    }
}
impl Transport for UnixTransport {
    fn send(&mut self, frame: &[u8], budget: &Budget) -> Result<(), Error> {
        let result = self.send_inner(frame, budget);
        result.map_err(|e| self.refuse(e))
    }
    fn receive(&mut self, budget: &Budget) -> Result<Vec<u8>, Error> {
        match self.receive_frame(budget)? {
            Some(frame) => Ok(frame),
            None => Err(self.refuse(Error::InvalidWire("worker socket EOF before reply"))),
        }
    }
    fn close(&mut self) {
        if let Some(stream) = self.stream.take() {
            let _ = stream.shutdown(Shutdown::Both);
        }
    }
}
impl Drop for UnixTransport {
    fn drop(&mut self) {
        self.close();
    }
}
