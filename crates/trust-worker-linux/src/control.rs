//! Post-entry B1 transport for the authenticated, protected worker FD3.
//!
//! Only successful trusted entry can lend this capability. FD3 is never owned
//! by a Rust destructor, shut down, duplicated or closed here. Closing is a
//! permanent logical latch; the caller must terminate the disposable worker
//! after completion/refusal. The outside owner still requires Finish, EOF and
//! successful reaped exit, and kills/reaps on every missing/abnormal outcome.
//!
//! Plain write with unblocked default SIGPIPE is a terminal abnormal exit;
//! ignored, handled or blocked SIGPIPE instead yields sticky I/O refusal.
//! No success may be credited from either outcome. This code does not
//! install a handler or rely on send/MSG_NOSIGNAL being admitted by the filter.

use std::io;
use std::time::{Duration, Instant};

use trust_process_isolation::{Budget, Charge, Error, Transport, frame_payload_length};

pub struct RetainedControl<'a> {
    budget: &'a Budget,
    closed: &'a mut bool,
}

impl<'a> RetainedControl<'a> {
    pub(crate) fn new(budget: &'a Budget, closed: &'a mut bool) -> Result<Self, Error> {
        let mut result = Self { budget, closed };
        let checked = result.check(budget);
        checked.map_err(|e| result.refuse(e))?;
        Ok(result)
    }
    fn check(&self, budget: &Budget) -> Result<(), Error> {
        self.budget.check()?;
        if !self.budget.shares_owner(budget) {
            return Err(Error::Identity);
        }
        if *self.closed {
            return Err(Error::Phase);
        }
        self.budget.charge(Charge { work: 1, ..Charge::default() })?;
        // SAFETY: successful entry authenticated FD3 and installed a filter
        // which denies its close/dup/F_SETFL. F_GETFL alone is admitted. Trusted
        // pre-entry setup excludes concurrent flag/FD mutators and constructors.
        let flags = unsafe { libc::fcntl(3, libc::F_GETFL) };
        self.budget.check()?;
        if flags < 0 || flags & libc::O_NONBLOCK == 0 {
            return Err(Error::InvalidWire("protected control is blocking"));
        }
        Ok(())
    }
    fn refuse(&mut self, error: Error) -> Error {
        *self.closed = true;
        self.budget.refuse(error)
    }
    fn wait(&self, event: i16) -> Result<(), Error> {
        self.budget.check()?;
        self.budget.charge(Charge { work: 1, ..Charge::default() })?;
        // A finite slice also observes shared in-process cancellation, without
        // renewing the original deadline. Kernel scheduling remains opaque;
        // the independent parent watchdog remains mandatory.
        let left = self.budget.deadline().saturating_duration_since(Instant::now());
        let left = left.min(Duration::from_millis(10));
        let timeout = libc::timespec {
            tv_sec: 0, // the bounded slice is always less than one second
            tv_nsec: left.subsec_nanos() as libc::c_long,
        };
        let mut poll = libc::pollfd { fd: 3, events: event, revents: 0 };
        // SAFETY: one initialized writable poll record and finite initialized
        // timeout, no signal-mask replacement or pointers retained by ppoll.
        let n = unsafe { libc::ppoll(&mut poll, 1, &timeout, std::ptr::null()) };
        let error = if n < 0 { Some(io::Error::last_os_error()) } else { None };
        self.budget.check()?;
        if let Some(error) = error {
            if error.kind() != io::ErrorKind::Interrupted {
                return Err(Error::InvalidWire("protected control poll"));
            }
        } else if n > 1 || poll.revents & libc::POLLNVAL != 0 {
            return Err(Error::InvalidWire("protected control poll descriptor"));
        }
        // HUP/ERR are observed by the next read/write, preserving EOF/EPIPE.
        Ok(())
    }
    fn read_exact(&self, bytes: &mut [u8]) -> Result<(), Error> {
        let mut done = 0;
        while done < bytes.len() {
            self.budget.check()?;
            let count = (bytes.len() - done).min(4096);
            self.budget.charge(Charge { work: count as u64, ..Charge::default() })?;
            // SAFETY: the retained FD3 and exact initialized destination slice
            // remain live throughout the syscall; its O_NONBLOCK is immutable.
            let n = unsafe { libc::read(3, bytes[done..done + count].as_mut_ptr().cast(), count) };
            let error = if n < 0 { Some(io::Error::last_os_error()) } else { None };
            self.budget.check()?;
            match (n, error) {
                (0, _) => return Err(Error::InvalidWire("protected control EOF/truncation")),
                (n, None) if n > 0 && n as usize <= count => done += n as usize,
                (_, Some(e)) if e.kind() == io::ErrorKind::Interrupted => continue,
                (_, Some(e)) if e.kind() == io::ErrorKind::WouldBlock => self.wait(libc::POLLIN)?,
                _ => return Err(Error::InvalidWire("protected control read")),
            }
        }
        self.budget.check()
    }
    fn send_inner(&self, frame: &[u8], budget: &Budget) -> Result<(), Error> {
        self.check(budget)?;
        let prefix = frame.get(..4).ok_or(Error::InvalidWire("short protected frame"))?;
        let length =
            frame_payload_length(prefix.try_into().map_err(|_| Error::Schema)?, self.budget)?;
        if length.checked_add(4).ok_or(Error::Overflow)? != frame.len() {
            return Err(Error::InvalidWire("protected control frame length"));
        }
        let mut done = 0;
        while done < frame.len() {
            self.budget.check()?;
            let count = (frame.len() - done).min(4096);
            self.budget.charge(Charge { work: count as u64, ..Charge::default() })?;
            // SAFETY: only initialized bytes from the live bounded frame are
            // read. FD3 is retained/nonblocking; SIGPIPE is terminal as above.
            let n = unsafe { libc::write(3, frame[done..done + count].as_ptr().cast(), count) };
            let error = if n < 0 { Some(io::Error::last_os_error()) } else { None };
            self.budget.check()?;
            match (n, error) {
                (n, None) if n > 0 && n as usize <= count => done += n as usize,
                (_, Some(e)) if e.kind() == io::ErrorKind::Interrupted => continue,
                (_, Some(e)) if e.kind() == io::ErrorKind::WouldBlock => {
                    self.wait(libc::POLLOUT)?
                }
                _ => return Err(Error::InvalidWire("protected control write")),
            }
        }
        self.budget.check()
    }
    fn receive_inner(&self, budget: &Budget) -> Result<Vec<u8>, Error> {
        self.check(budget)?;
        let mut prefix = [0; 4];
        self.read_exact(&mut prefix)?;
        let length =
            frame_payload_length(prefix, self.budget)?.checked_add(4).ok_or(Error::Overflow)?;
        self.budget.charge(Charge {
            allocation_bytes: length as u64,
            work: length as u64,
            ..Charge::default()
        })?;
        let mut bytes = Vec::new();
        bytes.try_reserve_exact(length).map_err(|_| Error::Allocation)?;
        self.budget.charge(Charge {
            allocation_bytes: bytes.capacity().saturating_sub(length) as u64,
            ..Charge::default()
        })?;
        self.budget.check()?;
        bytes.resize(length, 0);
        bytes[..4].copy_from_slice(&prefix);
        self.read_exact(&mut bytes[4..])?;
        // B1 decode, not raw I/O, charges wire bytes exactly once.
        Ok(bytes)
    }
}
impl Transport for RetainedControl<'_> {
    fn send(&mut self, frame: &[u8], budget: &Budget) -> Result<(), Error> {
        let result = self.send_inner(frame, budget);
        result.map_err(|e| self.refuse(e))
    }
    fn receive(&mut self, budget: &Budget) -> Result<Vec<u8>, Error> {
        let result = self.receive_inner(budget);
        result.map_err(|e| self.refuse(e))
    }
    fn close(&mut self) {
        *self.closed = true;
    }
}
impl Drop for RetainedControl<'_> {
    fn drop(&mut self) {
        self.close();
    }
}
