// Trust: cooperative cancellation on one actual private root socket.
// SPDX-License-Identifier: MIT OR Apache-2.0
// Copyright 2026 Andrew Yates

use std::{fmt, io};

#[cfg(unix)]
use std::{
    io::{Read as _, Write as _},
    os::fd::{AsRawFd as _, FromRawFd as _},
    os::unix::net::UnixStream,
    sync::Mutex,
};

/// Original private root-control custody. Data cannot construct this endpoint,
/// and it exposes neither a descriptor nor process-control authority.
pub struct RootControl {
    #[cfg(unix)]
    state: Mutex<State>,
    #[cfg(not(unix))]
    _unavailable: (),
}

#[cfg(unix)]
struct State {
    stream: UnixStream,
    stopped: Option<&'static str>,
    requested: bool,
    acknowledged: bool,
    acknowledgement_failed: bool,
}

impl fmt::Debug for RootControl {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("RootControl").finish_non_exhaustive()
    }
}

impl RootControl {
    /// Capture the helper-supplied Unix stream at stdin before configuration can
    /// launch a child. The retained endpoint is nonblocking and close-on-exec;
    /// stdin becomes `/dev/null`, so descendants get no competing reader.
    pub fn capture_stdin() -> io::Result<Self> {
        #[cfg(unix)]
        return Self::capture_descriptor(0);
        #[cfg(not(unix))]
        Err(io::Error::new(
            io::ErrorKind::Unsupported,
            "private root control is Unix-only",
        ))
    }

    #[cfg(unix)]
    fn capture_descriptor(stdin: std::os::fd::RawFd) -> io::Result<Self> {
        // SAFETY: zero initializes the whole storage; getsockname may write
        // only its actual address prefix.
        let mut address: libc::sockaddr_storage = unsafe { std::mem::zeroed() };
        let mut length = std::mem::size_of::<libc::sockaddr_storage>() as libc::socklen_t;
        // SAFETY: stdin is this new root's supplied endpoint; storage and length
        // are writable. No ownership is assumed until duplication succeeds.
        if unsafe { libc::getsockname(stdin, (&raw mut address).cast(), &mut length) } != 0 {
            return Err(io::Error::last_os_error());
        }
        if address.ss_family as libc::c_int != libc::AF_UNIX {
            return Err(io::Error::other(
                "private root control requires a Unix socket",
            ));
        }
        let mut kind: libc::c_int = 0;
        let mut kind_length = std::mem::size_of_val(&kind) as libc::socklen_t;
        // SAFETY: kind is initialized writable storage for SO_TYPE.
        if unsafe {
            libc::getsockopt(
                stdin,
                libc::SOL_SOCKET,
                libc::SO_TYPE,
                (&raw mut kind).cast(),
                &mut kind_length,
            )
        } != 0
        {
            return Err(io::Error::last_os_error());
        }
        if kind != libc::SOCK_STREAM {
            return Err(io::Error::other(
                "private root control requires a stream socket",
            ));
        }
        // SAFETY: duplicate this actual open endpoint into a new owned,
        // close-on-exec descriptor, never an environment-selected number.
        let copy = unsafe { libc::fcntl(stdin, libc::F_DUPFD_CLOEXEC, 3) };
        if copy < 0 {
            return Err(io::Error::last_os_error());
        }
        // SAFETY: F_DUPFD_CLOEXEC returned a new descriptor owned here.
        let stream = unsafe { UnixStream::from_raw_fd(copy) };
        stream.set_nonblocking(true)?;
        let null = std::fs::File::open("/dev/null")?;
        // SAFETY: replace only this process's stdin, keeping the original
        // private endpoint in `stream`. No compiler has been launched yet.
        if unsafe { libc::dup2(null.as_raw_fd(), stdin) } != stdin {
            return Err(io::Error::last_os_error());
        }
        Ok(Self::from_stream(stream))
    }

    #[cfg(unix)]
    fn from_stream(stream: UnixStream) -> Self {
        Self {
            state: Mutex::new(State {
                stream,
                stopped: None,
                requested: false,
                acknowledged: false,
                acknowledgement_failed: false,
            }),
        }
    }

    /// Native workload service owns the other end of this actual internal
    /// cancellation socket. Framed stop/transport-loss intent is relayed as
    /// the same queue protocol; only the scheduler can acknowledge its sticky
    /// dispatch stop. This creates no process/resource/output authority.
    #[cfg(unix)]
    pub(crate) fn from_workload_stream(stream: UnixStream) -> io::Result<Self> {
        stream.set_nonblocking(true)?;
        Ok(Self::from_stream(stream))
    }

    #[cfg(all(test, unix))]
    pub(crate) fn for_test(stream: UnixStream) -> io::Result<Self> {
        stream.set_nonblocking(true)?;
        Ok(Self::from_stream(stream))
    }

    /// Polling never acknowledges: only the scheduler may acknowledge once its
    /// own sticky stop flag prevents every later unit dispatch.
    pub(super) fn poll(&self) -> bool {
        #[cfg(unix)]
        {
            let mut state = self.state.lock().unwrap_or_else(|error| error.into_inner());
            let mut bytes = [0; 2];
            match state.stream.read(&mut bytes) {
                Ok(0) => {
                    state
                        .stopped
                        .get_or_insert("private root controller closed");
                }
                Ok(1) if bytes[0] == b'C' && !state.requested => {
                    state.requested = true;
                    state
                        .stopped
                        .get_or_insert("private root cancellation requested");
                }
                Ok(_) => {
                    state.stopped = Some("invalid private root control bytes");
                    state.acknowledgement_failed = true;
                }
                Err(error)
                    if matches!(
                        error.kind(),
                        io::ErrorKind::WouldBlock | io::ErrorKind::Interrupted
                    ) => {}
                Err(_) => {
                    state
                        .stopped
                        .get_or_insert("private root control read failed");
                    state.acknowledgement_failed = true;
                }
            }
            state.stopped.is_some()
        }
        #[cfg(not(unix))]
        false
    }

    pub(super) fn acknowledge_stopped(&self) {
        #[cfg(unix)]
        {
            let mut state = self.state.lock().unwrap_or_else(|error| error.into_inner());
            if state.requested
                && state.stopped.is_some()
                && !state.acknowledged
                && !state.acknowledgement_failed
            {
                match state.stream.write(b"A") {
                    Ok(1) => state.acknowledged = true,
                    Err(error)
                        if matches!(
                            error.kind(),
                            io::ErrorKind::WouldBlock | io::ErrorKind::Interrupted
                        ) => {}
                    _ => {
                        state.stopped = Some("private root acknowledgement failed");
                        state.acknowledgement_failed = true;
                    }
                }
            }
        }
    }

    pub(super) fn reason(&self) -> &'static str {
        #[cfg(unix)]
        {
            self.state
                .lock()
                .unwrap_or_else(|error| error.into_inner())
                .stopped
                .unwrap_or("private root cancellation")
        }
        #[cfg(not(unix))]
        "private root cancellation"
    }
}

#[cfg(all(test, unix))]
mod tests {
    use super::*;

    fn pair() -> (RootControl, UnixStream) {
        let (root, helper) = UnixStream::pair().unwrap();
        root.set_nonblocking(true).unwrap();
        helper.set_nonblocking(true).unwrap();
        (RootControl::from_stream(root), helper)
    }

    #[test]
    fn capture_contains_the_original_socket_and_restores_its_stdin_slot() {
        let (stdin, mut helper) = UnixStream::pair().unwrap();
        helper
            .set_read_timeout(Some(std::time::Duration::from_secs(60)))
            .unwrap();
        let root = RootControl::capture_descriptor(stdin.as_raw_fd()).unwrap();
        let state = root.state.lock().unwrap();
        // SAFETY: both descriptors are actually owned throughout these flag reads.
        let flags = unsafe { libc::fcntl(state.stream.as_raw_fd(), libc::F_GETFL) };
        assert_ne!(flags & libc::O_NONBLOCK, 0);
        assert_ne!(
            unsafe { libc::fcntl(state.stream.as_raw_fd(), libc::F_GETFD) } & libc::FD_CLOEXEC,
            0
        );
        drop(state);
        let mut byte = [0];
        // SAFETY: capture replaced this still-owned descriptor with /dev/null.
        assert_eq!(
            unsafe { libc::read(stdin.as_raw_fd(), byte.as_mut_ptr().cast(), 1) },
            0
        );
        helper.write_all(b"C").unwrap();
        assert!(
            root.poll(),
            "the original socket, not /dev/null, is retained"
        );
        root.acknowledge_stopped();
        helper.read_exact(&mut byte).unwrap();
        assert_eq!(byte, *b"A");
    }

    #[test]
    fn acknowledgement_retries_actual_socket_backpressure_without_blocking() {
        let (root, mut helper) = pair();
        {
            let mut state = root.state.lock().unwrap();
            let bytes = [b'F'; 4096];
            loop {
                match state.stream.write(&bytes) {
                    Ok(0) => panic!("control socket made no progress"),
                    Ok(_) => {}
                    Err(error) if error.kind() == io::ErrorKind::WouldBlock => break,
                    Err(error) => panic!("fill actual control socket: {error}"),
                }
            }
            // Fill any remaining sub-chunk space too: a failed large write
            // alone need not imply the one-byte acknowledgement would block.
            loop {
                match state.stream.write(b"F") {
                    Ok(1) => {}
                    Err(error) if error.kind() == io::ErrorKind::WouldBlock => break,
                    other => panic!("fill one-byte control capacity: {other:?}"),
                }
            }
        }
        helper.write_all(b"C").unwrap();
        assert!(root.poll());
        root.acknowledge_stopped();
        assert!(!root.state.lock().unwrap().acknowledged);
        let mut bytes = [0; 4096];
        loop {
            match helper.read(&mut bytes) {
                Ok(0) => panic!("actual control socket ended before acknowledgement"),
                Ok(n) => assert!(bytes[..n].iter().all(|byte| *byte == b'F')),
                Err(error) if error.kind() == io::ErrorKind::WouldBlock => break,
                Err(error) => panic!("drain actual control socket: {error}"),
            }
        }
        root.acknowledge_stopped();
        assert!(root.state.lock().unwrap().acknowledged);
        let mut byte = [0];
        assert_eq!(helper.read(&mut byte).unwrap(), 1);
        assert_eq!(byte, *b"A");
    }

    #[test]
    fn private_request_is_sticky_but_never_acknowledged_by_reading_alone() {
        let (root, mut helper) = pair();
        assert!(!root.poll());
        helper.write_all(b"C").unwrap();
        assert!(root.poll());
        let mut byte = [0];
        assert_eq!(
            helper.read(&mut byte).unwrap_err().kind(),
            io::ErrorKind::WouldBlock
        );
        root.acknowledge_stopped();
        assert_eq!(helper.read(&mut byte).unwrap(), 1);
        assert_eq!(byte, *b"A");
        assert!(root.poll());
        root.acknowledge_stopped();
        assert_eq!(
            helper.read(&mut byte).unwrap_err().kind(),
            io::ErrorKind::WouldBlock
        );
    }

    #[test]
    fn closed_or_malformed_control_stops_without_fabricating_acknowledgement() {
        for bytes in [b"X".as_slice(), b"CC".as_slice()] {
            let (root, mut helper) = pair();
            helper.write_all(bytes).unwrap();
            assert!(root.poll());
            root.acknowledge_stopped();
            let mut byte = [0];
            assert_eq!(
                helper.read(&mut byte).unwrap_err().kind(),
                io::ErrorKind::WouldBlock
            );
        }
        let (root, helper) = pair();
        drop(helper);
        assert!(root.poll());
        root.acknowledge_stopped();
        assert!(root.poll());
    }
}
