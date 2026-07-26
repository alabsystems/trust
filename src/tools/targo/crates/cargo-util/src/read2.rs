pub use self::imp::read2;
pub(crate) use self::imp::read2_interruptible;

/// Trust: whether an interruptible two-pipe reader should continue waiting for
/// data.
///
/// Upstream's `read2` callback returns `()`, so a reader has no way to say
/// "stop" — the loop runs until both pipes close no matter what the consumer
/// has already decided. A safety limit that cannot interrupt the read it is
/// bounding is not a limit, so the interruptible form exists alongside it.
/// Crate-private: the public `read2` compatibility API keeps upstream's shape.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum Read2Action {
    Continue,
    Stop,
}

#[cfg(unix)]
mod imp {
    use super::Read2Action;
    use libc::{F_GETFL, F_SETFL, O_NONBLOCK, c_int, fcntl};
    use std::io;
    use std::io::prelude::*;
    use std::mem;
    use std::os::unix::prelude::*;
    use std::process::{ChildStderr, ChildStdout};

    fn set_nonblock(fd: c_int) -> io::Result<()> {
        let flags = unsafe { fcntl(fd, F_GETFL) };
        if flags == -1 || unsafe { fcntl(fd, F_SETFL, flags | O_NONBLOCK) } == -1 {
            return Err(io::Error::last_os_error());
        }
        Ok(())
    }

    pub fn read2(
        out_pipe: ChildStdout,
        err_pipe: ChildStderr,
        data: &mut dyn FnMut(bool, &mut Vec<u8>, bool),
    ) -> io::Result<()> {
        read2_interruptible(out_pipe, err_pipe, None, &mut |is_out, bytes, eof| {
            data(is_out, bytes, eof);
            Read2Action::Continue
        })
        .map(drop)
    }

    pub(crate) fn read2_interruptible(
        mut out_pipe: ChildStdout,
        mut err_pipe: ChildStderr,
        deadline: Option<std::time::Instant>,
        data: &mut dyn FnMut(bool, &mut Vec<u8>, bool) -> Read2Action,
    ) -> io::Result<Read2Action> {
        set_nonblock(out_pipe.as_raw_fd())?;
        set_nonblock(err_pipe.as_raw_fd())?;

        let mut out_done = false;
        let mut err_done = false;
        let mut out = Vec::new();
        let mut err = Vec::new();

        let mut fds: [libc::pollfd; 2] = unsafe { mem::zeroed() };
        fds[0].fd = out_pipe.as_raw_fd();
        fds[0].events = libc::POLLIN;
        fds[1].fd = err_pipe.as_raw_fd();
        fds[1].events = libc::POLLIN;
        let mut nfds = 2;
        let mut errfd = 1;

        while nfds > 0 {
            // wait for either pipe to become readable using `poll`
            let poll_timeout = match deadline {
                Some(deadline) => {
                    let remaining = deadline
                        .checked_duration_since(std::time::Instant::now())
                        .ok_or_else(streaming_timeout_error)?;
                    // `poll` accepts signed milliseconds. Round a non-zero
                    // sub-millisecond remainder up so the deadline is not
                    // reported early, and cap long waits so they can be
                    // recomputed against the monotonic clock.
                    remaining
                        .as_millis()
                        .saturating_add(u128::from(remaining.subsec_nanos() % 1_000_000 != 0))
                        .clamp(1, c_int::MAX as u128) as c_int
                }
                None => -1,
            };
            let r = unsafe { libc::poll(fds.as_mut_ptr(), nfds, poll_timeout) };
            if r == -1 {
                let err = io::Error::last_os_error();
                if err.kind() == io::ErrorKind::Interrupted {
                    continue;
                }
                return Err(err);
            }
            if r == 0 {
                return Err(streaming_timeout_error());
            }

            // Trust: read one bounded chunk before invoking the callback.
            // Upstream's `read_to_end` on a nonblocking pipe keeps allocating
            // while a producer writes faster than Cargo processes its output,
            // so the higher layer's partial-line limit is never consulted until
            // the memory is already gone.
            if !err_done && fds[errfd].revents != 0 {
                err_done = read_available_chunk(&mut err_pipe, &mut err)?;
                if err_done {
                    nfds -= 1;
                }
                if data(false, &mut err, err_done) == Read2Action::Stop {
                    return Ok(Read2Action::Stop);
                }
            }
            if !out_done && fds[0].revents != 0 {
                out_done = read_available_chunk(&mut out_pipe, &mut out)?;
                if out_done {
                    fds[0].fd = err_pipe.as_raw_fd();
                    errfd = 0;
                    nfds -= 1;
                }
                if data(true, &mut out, out_done) == Read2Action::Stop {
                    return Ok(Read2Action::Stop);
                }
            }
        }
        if deadline.is_some_and(|deadline| std::time::Instant::now() >= deadline) {
            Err(streaming_timeout_error())
        } else {
            Ok(Read2Action::Continue)
        }
    }

    fn streaming_timeout_error() -> io::Error {
        io::Error::new(
            io::ErrorKind::TimedOut,
            "streaming process exceeded its wall-clock timeout",
        )
    }

    fn read_available_chunk(pipe: &mut impl Read, dst: &mut Vec<u8>) -> io::Result<bool> {
        const READ_CHUNK_BYTES: usize = 64 * 1024;
        let mut chunk = [0_u8; READ_CHUNK_BYTES];
        match pipe.read(&mut chunk) {
            Ok(0) => Ok(true),
            Ok(read) => {
                dst.try_reserve_exact(read).map_err(io::Error::other)?;
                dst.extend_from_slice(&chunk[..read]);
                Ok(false)
            }
            Err(error) if error.kind() == io::ErrorKind::WouldBlock => Ok(false),
            Err(error) => Err(error),
        }
    }
}

#[cfg(windows)]
mod imp {
    use super::Read2Action;
    use std::io;
    use std::os::windows::prelude::*;
    use std::process::{ChildStderr, ChildStdout};
    use std::slice;

    use miow::Overlapped;
    use miow::iocp::{CompletionPort, CompletionStatus};
    use miow::pipe::NamedPipe;
    use windows_sys::Win32::Foundation::{
        ERROR_BROKEN_PIPE, ERROR_NOT_FOUND, ERROR_OPERATION_ABORTED, HANDLE,
    };
    use windows_sys::Win32::System::IO::{CancelIoEx, GetOverlappedResult};

    struct Pipe<'a> {
        dst: &'a mut Vec<u8>,
        overlapped: Overlapped,
        pipe: NamedPipe,
        done: bool,
        pending: bool,
    }

    pub fn read2(
        out_pipe: ChildStdout,
        err_pipe: ChildStderr,
        data: &mut dyn FnMut(bool, &mut Vec<u8>, bool),
    ) -> io::Result<()> {
        read2_interruptible(out_pipe, err_pipe, None, &mut |is_out, bytes, eof| {
            data(is_out, bytes, eof);
            Read2Action::Continue
        })
        .map(drop)
    }

    pub(crate) fn read2_interruptible(
        out_pipe: ChildStdout,
        err_pipe: ChildStderr,
        deadline: Option<std::time::Instant>,
        data: &mut dyn FnMut(bool, &mut Vec<u8>, bool) -> Read2Action,
    ) -> io::Result<Read2Action> {
        let mut out = Vec::new();
        let mut err = Vec::new();

        let port = CompletionPort::new(1)?;
        port.add_handle(0, &out_pipe)?;
        port.add_handle(1, &err_pipe)?;

        unsafe {
            let mut out_pipe = Pipe::new(out_pipe, &mut out);
            let mut err_pipe = Pipe::new(err_pipe, &mut err);

            let read_result = (|| {
                out_pipe.read()?;
                err_pipe.read()?;

                let mut statuses = [CompletionStatus::zero(), CompletionStatus::zero()];

                while !out_pipe.done || !err_pipe.done {
                    let timeout = deadline
                        .map(|deadline| {
                            deadline
                                .checked_duration_since(std::time::Instant::now())
                                .ok_or_else(streaming_timeout_error)
                                .map(|remaining| remaining.max(std::time::Duration::from_millis(1)))
                        })
                        .transpose()?;
                    let completed = match port.get_many(&mut statuses, timeout) {
                        Ok(completed) => completed,
                        Err(error)
                            if error.raw_os_error()
                                == Some(windows_sys::Win32::Foundation::WAIT_TIMEOUT as i32) =>
                        {
                            return Err(streaming_timeout_error());
                        }
                        Err(error) => return Err(error),
                    };
                    for status in completed {
                        if status.token() == 0 {
                            out_pipe.complete(status);
                            if data(true, out_pipe.dst, out_pipe.done) == Read2Action::Stop {
                                return Ok(Read2Action::Stop);
                            }
                            out_pipe.read()?;
                        } else {
                            err_pipe.complete(status);
                            if data(false, err_pipe.dst, err_pipe.done) == Read2Action::Stop {
                                return Ok(Read2Action::Stop);
                            }
                            err_pipe.read()?;
                        }
                    }
                }

                if deadline.is_some_and(|deadline| std::time::Instant::now() >= deadline) {
                    Err(streaming_timeout_error())
                } else {
                    Ok(Read2Action::Continue)
                }
            })();

            // Every successful overlapped read owns pointers into `dst` and
            // `overlapped` until the kernel reports completion. Callback stops
            // and all I/O/IOCP error paths must therefore cancel and wait for
            // both operations before either Pipe (or its Vec) can be dropped.
            let cleanup_result = settle_pending_reads(&mut out_pipe, &mut err_pipe);
            combine_read_and_cleanup_results(read_result, cleanup_result)
        }
    }

    fn streaming_timeout_error() -> io::Error {
        io::Error::new(
            io::ErrorKind::TimedOut,
            "streaming process exceeded its wall-clock timeout",
        )
    }

    impl<'a> Pipe<'a> {
        unsafe fn new<P: IntoRawHandle>(p: P, dst: &'a mut Vec<u8>) -> Pipe<'a> {
            // SAFETY: Handle must be owned, open, and closeable with CloseHandle.
            let pipe = unsafe { NamedPipe::from_raw_handle(p.into_raw_handle()) };
            Pipe {
                dst,
                pipe,
                overlapped: Overlapped::zero(),
                done: false,
                pending: false,
            }
        }

        unsafe fn read(&mut self) -> io::Result<()> {
            if self.done {
                return Ok(());
            }
            assert!(
                !self.pending,
                "attempted to reuse an outstanding overlapped read"
            );
            let dst = unsafe { slice_to_bounded_end(self.dst) }?;
            // SAFETY: The buffer must be valid until the end of the I/O,
            // which is handled by completion or `settle_pending_reads`.
            match unsafe { self.pipe.read_overlapped(dst, self.overlapped.raw()) } {
                Ok(_) => {
                    // Even an immediately completed overlapped operation posts
                    // a completion packet because this handle has not enabled
                    // FILE_SKIP_COMPLETION_PORT_ON_SUCCESS.
                    self.pending = true;
                    Ok(())
                }
                Err(e) => {
                    if e.raw_os_error() == Some(ERROR_BROKEN_PIPE as i32) {
                        self.done = true;
                        Ok(())
                    } else {
                        Err(e)
                    }
                }
            }
        }

        unsafe fn complete(&mut self, status: &CompletionStatus) {
            assert!(
                self.pending,
                "received a completion without an outstanding read"
            );
            self.pending = false;
            let prev = self.dst.len();
            unsafe { self.dst.set_len(prev + status.bytes_transferred() as usize) };
            if status.bytes_transferred() == 0 {
                self.done = true;
            }
        }

        unsafe fn cancel(&mut self) -> io::Result<()> {
            if !self.pending {
                return Ok(());
            }
            // SAFETY: `pipe` and `overlapped` remain alive until the matching
            // wait below establishes that the operation has finished.
            let cancelled =
                unsafe { CancelIoEx(self.pipe.as_raw_handle() as HANDLE, self.overlapped.raw()) };
            if cancelled != 0 {
                return Ok(());
            }
            let error = io::Error::last_os_error();
            if error.raw_os_error() == Some(ERROR_NOT_FOUND as i32) {
                // The request completed before cancellation found it. Its
                // completion may still be queued, so `wait` remains required.
                Ok(())
            } else {
                Err(error)
            }
        }

        unsafe fn wait(&mut self) -> io::Result<()> {
            if !self.pending {
                return Ok(());
            }
            let mut transferred = 0;
            // SAFETY: there is exactly one operation using this OVERLAPPED and
            // its buffer. A blocking wait is required before those objects can
            // move or drop, including during unwinding.
            let completed = unsafe {
                GetOverlappedResult(
                    self.pipe.as_raw_handle() as HANDLE,
                    self.overlapped.raw(),
                    &mut transferred,
                    1,
                )
            };
            self.pending = false;
            if completed != 0 {
                return Ok(());
            }
            let error = io::Error::last_os_error();
            if matches!(
                error.raw_os_error(),
                Some(code)
                    if code == ERROR_OPERATION_ABORTED as i32
                        || code == ERROR_BROKEN_PIPE as i32
            ) {
                Ok(())
            } else {
                Err(error)
            }
        }
    }

    impl Drop for Pipe<'_> {
        fn drop(&mut self) {
            if self.pending {
                // This is the panic/unwind safety net. Normal returns use
                // `settle_pending_reads` so cleanup errors can be reported.
                unsafe {
                    let _ = self.cancel();
                    let _ = self.wait();
                }
            }
        }
    }

    unsafe fn settle_pending_reads(out: &mut Pipe<'_>, err: &mut Pipe<'_>) -> io::Result<()> {
        let mut first_error = None;
        for result in [
            unsafe { out.cancel() },
            unsafe { err.cancel() },
            unsafe { out.wait() },
            unsafe { err.wait() },
        ] {
            if let Err(error) = result
                && first_error.is_none()
            {
                first_error = Some(error);
            }
        }
        first_error.map_or(Ok(()), Err)
    }

    /// Trust: a stopped read leaves overlapped operations outstanding against
    /// buffers this function is about to drop. Both results have to be
    /// surfaced — reporting only the read error would hide a failure to settle
    /// them, which is a memory-safety condition rather than an I/O one.
    fn combine_read_and_cleanup_results(
        read: io::Result<Read2Action>,
        cleanup: io::Result<()>,
    ) -> io::Result<Read2Action> {
        match (read, cleanup) {
            (Ok(action), Ok(())) => Ok(action),
            (Err(error), Ok(())) | (Ok(_), Err(error)) => Err(error),
            (Err(read_error), Err(cleanup_error)) => Err(io::Error::other(format!(
                "{read_error}; additionally failed to settle overlapped pipe reads: {cleanup_error}"
            ))),
        }
    }

    /// Trust: the Windows counterpart of the bounded-chunk read on Unix —
    /// grow by a fixed increment and hand the OS only that much, so a fast
    /// writer cannot outrun the consumer's limit check.
    unsafe fn slice_to_bounded_end(v: &mut Vec<u8>) -> io::Result<&mut [u8]> {
        const READ_CHUNK_BYTES: usize = 64 * 1024;
        if v.capacity().saturating_sub(v.len()) < READ_CHUNK_BYTES {
            v.try_reserve_exact(READ_CHUNK_BYTES)
                .map_err(io::Error::other)?;
        }
        let available = v.capacity() - v.len();
        let read_len = available.min(READ_CHUNK_BYTES);
        Ok(unsafe { slice::from_raw_parts_mut(v.as_mut_ptr().add(v.len()), read_len) })
    }
}
