use libc::c_int;

use crate::FromEnvErrorInner;
use std::fs::{File, OpenOptions};
use std::io::{self, Read, Write};
use std::mem;
use std::mem::MaybeUninit;
use std::os::unix::prelude::*;
use std::path::Path;
use std::process::Command;
use std::sync::{
    atomic::{AtomicBool, Ordering},
    Arc,
};
use std::thread::{self, Builder, JoinHandle};
use std::time::Duration;

#[derive(Debug)]
/// This preserves the `--jobserver-auth` type at creation time,
/// so auth type will be passed down to and inherit from sub-Make processes correctly.
///
/// See <https://github.com/rust-lang/jobserver-rs/issues/99> for details.
enum ClientCreationArg {
    Fds,
    Fifo(Box<Path>),
}

#[derive(Debug)]
pub struct Client {
    read: File,
    write: File,
    creation_arg: ClientCreationArg,
    /// It is set to `None` if the pipe is shared with other processes, so it
    /// cannot support non-blocking mode.
    ///
    /// If it is set to `Some`, then it can only go from
    /// `Some(false)` -> `Some(true)` but not the other way around,
    /// since that could cause a race condition.
    is_non_blocking: Option<AtomicBool>,
}

#[derive(Debug)]
pub struct Acquired {
    byte: u8,
}

impl Client {
    pub(crate) fn transport_witnesses(&self) -> io::Result<crate::TransportWitnesses> {
        let read = self.read.as_fd().try_clone_to_owned()?;
        let write = self.write.as_fd().try_clone_to_owned()?;
        Ok(match &self.creation_arg {
            ClientCreationArg::Fds => crate::TransportWitnesses::NumericPipe { read, write },
            ClientCreationArg::Fifo(path) => crate::TransportWitnesses::NamedFifo {
                path: path.to_path_buf(),
                read,
                write,
            },
        })
    }

    // Trust: a named FIFO permits independent descriptions on Darwin, unlike
    // dup or /dev/fd on an anonymous pipe. Both sides stay nonblocking for a
    // bounded owner step; acquire_allow_interrupts still polls empty reads.
    pub(crate) fn open_fifo(path: &Path) -> io::Result<Client> {
        use std::os::unix::fs::OpenOptionsExt;

        if !path.is_absolute()
            || path
                .to_str()
                .is_none_or(|text| text.chars().any(char::is_whitespace))
        {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "jobserver FIFO path must be absolute UTF-8 without whitespace",
            ));
        }
        let open = |reading| {
            OpenOptions::new()
                .read(reading)
                .write(!reading)
                .custom_flags(libc::O_NOFOLLOW | libc::O_CLOEXEC | libc::O_NONBLOCK)
                .open(path)
        };
        // Trust: the nonblocking reader opens without waiting for a writer;
        // retaining it permits the nonblocking writer to open. Directional
        // descriptions also prevent Darwin's FIONREAD write-side overwrite.
        let read = open(true)?;
        let write = open(false)?;
        check_fifo_pair(&read, &write)?;
        Ok(Client {
            read,
            write,
            creation_arg: ClientCreationArg::Fifo(path.into()),
            is_non_blocking: Some(AtomicBool::new(true)),
        })
    }

    pub(crate) fn open_fifo_with_witnesses(
        path: &Path,
        read: BorrowedFd<'_>,
        write: BorrowedFd<'_>,
    ) -> io::Result<Client> {
        let witnesses = (File::from(read.try_clone_to_owned()?), File::from(write.try_clone_to_owned()?));
        check_fifo_pair(&witnesses.0, &witnesses.1)?;
        let client = Self::open_fifo(path)?;
        let expected = witnesses.0.metadata()?;
        let opened = client.read.metadata()?;
        if expected.dev() != opened.dev() || expected.ino() != opened.ino() {
            return Err(io::Error::new(io::ErrorKind::InvalidInput, "jobserver FIFO differs from retained witnesses"));
        }
        Ok(client)
    }

    pub fn new(mut limit: usize) -> io::Result<Client> {
        let client = unsafe { Client::mk()? };

        // I don't think the character written here matters, but I could be
        // wrong!
        const BUFFER: [u8; 128] = [b'|'; 128];

        let mut write = &client.write;

        set_nonblocking(write.as_raw_fd(), true)?;

        while limit > 0 {
            let n = limit.min(BUFFER.len());

            write.write_all(&BUFFER[..n])?;
            limit -= n;
        }

        set_nonblocking(write.as_raw_fd(), false)?;

        Ok(client)
    }

    unsafe fn mk() -> io::Result<Client> {
        let mut pipes = [0; 2];

        // Atomically-create-with-cloexec on Linux.
        #[cfg(target_os = "linux")]
        if libc::pipe2(pipes.as_mut_ptr(), libc::O_CLOEXEC) == -1 {
            return Err(io::Error::last_os_error());
        }

        #[cfg(not(target_os = "linux"))]
        {
            cvt(libc::pipe(pipes.as_mut_ptr()))?;
            drop(set_cloexec(pipes[0], true));
            drop(set_cloexec(pipes[1], true));
        }

        Ok(Client::from_fds(pipes[0], pipes[1]))
    }

    pub(crate) unsafe fn open(s: &str, check_pipe: bool) -> Result<Client, FromEnvErrorInner> {
        if let Some(client) = Self::from_fifo(s)? {
            return Ok(client);
        }
        if let Some(client) = Self::from_pipe(s, check_pipe)? {
            return Ok(client);
        }
        Err(FromEnvErrorInner::CannotParse(format!(
            "expected `fifo:PATH` or `R,W`, found `{s}`"
        )))
    }

    /// `--jobserver-auth=fifo:PATH`
    fn from_fifo(s: &str) -> Result<Option<Client>, FromEnvErrorInner> {
        let mut parts = s.splitn(2, ':');
        if parts.next().unwrap() != "fifo" {
            return Ok(None);
        }
        let path_str = parts.next().ok_or_else(|| {
            FromEnvErrorInner::CannotParse("expected a path after `fifo:`".to_string())
        })?;
        let path = Path::new(path_str);

        let open_file = |reading| {
            // Trust: open without a peer wait, then restore this importer's
            // existing blocking behavior after both directional ends exist.
            // An O_RDWR FIFO makes Darwin's FIONREAD overwrite the read-side
            // count with the write-side receive count, incorrectly reporting 0.
            OpenOptions::new()
                .read(reading)
                .write(!reading)
                .custom_flags(libc::O_NONBLOCK)
                .open(path)
                .map_err(|err| FromEnvErrorInner::CannotOpenPath(path_str.to_string(), err))
        };

        let read = open_file(true)?;
        let write = open_file(false)?;
        for file in [&read, &write] {
            set_nonblocking(file.as_raw_fd(), false)
                .map_err(|err| FromEnvErrorInner::CannotOpenPath(path_str.to_string(), err))?;
        }

        Ok(Some(Client {
            read,
            write,
            creation_arg: ClientCreationArg::Fifo(path.into()),
            is_non_blocking: Some(AtomicBool::new(false)),
        }))
    }

    /// `--jobserver-auth=R,W`
    unsafe fn from_pipe(s: &str, check_pipe: bool) -> Result<Option<Client>, FromEnvErrorInner> {
        let mut parts = s.splitn(2, ',');
        let read = parts.next().unwrap();
        let write = match parts.next() {
            Some(w) => w,
            None => return Ok(None),
        };
        let read = read
            .parse()
            .map_err(|e| FromEnvErrorInner::CannotParse(format!("cannot parse `read` fd: {e}")))?;
        let write = write
            .parse()
            .map_err(|e| FromEnvErrorInner::CannotParse(format!("cannot parse `write` fd: {e}")))?;

        // If either or both of these file descriptors are negative,
        // it means the jobserver is disabled for this process.
        if read < 0 {
            return Err(FromEnvErrorInner::NegativeFd(read));
        }
        if write < 0 {
            return Err(FromEnvErrorInner::NegativeFd(write));
        }

        let creation_arg = ClientCreationArg::Fds;

        // Ok so we've got two integers that look like file descriptors, but
        // for extra sanity checking let's see if they actually look like
        // valid files and instances of a pipe if feature enabled before we
        // return the client.
        //
        // If we're called from `make` *without* the leading + on our rule
        // then we'll have `MAKEFLAGS` env vars but won't actually have
        // access to the file descriptors.
        //
        // `NotAPipe` is a worse error, return it if it's reported for any of the two fds.
        match (fd_check(read, check_pipe), fd_check(write, check_pipe)) {
            (read_err @ Err(FromEnvErrorInner::NotAPipe(..)), _) => read_err?,
            (_, write_err @ Err(FromEnvErrorInner::NotAPipe(..))) => write_err?,
            (read_err, write_err) => {
                read_err?;
                write_err?;

                // Optimization: Try converting it to a fifo by using /dev/fd
                //
                // On linux, opening `/dev/fd/$fd` returns a fd with a new file description,
                // so we can set `O_NONBLOCK` on it without affecting other processes.
                //
                // On macOS, opening `/dev/fd/$fd` seems to be the same as `File::try_clone`.
                //
                // I tested this on macOS 14 and Linux 6.5.13
                #[cfg(target_os = "linux")]
                if let (Ok(read), Ok(write)) = (
                    File::open(format!("/dev/fd/{}", read)),
                    OpenOptions::new()
                        .write(true)
                        .open(format!("/dev/fd/{}", write)),
                ) {
                    return Ok(Some(Client {
                        read,
                        write,
                        creation_arg,
                        is_non_blocking: Some(AtomicBool::new(false)),
                    }));
                }
            }
        }

        Ok(Some(Client {
            read: clone_fd_and_set_cloexec(read)?,
            write: clone_fd_and_set_cloexec(write)?,
            creation_arg,
            is_non_blocking: None,
        }))
    }

    unsafe fn from_fds(read: c_int, write: c_int) -> Client {
        Client {
            read: File::from_raw_fd(read),
            write: File::from_raw_fd(write),
            creation_arg: ClientCreationArg::Fds,
            is_non_blocking: None,
        }
    }

    pub fn acquire(&self) -> io::Result<Acquired> {
        // Ignore interrupts and keep trying if that happens
        loop {
            if let Some(token) = self.acquire_allow_interrupts()? {
                return Ok(token);
            }
        }
    }

    /// Block waiting for a token, returning `None` if we're interrupted with
    /// EINTR.
    fn acquire_allow_interrupts(&self) -> io::Result<Option<Acquired>> {
        // We don't actually know if the file descriptor here is set in
        // blocking or nonblocking mode. AFAIK all released versions of
        // `make` use blocking fds for the jobserver, but the unreleased
        // version of `make` doesn't. In the unreleased version jobserver
        // fds are set to nonblocking and combined with `pselect`
        // internally.
        //
        // Here we try to be compatible with both strategies. We optimistically
        // try to read from the file descriptor which then may block, return
        // a token or indicate that polling is needed.
        // Blocking reads (if possible) allows the kernel to be more selective
        // about which readers to wake up when a token is written to the pipe.
        //
        // We use `poll` here to block this thread waiting for read
        // readiness, and then afterwards we perform the `read` itself. If
        // the `read` returns that it would block then we start over and try
        // again.
        //
        // Also note that we explicitly don't handle EINTR here. That's used
        // to shut us down, so we otherwise punt all errors upwards.
        unsafe {
            let mut fd: libc::pollfd = mem::zeroed();
            let mut read = &self.read;
            fd.fd = read.as_raw_fd();
            fd.events = libc::POLLIN;
            loop {
                let mut buf = [0];
                match read.read(&mut buf) {
                    Ok(1) => return Ok(Some(Acquired { byte: buf[0] })),
                    Ok(_) => {
                        return Err(io::Error::new(
                            io::ErrorKind::UnexpectedEof,
                            "early EOF on jobserver pipe",
                        ));
                    }
                    Err(e) => match e.kind() {
                        io::ErrorKind::WouldBlock => { /* fall through to polling */ }
                        io::ErrorKind::Interrupted => return Ok(None),
                        _ => return Err(e),
                    },
                }

                loop {
                    fd.revents = 0;
                    if libc::poll(&mut fd, 1, -1) == -1 {
                        let e = io::Error::last_os_error();
                        return match e.kind() {
                            io::ErrorKind::Interrupted => Ok(None),
                            _ => Err(e),
                        };
                    }
                    if fd.revents != 0 {
                        break;
                    }
                }
            }
        }
    }

    pub fn try_acquire(&self) -> io::Result<Option<Acquired>> {
        let mut buf = [0];
        let mut fifo = &self.read;

        if let Some(is_non_blocking) = self.is_non_blocking.as_ref() {
            if !is_non_blocking.load(Ordering::Relaxed) {
                set_nonblocking(fifo.as_raw_fd(), true)?;
                is_non_blocking.store(true, Ordering::Relaxed);
            }
        } else {
            return Err(io::ErrorKind::Unsupported.into());
        }

        loop {
            match fifo.read(&mut buf) {
                Ok(1) => break Ok(Some(Acquired { byte: buf[0] })),
                Ok(_) => {
                    break Err(io::Error::new(
                        io::ErrorKind::UnexpectedEof,
                        "early EOF on jobserver pipe",
                    ))
                }

                Err(e) if e.kind() == io::ErrorKind::WouldBlock => break Ok(None),
                Err(e) if e.kind() == io::ErrorKind::Interrupted => continue,

                Err(err) => break Err(err),
            }
        }
    }

    pub fn release(&self, data: Option<&Acquired>) -> io::Result<()> {
        // Trust: ordinary guard returns must not silently lose a token when
        // a nonblocking FIFO is full. Raw issuance adds no readiness wait:
        // explicitly nonblocking owners receive WouldBlock at capacity.
        self.release_with_wait(data, || {
            let mut descriptor = libc::pollfd {
                fd: self.write.as_raw_fd(),
                events: libc::POLLOUT,
                revents: 0,
            };
            loop {
                // SAFETY: the one pollfd is initialized and this Client owns
                // its live write description for the entire readiness wait.
                match unsafe { libc::poll(&mut descriptor, 1, -1) } {
                    -1 => {
                        let error = io::Error::last_os_error();
                        if error.kind() != io::ErrorKind::Interrupted {
                            return Err(error);
                        }
                    }
                    0 => {}
                    _ => return Ok(()),
                }
            }
        })
    }

    // Trust: the immediate waiter keeps the guarded/raw policy decision at
    // the actual WouldBlock boundary. It is not retained or user configurable.
    fn release_with_wait(
        &self,
        data: Option<&Acquired>,
        mut wait_writable: impl FnMut() -> io::Result<()>,
    ) -> io::Result<()> {
        let byte = data.map(|d| d.byte).unwrap_or(b'+');
        loop {
            match (&self.write).write(&[byte]) {
                Ok(1) => return Ok(()),
                Ok(_) => {
                    return Err(io::Error::new(
                        io::ErrorKind::Other,
                        "failed to write token back to jobserver",
                    ));
                }
                Err(error) if error.kind() == io::ErrorKind::Interrupted => {}
                Err(error) if error.kind() == io::ErrorKind::WouldBlock && data.is_some() => {
                    wait_writable()?;
                }
                Err(error) => return Err(error),
            }
        }
    }

    pub fn string_arg(&self) -> String {
        match &self.creation_arg {
            ClientCreationArg::Fifo(path) => format!("fifo:{}", path.display()),
            // Imports own clones of the caller's descriptors. Export those
            // same descriptors that configure() hands to the child, rather
            // than borrowing the original numbers after their owners close.
            ClientCreationArg::Fds => {
                format!("{},{}", self.read.as_raw_fd(), self.write.as_raw_fd())
            }
        }
    }

    pub fn available(&self) -> io::Result<usize> {
        let mut len = MaybeUninit::<c_int>::uninit();
        cvt(unsafe { libc::ioctl(self.read.as_raw_fd(), libc::FIONREAD, len.as_mut_ptr()) })?;
        Ok(unsafe { len.assume_init() } as usize)
    }

    pub fn configure(&self, cmd: &mut Command) {
        if matches!(self.creation_arg, ClientCreationArg::Fifo { .. }) {
            // We `File::open`ed it when inheriting from environment,
            // so no need to set cloexec for fifo.
            return;
        }
        // Here we basically just want to say that in the child process
        // we'll configure the read/write file descriptors to *not* be
        // cloexec, so they're inherited across the exec and specified as
        // integers through `string_arg` above.
        let read = self.read.as_raw_fd();
        let write = self.write.as_raw_fd();
        unsafe {
            cmd.pre_exec(move || {
                set_cloexec(read, false)?;
                set_cloexec(write, false)?;
                Ok(())
            });
        }
    }
}

// Trust: descriptor identity, rather than a pathname-only observation, binds
// the two opens to the same actual FIFO before either is exposed to callers.
fn check_fifo_pair(read: &File, write: &File) -> io::Result<()> {
    use std::os::unix::fs::{FileTypeExt, MetadataExt};

    let read = read.metadata()?;
    let write = write.metadata()?;
    if !read.file_type().is_fifo()
        || !write.file_type().is_fifo()
        || read.dev() != write.dev()
        || read.ino() != write.ino()
    {
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            "jobserver descriptions do not name the same FIFO",
        ));
    }
    Ok(())
}

#[derive(Debug)]
pub struct Helper {
    thread: JoinHandle<()>,
    state: Arc<super::HelperState>,
}

pub(crate) fn spawn_helper(
    client: crate::Client,
    state: Arc<super::HelperState>,
    mut f: Box<dyn FnMut(io::Result<crate::Acquired>) + Send>,
) -> io::Result<Helper> {
    #[cfg(not(miri))]
    {
        use std::sync::Once;

        static USR1_INIT: Once = Once::new();
        let mut err = None;
        USR1_INIT.call_once(|| unsafe {
            let mut new: libc::sigaction = mem::zeroed();
            new.sa_sigaction = sigusr1_handler as *const () as usize;
            new.sa_flags = libc::SA_SIGINFO as _;
            if libc::sigaction(libc::SIGUSR1, &new, std::ptr::null_mut()) != 0 {
                err = Some(io::Error::last_os_error());
            }
        });

        if let Some(e) = err.take() {
            return Err(e);
        }
    }

    let state2 = state.clone();
    let thread = Builder::new().spawn(move || {
        // Trust: `SIGUSR1` is the only way to interrupt this thread's blocking
        // `read`, and a thread inherits its signal mask. A process started with
        // the signal blocked would otherwise have a helper nobody can stop.
        #[cfg(not(miri))]
        unsafe {
            let mut set: libc::sigset_t = mem::zeroed();
            libc::sigemptyset(&mut set);
            libc::sigaddset(&mut set, libc::SIGUSR1);
            libc::pthread_sigmask(libc::SIG_UNBLOCK, &set, std::ptr::null_mut());
        }
        state2.for_each_request(|helper| loop {
            match client.inner.acquire_allow_interrupts() {
                Ok(Some(data)) => {
                    break f(Ok(crate::Acquired {
                        client: client.inner.clone(),
                        data,
                        disabled: false,
                    }));
                }
                Err(e) => break f(Err(e)),
                Ok(None) if helper.lock().producer_done => break,
                Ok(None) => {}
            }
        });
    })?;

    Ok(Helper { thread, state })
}

impl Helper {
    pub fn join(self) {
        let dur = Duration::from_millis(10);
        let mut state = self.state.lock();
        debug_assert!(state.producer_done);

        // We need to join our helper thread, and it could be blocked in one
        // of two locations. First is the wait for a request, but the
        // initial drop of `HelperState` will take care of that. Otherwise
        // it may be blocked in `client.acquire()`. We actually have no way
        // of interrupting that, so resort to `pthread_kill` as a fallback.
        // This signal should interrupt any blocking `read` call with
        // `io::ErrorKind::Interrupt` and cause the thread to cleanly exit.
        //
        // Note that we don't do this forever though since there's a chance
        // of bugs, so only do this opportunistically to make a best effort
        // at clearing ourselves up.
        for _ in 0..100 {
            if state.consumer_done {
                break;
            }
            #[cfg(not(miri))]
            unsafe {
                // Ignore the return value here of `pthread_kill`,
                // apparently on OSX if you kill a dead thread it will
                // return an error, but on other platforms it may not. In
                // that sense we don't actually know if this will succeed or
                // not!
                libc::pthread_kill(self.thread.as_pthread_t() as _, libc::SIGUSR1);
            }
            state = self
                .state
                .cvar
                .wait_timeout(state, dur)
                .unwrap_or_else(|e| e.into_inner())
                .0;
            thread::yield_now(); // we really want the other thread to run
        }

        // If we managed to actually see the consumer get done, then we can
        // definitely wait for the thread. Otherwise it's... off in the ether
        // I guess?
        if state.consumer_done {
            drop(self.thread.join());
        }
    }

    /// Trust: `join` without its bound. The signal is sent again every 10 ms
    /// for as long as the thread lives, because one sent while the thread is
    /// between its `producer_done` check and its `read` interrupts nothing. A
    /// thread that ended without setting `consumer_done` (its callback
    /// panicked) is seen through `is_finished`, so this cannot wait on a
    /// thread that no longer exists.
    ///
    /// Two states defeat the signal, and then this never returns: a `SIGUSR1`
    /// disposition replaced after the helper started (ignored, the signal
    /// interrupts nothing), and a callback that does not return, such as one
    /// writing a token back to a pool somebody over-filled. Giving up there
    /// would bring back the lost token, so it says once what it waits for.
    pub fn join_blocking(self) -> io::Result<()> {
        let dur = Duration::from_millis(10);
        let mut state = self.state.lock();
        debug_assert!(state.producer_done);
        let mut rounds = 0u32;
        while !state.consumer_done && !self.thread.is_finished() {
            rounds = rounds.saturating_add(1);
            if rounds == 1000 && !cfg!(miri) {
                eprintln!(
                    "jobserver: the helper thread has not stopped after 10 seconds; still \
                     waiting, because exiting now could lose a token it holds. It is blocked \
                     reading or writing the jobserver pool, or its callback has not returned, \
                     and SIGUSR1 does not interrupt it (was the signal's handler replaced?)."
                );
            }
            #[cfg(not(miri))]
            unsafe {
                // The handle is not joined yet, so the thread id is still
                // valid even if the thread has just ended.
                libc::pthread_kill(self.thread.as_pthread_t() as _, libc::SIGUSR1);
            }
            // Miri cannot send the signal, so there the wait stays bounded.
            #[cfg(miri)]
            if rounds > 100 {
                return Err(io::Error::new(
                    io::ErrorKind::TimedOut,
                    "jobserver helper thread cannot be interrupted under Miri; it was not joined",
                ));
            }
            state = self
                .state
                .cvar
                .wait_timeout(state, dur)
                .unwrap_or_else(|e| e.into_inner())
                .0;
        }
        drop(state);
        self.thread.join().map_err(|_| {
            io::Error::new(io::ErrorKind::Other, "jobserver helper thread panicked")
        })
    }
}

unsafe fn fcntl_check(fd: c_int) -> Result<(), FromEnvErrorInner> {
    match libc::fcntl(fd, libc::F_GETFD) {
        -1 => Err(FromEnvErrorInner::CannotOpenFd(
            fd,
            io::Error::last_os_error(),
        )),
        _ => Ok(()),
    }
}

unsafe fn fd_check(fd: c_int, check_pipe: bool) -> Result<(), FromEnvErrorInner> {
    if check_pipe {
        let mut stat = mem::zeroed();
        if libc::fstat(fd, &mut stat) == -1 {
            let last_os_error = io::Error::last_os_error();
            fcntl_check(fd)?;
            Err(FromEnvErrorInner::NotAPipe(fd, Some(last_os_error)))
        } else {
            // On android arm and i686 mode_t is u16 and st_mode is u32,
            // this generates a type mismatch when S_IFIFO (declared as mode_t)
            // is used in operations with st_mode, so we use this workaround
            // to get the value of S_IFIFO with the same type of st_mode.
            #[allow(unused_assignments)]
            let mut s_ififo = stat.st_mode;
            s_ififo = libc::S_IFIFO as _;
            if stat.st_mode & s_ififo == s_ififo {
                return Ok(());
            }
            Err(FromEnvErrorInner::NotAPipe(fd, None))
        }
    } else {
        fcntl_check(fd)
    }
}

fn clone_fd_and_set_cloexec(fd: c_int) -> Result<File, FromEnvErrorInner> {
    // Safety: fd is a valid fd and it remains open until returns
    unsafe { BorrowedFd::borrow_raw(fd) }
        .try_clone_to_owned()
        .map(File::from)
        .map_err(|err| FromEnvErrorInner::CannotOpenFd(fd, err))
}

fn set_cloexec(fd: c_int, set: bool) -> io::Result<()> {
    unsafe {
        let previous = cvt(libc::fcntl(fd, libc::F_GETFD))?;
        let new = if set {
            previous | libc::FD_CLOEXEC
        } else {
            previous & !libc::FD_CLOEXEC
        };
        if new != previous {
            cvt(libc::fcntl(fd, libc::F_SETFD, new))?;
        }
        Ok(())
    }
}

fn set_nonblocking(fd: c_int, set: bool) -> io::Result<()> {
    let status_flag = if set { libc::O_NONBLOCK } else { 0 };

    unsafe {
        cvt(libc::fcntl(fd, libc::F_SETFL, status_flag))?;
    }

    Ok(())
}

fn cvt(t: c_int) -> io::Result<c_int> {
    if t == -1 {
        Err(io::Error::last_os_error())
    } else {
        Ok(t)
    }
}

#[cfg(not(miri))]
extern "C" fn sigusr1_handler(
    _signum: c_int,
    _info: *mut libc::siginfo_t,
    _ptr: *mut libc::c_void,
) {
    // nothing to do
}

#[cfg(test)]
mod test {
    use super::Client as ClientImp;

    use crate::{test::run_named_fifo_try_acquire_tests, Client};

    use std::{fs::File, io::Write, os::unix::io::AsRawFd, sync::Arc};

    fn from_imp_client(imp: ClientImp) -> Client {
        Client {
            inner: Arc::new(imp),
        }
    }

    fn new_client_from_fifo() -> (Client, String) {
        let file = tempfile::NamedTempFile::new().unwrap();
        let fifo_path = file.path().to_owned();
        file.close().unwrap(); // Remove the NamedTempFile to create fifo

        nix::unistd::mkfifo(&fifo_path, nix::sys::stat::Mode::S_IRWXU).unwrap();

        let arg = format!("fifo:{}", fifo_path.to_str().unwrap());

        (
            ClientImp::from_fifo(&arg)
                .unwrap()
                .map(from_imp_client)
                .unwrap(),
            arg,
        )
    }

    fn new_client_from_pipe() -> (Client, String) {
        let (read, write) = nix::unistd::pipe().unwrap();
        let read = File::from(read);
        let mut write = File::from(write);

        write.write_all(b"1").unwrap();

        let arg = format!("{},{}", read.as_raw_fd(), write.as_raw_fd());

        (
            unsafe { ClientImp::from_pipe(&arg, true) }
                .unwrap()
                .map(from_imp_client)
                .unwrap(),
            arg,
        )
    }

    #[test]
    fn test_try_acquire_named_fifo() {
        run_named_fifo_try_acquire_tests(&new_client_from_fifo().0);
    }

    #[test]
    fn test_try_acquire_annoymous_pipe_linux_specific_optimization() {
        #[cfg(not(target_os = "linux"))]
        assert_eq!(
            new_client_from_pipe().0.try_acquire().unwrap_err().kind(),
            std::io::ErrorKind::Unsupported
        );

        #[cfg(target_os = "linux")]
        {
            let client = new_client_from_pipe().0;
            client.acquire().unwrap().drop_without_releasing();
            run_named_fifo_try_acquire_tests(&client);
        }
    }

    #[test]
    fn test_string_arg() {
        let (client, arg) = new_client_from_fifo();
        assert_eq!(client.inner.string_arg(), arg);

        let (client, _) = new_client_from_pipe();
        assert_eq!(
            client.inner.string_arg(),
            format!(
                "{},{}",
                client.inner.read.as_raw_fd(),
                client.inner.write.as_raw_fd()
            )
        );
    }

    // Trust: the pair check must reject a path replacement between opens,
    // represented deterministically by descriptors for two real FIFO nodes.
    #[test]
    fn explicit_fifo_pair_requires_one_actual_node() {
        let world = tempfile::tempdir().unwrap();
        let first = world.path().join("first");
        let second = world.path().join("second");
        for path in [&first, &second] {
            nix::unistd::mkfifo(
                path,
                nix::sys::stat::Mode::S_IRUSR | nix::sys::stat::Mode::S_IWUSR,
            )
            .unwrap();
        }
        let first = Client::from_fifo(&first).unwrap();
        let second = Client::from_fifo(&second).unwrap();
        for (file, mode) in [
            (&first.inner.read, libc::O_RDONLY),
            (&first.inner.write, libc::O_WRONLY),
        ] {
            // SAFETY: both Files remain owned throughout these read-only queries.
            let (status, descriptor) = unsafe {
                (
                    libc::fcntl(file.as_raw_fd(), libc::F_GETFL),
                    libc::fcntl(file.as_raw_fd(), libc::F_GETFD),
                )
            };
            assert!(status >= 0 && status & libc::O_NONBLOCK != 0);
            assert_eq!(status & libc::O_ACCMODE, mode);
            assert!(descriptor >= 0 && descriptor & libc::FD_CLOEXEC != 0);
        }
        assert!(super::check_fifo_pair(&first.inner.read, &first.inner.write).is_ok());
        assert!(super::check_fifo_pair(&first.inner.read, &second.inner.write).is_err());
        let regular = tempfile::tempfile().unwrap();
        assert!(super::check_fifo_pair(&first.inner.read, &regular).is_err());
    }

    #[test]
    fn witnessed_fifo_preserves_tokens_and_refuses_replaced_or_missing_path() {
        use std::os::fd::AsFd;
        let world = tempfile::tempdir().unwrap();
        let path = world.path().join("tokens");
        nix::unistd::mkfifo(&path, nix::sys::stat::Mode::S_IRUSR | nix::sys::stat::Mode::S_IWUSR).unwrap();
        let original = Client::from_fifo(&path).unwrap();
        original.release_raw().unwrap();
        let adopted = Client::from_fifo_with_witnesses(&path, original.inner.read.as_fd(), original.inner.write.as_fd()).unwrap();
        assert_eq!(adopted.inner.string_arg(), original.inner.string_arg());
        assert_eq!(adopted.available().unwrap(), 1);
        let token = adopted.acquire().unwrap();
        assert_eq!(original.available().unwrap(), 0);
        drop(token);
        assert_eq!(original.available().unwrap(), 1);
        std::fs::remove_file(&path).unwrap();
        assert!(Client::from_fifo_with_witnesses(&path, original.inner.read.as_fd(), original.inner.write.as_fd()).is_err());
        nix::unistd::mkfifo(&path, nix::sys::stat::Mode::S_IRUSR | nix::sys::stat::Mode::S_IWUSR).unwrap();
        assert!(Client::from_fifo_with_witnesses(&path, original.inner.read.as_fd(), original.inner.write.as_fd()).is_err());
        assert_eq!(original.available().unwrap(), 1);
    }

    // Trust: preserve the ordinary importer's blocking contract while using
    // the directional read endpoint required for accurate Darwin FIONREAD.
    #[test]
    fn ambient_fifo_import_keeps_blocking_modes_and_reports_queued_tokens() {
        let (client, _) = new_client_from_fifo();
        for (file, mode) in [
            (&client.inner.read, libc::O_RDONLY),
            (&client.inner.write, libc::O_WRONLY),
        ] {
            // SAFETY: these Files remain owned throughout the flag query.
            let flags = unsafe { libc::fcntl(file.as_raw_fd(), libc::F_GETFL) };
            assert!(flags >= 0);
            assert_eq!(flags & libc::O_ACCMODE, mode);
            assert_eq!(flags & libc::O_NONBLOCK, 0);
        }
        client.release_raw().unwrap();
        assert_eq!(client.available().unwrap(), 1);
        let token = client.acquire().unwrap();
        assert_eq!(client.available().unwrap(), 0);
        drop(token);
        assert_eq!(client.available().unwrap(), 1);
    }

    // Trust: the drain is causally invoked only after a real guarded write
    // encounters WouldBlock. No parent/child scheduling race or FIFO page-size
    // assumption can let a lost guard return pass this inventory check.
    #[test]
    fn explicit_fifo_guard_return_waits_without_losing_a_byte() {
        use std::io::Read;
        use std::os::unix::fs::OpenOptionsExt;

        let world = tempfile::tempdir().unwrap();
        let path = world.path().join("tokens");
        nix::unistd::mkfifo(
            &path,
            nix::sys::stat::Mode::S_IRUSR | nix::sys::stat::Mode::S_IWUSR,
        )
        .unwrap();
        let client = Client::from_fifo(&path).unwrap();
        let mut access = std::fs::OpenOptions::new()
            .read(true)
            .write(true)
            .custom_flags(libc::O_NONBLOCK)
            .open(&path)
            .unwrap();
        let fill = |access: &mut File| {
            let mut written = 0;
            for block in [&[b'+'; 4096][..], &[b'+'][..]] {
                loop {
                    match access.write(block) {
                        Ok(0) => panic!("FIFO fill wrote no bytes"),
                        Ok(count) => written += count,
                        Err(error) if error.kind() == std::io::ErrorKind::Interrupted => {}
                        Err(error) if error.kind() == std::io::ErrorKind::WouldBlock => break,
                        Err(error) => panic!("FIFO fill: {error}"),
                    }
                }
            }
            written
        };
        let initial = fill(&mut access);
        assert!(initial > 0);
        let guard = client.acquire().unwrap();
        // Darwin may free a writable byte immediately; other kernels may not
        // free a buffer slot yet. Restore actual pressure in either case.
        let additional = fill(&mut access);
        assert_eq!(
            client
                .inner
                .release_with_wait(None, || panic!("raw issuance waited"))
                .unwrap_err()
                .kind(),
            std::io::ErrorKind::WouldBlock
        );
        let mut drained = 0;
        let mut waits = 0;
        client
            .inner
            .release_with_wait(Some(&guard.data), || {
                waits += 1;
                let count = access.read(&mut [0; 4096])?;
                assert!(count > 0, "full FIFO produced no bytes");
                drained += count;
                Ok(())
            })
            .unwrap();
        guard.drop_without_releasing();
        assert!(waits > 0, "guard return never exercised WouldBlock");
        let mut remaining = 0;
        loop {
            match access.read(&mut [0; 4096]) {
                Ok(0) => panic!("FIFO unexpectedly closed"),
                Ok(count) => remaining += count,
                Err(error) if error.kind() == std::io::ErrorKind::Interrupted => {}
                Err(error) if error.kind() == std::io::ErrorKind::WouldBlock => break,
                Err(error) => panic!("FIFO drain: {error}"),
            }
        }
        assert_eq!(
            drained + remaining,
            initial + additional,
            "guard return lost or duplicated a byte"
        );
    }
}
