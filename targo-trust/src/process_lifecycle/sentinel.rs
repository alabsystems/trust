//! The stop sentinel: what stops targo-trust's children when targo-trust
//! itself dies, SIGKILL included.
//!
//! macOS has no `PR_SET_PDEATHSIG`, and Linux's reaches only a DIRECT child
//! (the Cargo driver), never the compilers under it, so neither platform can
//! make a child stop by itself when targo-trust dies. Instead:
//!
//! * `main` creates a socket pair before any other thread exists, both ends
//!   close-on-exec ([`install`]). targo-trust keeps one end for its whole life.
//! * With the first child it owns, targo-trust starts the SENTINEL: this same
//!   executable, re-run as `targo-trust __targo_stop_sentinel`, with the other
//!   end as its standard input, in a process group of its own (so the
//!   terminal's Ctrl-C does not reach it), with no other descriptor of
//!   targo-trust's: its stdout is `/dev/null`, its stderr is targo-trust's
//!   only when that is a terminal, and every other descriptor is marked
//!   close-on-exec before it runs (`hold_only_stdio`), so it never holds a
//!   pipe a caller is waiting to see closed.
//! * targo-trust writes one line per change: `+<pid> <start>` when it owns a
//!   child, `-<pid>` when it lets go ([`note_owned`], [`note_released`]).
//! * The sentinel reads those lines until end-of-file. The kernel closes
//!   targo-trust's end however targo-trust ends, so end-of-file arrives on a
//!   clean exit, an exit from another thread, a crash and SIGKILL alike. Then
//!   the sentinel stops every child still listed, through the one stop path,
//!   with cause `StopCause::OwnerEnded`, pinned by the start each line
//!   carried so a recycled pid is never signalled, and exits.
//!
//! The sentinel ignores SIGINT, SIGTERM and SIGHUP: it cannot outlive
//! targo-trust by more than one stop, and a signal aimed at "everything named
//! targo-trust" must not take it before it has done that. SIGKILL still ends
//! it, and then targo-trust's children are covered only by its own stop
//! paths, as they were before the sentinel existed.
//!
//! What it does not cover, stated where the guarantee is made: a child
//! spawned in the instant before its `+` line is written; lines that could
//! not be written because the sentinel had not read 1 MiB of earlier ones (a
//! one-time note says so); a child that left its own tree and group (a
//! double fork onto init), which no pid walk can find; and targets other than
//! macOS and Linux, where no start can be read and nothing is listed.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

/// The private subcommand `main` dispatches before anything else.
pub(crate) const SUBCOMMAND: &str = "__targo_stop_sentinel";

#[cfg(any(target_os = "macos", target_os = "linux"))]
pub(crate) use imp::{install, note_owned, note_released, run, sentinel_pid};

#[cfg(not(any(target_os = "macos", target_os = "linux")))]
mod inert {
    pub(crate) fn install() {}
    pub(crate) fn note_owned(_pid: u32, _start: Option<u64>) {}
    pub(crate) fn note_released(_pid: u32) {}
    pub(crate) fn sentinel_pid() -> Option<u32> {
        None
    }
    pub(crate) fn run() -> i32 {
        2
    }
}

#[cfg(not(any(target_os = "macos", target_os = "linux")))]
pub(crate) use inert::{install, note_owned, note_released, run, sentinel_pid};

#[cfg(any(target_os = "macos", target_os = "linux"))]
mod imp {
    use std::collections::BTreeMap;
    use std::io::{BufRead as _, Write as _};
    use std::os::fd::{AsRawFd as _, FromRawFd as _, OwnedFd};
    use std::process::{Command, Stdio};
    use std::sync::Mutex;

    use super::SUBCOMMAND;
    use crate::process_lifecycle::{
        Root, RootPin, STOP_GRACE, StopCause, configure_own_group, stop_roots_recorded,
    };

    /// Bytes of unsent lines targo-trust keeps while the sentinel is not
    /// reading (it may still be starting: a first exec can wait minutes behind
    /// the host's exec authorization on a loaded machine).
    const MAX_PENDING_BYTES: usize = 1 << 20;

    /// Children one sentinel tracks at most.
    const MAX_TRACKED: usize = 1 << 16;

    enum State {
        /// Installed; no child owned yet, so no sentinel started.
        Idle { sentinel_end: OwnedFd },
        /// The sentinel runs; lines go to `socket`.
        Running { pid: u32 },
        /// No sentinel: it could not start, or it is gone. Said once.
        Unavailable,
    }

    struct Lifeline {
        /// targo-trust's end. Never closed while the process lives.
        socket: OwnedFd,
        state: State,
        pending: Vec<u8>,
        noted_overflow: bool,
    }

    static LIFELINE: Mutex<Option<Lifeline>> = Mutex::new(None);

    /// Create the socket pair. Called once from `main` while the process has
    /// one thread, so no child can inherit an end before it is close-on-exec.
    pub(crate) fn install() {
        let Some((socket, sentinel_end)) = socket_pair() else {
            let _ = writeln!(
                std::io::stderr(),
                "targo trust: note: could not create the stop sentinel's socket ({}); this run's \
                 children are not stopped if targo-trust is killed",
                std::io::Error::last_os_error()
            );
            return;
        };
        if let Ok(mut lifeline) = LIFELINE.lock() {
            *lifeline = Some(Lifeline {
                socket,
                state: State::Idle { sentinel_end },
                pending: Vec::new(),
                noted_overflow: false,
            });
        }
    }

    /// targo-trust now owns `pid`, which started at `start`. Without a start
    /// the sentinel could not tell the child from a later process with its
    /// pid, so such a child is not listed.
    pub(crate) fn note_owned(pid: u32, start: Option<u64>) {
        if let Some(start) = start {
            send(format!("+{pid} {start}\n"), true);
        }
    }

    /// targo-trust has let go of `pid`.
    pub(crate) fn note_released(pid: u32) {
        send(format!("-{pid}\n"), false);
    }

    /// The sentinel's pid while it runs.
    pub(crate) fn sentinel_pid() -> Option<u32> {
        let lifeline = LIFELINE.lock().ok()?;
        match lifeline.as_ref()?.state {
            State::Running { pid } => Some(pid),
            _ => None,
        }
    }

    fn send(line: String, start_if_idle: bool) {
        let Ok(mut guard) = LIFELINE.lock() else { return };
        let Some(lifeline) = guard.as_mut() else { return };
        if matches!(lifeline.state, State::Idle { .. }) {
            if !start_if_idle {
                return;
            }
            start(lifeline);
        }
        if !matches!(lifeline.state, State::Running { .. }) {
            return;
        }
        if lifeline.pending.len() + line.len() > MAX_PENDING_BYTES {
            if !lifeline.noted_overflow {
                lifeline.noted_overflow = true;
                let _ = writeln!(
                    std::io::stderr(),
                    "targo trust: note: the stop sentinel has not read {MAX_PENDING_BYTES} bytes \
                     of records; children owned from now on are not stopped if targo-trust is \
                     killed"
                );
            }
            return;
        }
        lifeline.pending.extend_from_slice(line.as_bytes());
        flush(lifeline);
    }

    /// Write what the socket takes now; keep the rest for the next line.
    fn flush(lifeline: &mut Lifeline) {
        while !lifeline.pending.is_empty() {
            // SAFETY: `pending` is a live buffer of its own length.
            let sent = unsafe {
                libc::send(
                    lifeline.socket.as_raw_fd(),
                    lifeline.pending.as_ptr().cast(),
                    lifeline.pending.len(),
                    SEND_FLAGS,
                )
            };
            if sent > 0 {
                let sent = usize::try_from(sent).unwrap_or(0).min(lifeline.pending.len());
                lifeline.pending.drain(..sent);
                continue;
            }
            if sent == 0 {
                // Nothing taken and no error to read: try again with the next line.
                return;
            }
            let error = std::io::Error::last_os_error();
            match error.kind() {
                std::io::ErrorKind::Interrupted => continue,
                std::io::ErrorKind::WouldBlock => return,
                _ => {
                    lifeline.pending.clear();
                    lifeline.state = State::Unavailable;
                    let _ = writeln!(
                        std::io::stderr(),
                        "targo trust: note: the stop sentinel is gone ({error}); this run's \
                         children are not stopped if targo-trust is killed"
                    );
                    return;
                }
            }
        }
    }

    #[cfg(target_os = "linux")]
    const SEND_FLAGS: libc::c_int = libc::MSG_DONTWAIT | libc::MSG_NOSIGNAL;
    // macOS has no MSG_NOSIGNAL; the socket carries SO_NOSIGPIPE instead.
    #[cfg(target_os = "macos")]
    const SEND_FLAGS: libc::c_int = libc::MSG_DONTWAIT;

    /// Start the sentinel with the idle end as its standard input.
    fn start(lifeline: &mut Lifeline) {
        let State::Idle { sentinel_end } =
            std::mem::replace(&mut lifeline.state, State::Unavailable)
        else {
            return;
        };
        let started = (|| -> std::io::Result<std::process::Child> {
            let mut command = Command::new(sentinel_program()?);
            command
                .arg(SUBCOMMAND)
                .current_dir("/")
                .stdin(Stdio::from(sentinel_end))
                .stdout(Stdio::null())
                .stderr(if stderr_is_terminal() { Stdio::inherit() } else { Stdio::null() });
            configure_own_group(&mut command);
            hold_only_stdio(&mut command);
            command.spawn()
        })();
        match started {
            Ok(mut child) => {
                lifeline.state = State::Running { pid: child.id() };
                // Reap it when it exits (normally, after this process has), so
                // a sentinel that dies early does not linger as a zombie.
                let _ = std::thread::Builder::new()
                    .name("targo-trust-sentinel-reaper".to_string())
                    .spawn(move || {
                        let _ = child.wait();
                    });
            }
            Err(error) => {
                let _ = writeln!(
                    std::io::stderr(),
                    "targo trust: note: the stop sentinel could not start ({error}); this run's \
                     children are not stopped if targo-trust is killed"
                );
            }
        }
    }

    /// Fresh descriptors beyond the ones open when [`hold_only_stdio`] counts
    /// them that another thread could create before the fork (see there).
    const DESCRIPTOR_MARGIN: libc::c_int = 1024;

    /// The sentinel keeps only its stdio. It lives for the whole run, so a
    /// descriptor it inherits by accident stays open until targo-trust is
    /// gone: a probe's or a compile's pipe would then never reach end-of-file.
    /// Every descriptor targo-trust creates is close-on-exec, but on macOS a
    /// pipe becomes so only on a second call (`pipe`, then `fcntl`), and the
    /// toolchain that builds targo-trust predates the std change that gives a
    /// spawned child its stdio alone. So the sentinel marks every other
    /// descriptor close-on-exec between fork and exec, the way the lifecycle
    /// tests' fixtures do (`marking`, not closing: std reports a failed exec
    /// through a close-on-exec pipe of its own that must stay open).
    ///
    /// The range is bounded rather than the whole descriptor limit (a raised
    /// limit is 2^20 system calls in the forked child, every run): a new
    /// descriptor is always the lowest number free, so one created between the
    /// count here and the fork is below the number open now plus the number
    /// created since, and [`DESCRIPTOR_MARGIN`] is that "since", generously.
    /// Where the open descriptors cannot be listed in full, the whole limit is
    /// marked.
    fn hold_only_stdio(command: &mut Command) {
        use std::os::unix::process::CommandExt as _;
        let end = descriptor_scan_end();
        // SAFETY: the closure runs between fork and exec and calls only
        // `fcntl`, which is async-signal-safe; it allocates nothing.
        unsafe {
            command.pre_exec(move || {
                for fd in 3..end {
                    libc::fcntl(fd, libc::F_SETFD, libc::FD_CLOEXEC);
                }
                Ok(())
            });
        }
    }

    /// One past the highest descriptor the child could hold (see
    /// [`hold_only_stdio`]).
    fn descriptor_scan_end() -> libc::c_int {
        // SAFETY: a zeroed `rlimit` is a valid out-parameter.
        let mut limit: libc::rlimit = unsafe { std::mem::zeroed() };
        // SAFETY: `limit` is the one `rlimit` the call writes.
        let soft = if unsafe { libc::getrlimit(libc::RLIMIT_NOFILE, &raw mut limit) } == 0 {
            libc::c_int::try_from(limit.rlim_cur).unwrap_or(libc::c_int::MAX)
        } else {
            libc::c_int::MAX
        };
        match open_descriptors() {
            Some((count, highest)) => {
                highest.saturating_add(1).max(count.saturating_add(DESCRIPTOR_MARGIN).min(soft))
            }
            None => soft,
        }
    }

    /// How many descriptors are open, and the highest of them.
    #[cfg(target_os = "macos")]
    fn open_descriptors() -> Option<(libc::c_int, libc::c_int)> {
        let entry = std::mem::size_of::<libc::proc_fdinfo>();
        // SAFETY: `getpid` has no preconditions.
        let pid = unsafe { libc::getpid() };
        // SAFETY: a null buffer of size 0 asks only for the size the listing needs.
        let needed =
            unsafe { libc::proc_pidinfo(pid, libc::PROC_PIDLISTFDS, 0, std::ptr::null_mut(), 0) };
        let room = usize::try_from(needed).ok().filter(|&needed| needed > 0)? / entry + 64;
        let mut entries = vec![libc::proc_fdinfo { proc_fd: -1, proc_fdtype: 0 }; room];
        let bytes = libc::c_int::try_from(room * entry).ok()?;
        // SAFETY: `entries` is `bytes` long, which bounds what the call writes.
        let written = unsafe {
            libc::proc_pidinfo(pid, libc::PROC_PIDLISTFDS, 0, entries.as_mut_ptr().cast(), bytes)
        };
        let listed = usize::try_from(written).ok()? / entry;
        if listed >= room {
            // Possibly cut off at the buffer's end: not a full listing.
            return None;
        }
        let highest = entries[..listed].iter().map(|entry| entry.proc_fd).max()?;
        Some((libc::c_int::try_from(listed).ok()?, highest))
    }

    #[cfg(target_os = "linux")]
    fn open_descriptors() -> Option<(libc::c_int, libc::c_int)> {
        let mut count: libc::c_int = 0;
        let mut highest: libc::c_int = -1;
        for entry in std::fs::read_dir("/proc/self/fd").ok()?.flatten() {
            let fd = entry.file_name().to_str()?.parse::<libc::c_int>().ok()?;
            count = count.saturating_add(1);
            highest = highest.max(fd);
        }
        (highest >= 0).then_some((count, highest))
    }

    /// This executable. On Linux, `/proc/self/exe` runs the image this process
    /// runs even if its path was replaced or removed since.
    fn sentinel_program() -> std::io::Result<std::path::PathBuf> {
        #[cfg(target_os = "linux")]
        {
            Ok(std::path::PathBuf::from("/proc/self/exe"))
        }
        #[cfg(target_os = "macos")]
        {
            std::env::current_exe()
        }
    }

    fn stderr_is_terminal() -> bool {
        // SAFETY: `isatty` takes a descriptor number and reads nothing else.
        unsafe { libc::isatty(libc::STDERR_FILENO) == 1 }
    }

    /// A connected pair of stream sockets, both close-on-exec; targo-trust's
    /// end never raises SIGPIPE.
    fn socket_pair() -> Option<(OwnedFd, OwnedFd)> {
        let mut fds = [-1 as libc::c_int; 2];
        #[cfg(target_os = "linux")]
        let kind = libc::SOCK_STREAM | libc::SOCK_CLOEXEC;
        #[cfg(target_os = "macos")]
        let kind = libc::SOCK_STREAM;
        // SAFETY: `fds` is the two-element array `socketpair` writes.
        if unsafe { libc::socketpair(libc::AF_UNIX, kind, 0, fds.as_mut_ptr()) } != 0 {
            return None;
        }
        // SAFETY: both descriptors were just created and are owned here once.
        let (ours, theirs) =
            unsafe { (OwnedFd::from_raw_fd(fds[0]), OwnedFd::from_raw_fd(fds[1])) };
        #[cfg(target_os = "macos")]
        {
            for fd in [ours.as_raw_fd(), theirs.as_raw_fd()] {
                // SAFETY: `fd` is open and owned above. Not atomic with the
                // `socketpair`, which is why this runs single-threaded.
                if unsafe { libc::fcntl(fd, libc::F_SETFD, libc::FD_CLOEXEC) } != 0 {
                    return None;
                }
            }
            let on: libc::c_int = 1;
            // SAFETY: SO_NOSIGPIPE takes one `c_int`, passed by pointer and size.
            let set = unsafe {
                libc::setsockopt(
                    ours.as_raw_fd(),
                    libc::SOL_SOCKET,
                    libc::SO_NOSIGPIPE,
                    (&raw const on).cast(),
                    libc::socklen_t::try_from(std::mem::size_of::<libc::c_int>()).ok()?,
                )
            };
            if set != 0 {
                return None;
            }
        }
        Some((ours, theirs))
    }

    /// The sentinel's own body (`targo-trust __targo_stop_sentinel`): its exit
    /// status.
    pub(crate) fn run() -> i32 {
        for signal in [libc::SIGINT, libc::SIGTERM, libc::SIGHUP] {
            // SAFETY: SIG_IGN is a valid disposition for these signals.
            unsafe {
                libc::signal(signal, libc::SIG_IGN);
            }
        }
        // SAFETY: `getppid` has no preconditions.
        let owner = unsafe { libc::getppid() };
        let mut owned: BTreeMap<u32, u64> = BTreeMap::new();
        let stdin = std::io::stdin();
        let mut lines = stdin.lock();
        let mut line = Vec::new();
        loop {
            line.clear();
            match lines.read_until(b'\n', &mut line) {
                Ok(0) | Err(_) => break,
                Ok(_) => apply(&mut owned, &line),
            }
        }
        let roots: Vec<Root> =
            owned.iter().map(|(&pid, &start)| Root { pid, pin: RootPin::Started(start) }).collect();
        let (_, outcome) =
            stop_roots_recorded(&roots, StopCause::OwnerEnded, STOP_GRACE, &mut || false);
        if outcome.terminated > 0 {
            let mut text = format!(
                "targo trust: targo-trust (pid {owner}) ended while it owned running children; \
                 the stop sentinel sent SIGTERM to {} process(es)",
                outcome.terminated
            );
            if let Some(words) = outcome.kill_words(None) {
                text.push_str(" and ");
                text.push_str(&words);
            }
            let _ = writeln!(std::io::stderr(), "{text} (stop cause: owner-ended)");
        }
        0
    }

    /// Apply one `+<pid> <start>` or `-<pid>` line; anything else is ignored.
    fn apply(owned: &mut BTreeMap<u32, u64>, line: &[u8]) {
        let Ok(line) = std::str::from_utf8(line) else { return };
        let line = line.trim_end();
        if let Some(rest) = line.strip_prefix('+') {
            let mut fields = rest.split(' ');
            let (Some(pid), Some(start), None) = (fields.next(), fields.next(), fields.next())
            else {
                return;
            };
            if let (Ok(pid), Ok(start)) = (pid.parse::<u32>(), start.parse::<u64>()) {
                if pid > 0 && (owned.len() < MAX_TRACKED || owned.contains_key(&pid)) {
                    owned.insert(pid, start);
                }
            }
        } else if let Some(pid) = line.strip_prefix('-').and_then(|pid| pid.parse::<u32>().ok()) {
            owned.remove(&pid);
        }
    }

    #[cfg(test)]
    pub(crate) fn apply_for_test(owned: &mut BTreeMap<u32, u64>, line: &[u8]) {
        apply(owned, line);
    }

    #[cfg(test)]
    pub(crate) fn hold_only_stdio_for_test(command: &mut Command) {
        hold_only_stdio(command);
    }
}

#[cfg(all(test, any(target_os = "macos", target_os = "linux")))]
pub(crate) use imp::{apply_for_test, hold_only_stdio_for_test};
