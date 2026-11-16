//! SIGINT, SIGTERM and SIGHUP to targo-trust, and the end of the process that
//! started it.
//!
//! A handler that only writes the signal's number into a pipe (the one
//! async-signal-safe thing it does) wakes a STOPPER thread, which does the rest
//! outside signal context:
//!
//! 1. it records the cause, so the run's remaining paths stop publishing
//!    ([`hold_if_interrupted`]: every owned child's release, the compiler
//!    guard's `finish`, a bounded probe and `main`'s exit hold the thread that
//!    reaches them) and a child spawned from now on is stopped as soon as it is
//!    owned (`Ownership::of`);
//! 2. it stops every owned child through the one stop path (SIGTERM, then
//!    SIGKILL after `STOP_GRACE`); a second signal during the grace sends
//!    SIGKILL at once ([`escalated`], which every other stop in flight reads
//!    too), and puts the default dispositions back so a third one ends
//!    targo-trust outright (the sentinel then stops whatever is left);
//! 3. it prints `COULD NOT RUN` with the cause and what was stopped, and exits
//!    3 (`determinism_report::EXIT_COULD_NOT_RUN`): an interrupted run is no
//!    measurement, so it is no verdict either way (T7b).
//!
//! The stopper writes its lines through a thread of its own and never waits on
//! stderr before it stops anything: a stderr that does not drain (a pipe
//! nobody reads, a terminal held by XOFF, another thread blocked writing to
//! either while it holds std's stderr lock) can lose a line, never the stop or
//! the exit. A panic in the stopper exits 3 too, so the held threads never
//! hang the process.
//!
//! A run that has CONCLUDED -- `main`'s worker returned its exit code -- keeps
//! that code: a signal after that point stops nothing and changes nothing (a
//! refutation printed and returned stays exit 1, T7b). One atomic decides
//! which came first.
//!
//! A signal whose disposition was IGNORED when targo-trust started stays
//! ignored (a `nohup`, a shell's background job): the caller asked for that.
//!
//! The same thread watches targo-trust's parent. `targo trust` runs
//! targo-trust as a child of the `targo` executable, so a SIGTERM or SIGKILL
//! aimed at `targo` never reaches targo-trust; when the parent is gone
//! (`getppid` changed), the run stops exactly as for a signal, with cause
//! `StopCause::ParentEnded`. Like SIGHUP, it is not watched when SIGHUP was
//! ignored at start: a `nohup`ed run is meant to outlive its starter.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use std::process::ExitCode;
use std::sync::atomic::{AtomicBool, AtomicI32, Ordering};

use super::StopCause;

/// Where the run is: [`RUNNING`]; a positive signal number or [`PARENT_ENDED`]
/// once a stop has begun; or [`CONCLUDED`] once `main`'s worker returned. It
/// leaves [`RUNNING`] once, by compare-and-swap, so a stop and a conclusion
/// that race have one winner.
static STOPPING: AtomicI32 = AtomicI32::new(RUNNING);
const RUNNING: i32 = 0;
const PARENT_ENDED: i32 = -1;
const CONCLUDED: i32 = i32::MIN;

/// A second signal arrived during the stop's grace.
static ESCALATED: AtomicBool = AtomicBool::new(false);

/// The run's stop cause, once a signal (or the parent's end) has begun it.
pub(crate) fn interrupted() -> Option<StopCause> {
    match STOPPING.load(Ordering::Acquire) {
        RUNNING | CONCLUDED => None,
        PARENT_ENDED => Some(StopCause::ParentEnded),
        signal => Some(StopCause::Signal(signal)),
    }
}

/// A second signal has cut the stop's grace short: any stop in flight on any
/// thread sends SIGKILL now. The escalation poll of every in-process stop.
pub(crate) fn escalated() -> bool {
    ESCALATED.load(Ordering::Acquire)
}

/// Never return while the run is being stopped: the stopper thread owns the
/// exit (3), and nothing this thread would do next -- print a probe's failure,
/// publish a report of a compile it stopped -- is true of a run that was
/// interrupted. Returns at once otherwise.
pub(crate) fn hold_if_interrupted() {
    #[cfg(test)]
    if HOLD_PANICS_HERE.with(std::cell::Cell::get) {
        panic!("{HELD}");
    }
    if interrupted().is_some() {
        hold_forever();
    }
}

#[cfg(test)]
thread_local! {
    static HOLD_PANICS_HERE: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

/// What [`hold_if_interrupted`] panics with on a thread that [`hold_panics_here`]
/// marked.
#[cfg(test)]
pub(crate) const HELD: &str = "held: the run's stop has begun";

/// Test seam: on this thread only, [`hold_if_interrupted`] panics with [`HELD`]
/// as though a stop had begun, so a unit test can see a path reach the hold
/// without starting a stop in the shared test process or parking a thread.
#[cfg(test)]
pub(crate) fn hold_panics_here(on: bool) {
    HOLD_PANICS_HERE.with(|cell| cell.set(on));
}

fn hold_forever() -> ! {
    loop {
        std::thread::park();
    }
}

/// `main`'s exit: the worker's code, which then stands whatever arrives
/// later, unless a stop began first, in which case this thread holds and the
/// stopper's exit (3) is the one the process takes.
pub(crate) fn finish(code: ExitCode) -> ExitCode {
    match STOPPING.compare_exchange(RUNNING, CONCLUDED, Ordering::AcqRel, Ordering::Acquire) {
        Ok(_) => code,
        Err(_) => hold_forever(),
    }
}

/// `SIGINT` / `SIGTERM` / `SIGHUP` by name, for records and messages.
pub(crate) fn signal_name(signal: i32) -> String {
    #[cfg(unix)]
    {
        match signal {
            libc::SIGINT => return "SIGINT".to_string(),
            libc::SIGTERM => return "SIGTERM".to_string(),
            libc::SIGHUP => return "SIGHUP".to_string(),
            _ => {}
        }
    }
    format!("signal {signal}")
}

#[cfg(any(target_os = "macos", target_os = "linux"))]
pub(crate) use imp::install;

#[cfg(not(any(target_os = "macos", target_os = "linux")))]
pub(crate) fn install() {}

#[cfg(any(target_os = "macos", target_os = "linux"))]
mod imp {
    use std::io::Write as _;
    use std::os::fd::{AsRawFd as _, FromRawFd as _, IntoRawFd as _, OwnedFd};
    use std::sync::atomic::{AtomicI32, Ordering};
    use std::sync::mpsc;
    use std::time::Duration;

    use super::{ESCALATED, PARENT_ENDED, RUNNING, STOPPING, signal_name};
    use crate::process_lifecycle::{STOP_GRACE, StopCause, StopOutcome, owned_count, stop_owned};

    /// The signals that stop a run.
    const STOP_SIGNALS: [libc::c_int; 3] = [libc::SIGINT, libc::SIGTERM, libc::SIGHUP];

    /// How often the stopper re-reads `getppid` while no signal arrives.
    const PARENT_POLL: Duration = Duration::from_millis(250);

    /// How long the stopper waits for its last line to reach stderr before it
    /// exits without it. A stderr that drains takes microseconds; one that has
    /// not taken a few hundred bytes in this long is one nobody is reading, and
    /// the exit (3) is what a caller reads anyway. The length of the grace, so
    /// the slowest stop is at most twice it.
    const LAST_LINE_PATIENCE: Duration = STOP_GRACE;

    /// The handler's end of the self-pipe; -1 until installed.
    static SIGNAL_PIPE: AtomicI32 = AtomicI32::new(-1);

    extern "C" fn on_stop_signal(signal: libc::c_int) {
        let fd = SIGNAL_PIPE.load(Ordering::Relaxed);
        if fd < 0 {
            return;
        }
        // SAFETY: `errno_location` names this thread's errno, which `write`
        // may change; it is put back so the interrupted code never sees it.
        let saved = unsafe { *errno_location() };
        let byte = u8::try_from(signal).unwrap_or(u8::MAX);
        // SAFETY: `write` is async-signal-safe; one byte from a local. A full
        // pipe drops the byte, which loses nothing: a stop is already pending.
        let _ = unsafe { libc::write(fd, (&raw const byte).cast(), 1) };
        // SAFETY: as above.
        unsafe { *errno_location() = saved };
    }

    #[cfg(target_os = "macos")]
    unsafe fn errno_location() -> *mut libc::c_int {
        // SAFETY: returns this thread's errno slot; no preconditions.
        unsafe { libc::__error() }
    }

    #[cfg(target_os = "linux")]
    unsafe fn errno_location() -> *mut libc::c_int {
        // SAFETY: returns this thread's errno slot; no preconditions.
        unsafe { libc::__errno_location() }
    }

    /// Install the handlers and start the stopper. Called once from `main`
    /// while the process has one thread ([`crate::process_lifecycle::start`]).
    pub(crate) fn install() {
        let Some((read, write)) = self_pipe() else {
            let _ = writeln!(
                std::io::stderr(),
                "targo trust: note: could not create the signal pipe ({}); SIGINT, SIGTERM and \
                 SIGHUP keep their default actions, and only the stop sentinel stops this run's \
                 children if one ends it",
                std::io::Error::last_os_error()
            );
            return;
        };
        let watched: Vec<libc::c_int> =
            STOP_SIGNALS.into_iter().filter(|&signal| !inherited_ignore(signal)).collect();
        // A run started with SIGHUP ignored is meant to outlive whoever started
        // it, so its parent's end does not stop it either.
        let watch_parent = watched.contains(&libc::SIGHUP);
        // SAFETY: `getppid` has no preconditions.
        let parent = unsafe { libc::getppid() };
        let spawned = std::thread::Builder::new()
            .name("targo-trust-stop".to_string())
            .spawn(move || stopper(read, watch_parent.then_some(parent)));
        if spawned.is_err() {
            // No stopper, no handlers: a handler with nobody reading its pipe
            // would turn every signal into a no-op.
            return;
        }
        SIGNAL_PIPE.store(write.into_raw_fd(), Ordering::Release);
        for signal in watched {
            install_handler(signal);
        }
    }

    /// The signal's disposition was SIG_IGN when this process started.
    fn inherited_ignore(signal: libc::c_int) -> bool {
        // SAFETY: a zeroed `sigaction` is a valid out-parameter; a null new
        // action only reads the current one.
        let mut current: libc::sigaction = unsafe { std::mem::zeroed() };
        let read = unsafe { libc::sigaction(signal, std::ptr::null(), &raw mut current) };
        read == 0 && current.sa_sigaction == libc::SIG_IGN
    }

    fn install_handler(signal: libc::c_int) {
        // SAFETY: a zeroed `sigaction` with an empty mask is valid; the
        // handler is an `extern "C" fn(c_int)`, the form `sa_sigaction` takes
        // without SA_SIGINFO. SA_RESTART keeps every other thread's blocking
        // call from failing with EINTR.
        unsafe {
            let mut action: libc::sigaction = std::mem::zeroed();
            action.sa_sigaction = on_stop_signal as extern "C" fn(libc::c_int) as usize;
            libc::sigemptyset(&raw mut action.sa_mask);
            action.sa_flags = libc::SA_RESTART;
            libc::sigaction(signal, &raw const action, std::ptr::null_mut());
        }
    }

    /// Put the default actions back (after a second signal), so a third ends
    /// the process outright.
    fn restore_default_actions() {
        for signal in STOP_SIGNALS {
            if inherited_ignore(signal) {
                continue;
            }
            // SAFETY: SIG_DFL is always a valid disposition for these signals.
            unsafe {
                libc::signal(signal, libc::SIG_DFL);
            }
        }
    }

    /// A pipe whose two ends are close-on-exec and non-blocking.
    fn self_pipe() -> Option<(OwnedFd, OwnedFd)> {
        let mut fds = [-1 as libc::c_int; 2];
        #[cfg(target_os = "linux")]
        // SAFETY: `fds` is the two-element array `pipe2` writes.
        let created = unsafe { libc::pipe2(fds.as_mut_ptr(), libc::O_CLOEXEC | libc::O_NONBLOCK) };
        #[cfg(target_os = "macos")]
        // SAFETY: as above. Not atomic with the flags below, which is why this
        // runs while the process has one thread.
        let created = unsafe { libc::pipe(fds.as_mut_ptr()) };
        if created != 0 {
            return None;
        }
        // SAFETY: both descriptors were just created and are owned here once.
        let (read, write) = unsafe { (OwnedFd::from_raw_fd(fds[0]), OwnedFd::from_raw_fd(fds[1])) };
        #[cfg(target_os = "macos")]
        for fd in [read.as_raw_fd(), write.as_raw_fd()] {
            // SAFETY: `fd` is open and owned above.
            unsafe {
                if libc::fcntl(fd, libc::F_SETFD, libc::FD_CLOEXEC) != 0 {
                    return None;
                }
                let flags = libc::fcntl(fd, libc::F_GETFL);
                if flags < 0 || libc::fcntl(fd, libc::F_SETFL, flags | libc::O_NONBLOCK) != 0 {
                    return None;
                }
            }
        }
        Some((read, write))
    }

    /// Wait up to `timeout` (forever when `None`) for a signal's byte.
    fn next_signal(read: &OwnedFd, timeout: Option<Duration>) -> Option<i32> {
        let timeout_ms = timeout
            .map(|timeout| libc::c_int::try_from(timeout.as_millis()).unwrap_or(libc::c_int::MAX))
            .unwrap_or(-1);
        let mut poll = libc::pollfd { fd: read.as_raw_fd(), events: libc::POLLIN, revents: 0 };
        loop {
            // SAFETY: one valid `pollfd`.
            let ready = unsafe { libc::poll(&raw mut poll, 1, timeout_ms) };
            if ready < 0
                && std::io::Error::last_os_error().kind() == std::io::ErrorKind::Interrupted
            {
                continue;
            }
            if ready <= 0 {
                return None;
            }
            let mut byte = 0_u8;
            // SAFETY: reads at most one byte into a local.
            let read = unsafe { libc::read(read.as_raw_fd(), (&raw mut byte).cast(), 1) };
            return (read == 1).then_some(i32::from(byte));
        }
    }

    /// Exits 3 if the stopper unwinds: once a stop has begun every other
    /// thread holds, so a panic here must not leave the process hanging. The
    /// sentinel stops whatever the interrupted stop left.
    struct ExitOnUnwind;

    impl Drop for ExitOnUnwind {
        fn drop(&mut self) {
            std::process::exit(i32::from(crate::determinism_report::EXIT_COULD_NOT_RUN));
        }
    }

    /// The stopper's lines, written by a thread of their own so that no write
    /// to stderr can hold up the stop or the exit (module docs).
    struct Notes {
        lines: Option<mpsc::Sender<(String, mpsc::SyncSender<()>)>>,
    }

    impl Notes {
        fn start() -> Self {
            let (lines, queued) = mpsc::channel::<(String, mpsc::SyncSender<()>)>();
            let writer = std::thread::Builder::new()
                .name("targo-trust-stop-notes".to_string())
                .spawn(move || {
                    for (line, written) in queued {
                        let _ = std::io::stderr().write_all(line.as_bytes());
                        let _ = written.try_send(());
                    }
                });
            Notes { lines: writer.is_ok().then_some(lines) }
        }

        /// Queue `line` and wait up to `patience` for it to be written. With
        /// no writer thread (it could not start) the line is written here.
        fn say(&self, line: String, patience: Duration) {
            let Some(lines) = &self.lines else {
                let _ = std::io::stderr().write_all(line.as_bytes());
                return;
            };
            let (written, done) = mpsc::sync_channel(1);
            if lines.send((line, written)).is_ok() && !patience.is_zero() {
                let _ = done.recv_timeout(patience);
            }
        }
    }

    /// The stopper thread: wait for the first stop cause, then stop the run.
    fn stopper(read: OwnedFd, parent: Option<libc::pid_t>) {
        let exit_on_unwind = ExitOnUnwind;
        let cause = loop {
            let poll = parent.map(|_| PARENT_POLL);
            if let Some(signal) = next_signal(&read, poll) {
                break StopCause::Signal(signal);
            }
            if let Some(parent) = parent {
                // SAFETY: `getppid` has no preconditions.
                if unsafe { libc::getppid() } != parent {
                    break StopCause::ParentEnded;
                }
            }
        };
        let code = match cause {
            StopCause::Signal(signal) => signal,
            _ => PARENT_ENDED,
        };
        if STOPPING.compare_exchange(RUNNING, code, Ordering::AcqRel, Ordering::Acquire).is_err() {
            // The run concluded first: its exit stands, and `main` is taking
            // it. Later signals act as they would without this module.
            restore_default_actions();
            std::mem::forget(exit_on_unwind);
            return;
        }
        let why = match cause {
            StopCause::Signal(signal) => format!("interrupted by {}", signal_name(signal)),
            _ => format!(
                "the process that started targo-trust (pid {}) ended",
                parent.unwrap_or_default()
            ),
        };
        let notes = Notes::start();
        let owned = owned_count();
        if owned > 0 {
            notes.say(
                format!(
                    "targo trust: {why}: stopping {owned} child process tree(s) (SIGTERM now; \
                     SIGKILL after {}s, or at once on a second signal)\n",
                    STOP_GRACE.as_secs()
                ),
                Duration::ZERO,
            );
        }
        let mut second = None;
        let (trees, outcome) = stop_owned(cause, &mut || {
            if second.is_none() {
                second = next_signal(&read, Some(Duration::ZERO));
                if second.is_some() {
                    ESCALATED.store(true, Ordering::Release);
                }
            }
            second.is_some()
        });
        if second.is_some() {
            restore_default_actions();
        }
        notes.say(
            format!(
                "targo trust: COULD NOT RUN: {why}; {}. The run is no measurement, so it has no \
                 verdict (stop cause: {})\n",
                describe(trees, outcome, second),
                cause.label(),
            ),
            LAST_LINE_PATIENCE,
        );
        std::process::exit(i32::from(crate::determinism_report::EXIT_COULD_NOT_RUN));
    }

    /// What the stop did, in words.
    fn describe(trees: usize, outcome: StopOutcome, second: Option<i32>) -> String {
        if trees == 0 {
            // Not "no child": the per-user trustd, which a run may have
            // started and which outlives it by design, is never owned.
            return "no owned child process was running".to_string();
        }
        let mut text = format!(
            "stopped {trees} child process tree(s): SIGTERM to {} process(es)",
            outcome.terminated
        );
        // What the stop did decides the words, not merely that a second
        // signal was read (`StopOutcome::kill_words`), and the time is the
        // one measured, not the grace's length.
        if let Some(words) = outcome.kill_words(second) {
            text.push_str(", then ");
            text.push_str(&words);
        }
        text
    }

    #[cfg(test)]
    pub(crate) fn describe_for_test(
        trees: usize,
        outcome: StopOutcome,
        second: Option<i32>,
    ) -> String {
        describe(trees, outcome, second)
    }
}

#[cfg(all(test, any(target_os = "macos", target_os = "linux")))]
pub(crate) use imp::describe_for_test;
