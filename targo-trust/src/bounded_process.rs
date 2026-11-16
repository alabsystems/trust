//! Bounded subprocess capture for identity and metadata probes.

use std::fs::File;
use std::io::{self, Read};
use std::process::{Child, Command, Output, Stdio};
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::mpsc::{self, Receiver, RecvTimeoutError};
use std::thread;
use std::time::{Duration, Instant};

use crate::process_lifecycle::{self, StopCause, tree};

#[cfg(all(test, unix))]
mod conversation_tests;

/// How long after the leader exits a stream may stay open before the kernel
/// is asked who holds it. Past it, a stream a descendant of the probe holds
/// (in the probe's reach, or escaped from it) fails the probe at once rather
/// than spending its whole timeout on it. A stream only this program holds,
/// or nobody (its reader has yet to run), is waited for until the probe's
/// deadline ([`output_with_exact_deadline`]).
const POST_EXIT_PIPE_CLOSE_GRACE: Duration = Duration::from_millis(250);

/// How often, past [`POST_EXIT_PIPE_CLOSE_GRACE`], the wait for a stream that
/// is still open asks the kernel again who holds it.
const POST_EXIT_HOLDER_POLL: Duration = Duration::from_millis(20);

/// Multiplier applied to every probe deadline when this crate is compiled as a
/// test harness. See [`resolve_probe_deadline`] for why it exists and why it
/// cannot change what a released binary does.
///
/// Sized from measurement, not taste. On a developer host running several Rust
/// builds at once, 18 concurrently launched first-execs of a freshly written
/// `#!/bin/sh` script whose whole body is one `echo` took 272.9s–275.4s and were
/// released together within 2.5s of each other — a machine-wide barrier of
/// ~275s, not a per-process cost. This multiplier puts a 10s production probe at
/// 30 minutes in-harness, roughly 6.5x that measured barrier, and the 5s daemon
/// readiness waits at 15 minutes.
///
/// A multiplier is used rather than a flat generous floor so that a test may
/// still choose a deliberately tiny fixture deadline, traverse the real
/// resolution path, and prove a non-terminating child is failed closed in
/// fractions of a second. Under a floor, every such proof would cost the floor.
const TEST_HARNESS_DEADLINE_SCALE: u32 = 180;

/// Resolve a production probe deadline for the way this crate was compiled.
///
/// A probe deadline exists to catch a **hung** tool: one that will never make
/// progress, whatever the machine does. In a production `targo-trust` run a
/// probe is essentially alone on the box, so a 10s wall-clock bound measures
/// exactly that question, and every call site's constant is the answer it wants.
///
/// Under `cargo test` the identical bound measures something else entirely.
/// libtest runs the whole suite inside one process on a thread pool, and dozens
/// of these tests each write a *fresh* fixture executable into a temporary
/// directory and run it exactly once. That is structurally the opposite of
/// production, where the same stage2 binaries are re-executed and the host
/// authorizes their image once. Here the dominant cost of a probe is not the
/// fixture's own work, and not CPU or memory — 94% of memory was free while
/// this was failing — it is the operating system admitting a brand-new process
/// image. Fixtures sampled mid-suite were parked at `_dyld_start + 0` for
/// minutes at a time: the kernel had not yet let the dynamic loader run its
/// first instruction of a script whose entire body is one `echo`. The queue is
/// machine-global and shared with every other build on the box, and it drains as
/// a barrier rather than per process. So a fixed wall-clock bound in the harness
/// stops asking "is this tool hung?" and starts asking "how deep is the host's
/// exec-authorization queue right now?" — a question no probe should fail on.
///
/// The bound is therefore *stretched* under the test harness, never removed and
/// never conditioned on the observed result. A hung tool makes no progress ever,
/// so a stretched bound still catches it and the test merely takes longer to
/// fail; `trust_added::trustc_native::tests::capture_enforces_timeout_and_output_bound`
/// proves exactly that on the production capture path, with a child that never
/// terminates. A merely slow start now lands inside the bound and the probe goes
/// on to report what it actually observed.
///
/// Bounding output *progress* instead of elapsed time was considered and does
/// not work here: a process stalled before `_dyld_start` has produced no output
/// and cannot, so "no progress yet" and "hung" are indistinguishable in the one
/// window that matters. Bounding the harness's own probe concurrency does not
/// work either: the authorization queue is filled by every process on the
/// machine, not just this suite's.
///
/// The switch is `cfg(test)` — a property of how the crate was compiled, not of
/// the environment it is run in. A released `targo-trust` is not built with
/// `--test`, so this is the identity function there and the production guard is
/// exactly the one its call site wrote. An environment variable was rejected for
/// precisely that reason: it would let anything outside the binary lengthen a
/// production guard, which is the one thing this must never permit.
///
/// Production is not always the re-exec case either. The release identity
/// probes bind tools a build or an install has just written, so their first
/// exec is the one the queue holds, in a released binary too; their call
/// sites pass `release_cli::identity::TOOL_IDENTITY_PROBE_HANG_GUARD`, a
/// production bound already sized as a hang detector over that queue. The
/// stage2 identity probes pass it too, for the same reason: they bind the
/// stage2 files a build has just written (the self-verify harness's, check-all's
/// `trustc`/`targo`, the cargo-cache materializer's required tools, and release
/// upstream porting's `trustc -Vv`).
pub(crate) fn resolve_probe_deadline(production: Duration) -> Duration {
    stretched_probe_deadline(production, cfg!(test))
}

fn stretched_probe_deadline(production: Duration, under_test_harness: bool) -> Duration {
    if under_test_harness {
        production.saturating_mul(TEST_HARNESS_DEADLINE_SCALE)
    } else {
        production
    }
}

/// Capture a bounded subprocess under the caller's production probe deadline.
///
/// This is the single choke point every probe deadline in the crate flows
/// through — constants, inline literals, and caller-supplied values alike — so
/// resolving the deadline here cannot miss a probe site.
pub(crate) fn output(
    command: &mut Command,
    context: &str,
    max_stream_bytes: usize,
    timeout: Duration,
) -> Result<Output, String> {
    output_with_exact_deadline(command, context, max_stream_bytes, resolve_probe_deadline(timeout))
}

/// Capture with a caller-owned file as stdin, retaining the same probe bounds.
/// A file avoids pipe writes and their process-wide SIGPIPE behavior.
pub(crate) fn output_with_input_file(
    command: &mut Command,
    input: File,
    context: &str,
    max_stream_bytes: usize,
    timeout: Duration,
) -> Result<Output, String> {
    capture_with_input(
        command,
        Stdio::from(input),
        context,
        max_stream_bytes,
        resolve_probe_deadline(timeout),
    )
}

/// Capture a bounded subprocess under exactly the supplied deadline.
///
/// Two callers legitimately want the deadline stated rather than resolved:
///
/// * a deadline the **caller supplied at runtime** — a declared budget such as
///   `targo-trust verify-self --timeout-sec N` is data, and multiplying data by
///   a build-mode constant would silently answer a different question than the
///   caller asked. The harness stretch is for probe constants this code chose,
///   which have no declared value to distort;
/// * a test that **pins the deadline machinery itself** and wants a tiny bound
///   so it stays fast and precise, rather than having its own fixture deadline
///   stretched out from under it.
///
/// Every fixed probe constant must go through [`output`] instead.
pub(crate) fn output_with_exact_deadline(
    command: &mut Command,
    context: &str,
    max_stream_bytes: usize,
    timeout: Duration,
) -> Result<Output, String> {
    capture_with_input(command, Stdio::null(), context, max_stream_bytes, timeout)
}

fn capture_with_input(
    command: &mut Command,
    input: Stdio,
    context: &str,
    max_stream_bytes: usize,
    timeout: Duration,
) -> Result<Output, String> {
    capture_with_input_checked(
        command,
        input,
        context,
        max_stream_bytes,
        timeout,
        None,
        None,
        None,
        None,
        None,
        None,
    )
}

/// Interactive byte observation stays on the SAME bounded owning process.
/// The callback sees original read bytes (and an empty slice at physical EOF)
/// after the original prefix was retained. It grants no target/root authority.
#[derive(Clone)]
pub(crate) struct Conversation {
    observer: Arc<dyn Fn(usize, &[u8]) -> io::Result<()> + Send + Sync>,
    cancelled: Arc<AtomicBool>,
    stdout_prefix: usize,
    failure: Arc<std::sync::Mutex<Option<String>>>,
    reader_cancelled: Arc<AtomicBool>,
    readers: Arc<std::sync::Mutex<Vec<thread::JoinHandle<()>>>>,
}
impl Conversation {
    pub(crate) fn cancellation_flag(&self) -> Arc<AtomicBool> {
        Arc::clone(&self.cancelled)
    }
    pub(crate) fn new(
        observer: Arc<dyn Fn(usize, &[u8]) -> io::Result<()> + Send + Sync>,
        cancelled: Arc<AtomicBool>,
        stdout_prefix: usize,
    ) -> Self {
        Self {
            observer,
            cancelled,
            stdout_prefix,
            failure: Default::default(),
            reader_cancelled: Arc::new(AtomicBool::new(false)),
            readers: Default::default(),
        }
    }
    fn failure(&self) -> Option<String> {
        self.failure
            .lock()
            .map(|failure| failure.clone())
            .unwrap_or_else(|_| Some("original conversation observer poisoned".into()))
    }
    fn finish_readers(&self, failed: bool) -> Result<(), String> {
        if failed {
            self.cancelled.store(true, Ordering::Release);
        }
        self.reader_cancelled.store(true, Ordering::Release);
        let handles = std::mem::take(
            &mut *self
                .readers
                .lock()
                .map_err(|_| "original conversation reader registry poisoned")?,
        );
        let mut error = None;
        // The interactive read ends are pollable and remain owned by these
        // exact threads. Cancellation interrupts their own read, never emits
        // EOF or a hosted retirement claim, and every original handle joins.
        for handle in handles {
            if handle.join().is_err() {
                error.get_or_insert("original conversation reader panicked".to_owned());
            }
        }
        error.map_or(Ok(()), Err)
    }
}
struct ConversationReaders(Option<Conversation>);
impl ConversationReaders {
    fn finish(&mut self, failed: bool) -> Result<(), String> {
        self.0.take().map_or(Ok(()), |mode| mode.finish_readers(failed))
    }
}
impl Drop for ConversationReaders {
    fn drop(&mut self) {
        let _ = self.finish(true);
    }
}

/// Reuse the ordinary bounded owner/drain with an actual original image check
/// immediately after spawn. The callback cannot grant capacity; the launched
/// native custodian still owns/adopts the actual requested root independently.
#[cfg(unix)]
pub(crate) struct CheckedCapture {
    pub captured: Result<Output, String>,
    pub validation: Result<(), String>,
    /// Bounded actually read prefixes after failed capture. Neither EOF nor
    /// these bytes establish exit, retirement or resource release.
    pub failed_output: Option<PartialCapture>,
    /// Present in interactive mode even after successful capture. Output.stdout
    /// is then explicitly a bounded prefix; complete protocol bytes belong to
    /// the original observer/sink, not to this Vec.
    pub conversation_output: Option<PartialCapture>,
    /// Actual SAME owning wait, also retained on read/callback/cancel failure.
    /// This is only the outer child, never hosted target/cohort retirement.
    pub exit_observation: Option<std::process::ExitStatus>,
}
#[derive(Clone, Default)]
pub(crate) struct PartialCapture {
    pub bytes: [Vec<u8>; 2],
    pub eof: [bool; 2],
    pub bytes_seen: [u64; 2],
    pub read_errors: [Option<String>; 2],
}

/// A failed image check stops the owned child but retains bounded actual
/// stdout/stderr/exit evidence separately. Those bytes never become authority.
#[cfg(unix)]
pub(crate) fn output_with_checked_input_file(
    command: &mut Command,
    input: File,
    context: &str,
    max_stream_bytes: usize,
    deadline: Instant,
    check: &dyn Fn(&Child, Instant) -> Result<(), String>,
) -> CheckedCapture {
    output_with_checked_input_file_limits(
        command,
        input,
        context,
        [max_stream_bytes, max_stream_bytes],
        deadline,
        check,
    )
}
#[cfg(unix)]
pub(crate) fn output_with_checked_input_file_limits(
    command: &mut Command,
    input: File,
    context: &str,
    stream_limits: [usize; 2],
    deadline: Instant,
    check: &dyn Fn(&Child, Instant) -> Result<(), String>,
) -> CheckedCapture {
    checked_input(command, input, context, stream_limits, deadline, check, None)
}

/// Retain a finite interactive stdout prefix while observing every bounded raw
/// byte incrementally. Legacy file/EOF capture never selects this mode.
#[cfg(unix)]
pub(crate) fn output_with_checked_conversation(
    command: &mut Command,
    input: File,
    context: &str,
    stream_limits: [usize; 2],
    deadline: Instant,
    check: &dyn Fn(&Child, Instant) -> Result<(), String>,
    conversation: Conversation,
) -> CheckedCapture {
    checked_input(command, input, context, stream_limits, deadline, check, Some(conversation))
}

#[cfg(unix)]
fn checked_input(
    command: &mut Command,
    input: File,
    context: &str,
    stream_limits: [usize; 2],
    deadline: Instant,
    check: &dyn Fn(&Child, Instant) -> Result<(), String>,
    conversation: Option<Conversation>,
) -> CheckedCapture {
    let max_stream_bytes = stream_limits[0];
    let Some(timeout) =
        deadline.checked_duration_since(Instant::now()).filter(|left| !left.is_zero())
    else {
        return CheckedCapture {
            captured: Err(format!("{context} original deadline expired before launch")),
            validation: Err("native image validation was not attempted".into()),
            failed_output: None,
            conversation_output: None,
            exit_observation: None,
        };
    };
    let validation = std::sync::Mutex::new(None);
    let checked = |child: &Child, until: Instant| -> Result<(), String> {
        let outcome = check(child, until);
        if outcome.is_err() {
            let _ = process_lifecycle::stop_tree(child.id(), StopCause::Error);
        }
        *validation.lock().map_err(|_| format!("{context} image observation failed"))? =
            Some(outcome);
        Ok(())
    };
    let observed = Arc::new(std::sync::Mutex::new(PartialCapture::default()));
    let exit_observation = Arc::new(std::sync::Mutex::new(None));
    let mut readers = ConversationReaders(conversation.clone());
    let mut captured = capture_with_input_checked(
        command,
        Stdio::from(input),
        context,
        max_stream_bytes,
        timeout,
        Some(deadline),
        Some(&checked),
        Some(observed.clone()),
        Some(stream_limits[1]),
        conversation.clone(),
        Some(exit_observation.clone()),
    );
    if let Err(error) = readers.finish(captured.is_err()) {
        if captured.is_ok() {
            captured = Err(error);
        }
    }
    let validation = validation
        .into_inner()
        .ok()
        .flatten()
        .unwrap_or_else(|| Err("native image validation was not attempted".into()));
    let failed_output = if captured.is_err() {
        // The owned child was stopped/reaped by the common capture path. Let
        // original readers report actual available EOF/prefixes briefly; never
        // infer EOF, process retirement or release from this bounded wait.
        let until = deadline.min(Instant::now() + Duration::from_millis(250));
        while conversation.is_none() {
            let done = observed
                .lock()
                .map(|state| {
                    (0..2).all(|index| state.eof[index] || state.read_errors[index].is_some())
                })
                .unwrap_or(true);
            if done || Instant::now() >= until {
                break;
            }
            thread::sleep(Duration::from_millis(2));
        }
        observed.lock().ok().map(|bytes| bytes.clone())
    } else {
        None
    };
    let conversation_output =
        conversation.as_ref().and_then(|_| observed.lock().ok().map(|bytes| bytes.clone()));
    let exit_observation = exit_observation.lock().ok().and_then(|exit| *exit);
    CheckedCapture { captured, validation, failed_output, conversation_output, exit_observation }
}

fn capture_with_input_checked(
    command: &mut Command,
    input: Stdio,
    context: &str,
    max_stream_bytes: usize,
    timeout: Duration,
    original_deadline: Option<Instant>,
    check: Option<&dyn Fn(&Child, Instant) -> Result<(), String>>,
    observed: Option<Arc<std::sync::Mutex<PartialCapture>>>,
    stderr_limit: Option<usize>,
    conversation: Option<Conversation>,
    exit_observation: Option<Arc<std::sync::Mutex<Option<std::process::ExitStatus>>>>,
) -> Result<Output, String> {
    let stderr_limit = stderr_limit.unwrap_or(max_stream_bytes);
    if max_stream_bytes == 0
        || stderr_limit == 0
        || timeout.is_zero()
        || conversation
            .as_ref()
            .is_some_and(|mode| mode.stdout_prefix == 0 || mode.stdout_prefix > max_stream_bytes)
    {
        return Err(format!("{context} has an invalid zero output or timeout bound"));
    }
    if conversation.as_ref().is_some_and(|mode| mode.cancelled.load(Ordering::Acquire)) {
        return Err(format!("{context} original conversation stopped before launch"));
    }
    command.stdin(input).stdout(Stdio::piped()).stderr(Stdio::piped());
    let (mut child, _ownership) = process_lifecycle::spawn_owned(command)
        .map_err(|error| format!("{context} could not start: {error}"))?;
    if let Some(check) = check {
        let Some(deadline) = original_deadline else {
            stop_and_reap(&mut child, StopCause::Error, exit_observation.as_deref());
            return Err(format!("{context} checked capture lacks original deadline"));
        };
        if let Err(error) = check(&child, deadline) {
            stop_and_reap(&mut child, StopCause::Error, exit_observation.as_deref());
            return Err(error);
        }
    }
    let child_pid = child.id();
    let Some(stdout) = child.stdout.take() else {
        stop_and_reap(&mut child, StopCause::Error, exit_observation.as_deref());
        return Err(format!("{context} did not expose stdout"));
    };
    let Some(stderr) = child.stderr.take() else {
        stop_and_reap(&mut child, StopCause::Error, exit_observation.as_deref());
        return Err(format!("{context} did not expose stderr"));
    };
    // Named, and each read end duplicated, while this process still holds the
    // read ends: the reader threads own them from here, and close them at
    // end-of-file.
    let stdout_writer = pipe_writer(&stdout);
    let stderr_writer = pipe_writer(&stderr);
    let stdout_watch = watch_of(&stdout);
    let stderr_watch = watch_of(&stderr);
    let output_exceeded = Arc::new(AtomicBool::new(false));
    #[cfg(unix)]
    let [stdout_fd, stderr_fd] = {
        use std::os::fd::AsRawFd as _;
        [
            conversation.as_ref().map(|_| stdout.as_raw_fd()),
            conversation.as_ref().map(|_| stderr.as_raw_fd()),
        ]
    };
    #[cfg(not(unix))]
    let [stdout_fd, stderr_fd] = [None, None];
    let stdout_reader = spawn_observed_reader(
        stdout,
        max_stream_bytes,
        Arc::clone(&output_exceeded),
        observed.clone().map(|owner| (owner, 0)),
        conversation.clone().map(|mode| (mode, 0)),
        stdout_fd,
    );
    let stderr_reader = spawn_observed_reader(
        stderr,
        stderr_limit,
        Arc::clone(&output_exceeded),
        observed.map(|owner| (owner, 1)),
        conversation.clone().map(|mode| (mode, 1)),
        stderr_fd,
    );
    let Some(deadline) = original_deadline.or_else(|| Instant::now().checked_add(timeout)) else {
        stop_and_reap(&mut child, StopCause::Error, exit_observation.as_deref());
        return Err(format!("{context} timeout deadline overflowed"));
    };

    loop {
        if let Some(mode) = &conversation {
            if mode.cancelled.load(Ordering::Acquire) || mode.failure().is_some() {
                stop_and_reap(&mut child, StopCause::Error, exit_observation.as_deref());
                return Err(mode
                    .failure()
                    .unwrap_or_else(|| format!("{context} original conversation was cancelled")));
            }
        }
        if output_exceeded.load(Ordering::Acquire) {
            stop_and_reap(&mut child, StopCause::Bound, exit_observation.as_deref());
            return Err(output_bound_error(context, max_stream_bytes, stderr_limit));
        }
        match exited_without_reaping(&mut child) {
            Ok(true) => break,
            Ok(false) if Instant::now() < deadline => thread::sleep(Duration::from_millis(10)),
            Ok(false) => {
                stop_and_reap(&mut child, StopCause::Bound, exit_observation.as_deref());
                return Err(format!("{context} exceeded the {timeout:?} timeout"));
            }
            Err(error) => {
                stop_and_reap(&mut child, StopCause::Error, exit_observation.as_deref());
                return Err(format!("{context} could not be polled: {error}"));
            }
        }
    }
    // A signal that stopped this run may be why the child exited; its result
    // is no probe reading, and the stop owns the exit.
    process_lifecycle::signals::hold_if_interrupted();

    // The leader has exited, so all it wrote is in its pipes. WNOWAIT keeps
    // its PID reserved as the process-group ID while they drain, so no stop
    // below can signal a reused PGID.
    //
    // A stream still open POST_EXIT_PIPE_CLOSE_GRACE after that is judged by
    // who holds its write end, read from the kernel ([`Stream::holder`]):
    //
    // * nobody: the kernel reports the pipe hung up, and only its reader
    //   thread has yet to run (on a loaded host a woken thread can wait
    //   longer than the grace for a CPU). It is waited for;
    // * a running process the stop path reaches (the probe's group, the trees
    //   under its members, the groups they lead), or one of those whose
    //   descriptors cannot be read: a pipe-inheriting background descendant.
    //   The probe fails at once rather than spending its whole timeout on it;
    // * a process that is this program's own, outside that reach: this
    //   process, a child another of its threads started, or a descendant of
    //   such a child, in its tree or in the group it leads (where a child that
    //   exited and has yet to be reaped keeps its background jobs). A `fork`
    //   holds every descriptor until its exec, and macOS has no `pipe2`, so
    //   std makes a pipe close-on-exec with a second call and a child spawned
    //   in between keeps the end for its whole life, and hands it to its own
    //   children (Trust's std hands a child only its stdio since SP-1,
    //   a7f474346f; a toolchain older than that does not). That is not the
    //   probe's doing, and is waited for;
    // * anything else: a process in neither. Every descendant of the probe
    //   outside its reach is one: once the leader has exited, a descendant
    //   that left its group is re-parented away from this program. It is a
    //   background descendant, refused as one, once a second read
    //   POST_EXIT_HOLDER_POLL later agrees.
    //
    // A wait ends at the probe's own deadline, a hang detector, which fails
    // the probe closed. Before 2026-10-21 every stream still open when the
    // grace ran out was blamed on the probe, and the stop of a group down to
    // its unreaped leader failed with EPERM on macOS, so the first and third
    // cases failed probes that had done nothing wrong (land-gate run 15). A
    // redirected descendant holds neither stream and is removed by the group
    // cleanup below.
    let bound = AfterExit {
        context,
        child_pid,
        max_stream_bytes,
        stderr_limit,
        output_exceeded: &output_exceeded,
        timeout,
        grace_end: Instant::now()
            .checked_add(POST_EXIT_PIPE_CLOSE_GRACE)
            .unwrap_or(deadline)
            .min(deadline),
        deadline,
    };
    let mut streams = [
        Stream::new("stdout", stdout_reader, stdout_writer, stdout_watch),
        Stream::new("stderr", stderr_reader, stderr_writer, stderr_watch),
    ];
    let received = match conversation.as_ref() {
        Some(mode) => receive_after_exit_with_control(&mut streams, &bound, Some(mode)),
        None => receive_after_exit(&mut streams, &bound),
    };
    if let Err(error) = received {
        stop_and_reap(&mut child, StopCause::Bound, exit_observation.as_deref());
        return Err(error);
    }
    let [(stdout, stdout_exceeded), (stderr, stderr_exceeded)] =
        streams.map(|stream| stream.received.expect("received after exit"));
    // The leader exited; whatever is left of its group goes before it is reaped.
    let _ = process_lifecycle::stop_tree(child_pid, StopCause::LeaderExited);
    let status = child.wait().map_err(|error| format!("{context} could not be reaped: {error}"))?;
    if let Some(observed) = &exit_observation {
        if let Ok(mut original) = observed.lock() {
            *original = Some(status);
        }
    }
    if stdout_exceeded || stderr_exceeded {
        return Err(output_bound_error(context, max_stream_bytes, stderr_limit));
    }
    Ok(Output { status, stdout, stderr })
}

fn output_bound_error(context: &str, stdout: usize, stderr: usize) -> String {
    if stdout == stderr {
        format!("{context} output exceeded {stdout} bytes per stream")
    } else {
        format!(
            "{context} output exceeded configured bounds ({stdout} stdout/{stderr} stderr bytes)"
        )
    }
}

/// Stop the child through the one stop path, then reap it.
fn stop_and_reap(
    child: &mut Child,
    cause: StopCause,
    observed: Option<&std::sync::Mutex<Option<std::process::ExitStatus>>>,
) {
    let _ = process_lifecycle::stop_child(child, cause);
    if let Ok(status) = child.wait() {
        if let Some(observed) = observed {
            if let Ok(mut original) = observed.lock() {
                *original = Some(status);
            }
        }
    }
}

#[cfg(test)]
fn spawn_reader<R: Read + Send + 'static>(
    reader: R,
    max_stream_bytes: usize,
    output_exceeded: Arc<AtomicBool>,
) -> Receiver<io::Result<(Vec<u8>, bool)>> {
    spawn_observed_reader(reader, max_stream_bytes, output_exceeded, None, None, None)
}
struct ObservedReader<R> {
    inner: R,
    owner: Option<(Arc<std::sync::Mutex<PartialCapture>>, usize)>,
    limit: usize,
    conversation: Option<(Conversation, usize)>,
    poll_fd: Option<i32>,
}
impl<R: Read> Read for ObservedReader<R> {
    fn read(&mut self, buffer: &mut [u8]) -> io::Result<usize> {
        let result = match (&self.conversation, self.poll_fd) {
            (Some((mode, _)), Some(fd)) => {
                conversation_read_ready(fd, mode).and_then(|()| self.inner.read(buffer))
            }
            _ => self.inner.read(buffer),
        };
        if let Some((owner, index)) = &self.owner {
            if let Ok(mut observed) = owner.lock() {
                match &result {
                    Ok(0) => observed.eof[*index] = true,
                    Ok(count) => {
                        observed.bytes_seen[*index] =
                            observed.bytes_seen[*index].saturating_add(*count as u64);
                        let retained =
                            (*count).min(self.limit.saturating_sub(observed.bytes[*index].len()));
                        observed.bytes[*index].extend_from_slice(&buffer[..retained]);
                    }
                    Err(error) if error.kind() != io::ErrorKind::Interrupted => {
                        observed.read_errors[*index] = Some(error.to_string())
                    }
                    Err(_) => {}
                }
            }
        }
        if let (Err(error), Some((mode, _))) = (&result, &self.conversation) {
            if let Ok(mut failure) = mode.failure.lock() {
                failure
                    .get_or_insert_with(|| format!("original conversation read failed: {error}"));
            }
        }
        if let (Ok(count), Some((mode, index))) = (&result, &self.conversation) {
            struct PanicObservation<'a>(&'a Conversation);
            impl Drop for PanicObservation<'_> {
                fn drop(&mut self) {
                    if thread::panicking() {
                        if let Ok(mut failure) = self.0.failure.lock() {
                            failure.get_or_insert("original conversation observer panicked".into());
                        }
                    }
                }
            }
            let _original = PanicObservation(mode);
            if let Err(error) = (mode.observer)(*index, &buffer[..*count]) {
                if let Ok(mut failure) = mode.failure.lock() {
                    failure.get_or_insert_with(|| error.to_string());
                }
                return Err(error);
            }
        }
        result
    }
}
fn spawn_observed_reader<R: Read + Send + 'static>(
    reader: R,
    max_stream_bytes: usize,
    output_exceeded: Arc<AtomicBool>,
    owner: Option<(Arc<std::sync::Mutex<PartialCapture>>, usize)>,
    conversation: Option<(Conversation, usize)>,
    poll_fd: Option<i32>,
) -> Receiver<io::Result<(Vec<u8>, bool)>> {
    let (sender, receiver) = mpsc::sync_channel(1);
    let original = conversation.as_ref().map(|(mode, _)| mode.clone());
    let handle = thread::spawn(move || {
        let retain = conversation
            .as_ref()
            .filter(|(_, index)| *index == 0)
            .map_or(max_stream_bytes.saturating_add(1), |(mode, _)| mode.stdout_prefix);
        let reader = ObservedReader { inner: reader, owner, limit: retain, conversation, poll_fd };
        let _ = sender.send(drain_with_retention(
            reader,
            max_stream_bytes,
            retain,
            Some(&output_exceeded),
        ));
    });
    if let Some(mode) = original {
        // Only the original capture thread registers/consumes these handles.
        // Reader threads never take this mutex while running the observer.
        mode.readers.lock().expect("original reader registration").push(handle);
    }
    receiver
}

fn conversation_read_ready(fd: i32, mode: &Conversation) -> io::Result<()> {
    #[cfg(unix)]
    loop {
        if mode.reader_cancelled.load(Ordering::Acquire)
            || mode.cancelled.load(Ordering::Acquire)
            || mode.failure().is_some()
        {
            return Err(io::Error::other(
                "original conversation read cancelled; no physical EOF inferred",
            ));
        }
        let mut poll = libc::pollfd { fd, events: libc::POLLIN, revents: 0 };
        // fd names the SAME read end retained inside this reader. No other
        // thread consumes it or closes/reopens it while poll/read executes.
        let ready = unsafe { libc::poll(&mut poll, 1, 20) };
        if ready < 0 {
            let error = io::Error::last_os_error();
            if error.kind() == io::ErrorKind::Interrupted {
                continue;
            }
            return Err(error);
        }
        if ready > 0 {
            if poll.revents & libc::POLLNVAL != 0 {
                return Err(io::Error::other("original native read descriptor invalidated"));
            }
            return Ok(());
        }
    }
    #[cfg(not(unix))]
    {
        let _ = (fd, mode);
        Err(io::ErrorKind::Unsupported.into())
    }
}

#[cfg(test)]
fn drain(mut reader: impl Read, max_stream_bytes: usize) -> io::Result<(Vec<u8>, bool)> {
    drain_with_signal(&mut reader, max_stream_bytes, None)
}

fn drain_with_signal(
    reader: impl Read,
    max_stream_bytes: usize,
    output_exceeded: Option<&AtomicBool>,
) -> io::Result<(Vec<u8>, bool)> {
    drain_with_retention(
        reader,
        max_stream_bytes,
        max_stream_bytes.saturating_add(1),
        output_exceeded,
    )
}
fn drain_with_retention(
    mut reader: impl Read,
    max_stream_bytes: usize,
    retained_limit: usize,
    output_exceeded: Option<&AtomicBool>,
) -> io::Result<(Vec<u8>, bool)> {
    let mut seen = 0usize;

    let mut retained = Vec::with_capacity(retained_limit.min(8 * 1024));
    let mut exceeded = false;
    let mut chunk = [0_u8; 8 * 1024];
    loop {
        let read = reader.read(&mut chunk)?;
        if read == 0 {
            break;
        }
        let remaining = retained_limit.saturating_sub(retained.len());
        retained.extend_from_slice(&chunk[..read.min(remaining)]);
        seen = match seen.checked_add(read) {
            Some(total) => total,
            None => {
                exceeded = true;
                usize::MAX
            }
        };
        exceeded |= seen > max_stream_bytes;
        if exceeded {
            if let Some(output_exceeded) = output_exceeded {
                output_exceeded.store(true, Ordering::Release);
            }
        }
    }
    Ok((retained, exceeded))
}

/// The write end of the pipe `stream` reads, while this process holds it.
#[cfg(unix)]
fn pipe_writer(stream: &impl std::os::fd::AsRawFd) -> Option<tree::PipeWriter> {
    tree::pipe_writer_of(stream.as_raw_fd())
}

#[cfg(not(unix))]
fn pipe_writer<T>(_stream: &T) -> Option<tree::PipeWriter> {
    None
}

/// A duplicate of a pipe's read end, kept to ask the kernel whether any
/// process still holds the write end ([`writer_remains`]).
#[cfg(unix)]
type Watch = std::os::fd::OwnedFd;

/// No platform here can ask a pipe whether its writers are gone.
#[cfg(not(unix))]
type Watch = std::convert::Infallible;

/// A close-on-exec duplicate of the read end of the pipe `stream` reads;
/// `None` when it cannot be made.
#[cfg(unix)]
fn watch_of(stream: &impl std::os::fd::AsFd) -> Option<Watch> {
    stream.as_fd().try_clone_to_owned().ok()
}

#[cfg(not(unix))]
fn watch_of<T>(_stream: &T) -> Option<Watch> {
    None
}

/// Whether any process still holds the write end of the pipe `watch` reads:
/// `Some(false)` once the kernel reports the pipe hung up, which nothing can
/// undo (a write end is only ever inherited from, or passed by, a process
/// that holds one); `None` when the poll fails.
#[cfg(unix)]
fn writer_remains(watch: &Watch) -> Option<bool> {
    use std::os::fd::AsRawFd as _;
    let mut entry = libc::pollfd { fd: watch.as_raw_fd(), events: libc::POLLIN, revents: 0 };
    // SAFETY: `entry` is the one `pollfd` the call reads and writes, and a
    // zero timeout never blocks.
    let ready = unsafe { libc::poll(&raw mut entry, 1, 0) };
    if ready < 0 || entry.revents & libc::POLLNVAL != 0 {
        return None;
    }
    Some(entry.revents & libc::POLLHUP == 0)
}

#[cfg(not(unix))]
fn writer_remains(watch: &Watch) -> Option<bool> {
    match *watch {}
}

/// One captured stream once the probe's leader has exited.
struct Stream {
    name: &'static str,
    reader: Receiver<io::Result<(Vec<u8>, bool)>>,
    /// The pipe's write end, to read who holds it; `None` where it cannot be
    /// named.
    writer: Option<tree::PipeWriter>,
    /// A duplicate of the read end, to read whether any writer is left;
    /// `None` where none could be made.
    watch: Option<Watch>,
    /// The previous read of [`Stream::holder`] found [`Holder::Escaped`].
    escaped_before: bool,
    /// The reader's result, once it has arrived.
    received: Option<(Vec<u8>, bool)>,
}

/// Who holds a captured stream open once the probe's leader has exited.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Holder {
    /// No process: the kernel reports the pipe hung up, and only the stream's
    /// reader has yet to run.
    Nobody,
    /// A running process the probe's stop reaches -- the probe's own -- or
    /// one of those whose descriptors could not be read, or this platform
    /// cannot say.
    Probe,
    /// A process of this program's own that the probe's stop does not reach:
    /// this process, the tree under it, or a member of a group a child of this
    /// process leads (an exited, unreaped child's background job among them,
    /// re-parented out of the tree when that child exited).
    ThisProgram,
    /// A process in neither: a descendant of the probe that left its process
    /// group, re-parented away from this program when the leader exited.
    Escaped,
}

impl Stream {
    fn new(
        name: &'static str,
        reader: Receiver<io::Result<(Vec<u8>, bool)>>,
        writer: Option<tree::PipeWriter>,
        watch: Option<Watch>,
    ) -> Self {
        Stream { name, reader, writer, watch, escaped_before: false, received: None }
    }

    /// Wait up to `wait` for the reader's result, and keep it once it arrives.
    fn receive(&mut self, context: &str, wait: Duration) -> Result<(), String> {
        if self.received.is_some() {
            return Ok(());
        }
        match self.reader.recv_timeout(wait) {
            Ok(result) => {
                let read = result
                    .map_err(|error| format!("{context} could not read {}: {error}", self.name))?;
                self.received = Some(read);
                Ok(())
            }
            Err(RecvTimeoutError::Timeout) => Ok(()),
            Err(RecvTimeoutError::Disconnected) => {
                Err(format!("{context} {} reader disconnected", self.name))
            }
        }
    }

    /// Who holds this stream's write end now, once the leader `child_pid` has
    /// exited: whether the pipe has hung up, then the descriptor tables of
    /// the running processes a stop of `child_pid` reaches, then those of
    /// this program's own processes (its tree, and the groups its children
    /// lead).
    fn holder(&self, child_pid: u32) -> Holder {
        if self.watch.as_ref().and_then(writer_remains) == Some(false) {
            return Holder::Nobody;
        }
        let (Some(writer), Some(reach)) =
            (self.writer.as_ref(), process_lifecycle::running_reach(child_pid))
        else {
            return Holder::Probe;
        };
        if reach.iter().any(|&pid| tree::holds_pipe_writer(pid, writer) != Some(false)) {
            return Holder::Probe;
        }
        // This program: this process, the tree under it, and the groups that
        // its children lead. An exited child not yet reaped is another
        // child's leader in its own post-exit wait (another probe's): its
        // descendants were re-parented out of the tree when it exited, and its
        // own stop still reaches them through its group. A table that cannot
        // be read here counts as not holding the stream, which can only lead
        // to a refusal.
        let this = std::process::id();
        let mut program = Vec::new();
        if !tree::collect_process_tree(this, &mut program) {
            return Holder::Escaped;
        }
        let (mut children, mut group) = (Vec::new(), Vec::new());
        if tree::collect_children(this, &mut children) {
            for &child in &children {
                if tree::collect_process_group(child, &mut group) {
                    program.extend_from_slice(&group);
                }
            }
        }
        if program
            .iter()
            .copied()
            .filter(|pid| !reach.contains(pid))
            .any(|pid| tree::holds_pipe_writer(pid, writer) == Some(true))
        {
            return Holder::ThisProgram;
        }
        Holder::Escaped
    }
}

/// What bounds the wait for a probe's streams once its leader has exited.
struct AfterExit<'a> {
    context: &'a str,
    /// The exited, unreaped leader.
    child_pid: u32,
    max_stream_bytes: usize,
    stderr_limit: usize,
    /// Set by a reader whose stream went past its bound.
    output_exceeded: &'a AtomicBool,
    /// The probe's deadline as the caller stated it, for messages.
    timeout: Duration,
    /// The end of [`POST_EXIT_PIPE_CLOSE_GRACE`].
    grace_end: Instant,
    /// The probe's own deadline: the hang detector of this wait.
    deadline: Instant,
}

/// Receive both streams once the leader has exited, under the rule its call
/// site states: a stream a descendant of the probe still holds when the grace
/// ends fails the probe at once (one that escaped the probe's reach, on two
/// reads in a row), and any other is waited for until the probe's deadline, a
/// hang detector, which fails the probe closed. A stream past its byte bound
/// fails it at once, as it does while the leader runs.
fn receive_after_exit(streams: &mut [Stream; 2], bound: &AfterExit<'_>) -> Result<(), String> {
    receive_after_exit_with_control(streams, bound, None)
}
fn receive_after_exit_with_control(
    streams: &mut [Stream; 2],
    bound: &AfterExit<'_>,
    conversation: Option<&Conversation>,
) -> Result<(), String> {
    let context = bound.context;
    loop {
        if let Some(mode) = conversation {
            if mode.cancelled.load(Ordering::Acquire) || mode.failure().is_some() {
                bound.stop("original conversation")?;
                return Err(mode.failure().unwrap_or_else(|| {
                    format!("{context} original conversation cancelled during stream drain")
                }));
            }
        }
        for stream in streams.iter_mut() {
            stream.receive(context, Duration::ZERO)?;
        }
        let Some(open) = streams.iter().position(|stream| stream.received.is_none()) else {
            return Ok(());
        };
        if bound.output_exceeded.load(Ordering::Acquire) {
            bound.stop(streams[open].name)?;
            return Err(output_bound_error(context, bound.max_stream_bytes, bound.stderr_limit));
        }
        let now = Instant::now();
        if now < bound.grace_end {
            let wait = bound.grace_end - now;
            streams[open].receive(
                context,
                if conversation.is_some() { wait.min(Duration::from_millis(50)) } else { wait },
            )?;
            continue;
        }
        for stream in streams.iter_mut().filter(|stream| stream.received.is_none()) {
            match stream.holder(bound.child_pid) {
                Holder::Nobody | Holder::ThisProgram => stream.escaped_before = false,
                // One read can catch a holder of this program mid-change (a
                // descriptor closed between its listing and its read, a
                // writer gone between the scans): a second agrees or not.
                Holder::Escaped if !stream.escaped_before => stream.escaped_before = true,
                Holder::Escaped => {
                    bound.stop(stream.name)?;
                    return Err(format!(
                        "{context} spawned a background descendant that left its process group \
                         and kept {} open past the output deadline",
                        stream.name
                    ));
                }
                Holder::Probe => {
                    bound.stop(stream.name)?;
                    return Err(format!(
                        "{context} spawned a background descendant that kept {} open past the output deadline",
                        stream.name
                    ));
                }
            }
        }
        if now >= bound.deadline {
            let name = streams[open].name;
            bound.stop(name)?;
            return Err(format!(
                "{context} {name} was still open at the {:?} timeout, after the probe exited, \
                 and no process the probe's stop reaches held it",
                bound.timeout
            ));
        }
        streams[open].receive(context, (bound.deadline - now).min(POST_EXIT_HOLDER_POLL))?;
    }
}

impl AfterExit<'_> {
    /// Stop what is left of the probe through the one stop path, before a
    /// verdict on `stream`.
    fn stop(&self, stream: &str) -> Result<(), String> {
        process_lifecycle::stop_tree(self.child_pid, StopCause::Bound).map(|_| ()).map_err(
            |error| {
                format!(
                    "{} {stream} remained open and its process group could not be terminated: {error}",
                    self.context
                )
            },
        )
    }
}

/// Observe child exit without releasing its PID/PGID reservation on Unix.
pub(crate) fn exited_without_reaping(child: &mut Child) -> io::Result<bool> {
    #[cfg(unix)]
    {
        let pid = i32::try_from(child.id()).map_err(|_| {
            io::Error::new(io::ErrorKind::InvalidInput, "child pid does not fit platform pid_t")
        })?;
        let mut exit_info = std::mem::MaybeUninit::<libc::siginfo_t>::zeroed();
        let observed = unsafe {
            libc::waitid(
                libc::P_PID,
                pid as libc::id_t,
                exit_info.as_mut_ptr(),
                libc::WEXITED | libc::WNOHANG | libc::WNOWAIT,
            )
        };
        if observed < 0 {
            return Err(io::Error::last_os_error());
        }
        let exit_info = unsafe { exit_info.assume_init() };
        Ok(unsafe { exit_info.si_pid() } == pid)
    }
    #[cfg(not(unix))]
    {
        child.try_wait().map(|status| status.is_some())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn checked_failed_reader_retains_actual_prefix_and_error_without_eof_or_exit() {
        struct Fails(bool);
        impl Read for Fails {
            fn read(&mut self, bytes: &mut [u8]) -> io::Result<usize> {
                if self.0 {
                    return Err(io::Error::other("actual read failure"));
                }
                self.0 = true;
                bytes[..4].copy_from_slice(b"a\0b\xff");
                Ok(4)
            }
        }
        let owner = Arc::new(std::sync::Mutex::new(PartialCapture::default()));
        let mut reader = ObservedReader {
            inner: Fails(false),
            owner: Some((owner.clone(), 0)),
            limit: 3,
            conversation: None,
            poll_fd: None,
        };
        let mut buffer = [0; 8];
        assert_eq!(reader.read(&mut buffer).unwrap(), 4);
        assert!(reader.read(&mut buffer).is_err());
        let observed = owner.lock().unwrap();
        assert_eq!(observed.bytes[0], b"a\0b");
        assert_eq!(observed.bytes_seen[0], 4);
        assert!(!observed.eof[0]);
        assert!(observed.read_errors[0].as_deref().unwrap().contains("actual read failure"));
    }

    #[cfg(unix)]
    #[test]
    fn checked_capture_native_actor() {
        if std::env::var_os("TRUST_CHECKED_CAPTURE_ACTOR").is_none() {
            return;
        }
        let mut byte = [0; 1];
        std::io::stdin().read_exact(&mut byte).unwrap();
        use std::io::Write as _;
        std::io::stdout().write_all(&byte).unwrap();
        if std::env::var_os("TRUST_CHECKED_CAPTURE_STDERR_BURST").is_some() {
            std::io::stdout().write_all(b"native-before-stderr-bound").unwrap();
            std::io::stdout().flush().unwrap();
            std::io::stderr().write_all(&[b'e'; 128]).unwrap();
        }
    }

    #[cfg(unix)]
    #[test]
    fn checked_capture_matches_actual_native_image_and_refusal_reaps_the_owned_child() {
        let image = std::env::current_exe().unwrap();
        let held = File::open(&image).unwrap();
        for refuse in [false, true] {
            let mut command = Command::new(&image);
            command
                .args([
                    "--exact",
                    "bounded_process::tests::checked_capture_native_actor",
                    "--nocapture",
                ])
                .env("TRUST_CHECKED_CAPTURE_ACTOR", "1");
            let (input, release) = std::io::pipe().unwrap();
            let input = File::from(std::os::fd::OwnedFd::from(input));
            let release = std::sync::Mutex::new(release);
            use std::io::Write as _;
            let seen = std::sync::Mutex::new(None);
            let check = |child: &Child, _deadline: Instant| -> Result<(), String> {
                let native = trust_resource_provenance::process::read_identity(child.id())
                    .map_err(|error| error.to_string())?;
                assert!(
                    trust_resource_provenance::process::image_matches(native, &held, &image)
                        .unwrap()
                );
                *seen.lock().unwrap() = process_lifecycle::tree::identity(child.id())
                    .map(|identity| (child.id(), identity.start));
                if refuse {
                    Err("actual owned image check deliberately refused".into())
                } else {
                    release.lock().unwrap().write_all(b"z").unwrap();
                    Ok(())
                }
            };
            let output = output_with_checked_input_file(
                &mut command,
                input,
                "checked native actor",
                64 * 1024,
                Instant::now() + Duration::from_secs(10),
                &check,
            );
            if refuse {
                assert!(output.validation.unwrap_err().contains("deliberately refused"));
                assert!(!output.captured.unwrap().status.success());
            } else {
                output.validation.unwrap();
                let output = output.captured.unwrap();
                assert!(output.status.success());
                assert!(output.stdout.contains(&b'z'));
            }
            let (pid, birth) = seen.lock().unwrap().expect("actual held child observed");
            assert!(!process_lifecycle::tree::still_running(pid, Some(birth)));
        }
    }

    #[cfg(unix)]
    #[test]
    fn checked_distinct_stderr_bound_retains_actual_native_prefixes_after_reap() {
        use std::io::Write as _;
        let image = std::env::current_exe().unwrap();
        let held = File::open(&image).unwrap();
        let mut command = Command::new(&image);
        command
            .args([
                "--exact",
                "bounded_process::tests::checked_capture_native_actor",
                "--nocapture",
            ])
            .env("TRUST_CHECKED_CAPTURE_ACTOR", "1")
            .env("TRUST_CHECKED_CAPTURE_STDERR_BURST", "1");
        let (input, release) = std::io::pipe().unwrap();
        let input = File::from(std::os::fd::OwnedFd::from(input));
        let release = std::sync::Mutex::new(release);
        let seen = std::sync::Mutex::new(None);
        let check = |child: &Child, _deadline: Instant| -> Result<(), String> {
            let id = trust_resource_provenance::process::read_identity(child.id())
                .map_err(|e| e.to_string())?;
            assert!(trust_resource_provenance::process::image_matches(id, &held, &image).unwrap());
            *seen.lock().unwrap() = process_lifecycle::tree::identity(child.id())
                .map(|identity| (child.id(), identity.start));
            release.lock().unwrap().write_all(b"z").unwrap();
            Ok(())
        };
        let captured = output_with_checked_input_file_limits(
            &mut command,
            input,
            "distinct native stderr bound",
            [64 * 1024, 32],
            Instant::now() + Duration::from_secs(10),
            &check,
        );
        captured.validation.unwrap();
        assert!(captured.captured.unwrap_err().contains("output exceeded"));
        let actual = captured.failed_output.expect("failed native bytes retained");
        assert!(
            actual.bytes[0]
                .windows(b"native-before-stderr-bound".len())
                .any(|window| window == b"native-before-stderr-bound")
        );
        assert_eq!(actual.bytes[1], vec![b'e'; 33]);
        assert!(actual.bytes_seen[1] >= 128);
        let (pid, birth) = seen.lock().unwrap().unwrap();
        assert!(!process_lifecycle::tree::still_running(pid, Some(birth)));
    }

    #[cfg(unix)]
    #[test]
    fn closed_pipe_with_delayed_reader_delivery_is_not_a_background_descendant() {
        for (label, hold_stderr, overall_ms, should_pass) in [
            ("closed", false, 2000, true),
            ("inherited stderr", true, 2000, false),
            ("overall bound", false, 50, false),
        ] {
            let script = if hold_stderr {
                "/bin/sleep 10 </dev/null >/dev/null & printf delivered"
            } else {
                "printf delivered"
            };
            let mut command = Command::new("/bin/sh");
            command
                .args(["-c", script])
                .stdin(Stdio::null())
                .stdout(Stdio::piped())
                .stderr(Stdio::piped());
            let (mut child, _ownership) =
                process_lifecycle::spawn_owned(&mut command).expect("owned producer");
            let stdout = child.stdout.take().expect("producer stdout");
            let stderr = child.stderr.take().expect("producer stderr");
            let stdout_writer = pipe_writer(&stdout);
            let stderr_writer = pipe_writer(&stderr);
            let stdout_watch = watch_of(&stdout).expect("owned stdout monitor");
            let stderr_watch = watch_of(&stderr).expect("owned stderr monitor");
            let output_exceeded = Arc::new(AtomicBool::new(false));
            let stderr_reader = spawn_reader(stderr, 1024, Arc::clone(&output_exceeded));
            let (ready_tx, ready_rx) = mpsc::sync_channel(1);
            let (send, receive) = mpsc::sync_channel(1);
            let reader = thread::spawn(move || {
                let result = drain(stdout, 1024);
                ready_tx.send(()).expect("notify actual EOF");
                // Delay delivery only, after observing the producer's EOF.
                thread::sleep(Duration::from_millis(500));
                let _ = send.send(result);
            });
            ready_rx.recv_timeout(Duration::from_secs(2)).expect("actual pipe EOF");
            let exit_deadline = Instant::now() + Duration::from_secs(2);
            while !exited_without_reaping(&mut child).expect("observe producer exit") {
                assert!(Instant::now() < exit_deadline, "producer failed to exit");
                thread::sleep(Duration::from_millis(1));
            }
            let now = Instant::now();
            let bound = AfterExit {
                context: "delayed closed-pipe reader",
                child_pid: child.id(),
                max_stream_bytes: 1024,
                stderr_limit: 1024,
                output_exceeded: &output_exceeded,
                timeout: Duration::from_millis(overall_ms),
                grace_end: now + Duration::from_millis(5),
                deadline: now + Duration::from_millis(overall_ms),
            };
            let mut streams = [
                Stream::new("stdout", receive, stdout_writer, Some(stdout_watch)),
                Stream::new("stderr", stderr_reader, stderr_writer, Some(stderr_watch)),
            ];
            let result = receive_after_exit(&mut streams, &bound);
            let _ = process_lifecycle::stop_tree(child.id(), StopCause::LeaderExited);
            let status = child.wait().expect("reap producer after capture");
            reader.join().expect("reader joined");
            assert!(status.success());
            if should_pass {
                result.expect("closed pipes are not pipe-holding descendants");
                let (bytes, exceeded) = streams[0].received.take().expect("stdout delivered");
                assert_eq!(bytes, b"delivered");
                assert!(!exceeded);
                let (stderr, exceeded) = streams[1].received.take().expect("stderr delivered");
                assert!(stderr.is_empty());
                assert!(!exceeded);
            } else {
                let error = result.expect_err(label);
                if hold_stderr {
                    assert!(error.contains("background descendant"), "{error}");
                } else {
                    assert!(error.contains("timeout"), "{error}");
                    assert!(!error.contains("background descendant"), "{error}");
                }
            }
        }
    }

    #[cfg(unix)]
    #[test]
    fn file_input_preserves_nul_bytes_and_output_bounds() {
        let directory = tempfile::tempdir().expect("private input directory");
        let path = directory.path().join("input");
        let bytes = b"first\0line\nbreak\0last\0";
        std::fs::write(&path, bytes).expect("write input bytes");
        let captured = output_with_input_file(
            &mut Command::new("/bin/cat"),
            File::open(&path).expect("read-only input"),
            "file input probe",
            1024,
            Duration::from_secs(2),
        )
        .expect("bounded file input capture");
        assert!(captured.status.success());
        assert_eq!(captured.stdout, bytes);
        assert!(captured.stderr.is_empty());
        let error = output_with_input_file(
            &mut Command::new("/bin/cat"),
            File::open(&path).expect("fresh read-only input"),
            "file input bound",
            4,
            Duration::from_secs(2),
        )
        .expect_err("file stdin must not bypass the output bound");
        assert!(error.contains("output exceeded"));
    }

    #[cfg(unix)]
    #[test]
    fn rejects_oversized_hanging_and_background_probes() {
        let mut successful = Command::new("/bin/sh");
        successful.args(["-c", "printf bounded"]);
        let successful_output =
            output(&mut successful, "successful probe", 1024, Duration::from_secs(2))
                .expect("a completed child with closed streams must be accepted");
        assert!(successful_output.status.success());
        assert_eq!(successful_output.stdout, b"bounded");

        let (retained, exceeded) =
            drain(io::Cursor::new(vec![b'x'; 100_000]), 64 * 1024).expect("read bounded fixture");
        assert!(exceeded);
        assert_eq!(retained.len(), 64 * 1024 + 1);

        let mut oversized = Command::new("/bin/sh");
        oversized.args(["-c", "while :; do printf 0123456789abcdef; done"]);
        assert!(
            output(&mut oversized, "oversized probe", 1024, Duration::from_secs(5))
                .expect_err("oversized output must fail")
                .contains("output exceeded")
        );

        // Pins the deadline machinery, so it states the deadline exactly rather
        // than letting the harness stretch its own fixture bound.
        let mut hanging = Command::new("/bin/sh");
        hanging.args(["-c", "while :; do :; done"]);
        assert!(
            output_with_exact_deadline(
                &mut hanging,
                "hanging probe",
                1024,
                Duration::from_millis(100)
            )
            .expect_err("hanging command must fail")
            .contains("timeout")
        );

        let mut background = Command::new("/bin/sh");
        background.args(["-c", "sleep 10 & exit 0"]);
        assert!(
            output(&mut background, "background probe", 1024, Duration::from_secs(2))
                .expect_err("background descendant must fail")
                .contains("background descendant")
        );

        let marker = std::env::temp_dir()
            .join(format!("trust-bounded-process-descendant-{}", std::process::id()));
        let _ = std::fs::remove_file(&marker);
        let mut redirected_background = Command::new("/bin/sh");
        redirected_background
            .arg("-c")
            .arg(
                "sh -c 'trap \"\" HUP; sleep 1; printf survived > \"$1\"' descendant \"$1\" \
                 </dev/null >/dev/null 2>&1 & printf '%s' \"$!\"",
            )
            .arg("bounded-process-test")
            .arg(&marker);
        let redirected_output = output(
            &mut redirected_background,
            "redirected background probe",
            1024,
            Duration::from_secs(2),
        )
        .expect("closed probe streams may complete after group cleanup");
        let pid: i32 = String::from_utf8(redirected_output.stdout)
            .expect("pid UTF-8")
            .parse()
            .expect("numeric pid");
        // A killed grandchild can briefly remain as an init-owned zombie, for
        // which `kill(pid, 0)` misleadingly succeeds. Prove that it cannot
        // execute after cleanup instead.
        thread::sleep(Duration::from_millis(1_200));
        assert!(
            !marker.exists(),
            "redirected descendant {pid} survived cleanup and wrote its marker"
        );
        let _ = std::fs::remove_file(marker);
    }

    /// A hang detector, not a latency budget: what must happen happens long
    /// before it on any host.
    #[cfg(any(target_os = "macos", target_os = "linux"))]
    const HANG: Duration = Duration::from_secs(60);

    /// Wait until the probe's leader `leader` no longer runs.
    #[cfg(any(target_os = "macos", target_os = "linux"))]
    fn wait_for_exit(leader: u32) {
        let deadline = Instant::now() + HANG;
        while process_lifecycle::tree::still_running(leader, None) {
            assert!(Instant::now() < deadline, "the probe's leader {leader} never exited");
            thread::sleep(Duration::from_millis(10));
        }
    }

    /// A descendant of the probe that leaves the probe's process group and
    /// holds its stderr after the leader exits: the probe's own background
    /// process, which no stop of the leader's group reaches, and which the
    /// leader's exit re-parents away from this program.
    ///
    /// The fixture makes one: the leader forks, in a `pre_exec` hook (its
    /// stdio already in place), a child that leaves the leader's group,
    /// points its stdout at the null device the probe's stdin is, closes
    /// everything above stdio and becomes `sleep`, holding the probe's stderr
    /// and nothing else of it. The leader reports both pids through a pipe
    /// before its own exec, and the test ends the holder with SIGKILL.
    #[cfg(any(target_os = "macos", target_os = "linux"))]
    struct EscapedHolder {
        report: std::fs::File,
        pids: Option<(u32, u32, Option<u64>)>,
    }

    #[cfg(any(target_os = "macos", target_os = "linux"))]
    impl EscapedHolder {
        /// Arm `command` (a `/bin/sh -c` probe) to leave an escaped holder.
        fn arm(command: &mut Command) -> Self {
            use std::os::fd::{AsRawFd as _, FromRawFd as _, OwnedFd};
            use std::os::unix::process::CommandExt as _;
            let mut ends: [libc::c_int; 2] = [-1, -1];
            // SAFETY: `ends` is the two-element array `pipe` writes.
            let created = unsafe { libc::pipe(ends.as_mut_ptr()) };
            assert_eq!(created, 0, "the report pipe: {}", io::Error::last_os_error());
            for fd in ends {
                // SAFETY: both descriptors were just created here.
                unsafe { libc::fcntl(fd, libc::F_SETFD, libc::FD_CLOEXEC) };
            }
            // SAFETY: each descriptor was just created here and is owned once.
            let (report, report_end) =
                unsafe { (std::fs::File::from_raw_fd(ends[0]), OwnedFd::from_raw_fd(ends[1])) };
            // SAFETY: the hook runs between fork and exec and makes only
            // async-signal-safe calls (`fork`, `getpid`, `setpgid`, `dup2`,
            // `close`, `execve`, `_exit`, `write`); it allocates nothing: its
            // arrays are on the stack and point at static strings.
            unsafe {
                command.pre_exec(move || {
                    let holder = libc::fork();
                    if holder == 0 {
                        libc::setpgid(0, 0);
                        // fd 0 is the probe's null stdin: stdout leaves the probe's pipe.
                        libc::dup2(0, 1);
                        for fd in 3..1024 {
                            libc::close(fd);
                        }
                        let argv = [c"sleep".as_ptr(), c"120".as_ptr(), std::ptr::null()];
                        let envp = [std::ptr::null::<libc::c_char>()];
                        libc::execve(c"/bin/sleep".as_ptr(), argv.as_ptr(), envp.as_ptr());
                        libc::_exit(127);
                    }
                    if holder < 0 {
                        return Err(io::Error::last_os_error());
                    }
                    // Whichever runs first, the holder leads its own group
                    // before the leader reports it.
                    libc::setpgid(holder, holder);
                    let pids = [libc::getpid(), holder];
                    let bytes = std::mem::size_of_val(&pids);
                    let written = libc::write(report_end.as_raw_fd(), pids.as_ptr().cast(), bytes);
                    if usize::try_from(written).ok() != Some(bytes) {
                        return Err(io::Error::last_os_error());
                    }
                    Ok(())
                });
            }
            EscapedHolder { report, pids: None }
        }

        /// The leader's pid, the holder's, and the holder's start, as the
        /// leader reported them (read once; it reports before its exec).
        fn pids(&mut self) -> (u32, u32, Option<u64>) {
            if let Some(pids) = self.pids {
                return pids;
            }
            let mut bytes = [0_u8; 2 * std::mem::size_of::<libc::pid_t>()];
            self.report.read_exact(&mut bytes).expect("the leader reports its pids");
            let (leader, holder) = bytes.split_at(std::mem::size_of::<libc::pid_t>());
            let pid = |bytes: &[u8]| {
                let pid = libc::pid_t::from_ne_bytes(bytes.try_into().expect("one pid_t"));
                assert!(pid > 0, "a reported pid is positive: {pid}");
                pid
            };
            let (leader, holder) = (pid(leader), pid(holder));
            // SAFETY: `getpgid` takes no pointers.
            let group = unsafe { libc::getpgid(holder) };
            // A holder that already ended has no group to read (-1).
            assert!(
                group < 0 || group == holder,
                "the holder {holder} is not outside the probe's group {leader}: it is in {group}"
            );
            let (leader, holder) = (leader.unsigned_abs(), holder.unsigned_abs());
            let start = process_lifecycle::tree::identity(holder).map(|identity| identity.start);
            let pids = (leader, holder, start);
            self.pids = Some(pids);
            pids
        }

        /// End the holder with SIGKILL, while its pid still names it.
        fn kill(&mut self) {
            let (_, holder, start) = self.pids();
            // A non-positive pid would name a group or every process.
            let Ok(pid) = libc::pid_t::try_from(holder) else { return };
            if pid > 0 && start.is_some() && process_lifecycle::tree::still_running(holder, start) {
                // SAFETY: `kill` takes no pointers; the pid was re-read with
                // the start it was found with just above.
                unsafe { libc::kill(pid, libc::SIGKILL) };
            }
        }
    }

    /// `CMSG_SPACE`/`CMSG_LEN`'s argument for one descriptor.
    #[cfg(any(target_os = "macos", target_os = "linux"))]
    const ONE_FD: libc::c_uint = std::mem::size_of::<libc::c_int>() as libc::c_uint;

    /// A child of THIS program, started by another of its threads, holding a
    /// probe's stderr in a process group of its own: one shape land-gate run
    /// 15 may have met (2026-10-21, `2ffb273abe`). libtest runs the tests on
    /// threads of one process. A `fork` another test makes holds every
    /// descriptor this process has until its exec, and on macOS std makes a
    /// pipe with `pipe` and only then sets `FD_CLOEXEC` (there is no
    /// `pipe2`), so a child spawned in between keeps the probe's write end
    /// across its exec for as long as it lives. Trust's std hands a child only
    /// its stdio since SP-1 (a7f474346f); the 7d5533b2 seal that run 15 built
    /// this crate with predates it.
    ///
    /// The fixture makes one on purpose. The leader's `pre_exec` hook passes
    /// its stderr (the probe's pipe) and its pid to a thread of this process
    /// over a socket (`SCM_RIGHTS`) and waits for an answer. That thread
    /// starts the holder ([`Holding`]) with the descriptor as its stderr and
    /// nothing else of this process open, closes its own copy, and answers;
    /// only then does the leader exec. The test ends the holder's group with
    /// SIGKILL.
    #[cfg(any(target_os = "macos", target_os = "linux"))]
    struct SiblingHolder {
        started: thread::JoinHandle<Option<(u32, Child)>>,
    }

    /// Who holds the probe's stream for a [`SiblingHolder`].
    #[cfg(any(target_os = "macos", target_os = "linux"))]
    #[derive(Clone, Copy)]
    enum Holding {
        /// A child of this program, `sleep`, leading a group of its own.
        Child,
        /// The background job of a child of this program (`sh -c 'sleep 120
        /// & exit 0'`, leading a group of its own), once that child has
        /// exited and before it is reaped: another probe's job during that
        /// probe's own post-exit wait. The job was re-parented out of this
        /// program's tree when the child exited, and is in the child's group.
        ExitedChildsJob,
    }

    #[cfg(any(target_os = "macos", target_os = "linux"))]
    impl SiblingHolder {
        /// Arm `command` (a `/bin/sh -c` probe) to have its stderr held by a
        /// process of this program, as `holding` says.
        fn arm(command: &mut Command, holding: Holding) -> Self {
            use std::os::fd::{AsRawFd as _, FromRawFd as _, OwnedFd};
            use std::os::unix::process::CommandExt as _;
            let mut ends: [libc::c_int; 2] = [-1, -1];
            // SAFETY: `ends` is the two-element array `socketpair` writes.
            let created =
                unsafe { libc::socketpair(libc::AF_UNIX, libc::SOCK_STREAM, 0, ends.as_mut_ptr()) };
            assert_eq!(created, 0, "the hand-over socket: {}", io::Error::last_os_error());
            for fd in ends {
                // SAFETY: both descriptors were just created here.
                unsafe { libc::fcntl(fd, libc::F_SETFD, libc::FD_CLOEXEC) };
            }
            // SAFETY: each descriptor was just created here and is owned once.
            let (here, leader_end) =
                unsafe { (OwnedFd::from_raw_fd(ends[0]), OwnedFd::from_raw_fd(ends[1])) };
            // SAFETY: the hook runs between fork and exec and makes only
            // async-signal-safe calls (`getpid`, `sendmsg`, `read`); it
            // allocates nothing: the message, its control buffer and the
            // answer are on the stack, and its errors are raw OS errors.
            unsafe {
                command.pre_exec(move || {
                    let pid = libc::getpid();
                    let mut iov = libc::iovec {
                        iov_base: (&raw const pid).cast_mut().cast(),
                        iov_len: std::mem::size_of::<libc::pid_t>(),
                    };
                    // u64s: aligned for the `cmsghdr` written into it.
                    let mut control = [0_u64; 8];
                    let mut message: libc::msghdr = std::mem::zeroed();
                    message.msg_iov = &raw mut iov;
                    message.msg_iovlen = 1;
                    message.msg_control = control.as_mut_ptr().cast();
                    message.msg_controllen = libc::CMSG_SPACE(ONE_FD) as _;
                    let header = libc::CMSG_FIRSTHDR(&raw const message);
                    if header.is_null() {
                        return Err(io::Error::from_raw_os_error(libc::EINVAL));
                    }
                    (*header).cmsg_level = libc::SOL_SOCKET;
                    (*header).cmsg_type = libc::SCM_RIGHTS;
                    (*header).cmsg_len = libc::CMSG_LEN(ONE_FD) as _;
                    libc::CMSG_DATA(header)
                        .cast::<libc::c_int>()
                        .write_unaligned(libc::STDERR_FILENO);
                    let sent = libc::sendmsg(leader_end.as_raw_fd(), &raw const message, 0);
                    if usize::try_from(sent).ok() != Some(std::mem::size_of::<libc::pid_t>()) {
                        return Err(io::Error::last_os_error());
                    }
                    // The holder is in place once the answer comes; end of
                    // file means the test's thread gave up.
                    let mut answer = 0_u8;
                    if libc::read(leader_end.as_raw_fd(), (&raw mut answer).cast(), 1) != 1 {
                        return Err(io::Error::from_raw_os_error(libc::EPIPE));
                    }
                    Ok(())
                });
            }
            let started = thread::spawn(move || {
                let (leader, held) = receive_descriptor(&here)?;
                let (program, args): (&str, &[&str]) = match holding {
                    Holding::Child => ("/bin/sleep", &["120"]),
                    Holding::ExitedChildsJob => ("/bin/sh", &["-c", "sleep 120 & exit 0"]),
                };
                let mut starting = Command::new(program);
                starting.args(args).stdin(Stdio::null()).stdout(Stdio::null()).stderr(held);
                starting.process_group(0);
                // SAFETY: the hook runs between fork and exec and calls only
                // `close`, which is async-signal-safe; it allocates nothing.
                unsafe {
                    starting.pre_exec(|| {
                        for fd in 3..1024 {
                            libc::close(fd);
                        }
                        Ok(())
                    });
                }
                let holder = starting.spawn().expect("start the holder");
                // This process's own copy of the stream goes with the command.
                drop(starting);
                if let Holding::ExitedChildsJob = holding {
                    // The child has exited (unreaped) before the leader execs.
                    let hang = Instant::now() + HANG;
                    while process_lifecycle::tree::still_running(holder.id(), None) {
                        assert!(Instant::now() < hang, "the holder's shell never exited");
                        thread::sleep(Duration::from_millis(10));
                    }
                }
                let answer = 1_u8;
                // SAFETY: one byte, read from the stack.
                let answered =
                    unsafe { libc::write(here.as_raw_fd(), (&raw const answer).cast(), 1) };
                assert_eq!(answered, 1, "answer the leader: {}", io::Error::last_os_error());
                Some((leader, holder))
            });
            SiblingHolder { started }
        }

        /// From another thread: once the probe's leader has exited, let the
        /// holder keep the stream a second longer (well past the 250 ms the
        /// probe gives its pipes), then end it.
        fn release_after_the_leader_exits(self) -> thread::JoinHandle<()> {
            thread::spawn(move || {
                let Some((leader, holder)) = self.started.join().expect("the hand-over thread")
                else {
                    return;
                };
                wait_for_exit(leader);
                thread::sleep(Duration::from_secs(1));
                end_group(holder);
            })
        }

        /// End the holder now.
        fn release(self) {
            if let Some((_, holder)) = self.started.join().expect("the hand-over thread") {
                end_group(holder);
            }
        }
    }

    /// SIGKILL to the group `holder` leads, then reap it. It leads its own
    /// group and is not yet reaped, so its pid still names that group.
    #[cfg(any(target_os = "macos", target_os = "linux"))]
    fn end_group(mut holder: Child) {
        let group = libc::pid_t::try_from(holder.id()).unwrap_or(0);
        if group > 0 {
            // SAFETY: `kill` takes no pointers; a positive pid negated names
            // exactly the group it leads.
            unsafe { libc::kill(-group, libc::SIGKILL) };
        }
        let _ = holder.wait();
    }

    /// The leader's pid and the descriptor it passed over `socket`; `None`
    /// when the socket ended first (the probe never started, and its command,
    /// with the other end, was dropped).
    #[cfg(any(target_os = "macos", target_os = "linux"))]
    fn receive_descriptor(socket: &std::os::fd::OwnedFd) -> Option<(u32, std::os::fd::OwnedFd)> {
        use std::os::fd::{AsRawFd as _, FromRawFd as _, OwnedFd};
        let mut pid: libc::pid_t = 0;
        let mut iov = libc::iovec {
            iov_base: (&raw mut pid).cast(),
            iov_len: std::mem::size_of::<libc::pid_t>(),
        };
        let mut control = [0_u64; 8];
        // SAFETY: an all-zero `msghdr` is valid: null pointers, zero lengths.
        let mut message: libc::msghdr = unsafe { std::mem::zeroed() };
        message.msg_iov = &raw mut iov;
        message.msg_iovlen = 1;
        message.msg_control = control.as_mut_ptr().cast();
        message.msg_controllen = std::mem::size_of_val(&control) as _;
        // SAFETY: `message` points at `iov` and `control`, which outlive the call.
        let received = unsafe { libc::recvmsg(socket.as_raw_fd(), &raw mut message, 0) };
        if received == 0 {
            return None;
        }
        assert_eq!(
            usize::try_from(received).ok(),
            Some(std::mem::size_of::<libc::pid_t>()),
            "the leader's pid: {}",
            io::Error::last_os_error()
        );
        assert_eq!(message.msg_flags & libc::MSG_CTRUNC, 0, "the descriptor fit its buffer");
        // SAFETY: `message` is what `recvmsg` filled, its control in `control`.
        let header = unsafe { libc::CMSG_FIRSTHDR(&raw const message) };
        assert!(!header.is_null(), "the leader's message carries a descriptor");
        // SAFETY: a non-null header inside `control`, as `recvmsg` wrote it.
        let (level, kind) = unsafe { ((*header).cmsg_level, (*header).cmsg_type) };
        assert!(level == libc::SOL_SOCKET && kind == libc::SCM_RIGHTS, "an SCM_RIGHTS message");
        // SAFETY: an SCM_RIGHTS header's data is the descriptor it passed,
        // now this process's, owned once here.
        let held = unsafe {
            let fd = libc::CMSG_DATA(header).cast::<libc::c_int>().read_unaligned();
            libc::fcntl(fd, libc::F_SETFD, libc::FD_CLOEXEC);
            OwnedFd::from_raw_fd(fd)
        };
        let leader = u32::try_from(pid).ok().filter(|&leader| leader > 0);
        Some((leader.expect("the leader's pid is positive"), held))
    }

    /// A descendant of the probe that leaves its process group and keeps a
    /// stream open after the leader exits is a background descendant, and the
    /// probe fails at once: the stop reaches nothing of it, and it is in
    /// neither the probe's reach nor this program's tree. 2ffb273abe refused
    /// it; 6184d7081d waited for it until the probe's deadline and accepted
    /// whatever it wrote meanwhile (review of 2026-10-21). The holder is
    /// ended only after the verdict, so a wait reaches the deadline.
    #[cfg(any(target_os = "macos", target_os = "linux"))]
    #[test]
    fn a_descendant_that_leaves_the_probes_group_holding_a_stream_is_refused() {
        let mut probe = Command::new("/bin/sh");
        probe.args(["-c", "printf bounded"]);
        let mut holder = EscapedHolder::arm(&mut probe);
        let result = output(&mut probe, "escaped-holder probe", 1024, Duration::from_secs(2));
        // The report pipe's write end goes with the command: a probe that
        // never started ends the holder's read instead of hanging it.
        drop(probe);
        holder.kill();
        let error = result.expect_err("a stream an escaped descendant holds fails the probe");
        assert!(error.contains("background descendant"), "{error}");
        assert!(error.contains("left its process group"), "{error}");
    }

    /// Run 15's failure, made on purpose: the probe's leader exits with its
    /// output written, and its stderr stays open, held by a child another
    /// thread of this program started, which lets go a second later. That
    /// is not the probe's doing, so the probe waits for it (bounded by its own
    /// deadline, a hang detector) and returns its output. It must not blame
    /// the probe for a background descendant, and must not report the stop of
    /// a group down to its unreaped leader (EPERM on macOS) as a failure:
    /// before 2026-10-21 it did both ("successful probe stderr remained open
    /// and its process group could not be terminated: Operation not permitted
    /// (os error 1)").
    #[cfg(any(target_os = "macos", target_os = "linux"))]
    #[test]
    fn a_stream_held_by_another_child_of_this_program_is_waited_for_not_blamed_on_the_probe() {
        let mut probe = Command::new("/bin/sh");
        probe.args(["-c", "printf bounded"]);
        let releaser =
            SiblingHolder::arm(&mut probe, Holding::Child).release_after_the_leader_exits();
        let result = output(&mut probe, "sibling-held probe", 1024, Duration::from_secs(2));
        // The hand-over socket's other end goes with the command: a probe
        // that never started ends the hand-over instead of hanging it.
        drop(probe);
        releaser.join().expect("the releaser ends the holder");
        let output = result.expect("a probe whose stream only this program held is accepted");
        assert!(output.status.success());
        assert_eq!(output.stdout, b"bounded");
    }

    /// As above, held by the background job of a child of this program after
    /// that child has exited and before it is reaped ([`Holding::ExitedChildsJob`]):
    /// another probe's job, which leaked this probe's write end through its
    /// leader, during that probe's own post-exit wait. The job was re-parented
    /// out of this program's tree when that child exited, but is in that
    /// child's group, which that child's own stop reaches. That is not this
    /// probe's doing either, and is waited for.
    #[cfg(any(target_os = "macos", target_os = "linux"))]
    #[test]
    fn a_stream_held_in_the_group_of_an_exited_child_of_this_program_is_waited_for() {
        let mut probe = Command::new("/bin/sh");
        probe.args(["-c", "printf bounded"]);
        let releaser = SiblingHolder::arm(&mut probe, Holding::ExitedChildsJob)
            .release_after_the_leader_exits();
        let result = output(&mut probe, "exited-sibling-group probe", 1024, Duration::from_secs(2));
        drop(probe);
        releaser.join().expect("the releaser ends the holder");
        let output = result.expect("a probe whose stream only this program held is accepted");
        assert_eq!(output.stdout, b"bounded");
    }

    /// As above, with a live member left in the probe's group that holds
    /// neither stream: the shell points its own stdio at the null device
    /// before it starts the job, so the member never had them. A live member
    /// is not a holder; the stop after the capture removes it, as the
    /// redirected-background case pins.
    #[cfg(any(target_os = "macos", target_os = "linux"))]
    #[test]
    fn a_live_group_member_holding_no_stream_is_not_blamed_for_a_holder_of_this_program() {
        let mut probe = Command::new("/bin/sh");
        probe.args(["-c", "printf bounded; exec >/dev/null 2>&1; sleep 30 & exit 0"]);
        let releaser =
            SiblingHolder::arm(&mut probe, Holding::Child).release_after_the_leader_exits();
        let result = output(&mut probe, "member-and-sibling probe", 1024, Duration::from_secs(2));
        drop(probe);
        releaser.join().expect("the releaser ends the holder");
        let output = result.expect("a live member that holds no stream is not a pipe holder");
        assert_eq!(output.stdout, b"bounded");
    }

    /// The wait for a holder of this program is bounded: one that never lets
    /// go fails the probe closed at the probe's own deadline. The error names
    /// a timeout either way (the leader's or the stream's), never a
    /// background descendant or a stop that could not be made.
    #[cfg(any(target_os = "macos", target_os = "linux"))]
    #[test]
    fn a_stream_held_by_this_program_past_the_deadline_fails_closed() {
        let mut probe = Command::new("/bin/sh");
        probe.args(["-c", "printf bounded"]);
        let holder = SiblingHolder::arm(&mut probe, Holding::Child);
        let result = output_with_exact_deadline(
            &mut probe,
            "sibling-held probe",
            1024,
            Duration::from_secs(3),
        );
        drop(probe);
        holder.release();
        let error = result.expect_err("a stream that never closes must fail the probe");
        assert!(error.contains("timeout"), "{error}");
        assert!(!error.contains("background descendant"), "{error}");
        assert!(!error.contains("could not be terminated"), "{error}");
    }

    /// The kernel reports a pipe hung up exactly when no write end is left
    /// anywhere, bytes still buffered or not: what tells a stream whose
    /// reader has yet to run from one some process still holds.
    ///
    /// "Anywhere" includes a child another test of this binary is forking
    /// right now: until its exec it holds a copy of every descriptor this
    /// process has, this pipe's write end included (measured: the whole
    /// binary, run in parallel, once read the pipe as still written just
    /// after this test closed its last end). So the hang-up is waited for,
    /// under a one-minute hang detector; once seen it never reverts.
    #[cfg(unix)]
    #[test]
    fn a_pipe_reads_as_hung_up_exactly_when_no_write_end_is_left() {
        use std::io::Write as _;
        let (mut reader, mut writer) = io::pipe().expect("pipe");
        let watch = watch_of(&reader).expect("duplicate the read end");
        assert_eq!(writer_remains(&watch), Some(true), "a write end is open, nothing written");
        writer.write_all(b"buffered").expect("write");
        assert_eq!(writer_remains(&watch), Some(true), "a write end is open, bytes buffered");
        let second = writer.try_clone().expect("duplicate the write end");
        drop(writer);
        assert_eq!(writer_remains(&watch), Some(true), "one of two write ends is open");
        drop(second);
        let hang = Instant::now() + Duration::from_secs(60);
        while writer_remains(&watch) != Some(false) {
            assert!(Instant::now() < hang, "the pipe never hung up once no write end was left");
            thread::sleep(Duration::from_millis(10));
        }
        assert_eq!(writer_remains(&watch), Some(false), "no write end is left, bytes buffered");
        let mut drained = Vec::new();
        reader.read_to_end(&mut drained).expect("drain");
        assert_eq!(drained, b"buffered");
        assert_eq!(writer_remains(&watch), Some(false), "no write end is left, nothing buffered");
    }

    #[test]
    fn probe_deadlines_are_production_exact_and_stretch_only_under_the_test_harness() {
        for production in [
            Duration::from_millis(1),
            Duration::from_secs(5),
            Duration::from_secs(10),
            Duration::from_secs(5 * 60),
            Duration::from_secs(12 * 60 * 60),
        ] {
            assert_eq!(
                stretched_probe_deadline(production, false),
                production,
                "a production build must use the caller's probe deadline unchanged"
            );
            let stretched = stretched_probe_deadline(production, true);
            assert_eq!(stretched, production * TEST_HARNESS_DEADLINE_SCALE);
            assert!(
                stretched > production,
                "the harness deadline must never be shorter than the production one"
            );
        }
        assert_eq!(
            stretched_probe_deadline(Duration::MAX, true),
            Duration::MAX,
            "an unrepresentable stretch must saturate rather than wrap into a shorter bound"
        );
        assert_eq!(
            resolve_probe_deadline(Duration::from_secs(10)),
            stretched_probe_deadline(Duration::from_secs(10), cfg!(test))
        );
    }

    #[cfg(unix)]
    #[test]
    fn output_applies_the_harness_stretch_and_still_fails_a_nonterminating_probe_closed() {
        let requested = Duration::from_millis(2);
        let effective = resolve_probe_deadline(requested);
        let mut nonterminating = Command::new("/bin/sh");
        nonterminating.args(["-c", "while :; do :; done"]);
        let started = Instant::now();
        let error = output(&mut nonterminating, "stretched probe", 1024, requested)
            .expect_err("a nonterminating child must still fail closed under the harness");
        assert!(error.contains("timeout"), "{error}");
        // Asserting a lower bound on elapsed time is monotone in the safe
        // direction: contention can only make the observed elapsed time longer,
        // so this assertion cannot itself become a wall-clock flake.
        assert!(
            started.elapsed() >= effective,
            "output did not resolve {requested:?} through the harness stretch to {effective:?}"
        );
    }
}
