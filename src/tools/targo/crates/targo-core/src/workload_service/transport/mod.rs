//! One bounded owner of the actual service input and framed output. ACKs only
//! continue the original graph; stop intent uses the existing queue protocol.
use std::fs::File;
use std::io::{self, Read as _, Write as _};
use std::os::fd::{AsFd as _, AsRawFd as _};
use std::os::unix::{fs::FileTypeExt as _, net::UnixStream};
use std::sync::{
    Arc, Mutex, TryLockError,
    atomic::{AtomicBool, Ordering},
    mpsc::{self, Receiver, TrySendError},
};
use std::time::{Duration, Instant};
use trust_resource_controller::workload::{
    Continuation, Decision,
    service::{Binding, Stop},
};

const PREFIX_BYTES: usize = 64 * 1024;
fn invalid(reason: impl Into<String>) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, reason.into())
}
fn lock<T>(mutex: &Mutex<T>, deadline: Instant) -> io::Result<std::sync::MutexGuard<'_, T>> {
    loop {
        if Instant::now() >= deadline {
            return Err(io::ErrorKind::TimedOut.into());
        }
        match mutex.try_lock() {
            Ok(value) => return Ok(value),
            Err(TryLockError::Poisoned(_)) => {
                return Err(invalid("original service owner poisoned"));
            }
            Err(TryLockError::WouldBlock) => std::thread::sleep(Duration::from_millis(1)),
        }
    }
}
fn poll(
    file: &File,
    events: i16,
    deadline: Instant,
    stop: Option<&AtomicBool>,
    phase: Option<&Mutex<Option<Instant>>>,
) -> io::Result<()> {
    loop {
        if stop.is_some_and(|stop| stop.load(Ordering::Acquire)) {
            return Err(io::ErrorKind::Interrupted.into());
        }
        let effective = match phase {
            Some(phase) => lock(phase, deadline)?.unwrap_or(deadline).min(deadline),
            None => deadline,
        };
        let remaining = effective.saturating_duration_since(Instant::now());
        if remaining.is_zero() {
            return Err(io::ErrorKind::TimedOut.into());
        }
        let mut pfd = libc::pollfd {
            fd: file.as_raw_fd(),
            events,
            revents: 0,
        };
        let millis = remaining.as_millis().clamp(1, 50) as libc::c_int;
        // SAFETY: one borrowed live description, initialized writable pollfd.
        let result = unsafe { libc::poll(&mut pfd, 1, millis) };
        if result < 0 {
            let error = io::Error::last_os_error();
            if error.kind() == io::ErrorKind::Interrupted {
                continue;
            }
            return Err(error);
        }
        if result > 0 {
            if pfd.revents & libc::POLLNVAL != 0 {
                return Err(invalid("original service description closed"));
            }
            // HUP is delivered to read as physical EOF, never fabricated by
            // polling. Writable errors similarly remain actual write errors.
            if pfd.revents & (events | libc::POLLHUP | libc::POLLERR) != 0 {
                return Ok(());
            }
        }
    }
}

pub(crate) struct Input {
    file: File,
    prefix: Vec<u8>,
    seen: u64,
    phase_deadline: Option<Arc<Mutex<Option<Instant>>>>,
}
impl Input {
    pub(crate) fn observation(&self) -> (Vec<u8>, u64) {
        (self.prefix.clone(), self.seen)
    }
    pub(crate) fn phase_deadline(&mut self, deadline: Arc<Mutex<Option<Instant>>>) {
        self.phase_deadline = Some(deadline);
    }
    pub(crate) fn capture_stdin() -> io::Result<Self> {
        let file = File::from(std::io::stdin().as_fd().try_clone_to_owned()?);
        let kind = file.metadata()?.file_type();
        if !kind.is_fifo() && !kind.is_socket() {
            return Err(invalid(
                "interactive workload requires its actual native pipe/socket input",
            ));
        }
        let null = File::open("/dev/null")?;
        // SAFETY: fixed startup has consumed bootstrap descriptors; contain
        // only this root's stdin before project code/threads/children. The
        // original same pipe/socket remains held privately and close-on-exec.
        if unsafe { libc::dup2(null.as_raw_fd(), 0) } != 0 {
            return Err(io::Error::last_os_error());
        }
        Ok(Self {
            file,
            prefix: Vec::new(),
            seen: 0,
            phase_deadline: None,
        })
    }
    #[cfg(test)]
    pub(crate) fn from_stream(stream: UnixStream) -> Self {
        Self {
            file: File::from(std::os::fd::OwnedFd::from(stream)),
            prefix: Vec::new(),
            seen: 0,
            phase_deadline: None,
        }
    }
    fn exact(
        &mut self,
        mut bytes: &mut [u8],
        deadline: Instant,
        stop: Option<&AtomicBool>,
    ) -> io::Result<()> {
        while !bytes.is_empty() {
            poll(
                &self.file,
                libc::POLLIN,
                deadline,
                stop,
                self.phase_deadline.as_deref(),
            )?;
            let count = match self.file.read(bytes) {
                Err(error) if error.kind() == io::ErrorKind::Interrupted => continue,
                result => result?,
            };
            if count == 0 {
                return Err(io::ErrorKind::UnexpectedEof.into());
            }
            self.seen = self
                .seen
                .checked_add(count as u64)
                .ok_or_else(|| invalid("service input count overflow"))?;
            let keep = count.min(PREFIX_BYTES.saturating_sub(self.prefix.len()));
            self.prefix.extend_from_slice(&bytes[..keep]);
            bytes = &mut bytes[count..];
        }
        Ok(())
    }
    pub(crate) fn frame(
        &mut self,
        deadline: Instant,
        stop: Option<&AtomicBool>,
    ) -> io::Result<Vec<u8>> {
        let mut length = [0; 4];
        self.exact(&mut length, deadline, stop)?;
        let length = u32::from_be_bytes(length) as usize;
        if length == 0 || length > trust_resource_controller::MAX_PAYLOAD {
            return Err(invalid("service frame exceeds its original finite bound"));
        }
        let mut bytes = Vec::new();
        bytes.try_reserve_exact(length).map_err(io::Error::other)?;
        bytes.resize(length, 0);
        self.exact(&mut bytes, deadline, stop)?;
        Ok(bytes)
    }
}

pub(crate) struct Output {
    file: Mutex<File>,
    deadline: Instant,
    failed: AtomicBool,
    cancelled: Arc<AtomicBool>,
}
impl Output {
    pub(crate) fn capture_stdout(
        deadline: Instant,
        cancelled: Arc<AtomicBool>,
    ) -> io::Result<Arc<Self>> {
        let file = File::from(std::io::stdout().as_fd().try_clone_to_owned()?);
        let kind = file.metadata()?.file_type();
        if !kind.is_fifo() && !kind.is_socket() {
            return Err(invalid(
                "interactive workload requires its actual original pipe/socket output",
            ));
        }
        // The private service exclusively owns this original protocol writer;
        // no arbitrary child/config code may write the stream. Nonblocking IO
        // prevents a large framed write from outrunning the original deadline.
        let flags = unsafe { libc::fcntl(file.as_raw_fd(), libc::F_GETFL) };
        if flags < 0
            || unsafe { libc::fcntl(file.as_raw_fd(), libc::F_SETFL, flags | libc::O_NONBLOCK) } < 0
        {
            return Err(io::Error::last_os_error());
        }
        let null = std::fs::OpenOptions::new().write(true).open("/dev/null")?;
        // SAFETY: only this fixed service owns stdout before project/config
        // code. Keep the original pipe private/CLOEXEC; ordinary prints and
        // inherited stdout cannot corrupt its framed protocol.
        if unsafe { libc::dup2(null.as_raw_fd(), 1) } != 1 {
            return Err(io::Error::last_os_error());
        }
        Ok(Arc::new(Self {
            file: Mutex::new(file),
            deadline,
            failed: AtomicBool::new(false),
            cancelled,
        }))
    }
    #[cfg(test)]
    fn from_stream(stream: UnixStream, deadline: Instant) -> Arc<Self> {
        stream.set_nonblocking(true).unwrap();
        Arc::new(Self {
            file: Mutex::new(File::from(std::os::fd::OwnedFd::from(stream))),
            deadline,
            failed: AtomicBool::new(false),
            cancelled: Arc::new(AtomicBool::new(false)),
        })
    }
    pub(crate) fn frame(&self, bytes: &[u8], deadline: Instant) -> io::Result<()> {
        let result = (|| {
            if self.failed.load(Ordering::Acquire)
                || self.cancelled.load(Ordering::Acquire)
                || bytes.is_empty()
                || bytes.len() > trust_resource_controller::MAX_PAYLOAD
            {
                return Err(invalid(
                    "original service output unusable or frame unbounded",
                ));
            }
            let deadline = deadline.min(self.deadline);
            let mut original = lock(&self.file, deadline)?;
            let length = u32::try_from(bytes.len())
                .map_err(|_| invalid("service frame length overflow"))?
                .to_be_bytes();
            for mut part in [&length[..], bytes] {
                while !part.is_empty() {
                    poll(
                        &original,
                        libc::POLLOUT,
                        deadline,
                        Some(&self.cancelled),
                        None,
                    )?;
                    let count = match original.write(part) {
                        Err(error)
                            if matches!(
                                error.kind(),
                                io::ErrorKind::Interrupted | io::ErrorKind::WouldBlock
                            ) =>
                        {
                            continue;
                        }
                        result => result?,
                    };
                    if count == 0 {
                        return Err(io::ErrorKind::WriteZero.into());
                    }
                    part = &part[count..];
                }
            }
            Ok(())
        })();
        if result.is_err() {
            self.failed.store(true, Ordering::Release);
        }
        result
    }
}

struct Expected {
    sequence: u64,
    sha256: [u8; 32],
}
struct State {
    expected: Option<Expected>,
    failure: Option<String>,
    stopped: bool,
    prefix: Vec<u8>,
    bytes_seen: u64,
}
pub(crate) struct Control {
    binding: Binding,
    state: Arc<Mutex<State>>,
    received: Receiver<Decision>,
    pub(super) cancelled: Arc<AtomicBool>,
    stopping: Arc<AtomicBool>,
    thread: Option<std::thread::JoinHandle<()>>,
    next_sequence: u64,
    phase_deadline: Arc<Mutex<Option<Instant>>>,
    compile_started: bool,
}
#[derive(Clone, Copy)]
enum Protocol {
    Workload,
    NativeJob(trust_resource_controller::native_job::service::Binding),
}
impl Control {
    pub(crate) fn start_native_job(
        binding: trust_resource_controller::native_job::service::Binding,
        input: Input,
        deadline: Instant,
        cancelled: Arc<AtomicBool>,
    ) -> io::Result<(Self, crate::context::root_control::RootControl)> {
        // Common equality DATA only; Protocol keeps native111 framing distinct
        // and never accepts legacy continuations for this original endpoint.
        let common = Binding {
            root_attempt: binding.root_attempt,
            invocation_sha256: binding.invocation_sha256,
        };
        Self::start_protocol(
            common,
            input,
            deadline,
            cancelled,
            Protocol::NativeJob(binding),
        )
    }
    /// Internal actual cancellation socket uses the existing RootControl C/A
    /// protocol; it grants no CPU, output, execution or new root authority.
    pub(super) fn start(
        binding: Binding,
        input: Input,
        deadline: Instant,
        cancelled: Arc<AtomicBool>,
    ) -> io::Result<(Self, crate::context::root_control::RootControl)> {
        Self::start_protocol(binding, input, deadline, cancelled, Protocol::Workload)
    }
    fn start_protocol(
        binding: Binding,
        mut input: Input,
        deadline: Instant,
        cancelled: Arc<AtomicBool>,
        protocol: Protocol,
    ) -> io::Result<(Self, crate::context::root_control::RootControl)> {
        let (queue, mut cancel) = UnixStream::pair()?;
        cancel.set_nonblocking(true)?;
        let queue = crate::context::root_control::RootControl::from_workload_stream(queue)?;
        let phase_deadline = Arc::new(Mutex::new(None));
        input.phase_deadline = Some(phase_deadline.clone());
        let state = Arc::new(Mutex::new(State {
            expected: None,
            failure: None,
            stopped: false,
            prefix: input.prefix.clone(),
            bytes_seen: input.seen,
        }));
        let (send, received) = mpsc::sync_channel(1);
        let stopping = Arc::new(AtomicBool::new(false));
        let original = state.clone();
        let done = stopping.clone();
        let signalled = cancelled.clone();
        let bind = binding.clone();
        let thread = std::thread::Builder::new()
            .name("targo-workload-input".into())
            .spawn(move || {
                let outcome = (|| -> io::Result<()> {
                    loop {
                        let before = input.seen;
                        let bytes = match input.frame(deadline, Some(&done)) {
                            Err(_) if done.load(Ordering::Acquire) => {
                                return if input.seen == before {
                                    Ok(())
                                } else {
                                    Err(invalid(
                                        "original service input stopped within a partial frame",
                                    ))
                                };
                            }
                            Err(error)
                                if error.kind() == io::ErrorKind::UnexpectedEof
                                    && lock(&original, deadline)?.stopped =>
                            {
                                return Ok(());
                            }
                            result => result?,
                        };
                        {
                            let mut state = lock(&original, deadline)?;
                            state.prefix = input.prefix.clone();
                            state.bytes_seen = input.seen;
                        }
                        let stop = match protocol {
                            Protocol::Workload => Stop::decode(&bytes, &bind).is_ok(),
                            Protocol::NativeJob(binding) => {
                                trust_resource_controller::native_job::service::Stop::decode(
                                    &bytes, binding,
                                )
                                .is_ok()
                            }
                        };
                        if stop {
                            let mut state = lock(&original, deadline)?;
                            if state.stopped {
                                return Err(invalid("duplicate original workload stop"));
                            }
                            state.stopped = true;
                            signalled.store(true, Ordering::Release);
                            cancel.write_all(b"C")?;
                            // No fabricated queue acknowledgement or native terminal.
                            continue;
                        }
                        if matches!(protocol, Protocol::NativeJob(_)) {
                            return Err(invalid(
                                "native job input accepted no legacy checkpoint/continuation frame",
                            ));
                        }
                        let ack = Continuation::decode(&bytes)?;
                        let mut state = lock(&original, deadline)?;
                        let expected = state.expected.take().ok_or_else(|| {
                            invalid("workload continuation has no actual pending checkpoint")
                        })?;
                        ack.check_binding(
                            bind.invocation_sha256,
                            bind.root_attempt,
                            expected.sequence,
                            expected.sha256,
                        )?;
                        if state.stopped {
                            return Err(invalid("workload continuation after original stop"));
                        }
                        if ack.decision == Decision::Stop {
                            state.stopped = true;
                            signalled.store(true, Ordering::Release);
                            cancel.write_all(b"C")?;
                        }
                        match send.try_send(ack.decision) {
                            Ok(()) => {}
                            Err(TrySendError::Full(_)) => {
                                return Err(invalid("workload continuation queue overflow"));
                            }
                            Err(TrySendError::Disconnected(_)) => return Ok(()),
                        }
                    }
                })();
                // Include every actual read, even when finalization interrupted
                // a still-open partial frame. No EOF/retirement is inferred.
                if let Ok(mut state) = original.lock() {
                    state.prefix = input.prefix;
                    state.bytes_seen = input.seen;
                }
                if let Err(error) = outcome {
                    // Preserve actual received input prefixes even on malformed or
                    // incomplete frames. EOF is cancellation intent, not retirement.
                    if let Ok(mut state) = original.lock() {
                        state.failure = Some(error.to_string());
                    }
                    signalled.store(true, Ordering::Release);
                    let _ = cancel.write_all(b"C");
                }
            })?;
        Ok((
            Self {
                binding,
                state,
                received,
                cancelled,
                stopping,
                thread: Some(thread),
                next_sequence: 1,
                phase_deadline,
                compile_started: false,
            },
            queue,
        ))
    }
    pub(super) fn expect(
        &mut self,
        sequence: u64,
        sha256: [u8; 32],
        deadline: Instant,
    ) -> io::Result<()> {
        if sequence != self.next_sequence {
            return Err(invalid(
                "workload checkpoint does not continue the original graph sequence",
            ));
        }
        let mut state = lock(&self.state, deadline)?;
        if self.cancelled.load(Ordering::Acquire)
            || state.failure.is_some()
            || state.stopped
            || state.expected.is_some()
        {
            return Err(invalid(
                "original workload control cannot arm another checkpoint",
            ));
        }
        // Validate the fixed population bound without interpreting ACK data as
        // permission. The queue/phase/output owner remains independently live.
        Continuation {
            invocation_sha256: self.binding.invocation_sha256,
            root_attempt: self.binding.root_attempt,
            checkpoint: sequence,
            checkpoint_sha256: sha256,
            decision: Decision::Continue,
        }
        .validate()?;
        state.expected = Some(Expected { sequence, sha256 });
        self.next_sequence += 1;
        Ok(())
    }
    pub(super) fn begin_compile(&mut self, deadline: Instant) -> io::Result<()> {
        let mut phase = self
            .phase_deadline
            .lock()
            .map_err(|_| invalid("original compiler deadline owner poisoned"))?;
        if self.cancelled.load(Ordering::Acquire)
            || self.compile_started
            || phase.is_some()
            || self.next_sequence != 1
        {
            return Err(invalid("original compiler phase cannot begin again"));
        }
        *phase = Some(deadline);
        self.compile_started = true;
        Ok(())
    }
    pub(crate) fn begin_native_node(&mut self, deadline: Instant) -> io::Result<()> {
        let mut phase = self
            .phase_deadline
            .lock()
            .map_err(|_| invalid("native node deadline owner poisoned"))?;
        if self.cancelled.load(Ordering::Acquire) || phase.is_some() {
            return Err(invalid("native node deadline overlaps another active node"));
        }
        *phase = Some(deadline);
        Ok(())
    }
    pub(crate) fn end_native_node(&mut self) -> io::Result<()> {
        self.phase_deadline
            .lock()
            .map_err(|_| invalid("native node deadline owner poisoned"))?
            .take()
            .ok_or_else(|| invalid("native node deadline has no actual active interval"))?;
        Ok(())
    }
    pub(super) fn compiler_retired(&mut self) -> io::Result<()> {
        self.phase_deadline
            .lock()
            .map_err(|_| invalid("original compiler deadline owner poisoned"))?
            .take()
            .ok_or_else(|| invalid("original compiler deadline was not active"))?;
        Ok(())
    }
    pub(super) fn wait(&mut self, deadline: Instant) -> io::Result<Decision> {
        loop {
            if Instant::now() >= deadline {
                return Err(io::ErrorKind::TimedOut.into());
            }
            match self.received.recv_timeout(
                deadline
                    .saturating_duration_since(Instant::now())
                    .min(Duration::from_millis(50)),
            ) {
                Ok(value) => return Ok(value),
                Err(mpsc::RecvTimeoutError::Disconnected) => {
                    return Err(invalid("original workload continuation owner ended"));
                }
                Err(mpsc::RecvTimeoutError::Timeout) => {}
            }
            if self.cancelled.load(Ordering::Acquire) {
                return Err(invalid(
                    "original workload stopped while awaiting continuation",
                ));
            }
        }
    }
    pub(crate) fn observation(&self) -> io::Result<(Vec<u8>, u64, Option<String>, bool)> {
        let state = self
            .state
            .lock()
            .map_err(|_| invalid("original service input owner poisoned"))?;
        Ok((
            state.prefix.clone(),
            state.bytes_seen,
            state.failure.clone(),
            state.stopped,
        ))
    }
    pub(crate) fn finish(&mut self) -> io::Result<()> {
        self.stopping.store(true, Ordering::Release);
        if self
            .thread
            .take()
            .is_some_and(|thread| thread.join().is_err())
        {
            self.state
                .lock()
                .map_err(|_| invalid("original service input owner poisoned"))?
                .failure
                .get_or_insert("original service input owner panicked".into());
        }
        let state = self
            .state
            .lock()
            .map_err(|_| invalid("original service input owner poisoned"))?;
        if let Some(reason) = &state.failure {
            return Err(invalid(reason.clone()));
        }
        Ok(())
    }
}
impl Drop for Control {
    fn drop(&mut self) {
        self.stopping.store(true, Ordering::Release);
        if let Some(thread) = self.thread.take() {
            let _ = thread.join();
        }
    }
}

#[cfg(test)]
mod tests;
