//! Local ownership bookend for in-process protected work.
//!
//! This registry grants no execution, CPU, GNU, memory, SDK or release authority.
//! Registration precedes an independently admitted launch and retains its actual
//! Child/readers/JoinHandle. LocalJoinedScope proves only these local joins. A
//! separate original Host/member/loan/foreign-scope closure is still required.

use std::fmt;
use std::fs::File;
use std::io::{self, Read, Seek};
use std::os::fd::AsRawFd;
use std::process::{Child, ChildStderr, ChildStdout, Command, ExitStatus, Output};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Mutex, MutexGuard, Weak};
use std::thread::{self, JoinHandle};
use std::time::{Duration, Instant};

use super::WithheldLease;

/// Opaque equality observation, with no constructor from bytes, paths or FDs.
#[derive(Clone)]
pub struct ScopeIdentity(Arc<()>);

impl PartialEq for ScopeIdentity {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.0, &other.0)
    }
}
impl Eq for ScopeIdentity {}
impl fmt::Debug for ScopeIdentity {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("ScopeIdentity").finish_non_exhaustive()
    }
}

#[derive(PartialEq)]
enum Phase {
    Open,
    Sealed,
    Joined,
}

struct State {
    phase: Phase,
    failure: Option<String>,
    children: Vec<Arc<ChildSlot>>,
    readers: Vec<Arc<ReaderSlot>>,
    workers: Vec<Arc<WorkerSlot>>,
    native_scopes: Vec<Arc<thread_scope::NativeScope>>,
}

struct Inner {
    original: Arc<WithheldLease>,
    identity: ScopeIdentity,
    deadline: Instant,
    state: Mutex<State>,
}

impl Inner {
    fn state(&self) -> io::Result<MutexGuard<'_, State>> {
        self.state.lock().map_err(|_| io::Error::other("protected scope poisoned"))
    }

    fn check(&self) -> io::Result<()> {
        let result = (|| {
            before(self.deadline)?;
            self.original.check_current()?;
            let state = self.state()?;
            if let Some(failure) = &state.failure {
                return Err(io::Error::other(failure.clone()));
            }
            drop(state);
            before(self.deadline)
        })();
        result.inspect_err(|error| self.fail(error.to_string()))
    }

    fn fail(&self, reason: impl Into<String>) {
        // No blocking recovery through a poisoned registry and no release.
        if let Ok(mut state) = self.state.lock() {
            state.failure.get_or_insert_with(|| reason.into());
        }
    }
}

impl Drop for Inner {
    fn drop(&mut self) {
        // Recover poisoned contents ONLY to retain them. Poison never becomes
        // completion and must not implicitly drop/detach the actual handles.
        let state = self.state.get_mut().unwrap_or_else(|error| error.into_inner());
        let joined = state.phase == Phase::Joined && state.failure.is_none();
        if !joined {
            // Unknown ownership must not detach Child/JoinHandle or close its
            // only retained inputs. Keep actual originals until process death;
            // durable WITHHELD survives that death independently.
            std::mem::forget(std::mem::take(&mut state.children));
            std::mem::forget(std::mem::take(&mut state.readers));
            std::mem::forget(std::mem::take(&mut state.workers));
            std::mem::forget(std::mem::take(&mut state.native_scopes));
            std::mem::forget(Arc::clone(&self.original));
        }
    }
}

#[must_use]
pub struct ProtectedWorkScope {
    inner: Arc<Inner>,
}

impl Drop for ProtectedWorkScope {
    fn drop(&mut self) {
        // Only explicit seal transfers the original coordinator to the joined
        // path. Surviving dispatchers/readers must not keep lost ownership Open.
        if let Ok(mut state) = self.inner.state() {
            if state.phase == Phase::Open {
                state.phase = Phase::Sealed;
                state
                    .failure
                    .get_or_insert_with(|| "original scope owner dropped before seal".into());
            }
        }
    }
}

impl ProtectedWorkScope {
    /// Restricts work under the SAME original guard and deadline. No launch is
    /// authorized by this constructor. A guard binds at most one scope.
    pub fn new(original: Arc<WithheldLease>, deadline: Instant) -> io::Result<Self> {
        before(deadline)?;
        original.check_current()?;
        before(deadline)?;
        original
            .protected_scope
            .compare_exchange(
                false,
                true,
                std::sync::atomic::Ordering::AcqRel,
                std::sync::atomic::Ordering::Acquire,
            )
            .map_err(|_| io::Error::other("original guard already bound to a protected scope"))?;
        let inner = Arc::new(Inner {
            original,
            identity: ScopeIdentity(Arc::new(())),
            deadline,
            state: Mutex::new(State {
                phase: Phase::Open,
                failure: None,
                children: Vec::new(),
                readers: Vec::new(),
                workers: Vec::new(),
                native_scopes: Vec::new(),
            }),
        });
        inner.check()?;
        Ok(Self { inner })
    }

    pub fn identity(&self) -> &ScopeIdentity {
        &self.inner.identity
    }
    pub fn dispatcher(&self) -> ScopeDispatch {
        ScopeDispatch { inner: Arc::clone(&self.inner) }
    }
    pub fn check_current(&self) -> io::Result<()> {
        self.inner.check()
    }

    /// Irreversible: all existing dispatchers see Sealed, including cloned
    /// Bootstrap execution contexts. No unseal or renewed deadline exists.
    pub fn seal(self) -> SealedWorkScope {
        if let Ok(mut state) = self.inner.state() {
            if state.phase == Phase::Open {
                state.phase = Phase::Sealed;
            } else {
                state.failure.get_or_insert_with(|| "protected scope could not seal".into());
            }
        }
        // Drop of this original owner now observes the explicit Sealed state;
        // clone extends the SAME original, never reconstructing an acquisition.
        SealedWorkScope { inner: Arc::clone(&self.inner) }
    }
}

#[derive(Clone)]
pub struct ScopeDispatch {
    inner: Arc<Inner>,
}

/// An installed restriction without an owning reference to the original guard.
/// Expired/sealed never becomes a standalone fallback or a new scope.
pub struct WeakScopeDispatch {
    inner: Weak<Inner>,
}
impl WeakScopeDispatch {
    pub fn upgrade(&self) -> io::Result<ScopeDispatch> {
        let inner = self
            .inner
            .upgrade()
            .ok_or_else(|| io::Error::other("original protected scope ended"))?;
        let dispatch = ScopeDispatch { inner };
        dispatch.check_current()?;
        Ok(dispatch)
    }
}

impl ScopeDispatch {
    pub fn downgrade(&self) -> WeakScopeDispatch {
        WeakScopeDispatch { inner: Arc::downgrade(&self.inner) }
    }
    pub fn identity(&self) -> &ScopeIdentity {
        &self.inner.identity
    }
    pub fn deadline(&self) -> Instant {
        self.inner.deadline
    }
    pub fn check_current(&self) -> io::Result<()> {
        self.inner.check()?;
        if self.inner.state()?.phase != Phase::Open {
            return Err(io::Error::other("protected dispatch permanently sealed"));
        }
        before(self.inner.deadline)
    }

    pub fn register_launch(&self) -> io::Result<LaunchRegistration> {
        self.check_current()?;
        let mut state = self.inner.state()?;
        if state.phase != Phase::Open {
            return Err(io::Error::other("protected dispatch sealed"));
        }
        let slot = Arc::new(ChildSlot {
            child: Mutex::new(ChildState::Pending),
            readers: Mutex::new(Vec::new()),
            joined_issued: AtomicBool::new(false),
        });
        let identity =
            LaunchIdentity { scope: self.inner.identity.clone(), slot: Arc::downgrade(&slot) };
        state.children.push(Arc::clone(&slot));
        Ok(LaunchRegistration { inner: Arc::clone(&self.inner), slot, identity, finished: false })
    }

    pub fn register_worker(&self) -> io::Result<WorkerRegistration> {
        self.check_current()?;
        let mut state = self.inner.state()?;
        if state.phase != Phase::Open {
            return Err(io::Error::other("protected dispatch sealed"));
        }
        let slot = Arc::new(WorkerSlot { worker: Mutex::new(None) });
        state.workers.push(Arc::clone(&slot));
        Ok(WorkerRegistration { inner: Arc::clone(&self.inner), slot, finished: false })
    }

    /// Permanent uncertainty; cannot be cleared by subsequent successful waits.
    pub fn record_failure(&self, reason: &str) {
        self.inner.fail(reason.to_owned());
    }
}

enum ChildState {
    Pending,
    SpawnFailed,
    Running(Child),
    Reaped(ExitStatus),
}
struct ChildSlot {
    child: Mutex<ChildState>,
    readers: Mutex<Vec<Arc<ReaderSlot>>>,
    joined_issued: AtomicBool,
}

/// Equality observation of one original launch, never a wait/release grant.
#[derive(Clone)]
pub struct LaunchIdentity {
    scope: ScopeIdentity,
    slot: Weak<ChildSlot>,
}
impl PartialEq for LaunchIdentity {
    fn eq(&self, other: &Self) -> bool {
        self.scope == other.scope && Weak::ptr_eq(&self.slot, &other.slot)
    }
}
impl Eq for LaunchIdentity {}
impl fmt::Debug for LaunchIdentity {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("LaunchIdentity").finish_non_exhaustive()
    }
}

/// One-use local child reap plus all of its original readers' actual EOF.
/// This is not Host/member/loan closure and cannot release WithheldLease.
pub struct JoinedChild {
    identity: LaunchIdentity,
}
impl JoinedChild {
    pub fn identity(&self) -> &LaunchIdentity {
        &self.identity
    }
}

#[must_use]
pub struct LaunchRegistration {
    inner: Arc<Inner>,
    slot: Arc<ChildSlot>,
    identity: LaunchIdentity,
    finished: bool,
}

impl LaunchRegistration {
    pub fn identity(&self) -> &LaunchIdentity {
        &self.identity
    }
    /// Retain the actual private capture before this associated child launch.
    /// Reading remains unavailable until that child's original owning wait.
    pub fn capture_file(&self, file: File) -> io::Result<ScopedCapture> {
        self.inner.check()?;
        let slot = Arc::new(ReaderSlot {
            reader: Mutex::new(ReaderState { pipe: Some(Pipe::Capture(file)), eof: false }),
        });
        let mut state = self.inner.state()?;
        if state.phase != Phase::Open {
            return Err(io::Error::other("capture registration sealed"));
        }
        state.readers.push(Arc::clone(&slot));
        self.slot
            .readers
            .lock()
            .map_err(|_| io::Error::other("child capture inventory poisoned"))?
            .push(Arc::clone(&slot));
        Ok(ScopedCapture {
            reader: ScopedReader { inner: Arc::clone(&self.inner), slot },
            child: Arc::clone(&self.slot),
        })
    }

    /// Launch through std only AFTER the caller's existing admission. This
    /// method does not acquire or replace any scheduling/resource authority.
    pub fn spawn(self, command: &mut Command) -> io::Result<ScopedChild> {
        self.inner.check()?;
        let spawned = {
            let state = self.inner.state()?;
            if state.phase != Phase::Open {
                return Err(io::Error::other("protected dispatch sealed before launch"));
            }
            before(self.inner.deadline)?;
            // The SAME seal gate covers actual delivery. A pre-existing
            // registration cannot race seal and start work afterward.
            command.spawn()
        };
        // SAFETY: this is exactly the actual spawn result for this registration.
        unsafe { self.complete_spawn(spawned) }
    }

    /// Call with the result of the independently admitted actual spawn. On all
    /// post-launch errors the original Child remains in this scope registry.
    ///
    /// # Safety
    /// The result must be the single actual launch for this registration, not
    /// a reconstructed error/status. Actual delivery must occur under this
    /// scope's original seal gate. No other owner may wait its Child.
    pub unsafe fn complete_spawn(mut self, spawned: io::Result<Child>) -> io::Result<ScopedChild> {
        self.finished = true;
        let mut slot = match self.slot.child.lock() {
            Ok(slot) => slot,
            Err(error) => {
                self.inner.fail("child slot poisoned");
                error.into_inner()
            }
        };
        let mut child = match spawned {
            Ok(child) => child,
            Err(error) => {
                *slot = ChildState::SpawnFailed;
                return Err(error);
            }
        };
        let out = child.stdout.take().map(Pipe::Out);
        let err = child.stderr.take().map(Pipe::Err);
        *slot = ChildState::Running(child);
        drop(slot);
        let mut state = match self.inner.state.lock() {
            Ok(state) => state,
            Err(error) => error.into_inner(), // retention only; check below refuses poison
        };
        let mut reader = |pipe: Option<Pipe>| {
            pipe.map(|pipe| {
                let slot = Arc::new(ReaderSlot {
                    reader: Mutex::new(ReaderState { pipe: Some(pipe), eof: false }),
                });
                state.readers.push(Arc::clone(&slot));
                slot
            })
        };
        let stdout = reader(out);
        let stderr = reader(err);
        let mut child_readers = match self.slot.readers.lock() {
            Ok(readers) => readers,
            Err(error) => {
                state.failure.get_or_insert_with(|| "child reader inventory poisoned".into());
                error.into_inner()
            }
        };
        child_readers.extend(stdout.iter().chain(stderr.iter()).cloned());
        drop(child_readers);
        drop(state);
        self.inner.check()?;
        Ok(ScopedChild {
            inner: Arc::clone(&self.inner),
            slot: Arc::clone(&self.slot),
            identity: self.identity.clone(),
            stdout,
            stderr,
        })
    }
}

impl Drop for LaunchRegistration {
    fn drop(&mut self) {
        if !self.finished {
            self.inner.fail("launch registration abandoned");
        }
    }
}

#[must_use]
pub struct ScopedChild {
    inner: Arc<Inner>,
    slot: Arc<ChildSlot>,
    identity: LaunchIdentity,
    stdout: Option<Arc<ReaderSlot>>,
    stderr: Option<Arc<ReaderSlot>>,
}

impl ScopedChild {
    pub fn identity(&self) -> &LaunchIdentity {
        &self.identity
    }
    /// Emits exactly once from the actual retained wait/reader owners. No
    /// status value, EOF boolean, PID or outside callback can construct it.
    pub fn joined(&self) -> io::Result<JoinedChild> {
        self.inner.check()?;
        if !matches!(
            *self.slot.child.lock().map_err(|_| io::Error::other("child poisoned"))?,
            ChildState::Reaped(_)
        ) {
            return Err(io::Error::new(io::ErrorKind::WouldBlock, "original child not reaped"));
        }
        for reader in
            self.slot.readers.lock().map_err(|_| io::Error::other("child readers poisoned"))?.iter()
        {
            if !reader.reader.lock().map_err(|_| io::Error::other("reader poisoned"))?.eof {
                return Err(io::Error::new(
                    io::ErrorKind::WouldBlock,
                    "original child readers lack actual EOF",
                ));
            }
        }
        self.inner.check()?;
        self.slot
            .joined_issued
            .compare_exchange(false, true, Ordering::AcqRel, Ordering::Acquire)
            .map_err(|_| io::Error::other("original child join already consumed"))?;
        before(self.inner.deadline).inspect_err(|error| self.inner.fail(error.to_string()))?;
        Ok(JoinedChild { identity: self.identity.clone() })
    }
    pub fn take_stdout(&mut self) -> Option<ScopedReader> {
        self.stdout.take().map(|slot| ScopedReader { inner: Arc::clone(&self.inner), slot })
    }
    pub fn take_stderr(&mut self) -> Option<ScopedReader> {
        self.stderr.take().map(|slot| ScopedReader { inner: Arc::clone(&self.inner), slot })
    }
    pub fn wait(&mut self) -> io::Result<ExitStatus> {
        loop {
            self.inner.check().inspect_err(|e| self.inner.fail(e.to_string()))?;
            if let Some(status) =
                wait_once(&self.slot).inspect_err(|e| self.inner.fail(e.to_string()))?
            {
                before(self.inner.deadline)?;
                return Ok(status);
            }
            pause(self.inner.deadline)?;
        }
    }
    pub fn wait_with_output(self) -> io::Result<Output> {
        self.wait_with_output_and_join().map(|(output, _)| output)
    }
    /// Keep completed child observations separate from acceptance of the
    /// original one-use local bookend. Neither output nor an error is closure.
    pub fn wait_with_output_observed(mut self) -> io::Result<(Output, io::Result<JoinedChild>)> {
        let mut out = self.take_stdout();
        let mut err = self.take_stderr();
        let mut stdout = Vec::new();
        let mut stderr = Vec::new();
        loop {
            self.inner.check().inspect_err(|e| self.inner.fail(e.to_string()))?;
            let out_done = drain(&mut out, &mut stdout)?;
            let err_done = drain(&mut err, &mut stderr)?;
            let status = wait_once(&self.slot).inspect_err(|e| self.inner.fail(e.to_string()))?;
            if let (true, true, Some(status)) = (out_done, err_done, status) {
                let joined = self.joined();
                return Ok((Output { status, stdout, stderr }, joined));
            }
            pause(self.inner.deadline)?;
        }
    }
    pub fn wait_with_output_and_join(self) -> io::Result<(Output, JoinedChild)> {
        let (output, joined) = self.wait_with_output_observed()?;
        Ok((output, joined?))
    }
}

fn wait_once(slot: &ChildSlot) -> io::Result<Option<ExitStatus>> {
    let mut state = slot.child.lock().map_err(|_| io::Error::other("child slot poisoned"))?;
    match &mut *state {
        ChildState::Reaped(status) => Ok(Some(*status)),
        ChildState::Running(child) => {
            drop(child.stdin.take()); // matches std Child::wait: close its input before waiting
            if let Some(status) = child.try_wait()? {
                *state = ChildState::Reaped(status);
                Ok(Some(status))
            } else {
                Ok(None)
            }
        }
        _ => Err(io::Error::other("child has no actual successful launch")),
    }
}

enum Pipe {
    Out(ChildStdout),
    Err(ChildStderr),
    Capture(File),
}
impl Pipe {
    fn fd(&self) -> i32 {
        match self {
            Self::Out(p) => p.as_raw_fd(),
            Self::Err(p) => p.as_raw_fd(),
            Self::Capture(p) => p.as_raw_fd(),
        }
    }
    fn read(&mut self, bytes: &mut [u8]) -> io::Result<usize> {
        match self {
            Self::Out(p) => p.read(bytes),
            Self::Err(p) => p.read(bytes),
            Self::Capture(p) => p.read(bytes),
        }
    }
}
struct ReaderState {
    pipe: Option<Pipe>,
    eof: bool,
}
struct ReaderSlot {
    reader: Mutex<ReaderState>,
}

/// The original private pipe, with no clone/raw-FD/export operation. EOF is
/// recorded only by its actual read(2), never by child exit or an empty buffer.
pub struct ScopedReader {
    inner: Arc<Inner>,
    slot: Arc<ReaderSlot>,
}

/// Actual private capture retained before its associated actual child launch.
pub struct ScopedCapture {
    reader: ScopedReader,
    child: Arc<ChildSlot>,
}
impl ScopedCapture {
    pub fn read_after_wait(mut self) -> io::Result<Vec<u8>> {
        let result = (|| {
            self.reader.inner.check()?;
            if !matches!(
                *self.child.child.lock().map_err(|_| io::Error::other("child poisoned"))?,
                ChildState::Reaped(_)
            ) {
                return Err(io::Error::other("capture requires original child owning wait"));
            }
            {
                let mut state = self
                    .reader
                    .slot
                    .reader
                    .lock()
                    .map_err(|_| io::Error::other("capture poisoned"))?;
                let Some(Pipe::Capture(file)) = state.pipe.as_mut() else {
                    return Err(io::Error::other("missing original capture"));
                };
                file.rewind()?;
            }
            let mut bytes = Vec::new();
            self.reader.read_to_end(&mut bytes)?;
            self.reader.inner.check()?;
            Ok(bytes)
        })();
        result.inspect_err(|error| self.reader.inner.fail(error.to_string()))
    }
}

impl ScopedReader {
    fn read_ready(&mut self, bytes: &mut [u8], blocking: bool) -> io::Result<Option<usize>> {
        if bytes.is_empty() {
            return Ok(Some(0));
        }
        loop {
            self.inner.check()?;
            let mut state =
                self.slot.reader.lock().map_err(|_| io::Error::other("reader poisoned"))?;
            if state.eof {
                return Ok(Some(0));
            }
            let pipe =
                state.pipe.as_mut().ok_or_else(|| io::Error::other("missing original reader"))?;
            let mut poll = libc::pollfd { fd: pipe.fd(), events: libc::POLLIN, revents: 0 };
            // Only this non-Clone reader can read this original pipe. poll does
            // not change OFD flags or its cursor and never claims EOF itself.
            let ready = unsafe { libc::poll(&mut poll, 1, 0) };
            if ready < 0 {
                let error = io::Error::last_os_error();
                if error.kind() == io::ErrorKind::Interrupted {
                    continue;
                }
                return Err(error);
            }
            if ready > 0 {
                match pipe.read(bytes) {
                    Ok(0) => {
                        state.eof = true;
                        state.pipe.take();
                        return Ok(Some(0));
                    }
                    Ok(n) => return Ok(Some(n)),
                    Err(error) if error.kind() == io::ErrorKind::Interrupted => continue,
                    Err(error) => return Err(error),
                }
            }
            drop(state);
            if !blocking {
                return Ok(None);
            }
            pause(self.inner.deadline)?;
        }
    }
}

impl Read for ScopedReader {
    fn read(&mut self, bytes: &mut [u8]) -> io::Result<usize> {
        self.read_ready(bytes, true)
            .map(|n| n.expect("blocking read"))
            .inspect_err(|e| self.inner.fail(e.to_string()))
    }
}

fn drain(reader: &mut Option<ScopedReader>, bytes: &mut Vec<u8>) -> io::Result<bool> {
    let Some(reader) = reader else {
        return Ok(true);
    };
    let mut buffer = [0; 16384];
    match reader.read_ready(&mut buffer, false).inspect_err(|e| reader.inner.fail(e.to_string()))? {
        Some(0) => Ok(true),
        Some(n) => {
            bytes.extend_from_slice(&buffer[..n]);
            Ok(false)
        }
        None => Ok(false),
    }
}

trait ActualWorker: Send + Sync {
    fn join(&self, deadline: Instant) -> io::Result<()>;
}
struct Worker<T> {
    handle: Mutex<Option<JoinHandle<T>>>,
    result: Mutex<Option<T>>,
}
impl<T: Send + 'static> ActualWorker for Worker<T> {
    fn join(&self, deadline: Instant) -> io::Result<()> {
        let mut handle =
            self.handle.lock().map_err(|_| io::Error::other("worker handle poisoned"))?;
        if let Some(handle) = handle.as_ref() {
            while !handle.is_finished() {
                pause(deadline)?;
            }
        }
        if let Some(handle) = handle.take() {
            let result =
                handle.join().map_err(|_| io::Error::other("protected worker panicked"))?;
            *self.result.lock().map_err(|_| io::Error::other("worker result poisoned"))? =
                Some(result);
        }
        before(deadline)
    }
}
struct WorkerSlot {
    worker: Mutex<Option<Arc<dyn ActualWorker>>>,
}

#[must_use]
pub struct WorkerRegistration {
    inner: Arc<Inner>,
    slot: Arc<WorkerSlot>,
    finished: bool,
}
impl WorkerRegistration {
    /// Starts the actual owned worker while holding the original seal gate.
    /// Resource admission of work inside that worker remains the caller's job.
    pub fn spawn<T, F>(self, builder: thread::Builder, work: F) -> io::Result<ScopedWorker<T>>
    where
        T: Send + 'static,
        F: FnOnce() -> T + Send + 'static,
    {
        self.inner.check()?;
        let handle = {
            let state = self.inner.state()?;
            if state.phase != Phase::Open {
                return Err(io::Error::other("protected dispatch sealed before worker launch"));
            }
            before(self.inner.deadline)?;
            builder.spawn(work)?
        };
        // SAFETY: actual launch was serialized with this scope's seal.
        unsafe { self.complete_spawn(handle) }
    }

    /// # Safety
    /// The handle must be the single actual worker for this registration and
    /// its delivery must be serialized with the original protected seal gate.
    pub unsafe fn complete_spawn<T: Send + 'static>(
        mut self,
        handle: JoinHandle<T>,
    ) -> io::Result<ScopedWorker<T>> {
        let worker =
            Arc::new(Worker { handle: Mutex::new(Some(handle)), result: Mutex::new(None) });
        match self.slot.worker.lock() {
            Ok(mut slot) => *slot = Some(worker.clone()),
            Err(error) => {
                *error.into_inner() = Some(worker.clone());
                self.inner.fail("worker registration poisoned");
            }
        }
        self.finished = true;
        self.inner.check()?;
        Ok(ScopedWorker { inner: Arc::clone(&self.inner), worker })
    }
}
impl Drop for WorkerRegistration {
    fn drop(&mut self) {
        if !self.finished {
            self.inner.fail("worker registration abandoned");
        }
    }
}
pub struct ScopedWorker<T> {
    inner: Arc<Inner>,
    worker: Arc<Worker<T>>,
}
impl<T: Send + 'static> ScopedWorker<T> {
    pub fn join(self) -> io::Result<T> {
        self.worker.join(self.inner.deadline).inspect_err(|e| self.inner.fail(e.to_string()))?;
        self.inner.check()?;
        self.worker
            .result
            .lock()
            .map_err(|_| io::Error::other("worker result poisoned"))?
            .take()
            .ok_or_else(|| io::Error::other("worker result already consumed"))
    }
}

#[must_use]
pub struct SealedWorkScope {
    inner: Arc<Inner>,
}
impl SealedWorkScope {
    pub fn identity(&self) -> &ScopeIdentity {
        &self.inner.identity
    }
    pub fn join(self) -> Result<LocalJoinedScope, ScopeFailure> {
        let result = (|| {
            self.inner.check()?;
            let (workers, children, readers, native_scopes) = {
                let state = self.inner.state()?;
                if state.phase != Phase::Sealed {
                    return Err(io::Error::other("scope not sealed"));
                }
                (
                    state.workers.clone(),
                    state.children.clone(),
                    state.readers.clone(),
                    state.native_scopes.clone(),
                )
            };
            for region in native_scopes {
                if !region.joined() {
                    return Err(io::Error::other("original native thread scope has not joined"));
                }
            }
            for slot in workers {
                let worker = slot
                    .worker
                    .lock()
                    .map_err(|_| io::Error::other("worker poisoned"))?
                    .clone()
                    .ok_or_else(|| io::Error::other("worker launch still pending"))?;
                worker.join(self.inner.deadline)?;
            }
            // Reader workers must be actually joined and every original pipe
            // must have read EOF. Do not convert unread output into completion.
            for slot in readers {
                if !slot.reader.lock().map_err(|_| io::Error::other("reader poisoned"))?.eof {
                    return Err(io::Error::other("original reader has not reached actual EOF"));
                }
            }
            for slot in children {
                if matches!(
                    *slot.child.lock().map_err(|_| io::Error::other("child poisoned"))?,
                    ChildState::SpawnFailed
                ) {
                    continue;
                }
                while wait_once(&slot)?.is_none() {
                    pause(self.inner.deadline)?;
                }
            }
            self.inner.check()?;
            self.inner.state()?.phase = Phase::Joined;
            before(self.inner.deadline)
        })();
        match result {
            Ok(()) => Ok(LocalJoinedScope { inner: self.inner }),
            Err(error) => {
                self.inner.fail(error.to_string());
                Err(ScopeFailure { inner: self.inner, error })
            }
        }
    }
}

/// Local wait/EOF/join bookends only. No release, serialization or conversion
/// to HostRoot ClosedRoot/protected-scope closure exists.
#[must_use]
pub struct LocalJoinedScope {
    inner: Arc<Inner>,
}
impl LocalJoinedScope {
    pub fn identity(&self) -> &ScopeIdentity {
        &self.inner.identity
    }
    pub fn check_current(&self) -> io::Result<()> {
        self.inner.check()
    }
}

#[must_use]
pub struct ScopeFailure {
    inner: Arc<Inner>,
    error: io::Error,
}
impl ScopeFailure {
    pub fn identity(&self) -> &ScopeIdentity {
        &self.inner.identity
    }
    pub fn error(&self) -> &io::Error {
        &self.error
    }
}
impl fmt::Debug for ScopeFailure {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("ScopeFailure").field(&self.error).finish()
    }
}
impl fmt::Display for ScopeFailure {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.error.fmt(f)
    }
}
impl std::error::Error for ScopeFailure {}

fn before(deadline: Instant) -> io::Result<()> {
    if Instant::now() >= deadline {
        Err(io::Error::new(io::ErrorKind::TimedOut, "original protected-scope deadline elapsed"))
    } else {
        Ok(())
    }
}
fn pause(deadline: Instant) -> io::Result<()> {
    before(deadline)?;
    thread::sleep(Duration::from_millis(1).min(deadline.saturating_duration_since(Instant::now())));
    before(deadline)
}

#[cfg(test)]
mod tests;

mod thread_scope;
pub use thread_scope::{ScopedThread, ScopedThreads};
mod input;
pub use input::{OriginalSourceOffer, OriginalSourceRoot, SourceOfferData};
#[cfg(feature = "resident-inputs")]
pub use input::{RefusedInputRetirement, RetiredResidentInputs};
