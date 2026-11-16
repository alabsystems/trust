//! One original paired input reader. A continuation acknowledges an observed
//! node; it never supplies native admission, a bank loan or a replacement root.
use crate::context::root_control::RootControl;
use crate::workload_service::transport::Input;
use std::io::{self, Write as _};
use std::os::unix::net::UnixStream;
use std::sync::{
    Arc, Mutex, TryLockError,
    atomic::{AtomicBool, Ordering},
    mpsc::{self, Receiver, TrySendError},
};
use std::time::{Duration, Instant};
use trust_resource_controller::paired_qualification::service::{
    Binding, Checkpoint, Control as Frame,
};

fn error(reason: impl Into<String>) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, reason.into())
}
fn lock<T>(value: &Mutex<T>, deadline: Instant) -> io::Result<std::sync::MutexGuard<'_, T>> {
    loop {
        if Instant::now() >= deadline {
            return Err(io::ErrorKind::TimedOut.into());
        }
        match value.try_lock() {
            Ok(value) => return Ok(value),
            Err(TryLockError::Poisoned(_)) => return Err(error("paired input owner poisoned")),
            Err(TryLockError::WouldBlock) => std::thread::sleep(Duration::from_millis(1)),
        }
    }
}
struct State {
    expected: Option<Checkpoint>,
    failure: Option<String>,
    stopped: bool,
    prefix: Vec<u8>,
    seen: u64,
}
pub(super) struct Control {
    state: Arc<Mutex<State>>,
    received: Receiver<()>,
    cancelled: Arc<AtomicBool>,
    stopping: Arc<AtomicBool>,
    worker: Option<std::thread::JoinHandle<()>>,
    next: u64,
    phase: Arc<Mutex<Option<Instant>>>,
    deadline: Instant,
}
impl Control {
    pub(super) fn start(
        binding: Binding,
        repetitions: u32,
        mut input: Input,
        deadline: Instant,
        cancelled: Arc<AtomicBool>,
    ) -> io::Result<(Self, RootControl)> {
        let (queue, mut cancel) = UnixStream::pair()?;
        cancel.set_nonblocking(true)?;
        let root = RootControl::from_workload_stream(queue)?;
        let phase = Arc::new(Mutex::new(None));
        input.phase_deadline(phase.clone());
        let (prefix, seen) = input.observation();
        let state = Arc::new(Mutex::new(State {
            expected: None,
            failure: None,
            stopped: false,
            prefix,
            seen,
        }));
        let (send, received) = mpsc::sync_channel(1);
        let stopping = Arc::new(AtomicBool::new(false));
        let original = state.clone();
        let done = stopping.clone();
        let stopped = cancelled.clone();
        let worker=std::thread::Builder::new().name("targo-paired-input".into()).spawn(move||{
            let outcome=(||->io::Result<()>{loop{
                let before=input.observation().1;
                let bytes=match input.frame(deadline,Some(&done)){
                    Err(_)if done.load(Ordering::Acquire)=>{return if input.observation().1==before{Ok(())}else{Err(error("paired input stopped within a partial original frame"))}},
                    Err(cause)if cause.kind()==io::ErrorKind::UnexpectedEof&&lock(&original,deadline)?.stopped=>return Ok(()),
                    result=>result?,
                };
                {let(prefix,seen)=input.observation();let mut state=lock(&original,deadline)?;state.prefix=prefix;state.seen=seen;}
                match Frame::decode(&bytes,&binding,repetitions)?{
                    Frame::Stop(_)=>{let mut state=lock(&original,deadline)?;if state.stopped{return Err(error("duplicate paired stop"))}state.stopped=true;stopped.store(true,Ordering::Release);cancel.write_all(b"C")?;},
                    Frame::Continue(observed)=>{
                        let mut state=lock(&original,deadline)?;
                        let expected=state.expected.take().ok_or_else(||error("paired continuation has no original pending checkpoint"))?;
                        if state.stopped||observed!=expected{return Err(error("paired continuation changed original node/outcome/binding or followed stop"))}
                        match send.try_send(()){Ok(())=>{},Err(TrySendError::Full(_))=>return Err(error("paired continuation overflow")),Err(TrySendError::Disconnected(_))=>return Ok(())}
                    }
                }
            }})();
            let(prefix,seen)=input.observation();if let Ok(mut state)=original.lock(){state.prefix=prefix;state.seen=seen;}
            if let Err(cause)=outcome{if let Ok(mut state)=original.lock(){state.failure=Some(cause.to_string());}stopped.store(true,Ordering::Release);let _=cancel.write_all(b"C");}
        })?;
        Ok((
            Self {
                state,
                received,
                cancelled,
                stopping,
                worker: Some(worker),
                next: 1,
                phase,
                deadline,
            },
            root,
        ))
    }
    pub(super) fn begin_phase(&self, until: Instant) -> io::Result<()> {
        if self.cancelled.load(Ordering::Acquire) {
            return Err(error("paired input already stopped"));
        }
        let mut phase = lock(&self.phase, self.deadline)?;
        if phase.is_some() {
            return Err(error("paired phase overlapped original active phase"));
        }
        *phase = Some(until.min(self.deadline));
        Ok(())
    }
    pub(super) fn end_phase(&self) -> io::Result<()> {
        lock(&self.phase, self.deadline)?
            .take()
            .ok_or_else(|| error("paired phase was not active"))?;
        Ok(())
    }
    /// Caller has returned from and joined the original stage's actual graph.
    /// Clearing its input timer releases no native member, phase or credit.
    pub(super) fn stage_joined(&self) -> io::Result<()> {
        lock(&self.phase, self.deadline)?.take();
        Ok(())
    }
    pub(super) fn expect(&mut self, checkpoint: Checkpoint, until: Instant) -> io::Result<()> {
        if checkpoint.sequence != self.next || self.cancelled.load(Ordering::Acquire) {
            return Err(error(
                "paired checkpoint cannot restart or continue stopped original graph",
            ));
        }
        let mut state = lock(&self.state, until.min(self.deadline))?;
        if state.stopped || state.failure.is_some() || state.expected.is_some() {
            return Err(error("paired input cannot arm another checkpoint"));
        }
        state.expected = Some(checkpoint);
        self.next = self
            .next
            .checked_add(1)
            .ok_or_else(|| error("paired checkpoint overflow"))?;
        Ok(())
    }
    pub(super) fn wait(&self, until: Instant) -> io::Result<()> {
        loop {
            let left = until
                .min(self.deadline)
                .saturating_duration_since(Instant::now());
            if left.is_zero() {
                return Err(io::ErrorKind::TimedOut.into());
            }
            match self
                .received
                .recv_timeout(left.min(Duration::from_millis(50)))
            {
                Ok(()) => return Ok(()),
                Err(mpsc::RecvTimeoutError::Disconnected) => {
                    return Err(error("paired input worker ended"));
                }
                Err(mpsc::RecvTimeoutError::Timeout) => {}
            }
            if self.cancelled.load(Ordering::Acquire) {
                return Err(error(
                    "paired graph stopped while awaiting original continuation",
                ));
            }
        }
    }
    pub(super) fn finish(&mut self) -> io::Result<()> {
        self.stopping.store(true, Ordering::Release);
        if let Some(worker) = self.worker.take() {
            worker
                .join()
                .map_err(|_| error("paired input worker panicked"))?;
        }
        let state = lock(&self.state, self.deadline)?;
        if let Some(cause) = &state.failure {
            return Err(error(cause.clone()));
        }
        if state.expected.is_some() {
            return Err(error(
                "paired graph ended with an unacknowledged original checkpoint",
            ));
        }
        Ok(())
    }
    pub(super) fn observation(&self) -> io::Result<(Vec<u8>, u64, Option<String>, bool)> {
        let state = lock(&self.state, self.deadline)?;
        Ok((
            state.prefix.clone(),
            state.seen,
            state.failure.clone(),
            state.stopped,
        ))
    }
}
impl Drop for Control {
    fn drop(&mut self) {
        let _ = self.finish();
    }
}

#[cfg(test)]
mod tests;
