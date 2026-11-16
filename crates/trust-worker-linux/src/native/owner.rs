//! Private ownership prerequisite for a separate native broker process.
//!
//! No broker executable, IPC protocol, native loader, or compiler admission is
//! activated here. In particular, `Service` must never run in this monitor or
//! the compiler caller: its opaque ioctl/pread intervals belong to a separately
//! owned, pinned broker executable. A copied post-fork Budget is not a grant.
//!
//! The monitor starts before accepting the two exclusive direct-child guards.
//! Both children must remain in trusted single-thread startup, with creation of
//! threads/descendants and later exec prohibited, until Watching is observed.
//! The native worker and broker each need their own enforced address-space limit
//! and external aggregate containment. Kernel scheduling/reap latency is not a
//! hard bound; a pending cleanup retains custody and is always a refusal.
use std::sync::{Arc, Mutex, MutexGuard};
use std::thread::{self, JoinHandle};
use std::time::{Duration, Instant};

use trust_process_isolation::{Budget, Charge};

use crate::Error;
use crate::launcher::child::Child;

const QUANTUM: Duration = Duration::from_millis(1);
const STACK: usize = 256 * 1024;
// The requested monitor stack plus finite library/thread bookkeeping is a
// logical admission debit. It is not a measured allocator, RSS or kernel cap.
const BOOKKEEPING: usize = 16 * 1024;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum Phase {
    Waiting,
    Arming,
    Watching,
    FinishRequested,
    Finishing,
    Stopping,
    Reaped,
    CleanupFailed,
}
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum Cause {
    ParentFinished,
    ParentRefused,
    OwnerDropped,
    Deadline,
    BudgetRefused,
    InvalidPair,
    WorkerExited,
    BrokerExited,
    MonitorError,
    MonitorPanicked,
}
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) struct Observation {
    pub phase: Phase,
    pub cause: Option<Cause>,
    pub worker_status: Option<i32>,
    pub broker_status: Option<i32>,
    pub grant_valid: bool,
    pub monitor_exited: bool,
}
/// Child cleanup only. This is never a macro, solver or proof verdict. A true
/// grant_valid says only that the original grant survived owned child/FD cleanup.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) struct CleanupReceipt {
    pub cause: Cause,
    pub worker_status: i32,
    pub broker_status: i32,
    pub grant_valid: bool,
    pub elapsed: Duration,
}

struct Pair {
    worker: Child,
    broker: Child,
}
struct State {
    pair: Option<Pair>,
    phase: Phase,
    cause: Option<Cause>,
    abandoned: bool,
    worker_status: Option<i32>,
    broker_status: Option<i32>,
    monitor_started: bool,
    parent_finished: bool,
    #[cfg(test)]
    panic_wait: bool,
    #[cfg(test)]
    panic_after_transfer: bool,
    #[cfg(test)]
    panic_watch: bool,
}
struct Shared {
    state: Mutex<State>,
    budget: Budget,
}
impl Shared {
    fn state(&self) -> MutexGuard<'_, State> {
        match self.state.lock() {
            Ok(state) => state,
            Err(poisoned) => {
                self.budget.refuse(trust_process_isolation::Error::Poisoned);
                let mut state = poisoned.into_inner();
                state.cause.get_or_insert(Cause::MonitorError);
                state
            }
        }
    }
    fn request(&self, cause: Cause) {
        self.state().cause.get_or_insert(cause);
        if cause != Cause::ParentFinished {
            self.budget.cancel();
        }
    }
}
struct Handle {
    shared: Arc<Shared>,
    monitor: JoinHandle<()>,
    started: Instant,
}
impl Drop for Handle {
    fn drop(&mut self) {
        let mut state = self.shared.state();
        if matches!(state.phase, Phase::Reaped) {
            return;
        }
        state.abandoned = true;
        state.cause.get_or_insert(Cause::OwnerDropped);
        drop(state);
        self.shared.budget.cancel();
        // Dropping JoinHandle detaches; it never waits for opaque kernel/reap
        // IO. The monitor's Arc and local Pair retain exclusive cleanup custody.
    }
}

pub(super) struct Prepared {
    handle: Handle,
}
pub(super) struct Running {
    handle: Handle,
}

impl Prepared {
    /// Establish the original grant before launching either process. No live
    /// children exist if thread creation fails. This is not a broker launcher.
    pub fn new(budget: &Budget) -> Result<Self, Error> {
        let started = Instant::now();
        budget
            .charge(Charge {
                allocation_bytes: (STACK + BOOKKEEPING) as u64,
                work: 1024,
                calls: 1,
                ..Charge::default()
            })
            .map_err(Error::Budget)?;
        let shared = Arc::new(Shared {
            state: Mutex::new(State {
                pair: None,
                phase: Phase::Waiting,
                cause: None,
                abandoned: false,
                worker_status: None,
                broker_status: None,
                monitor_started: false,
                parent_finished: false,
                #[cfg(test)]
                panic_wait: false,
                #[cfg(test)]
                panic_after_transfer: false,
                #[cfg(test)]
                panic_watch: false,
            }),
            budget: budget.clone(),
        });
        let monitor_shared = Arc::clone(&shared);
        let monitor = thread::Builder::new()
            .stack_size(STACK)
            .spawn(move || monitor(monitor_shared))
            .map_err(|error| {
                budget.refuse(trust_process_isolation::Error::Allocation);
                Error::System("native ownership monitor", error)
            })?;
        let handle = Handle { shared, monitor, started };
        // No children exist yet. Do not return a launch prerequisite until the
        // monitor has entered its protected custody rendezvous. Thread-entry
        // failure or an expired original grant cancels the empty owner.
        loop {
            budget.charge(Charge { work: 16, ..Charge::default() }).map_err(Error::Budget)?;
            let began = handle.shared.state().monitor_started;
            if handle.monitor.is_finished() {
                budget.cancel();
                return Err(Error::Contract("native monitor stopped before launch"));
            }
            if began {
                budget.check().map_err(Error::Budget)?;
                return Ok(Self { handle });
            }
            thread::sleep(QUANTUM);
        }
    }

    /// Transfer both exclusive guards exactly once, including on a late or
    /// invalid adoption. The monitor then owns all kill/reap and FD cleanup.
    /// A Running handle must observe Watching with no cause and a valid grant
    /// before any broker request, and debit/check that same original grant at
    /// the actual IPC boundary. A late grant is never replaced: it still
    /// accepts the guards for cleanup.
    pub fn attach(self, worker: Child, broker: Child) -> Running {
        {
            let mut state = self.handle.shared.state();
            state.pair = Some(Pair { worker, broker });
            state.phase = Phase::Arming;
        }
        Running { handle: self.handle }
    }
}

impl Running {
    /// The parent admitted terminal protocol, but the pinned worker must still
    /// await its exit acknowledgement. Observe Finishing before sending it:
    /// the monitor first confirms both children remain alive. Neither this
    /// request nor a later zero worker exit is completion authority.
    pub fn request_worker_exit(&self) -> Result<(), Error> {
        self.handle.shared.budget.check().map_err(Error::Budget)?;
        let mut state = self.handle.shared.state();
        if state.phase != Phase::Watching || state.cause.is_some() {
            drop(state);
            self.handle.shared.request(Cause::ParentRefused);
            return Err(Error::Contract("native worker cannot arm completion"));
        }
        state.phase = Phase::FinishRequested;
        Ok(())
    }

    /// Parent-side polling is nonblocking with respect to broker/kernel IO.
    /// Mutex critical sections contain only fixed-size state and no callbacks.
    pub fn observe(&self) -> Observation {
        let charged =
            self.handle.shared.budget.charge(Charge { work: 16, ..Charge::default() }).is_ok();
        let mut observation = {
            let state = self.handle.shared.state();
            Observation {
                phase: state.phase,
                cause: state.cause,
                worker_status: state.worker_status,
                broker_status: state.broker_status,
                grant_valid: false,
                monitor_exited: self.handle.monitor.is_finished(),
            }
        };
        // Poison or expiry discovered during the fixed-size observation must
        // never leave an earlier pre-lock successful charge as admission.
        observation.grant_valid = charged && self.handle.shared.budget.check().is_ok();
        observation
    }

    /// The parent must independently validate bounded broker IPC/output before
    /// this shutdown request. It conveys no success authority to the supervisor.
    pub fn request_finished(&self) -> Result<(), Error> {
        self.handle.shared.budget.check().map_err(Error::Budget)?;
        let mut state = self.handle.shared.state();
        if state.cause.is_some() {
            drop(state);
            self.handle.shared.request(Cause::ParentRefused);
            return Err(Error::Contract("native pair already refused"));
        }
        if state.phase == Phase::Finishing && !state.parent_finished {
            // The monitor must observe an actual zero exit before shutdown.
            // This never signals a still-exiting successful worker.
            state.parent_finished = true;
            return Ok(());
        }
        if state.phase != Phase::Watching {
            drop(state);
            self.handle.shared.request(Cause::ParentRefused);
            return Err(Error::Contract("native pair is not armed"));
        }
        state.cause = Some(Cause::ParentFinished);
        Ok(())
    }
    pub fn refuse(&self) {
        self.handle.shared.request(Cause::ParentRefused);
    }

    /// A pending, failed or unobserved reap is a refusal; this call never joins.
    /// The detached owner remains responsible even after Err consumes Running.
    pub fn finish(self) -> Result<CleanupReceipt, Observation> {
        let observation = self.observe();
        if observation.phase != Phase::Reaped || !observation.monitor_exited {
            return Err(observation);
        }
        let (Some(cause), Some(worker_status), Some(broker_status)) =
            (observation.cause, observation.worker_status, observation.broker_status)
        else {
            return Err(observation);
        };
        let budget = self.handle.shared.budget.clone();
        let started = self.handle.started;
        drop(self);
        let grant_valid = budget.check().is_ok();
        let elapsed = started.elapsed();
        // Child guards, pidfds, shared state and the parent's JoinHandle have
        // dropped before this check. There is no join or live broker IO here.
        let grant_valid = grant_valid && budget.check().is_ok();
        Ok(CleanupReceipt { cause, worker_status, broker_status, grant_valid, elapsed })
    }
}

fn refusal_cause(error: trust_process_isolation::Error) -> Cause {
    if error == trust_process_isolation::Error::Deadline {
        Cause::Deadline
    } else {
        Cause::BudgetRefused
    }
}
fn monitor(shared: Arc<Shared>) {
    // A prepared handle can arrive late. Keep its empty cleanup rendezvous alive
    // until attach/drop, so no transferred guard ever lands in an exited thread.
    // Pair stays outside the protected closure: unwind never drops/reaps the
    // first child before the monitor can signal the second one. A panic before
    // transfer keeps a refused cleanup rendezvous alive until attach/drop.
    let mut incoming = None;
    loop {
        let next = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            if let Err(error) = shared.budget.charge(Charge { work: 64, ..Charge::default() }) {
                shared.state().cause.get_or_insert(refusal_cause(error));
            }
            let mut state = shared.state();
            state.monitor_started = true;
            #[cfg(test)]
            if state.panic_wait {
                state.panic_wait = false;
                drop(state);
                panic!("ownership rendezvous failure fixture");
            }
            incoming = state.pair.take();
            if incoming.is_some() {
                #[cfg(test)]
                if state.panic_after_transfer {
                    state.panic_after_transfer = false;
                    drop(state);
                    panic!("transferred ownership failure fixture");
                }
                return Advance::Attached;
            }
            if state.abandoned {
                return Advance::Abandoned;
            }
            drop(state);
            thread::sleep(QUANTUM);
            Advance::Waiting
        }));
        match next {
            Ok(Advance::Attached) => break,
            Ok(Advance::Abandoned) => return,
            Ok(Advance::Waiting) => {}
            Err(_) => {
                shared.budget.cancel();
                shared.state().cause.get_or_insert(Cause::MonitorPanicked);
                if incoming.is_some() {
                    break;
                }
            }
        }
    }
    let Some(mut pair) = incoming else {
        return;
    };
    let prior_refusal = shared.state().cause;
    let cause = prior_refusal.unwrap_or_else(|| {
        std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| watch(&shared, &pair)))
            .unwrap_or(Cause::MonitorPanicked)
    });
    if cause != Cause::ParentFinished {
        shared.budget.cancel();
        pair.worker.budget.cancel();
        pair.broker.budget.cancel();
    }
    {
        let mut state = shared.state();
        state.cause = Some(cause);
        state.phase = Phase::Stopping;
    }
    // Signal both before either opaque waitpid. Unreaped leaders reserve their
    // PID/PGID, and mandatory pidfds pin independent stop authority. No broker
    // ioctl/pread, parent callback, or join is executed by this owner.
    pair.worker.request_stop();
    pair.broker.request_stop();
    let worker_status = pair.worker.stop_and_reap().ok();
    let broker_status = if pair.worker.pid == pair.broker.pid && worker_status.is_some() {
        // This invalid pair never arms. Both guards named the same reserved
        // child; its actual reap disarms the duplicate without signalling a
        // reused numeric PID. It does not count as a second child reap.
        pair.broker.reaped = true;
        None
    } else {
        pair.broker.stop_and_reap().ok()
    };
    {
        let mut state = shared.state();
        state.worker_status = worker_status;
        state.broker_status = broker_status;
        if worker_status.is_none() || broker_status.is_none() {
            state.phase = Phase::CleanupFailed;
        }
    }
    // Failed cleanup keeps the local guards; their Drop retries while this
    // detached owner retains custody. It can block indefinitely in kernel
    // cleanup, but cannot publish Reaped or a successful grant in that case.
    drop(pair);
    let mut state = shared.state();
    if worker_status.is_some() && broker_status.is_some() {
        state.phase = Phase::Reaped;
    }
}

enum Advance {
    Waiting,
    Attached,
    Abandoned,
}

fn watch(shared: &Shared, pair: &Pair) -> Cause {
    if pair.worker.pid <= 0
        || pair.broker.pid <= 0
        || pair.worker.pid == pair.broker.pid
        || pair.worker.reaped
        || pair.broker.reaped
        || pair.worker.pidfd.is_none()
        || pair.broker.pidfd.is_none()
        || !shared.budget.shares_owner(&pair.worker.budget)
        || !shared.budget.shares_owner(&pair.broker.budget)
    {
        return Cause::InvalidPair;
    }
    if let Err(error) = shared.budget.check() {
        return refusal_cause(error);
    }
    // Child constructors are private trusted launcher output. Their pidfds
    // were opened against the still-unreaped direct child; this check verifies
    // wait ownership before activation, not a worker-provided PID declaration.
    match (pair.worker.exited(), pair.broker.exited()) {
        (Ok(false), Ok(false)) => {}
        (Ok(true), _) => return Cause::WorkerExited,
        (_, Ok(true)) => return Cause::BrokerExited,
        _ => return Cause::MonitorError,
    }
    if let Err(error) = shared.budget.check() {
        return refusal_cause(error);
    }
    {
        let mut state = shared.state();
        if let Some(cause) = state.cause {
            return cause;
        }
        state.phase = Phase::Watching;
    }
    loop {
        #[cfg(test)]
        if shared.state().panic_watch {
            panic!("owned monitor failure fixture");
        }
        if let Some(cause) = shared.state().cause {
            return cause;
        }
        if let Err(error) = shared.budget.charge(Charge { work: 64, ..Charge::default() }) {
            return refusal_cause(error);
        }
        match (pair.worker.successful_exit(), pair.broker.exited()) {
            (_, Ok(true)) => return Cause::BrokerExited,
            (Ok(None), Ok(false)) => {
                let mut state = shared.state();
                if let Some(cause) = state.cause {
                    return cause;
                }
                if state.phase == Phase::FinishRequested {
                    state.phase = Phase::Finishing;
                }
            }
            (Ok(Some(true)), Ok(false)) => {
                let state = shared.state();
                if let Some(cause) = state.cause {
                    return cause;
                }
                if state.phase != Phase::Finishing {
                    return Cause::WorkerExited;
                }
                if state.parent_finished {
                    return Cause::ParentFinished;
                }
                // Keep exclusive child/broker custody until parent validation
                // or the original deadline, never accept zero exit alone.
            }
            (Ok(Some(false)), _) => return Cause::WorkerExited,
            _ => return Cause::MonitorError,
        }
        thread::sleep(QUANTUM);
    }
}

#[cfg(test)]
mod tests;
