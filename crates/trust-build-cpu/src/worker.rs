// SPDX-License-Identifier: MIT OR Apache-2.0
// Copyright 2026 Andrew Yates

//! Join local GNU tokens to worker-owned global CPU leases.

use std::io;
use std::sync::atomic::{AtomicU8, Ordering};
use std::sync::{Arc, Condvar, Mutex, Weak};
use std::thread::{self, JoinHandle};
use std::time::Duration;

use crate::{ExternalDebt, Lease, LegacyFence, Owner, Pool, invalid};

mod gate;
pub use gate::WorkerPause;
#[cfg(all(feature = "native-host", any(target_os = "linux", target_os = "macos")))]
mod workload;

#[derive(Clone)]
enum Admission {
    Native {
        pool: Pool,
        limit: Arc<dyn Fn(u32) -> u32 + Send + Sync>,
    },
    Shared {
        debt: Arc<ExternalDebt>,
        limit: Arc<dyn Fn(u32) -> u32 + Send + Sync>,
    },
    #[cfg(all(feature = "native-host", any(target_os = "linux", target_os = "macos")))]
    Workload(workload::Admission),
}

/// A local jobserver with one already-owned implicit global credit.
///
/// The caller must borrow an inherited implicit credit for synchronous nested
/// work, rather than reacquiring one while its parent waits. This constructor
/// deliberately cannot allocate an implicit credit or invent descendant custody.
#[derive(Clone)]
pub struct WorkerClient {
    local: jobserver::Client,
    admission: Admission,
    implicit: Arc<Lease>,
    owner: Owner,
    fence: Option<Arc<LegacyFence>>,
    admission_gate: Option<Arc<gate::Gate>>,
}

impl WorkerClient {
    /// Bind an existing local jobserver and implicit global lease to a live
    /// observation callback. A zero observation pauses extra admission.
    /// The callback must be bounded/nonblocking (read a cached observation).
    pub fn new(
        local: jobserver::Client,
        pool: Pool,
        implicit: Arc<Lease>,
        limit: Arc<dyn Fn(u32) -> u32 + Send + Sync>,
        owner: Owner,
    ) -> io::Result<Self> {
        // A named FIFO provides independent nonblocking descriptions on
        // macOS. Never mutate an inherited anonymous pipe's blocking mode.
        // Dropping a probe immediately returns any token it acquired.
        drop(local.try_acquire()?);
        if owner.pid == 0 || !pool.contains(&implicit)? {
            return Err(invalid("worker implicit credit does not belong to its CPU pool"));
        }
        Ok(Self {
            local,
            admission: Admission::Native { pool, limit },
            implicit,
            owner,
            fence: None,
            admission_gate: None,
        })
    }

    /// Join local tokens to the activated native/external transaction. Retained
    /// external debt remains unavailable after its owner's descriptors close.
    /// The implicit lease must belong to this exact checked native backing.
    pub fn new_shared(
        local: jobserver::Client,
        debt: Arc<ExternalDebt>,
        implicit: Arc<Lease>,
        limit: Arc<dyn Fn(u32) -> u32 + Send + Sync>,
        owner: Owner,
    ) -> io::Result<Self> {
        let mut client = Self::new(local, debt.native_pool()?, implicit, limit.clone(), owner)?;
        client.admission = Admission::Shared { debt, limit };
        client.admission_gate = Some(gate::Gate::new());
        Ok(client)
    }

    /// Retain the native epoch's legacy exclusion in every issued credit.
    /// Production native-epoch callers must supply their validated fence.
    pub fn with_fence(mut self, fence: Arc<LegacyFence>) -> Self {
        self.fence = Some(fence);
        self
    }

    /// The actual implicit credit. A checked child launcher can clone this
    /// lease and inherit its descriptor; a path/PID is not a substitute.
    pub fn implicit(&self) -> &Arc<Lease> {
        &self.implicit
    }

    /// The epoch fence retained by this client's implicit worker.
    pub fn fence(&self) -> Option<&Arc<LegacyFence>> {
        self.fence.as_ref()
    }

    /// Exclude extras only after the caller separately quiesces implicit work.
    /// Returns None while an acquisition or offered/active extra is outstanding.
    /// Legacy non-shared workers do not support this phase transition.
    pub fn try_pause_extras(&self) -> io::Result<Option<WorkerPause>> {
        self.admission_gate
            .as_ref()
            .ok_or_else(|| {
                io::Error::new(
                    io::ErrorKind::Unsupported,
                    "legacy workers cannot enter a retained loan phase",
                )
            })?
            .pause()
    }

    /// Observe extra admission state; this is not an implicit dispatch permit.
    /// The execution owner must serialize implicit dispatch with its own phase
    /// transition, not authorize it from this potentially stale observation.
    pub fn extra_admission_running(&self) -> bool {
        self.admission_gate.as_ref().is_none_or(|gate| gate.running())
    }

    /// Acquire both credits, or neither, without waiting on either semaphore.
    /// A global refusal immediately returns the local token, preventing the
    /// hold-and-wait deadlock between independent pools and nested roots.
    pub fn try_acquire(&self) -> io::Result<Option<Credit>> {
        let attempt = match &self.admission_gate {
            Some(gate) => match gate.begin()? {
                Some(attempt) => Some(attempt),
                None => return Ok(None),
            },
            None => None,
        };
        let Some(local) = self.local.try_acquire()? else { return Ok(None) };
        #[cfg(all(feature = "native-host", any(target_os = "linux", target_os = "macos")))]
        let mut workload_loan = None;
        let cpu = match &self.admission {
            Admission::Shared { debt, limit } => {
                debt.try_acquire_observed(self.owner, |held| limit(held))?
            }
            Admission::Native { pool, limit } => {
                pool.try_acquire_observed(self.owner, |held| limit(held))?
            }
            #[cfg(all(feature = "native-host", any(target_os = "linux", target_os = "macos")))]
            Admission::Workload(admission) => match admission.try_acquire() {
                Ok(Some((lease, loan))) => {
                    workload_loan = Some(loan);
                    Some(lease)
                }
                Ok(None) => None,
                Err(error) => {
                    if let Some(gate) = &self.admission_gate {
                        gate.poison();
                    }
                    return Err(error);
                }
            },
        };
        let Some(cpu) = cpu else {
            return Ok(None);
        };
        Ok(Some(Credit {
            _local: local,
            cpu: Arc::new(cpu),
            ticket: Arc::new(AtomicU8::new(OFFERED)),
            fence: self.fence.clone(),
            #[cfg(all(feature = "native-host", any(target_os = "linux", target_os = "macos")))]
            workload_loan,
            admission: attempt.map(gate::Attempt::publish).transpose()?,
        }))
    }

    /// Handle requests for runnable workers. Do not use this to prefetch CPU
    /// leases for queued work which is not yet eligible to execute.
    pub fn into_helper_thread(
        self,
        mut callback: impl FnMut(io::Result<Credit>) + Send + 'static,
    ) -> io::Result<WorkerHelper> {
        let state = Arc::new((Mutex::new(Requests::default()), Condvar::new()));
        let worker_state = Arc::clone(&state);
        let thread =
            thread::Builder::new().name("trust-cpu-admission".into()).spawn(move || {
                loop {
                    let (lock, wake) = &*worker_state;
                    let mut pending =
                        lock.lock().unwrap_or_else(std::sync::PoisonError::into_inner);
                    while pending.count == 0 && !pending.stop {
                        pending =
                            wake.wait(pending).unwrap_or_else(std::sync::PoisonError::into_inner);
                    }
                    if pending.stop {
                        return;
                    }
                    drop(pending);
                    let result = match self.try_acquire() {
                        Ok(None) => {
                            let pending =
                                lock.lock().unwrap_or_else(std::sync::PoisonError::into_inner);
                            if pending.stop {
                                return;
                            }
                            // Bounded polling also observes cross-process releases
                            // and new cached telemetry without a GUI dependency.
                            drop(wake.wait_timeout(pending, Duration::from_millis(10)));
                            continue;
                        }
                        Ok(Some(credit)) => Ok(credit),
                        Err(error) => Err(error),
                    };
                    let mut pending =
                        lock.lock().unwrap_or_else(std::sync::PoisonError::into_inner);
                    if pending.stop {
                        drop(pending);
                        if let Ok(credit) = result {
                            // This helper has not published or dispatched the
                            // offer. Atomically cancel before returning it.
                            let _ = credit.retire_unused();
                        }
                        return;
                    }
                    if pending.count == 0 {
                        // `cancel_request` withdrew the request this credit
                        // was fetched for, so nobody waits for it. It was
                        // never published: settle it here, and report only a
                        // failed settlement or a failed admission.
                        drop(pending);
                        if let Err(error) = result.and_then(Credit::retire_unused) {
                            callback(Err(error));
                        }
                        continue;
                    }
                    pending.count -= 1;
                    if let Ok(credit) = &result {
                        pending.tickets.retain(|ticket| ticket.strong_count() != 0);
                        pending.tickets.push(Arc::downgrade(&credit.ticket));
                    }
                    drop(pending);
                    callback(result);
                }
            })?;
        Ok(WorkerHelper { state, thread: Some(thread) })
    }
}

/// One runnable worker's inseparable local token and global CPU lease.
/// Dropping the local token never unlocks a descendant's duplicated CPU lease.
pub struct Credit {
    // Keep the local token alive until this entire value is dropped.
    _local: jobserver::Acquired,
    cpu: Arc<Lease>,
    ticket: Arc<AtomicU8>,
    fence: Option<Arc<LegacyFence>>,
    #[cfg(all(feature = "native-host", any(target_os = "linux", target_os = "macos")))]
    workload_loan: Option<trust_resource_controller::client::workload::WorkerLoan>,
    // LAST: do not report a drained extra before its original backing drops.
    admission: Option<gate::Permit>,
}

const OFFERED: u8 = 0;
const COMMITTED: u8 = 1;
const CANCELLED: u8 = 2;

impl Credit {
    /// Retire an offer only after atomically preventing its dispatch. This is
    /// an explicit protocol edge; generic Drop never returns a workload unit.
    pub fn retire_unused(self) -> io::Result<()> {
        match self.ticket.compare_exchange(OFFERED, CANCELLED, Ordering::AcqRel, Ordering::Acquire)
        {
            Ok(_) | Err(CANCELLED) => {}
            Err(_) => return Err(invalid("a committed worker is not an unused offer")),
        }
        // Only the native-host workload loan needs this credit mutably.
        #[cfg(all(feature = "native-host", any(target_os = "linux", target_os = "macos")))]
        {
            let mut credit = self;
            if let Some(loan) = credit.workload_loan.take() {
                // SAFETY: CANCELLED is terminal; commit requires OFFERED. This
                // exact offer has never authorized a dispatched SDK task.
                let result = unsafe { loan.settle_unused_offer_after_cancel(workload::deadline()) };
                if let Err(error) = result {
                    if let Some(admission) = &credit.admission {
                        admission.poison();
                    }
                    return Err(io::Error::other(error.to_string()));
                }
            }
        }
        Ok(())
    }

    /// Return a committed original worker loan after its producing SDK task
    /// has positively finished. GNU and admission custody span the host ACK.
    ///
    /// # Safety
    /// The actual task using this unit must be joined or positively parked,
    /// with no producing work or children left using it. A completion counter,
    /// generic Drop or unjoined notification does not establish this condition.
    pub unsafe fn retire_after_sdk_quiescence(self) -> io::Result<()> {
        if !self.is_committed() {
            return Err(invalid("SDK settlement requires a committed worker"));
        }
        // Only the native-host workload loan needs this credit mutably.
        #[cfg(all(feature = "native-host", any(target_os = "linux", target_os = "macos")))]
        {
            let mut credit = self;
            if let Some(loan) = credit.workload_loan.take() {
                // SAFETY: the caller establishes the actual SDK task's quiescence.
                let result = unsafe { loan.settle_after_sdk_quiescence(workload::deadline()) };
                if let Err(error) = result {
                    if let Some(admission) = &credit.admission {
                        admission.poison();
                    }
                    return Err(io::Error::other(error.to_string()));
                }
            }
        }
        Ok(())
    }

    /// Whether this credit was already committed to a prior worker dispatch.
    pub fn is_committed(&self) -> bool {
        self.ticket.load(Ordering::Acquire) == COMMITTED
    }

    /// Commit this offered credit once, immediately before dispatching work.
    /// A helper cancellation that wins this race refuses the dispatch. A
    /// committed worker retains its backing until it and its children finish.
    pub fn commit(&mut self) -> bool {
        if let Some(admission) = &self.admission {
            return admission.commit(&self.ticket);
        }
        self.ticket
            .compare_exchange(OFFERED, COMMITTED, Ordering::AcqRel, Ordering::Acquire)
            .is_ok()
    }

    /// The worker's actual CPU backing for a checked child handoff.
    pub fn cpu(&self) -> &Arc<Lease> {
        &self.cpu
    }

    /// The actual epoch fence carried by this credit, if one was supplied.
    pub fn fence(&self) -> Option<&Arc<LegacyFence>> {
        self.fence.as_ref()
    }
}

impl std::fmt::Debug for Credit {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("WorkerCredit")
            .field("cpu", &self.cpu)
            .field("committed", &self.is_committed())
            .finish_non_exhaustive()
    }
}

impl Drop for Credit {
    fn drop(&mut self) {
        #[cfg(all(feature = "native-host", any(target_os = "linux", target_os = "macos")))]
        if self.workload_loan.is_some() {
            // No RPC, return or retry on Drop. The original host/root bank
            // keeps this unresolved entry; this compiler may not lend its
            // primary or admit more extras after losing settlement ownership.
            if let Some(admission) = &self.admission {
                admission.poison();
            }
        }
    }
}

#[derive(Default)]
struct Requests {
    count: usize,
    stop: bool,
    tickets: Vec<Weak<AtomicU8>>,
}

/// Cancellable admission helper; active credits live independently of it.
pub struct WorkerHelper {
    state: Arc<(Mutex<Requests>, Condvar)>,
    thread: Option<JoinHandle<()>>,
}

impl WorkerHelper {
    /// Request one credit for work that is ready to run.
    pub fn request_token(&self) {
        let (lock, wake) = &*self.state;
        let mut state = lock.lock().unwrap_or_else(std::sync::PoisonError::into_inner);
        if state.stop {
            return;
        }
        state.count = state.count.saturating_add(1);
        wake.notify_one();
    }

    /// Withdraw one request made by [`WorkerHelper::request_token`] whose
    /// credit has not been handed to the callback; true if one was withdrawn.
    /// A caller that satisfied its waiter some other way uses this so the
    /// helper stops polling for, and never takes, a credit nobody waits for.
    /// A credit the helper is fetching for the withdrawn request is retired
    /// unused instead of reaching the callback.
    pub fn cancel_request(&self) -> bool {
        let (lock, _) = &*self.state;
        let mut state = lock.lock().unwrap_or_else(std::sync::PoisonError::into_inner);
        if state.stop || state.count == 0 {
            return false;
        }
        state.count -= 1;
        true
    }

    /// The requests whose credit has not been handed to the callback,
    /// including the one the helper is fetching.
    pub fn outstanding_requests(&self) -> usize {
        let (lock, _) = &*self.state;
        lock.lock().unwrap_or_else(std::sync::PoisonError::into_inner).count
    }

    /// [`WorkerHelper::cancel`], then join the helper thread and report how
    /// it ended. `Drop` does the same and discards the outcome; `Err` here
    /// means the thread panicked, which is a panic of the callback.
    pub fn shutdown(mut self) -> io::Result<()> {
        self.cancel();
        match self.thread.take().map(JoinHandle::join) {
            Some(Err(_)) => Err(io::Error::other("worker admission helper thread panicked")),
            Some(Ok(())) | None => Ok(()),
        }
    }

    /// Stop pending admission and revoke offered, uncommitted dispatches.
    /// Already committed work is not revoked and keeps its leases alive.
    pub fn cancel(&self) {
        let (lock, wake) = &*self.state;
        let mut state = lock.lock().unwrap_or_else(std::sync::PoisonError::into_inner);
        state.stop = true;
        for ticket in state.tickets.iter().filter_map(Weak::upgrade) {
            let _ =
                ticket.compare_exchange(OFFERED, CANCELLED, Ordering::AcqRel, Ordering::Acquire);
        }
        wake.notify_one();
    }
}

impl Drop for WorkerHelper {
    fn drop(&mut self) {
        self.cancel();
        if let Some(thread) = self.thread.take() {
            let _ = thread.join();
        }
    }
}

#[cfg(test)]
mod tests;
