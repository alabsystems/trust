//! Keep each codegen worker's original credit until its actual thread joins.

use std::collections::HashMap;
use std::io;
use std::thread::{JoinHandle, ThreadId};

struct Running<C> {
    thread: JoinHandle<()>,
    credit: Option<C>,
}

pub(super) struct Workers<C> {
    running: HashMap<ThreadId, Running<C>>,
    implicit: Option<ThreadId>,
}

impl<C> Workers<C> {
    pub(super) fn new() -> Self {
        Self { running: HashMap::new(), implicit: None }
    }

    pub(super) fn start(&mut self, thread: JoinHandle<()>, credit: Option<C>) {
        let id = thread.thread().id();
        assert!(!self.running.contains_key(&id), "codegen worker registered twice");
        if credit.is_none() {
            assert!(self.implicit.replace(id).is_none(), "implicit codegen unit used twice");
        }
        self.running.insert(id, Running { thread, credit });
    }

    /// A fresh, committed original extra may fund the already-running worker,
    /// allowing the frontend to resume on its actual implicit unit. This
    /// returns no credit or completion claim for either task.
    pub(super) fn fund_implicit(&mut self, credit: C) {
        let id = self.implicit.take().expect("no implicit codegen worker to fund");
        let running = self.running.get_mut(&id).expect("implicit codegen worker is absent");
        assert!(running.credit.replace(credit).is_none(), "implicit worker already funded");
    }

    /// Notification is only a lookup key. The exact original handle must join
    /// before its credit can be returned. A panic or absent handle is unknown.
    pub(super) fn finish(&mut self, id: ThreadId) -> io::Result<Option<C>> {
        let running = self
            .running
            .remove(&id)
            .ok_or_else(|| io::Error::other("codegen completion has no original worker"))?;
        running.thread.join().map_err(|_| io::Error::other("codegen worker join failed"))?;
        if running.credit.is_none() {
            if self.implicit != Some(id) {
                return Err(io::Error::other("codegen implicit ownership changed"));
            }
            self.implicit = None;
        }
        Ok(running.credit)
    }

    pub(super) fn is_empty(&self) -> bool {
        self.running.is_empty() && self.implicit.is_none()
    }

    pub(super) fn has_implicit(&self) -> bool {
        self.implicit.is_some()
    }
}

impl<C> Drop for Workers<C> {
    fn drop(&mut self) {
        // A failed coordinator still owns its producing siblings. Joining is
        // cleanup, never successful codegen: preserve the original unwind and
        // do not manufacture a bank return for an unsettled workload loan.
        for (_, running) in self.running.drain() {
            let _ = running.thread.join();
            drop(running.credit);
        }
        self.implicit = None;
    }
}

#[cfg(test)]
#[path = "worker_ownership/tests.rs"]
mod tests;
