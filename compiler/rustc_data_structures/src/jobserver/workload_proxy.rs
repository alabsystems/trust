//! Exact SDK thread-pool ownership of the original primary and worker loans.

use std::collections::HashMap;
use std::sync::Arc;
use std::thread::ThreadId;

use super::{Acquired, Proxy, native_park};

enum Funding {
    Implicit,
    Extra(Acquired),
}

pub(super) struct Assignments {
    active: HashMap<ThreadId, Vec<Funding>>,
    implicit_occupied: bool,
}

impl Assignments {
    pub(super) fn new(owner: ThreadId) -> Self {
        Self { active: HashMap::from([(owner, vec![Funding::Implicit])]), implicit_occupied: true }
    }

    pub(super) fn implicit_available(&self) -> bool {
        !self.implicit_occupied
    }

    fn assign(&mut self, owner: ThreadId, credit: Option<Acquired>) {
        let funding = match credit {
            Some(credit) => Funding::Extra(credit),
            None => {
                assert!(!self.implicit_occupied, "workload primary used twice");
                self.implicit_occupied = true;
                Funding::Implicit
            }
        };
        self.active.entry(owner).or_default().push(funding);
    }

    fn release(&mut self, owner: ThreadId) -> Option<Acquired> {
        let stack = self.active.get_mut(&owner).expect("workload task has no original funding");
        let funding = stack.pop().expect("workload funding stack is empty");
        if stack.is_empty() {
            self.active.remove(&owner);
        }
        match funding {
            Funding::Extra(credit) => Some(credit),
            Funding::Implicit => {
                assert!(self.implicit_occupied, "workload primary ownership changed");
                self.implicit_occupied = false;
                None
            }
        }
    }

    pub(super) fn matches(&self, active: &HashMap<ThreadId, u16>) -> bool {
        self.active.len() == active.len()
            && self
                .active
                .iter()
                .all(|(id, stack)| active.get(id).copied().map(usize::from) == Some(stack.len()))
            && self
                .active
                .values()
                .flatten()
                .filter(|funding| matches!(funding, Funding::Implicit))
                .count()
                == usize::from(self.implicit_occupied)
    }
}

pub(super) fn acquire(proxy: &Proxy, registry: &Arc<native_park::Registry>) {
    let mut requested = false;
    loop {
        let admission = registry.enter().expect("workload dispatch is parked or poisoned");
        let mut data = proxy.shared.data.lock();
        assert!(data.error.is_none(), "workload admission failed: {:?}", data.error);
        let credit = if requested && !data.tokens.is_empty() {
            let mut credit = data.tokens.pop().expect("workload reserved offer absent");
            if !credit.commit() {
                data.used = data.used.checked_sub(1).expect("workload reservation underflow");
                drop(data);
                credit.retire_unused().expect("cancelled workload offer settlement failed");
                proxy.request_token();
                drop(admission);
                continue;
            }
            data.pending = data.pending.checked_sub(1).expect("workload pending underflow");
            Some(credit)
        } else if data.workload.as_ref().expect("workload assignments absent").implicit_available()
        {
            if requested {
                data.pending = data.pending.checked_sub(1).expect("workload pending underflow");
            }
            data.used = data.used.checked_add(1).expect("workload active overflow");
            None
        } else {
            if !requested {
                // Trust (RUSTC-FRONTEND-TOKEN-LEAK-1): file the request
                // first, as the other two waiters do. It panics once the
                // helper is retired, and must not leave a waiter counted
                // that filed nothing.
                proxy.request_token();
                data.pending = data.pending.checked_add(1).expect("workload pending overflow");
                requested = true;
            }
            drop(admission);
            proxy.shared.wake_pending.wait(&mut data);
            drop(data);
            continue;
        };
        let owner = std::thread::current().id();
        data.workload.as_mut().expect("workload assignments absent").assign(owner, credit);
        let active = data.active.as_mut().expect("workload active tracking absent");
        let count = active.entry(owner).or_default();
        *count = count.checked_add(1).expect("workload active count overflow");
        return;
    }
}

pub(super) fn release(proxy: &Proxy) {
    let registry = proxy.shared.registry.as_ref().expect("workload registry absent");
    let _admission = registry.enter().expect("workload release after unresolved loan");
    let mut data = proxy.shared.data.lock();
    let owner = std::thread::current().id();
    let credit = data.workload.as_mut().expect("workload assignments absent").release(owner);
    let active = data.active.as_mut().expect("workload active tracking absent");
    let count = active.get_mut(&owner).expect("workload task released without dispatch");
    *count = count.checked_sub(1).expect("workload active count underflow");
    if *count == 0 {
        active.remove(&owner);
    }
    data.used = data.used.checked_sub(1).expect("workload use count underflow");
    proxy.shared.wake_pending.notify_all();
    drop(data);
    if let Some(credit) = credit {
        // SAFETY: the maintained SDK thread pool invokes this release handler
        // after its producing work quiesces, before sleeping or reacquisition.
        // The exact releasing thread's original credit is removed above;
        // admission stays serialized through the authenticated return ACK.
        unsafe { credit.retire_after_sdk_quiescence() }
            .expect("workload SDK task settlement failed");
    }
}

#[cfg(test)]
#[path = "workload_proxy/tests.rs"]
mod tests;
