// trust-js-reactor: the TrustJS deterministic event loop (M2 D1).
//
// A host-clock-free reactor mirroring the M0 trace driver's proven model
// (crates/trust-js-trace/js/trace_driver.mjs):
//
//   * a FIFO microtask (Promise-job) queue,
//   * a (deadline, seq)-ordered macrotask/timer queue,
//   * a virtual clock that starts at a caller-provided epoch and advances ONLY
//     when the loop pops a timer (never real time),
//   * a REUSABLE Promise state machine (pending/fulfilled/rejected, the
//     already-resolved guard, thenable assimilation via a queued job, reaction
//     records, `then` producing a dependent promise, all/allSettled/race/any),
//   * unhandled-rejection tracking as an observable signal,
//   * and a DRAIN loop: microtasks to empty, then the earliest timer (advancing
//     the clock to its deadline), then microtasks again — until both queues are
//     empty or a step budget trips a typed `ReactorError::Budget`.
//
// Determinism is the invariant. Given the same sequence of enqueue/resolve
// calls the drain order and the virtual-clock values are byte-identical across
// runs: no `Instant::now`, no thread scheduling, and no hash-map iteration order
// in any observable path (microtasks are a `VecDeque`, timers a `BTreeMap` over
// `(deadline, seq)`, the unhandled set an insertion-ordered `IndexMap`, promises
// a dense `Vec`). This is what makes the eventual async ObservableTrace
// byte-reproducible.
//
// The reactor is the ENGINE only: it never interprets JS. Everything requiring
// a JS interpreter is a typed seam on the `Host` trait (see host.rs), which the
// M2 interpreter implements by plugging in its `JsValue` and function-call
// closure.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

mod error;
mod host;
mod types;

pub use error::ReactorError;
pub use host::{Completion, Host, RejectionEvent, ThenLookup};
pub use types::{Capability, PromiseId, PromiseStatus, TimerId};

use indexmap::IndexMap;
use std::cell::RefCell;
use std::collections::{BTreeMap, VecDeque};
use std::rc::Rc;
use types::{
    AggState, Handler, Internal, Job, PromiseRecord, PromiseState, ReactionRecord, TimerEntry,
    TimerKey,
};

/// The deterministic event loop. Generic over the host value type `V` and host
/// callback handle `F`; all engine operations that need a JS interpreter are
/// threaded through a `Host` implementation supplied per call.
pub struct Reactor<V, F> {
    /// FIFO microtask (Promise-job) queue.
    microtasks: VecDeque<Job<V, F>>,
    /// (deadline, seq)-ordered timer queue.
    timers: BTreeMap<TimerKey, TimerEntry<F>>,
    /// TimerId -> its current ordering key, so `clear_timer` is O(log n) and an
    /// interval's stable id survives re-arming.
    id_to_key: BTreeMap<TimerId, TimerKey>,
    /// The virtual clock (advances only when a timer pops).
    clock: u64,
    /// Monotonic sequence for timer ordering + timer ids.
    seq: u64,
    /// Dense promise table, indexed by `PromiseId`.
    promises: Vec<PromiseRecord<V, F>>,
    /// Currently-outstanding unhandled rejections, in signal order.
    outstanding: IndexMap<PromiseId, V>,
    /// Steps spent this reactor's lifetime (jobs + timers), against the budget.
    steps: u64,
    /// The step ceiling; a drain that would exceed it fails closed.
    budget: u64,
}

impl<V, F> Reactor<V, F> {
    /// The default step budget (1e7), mirroring the driver's TIMER_CAP role: a
    /// ceiling that makes runaway rescheduling terminate deterministically.
    pub const DEFAULT_STEP_BUDGET: u64 = 10_000_000;

    /// A reactor whose virtual clock starts at `epoch` (the caller's pinned
    /// FIXED_EPOCH). Default step budget.
    #[must_use]
    pub fn new(epoch: u64) -> Self {
        Self::with_budget(epoch, Self::DEFAULT_STEP_BUDGET)
    }

    /// A reactor with an explicit step budget (for tests that want to trip it).
    #[must_use]
    pub fn with_budget(epoch: u64, budget: u64) -> Self {
        Self {
            microtasks: VecDeque::new(),
            timers: BTreeMap::new(),
            id_to_key: BTreeMap::new(),
            clock: epoch,
            seq: 0,
            promises: Vec::new(),
            outstanding: IndexMap::new(),
            steps: 0,
            budget,
        }
    }

    /// The current virtual-clock value.
    #[must_use]
    pub fn now(&self) -> u64 {
        self.clock
    }

    /// Number of pending microtasks.
    #[must_use]
    pub fn microtasks_pending(&self) -> usize {
        self.microtasks.len()
    }

    /// Number of pending timers.
    #[must_use]
    pub fn timers_pending(&self) -> usize {
        self.timers.len()
    }

    /// Is there any queued work?
    #[must_use]
    pub fn has_work(&self) -> bool {
        !self.microtasks.is_empty() || !self.timers.is_empty()
    }

    /// Steps consumed so far (jobs + timers).
    #[must_use]
    pub fn steps(&self) -> u64 {
        self.steps
    }

    /// The observable status of a promise.
    ///
    /// # Panics
    /// Panics if `id` was never issued by this reactor.
    #[must_use]
    pub fn status(&self, id: PromiseId) -> PromiseStatus {
        match self.promises[id].state {
            PromiseState::Pending => PromiseStatus::Pending,
            PromiseState::Fulfilled(_) => PromiseStatus::Fulfilled,
            PromiseState::Rejected(_) => PromiseStatus::Rejected,
        }
    }

    fn next_seq(&mut self) -> u64 {
        let s = self.seq;
        self.seq += 1;
        s
    }

    fn charge(&mut self) -> Result<(), ReactorError> {
        self.steps += 1;
        if self.steps > self.budget {
            Err(ReactorError::Budget { limit: self.budget })
        } else {
            Ok(())
        }
    }
}

impl<V: Clone, F: Clone> Reactor<V, F> {
    /// The settled value/reason of a promise, if settled. Cloned out.
    ///
    /// # Panics
    /// Panics if `id` was never issued by this reactor.
    #[must_use]
    pub fn settled_value(&self, id: PromiseId) -> Option<V> {
        match &self.promises[id].state {
            PromiseState::Pending => None,
            PromiseState::Fulfilled(v) | PromiseState::Rejected(v) => Some(v.clone()),
        }
    }

    /// The currently-outstanding unhandled rejections, in signal order (id +
    /// reason). Empty once every rejection has been handled.
    #[must_use]
    pub fn unhandled_rejections(&self) -> Vec<(PromiseId, V)> {
        self.outstanding
            .iter()
            .map(|(id, r)| (*id, r.clone()))
            .collect()
    }

    // -- queueing ----------------------------------------------------------

    /// `queueMicrotask(f)` — enqueue a host job onto the microtask queue.
    pub fn queue_microtask(&mut self, f: F) {
        self.microtasks.push_back(Job::HostMicrotask(f));
    }

    /// Arm a one-shot timer (`setTimeout`): fire `f` at `now() + delay`. Returns
    /// its id.
    pub fn set_timeout(&mut self, f: F, delay: u64) -> TimerId {
        self.arm(f, delay, None)
    }

    /// Arm a periodic timer (`setInterval`): fire `f` every `delay`, re-arming
    /// after each firing. Returns its stable id.
    pub fn set_interval(&mut self, f: F, delay: u64) -> TimerId {
        self.arm(f, delay, Some(delay))
    }

    fn arm(&mut self, f: F, delay: u64, interval: Option<u64>) -> TimerId {
        let s = self.next_seq();
        let id = s;
        let key: TimerKey = (self.clock.saturating_add(delay), s);
        self.id_to_key.insert(id, key);
        self.timers.insert(key, TimerEntry { id, f, interval });
        id
    }

    /// Cancel a timer (`clearTimeout` / `clearInterval`). A no-op if the id is
    /// unknown or already fired (for a one-shot).
    pub fn clear_timer(&mut self, id: TimerId) {
        if let Some(key) = self.id_to_key.remove(&id) {
            self.timers.remove(&key);
        }
    }

    // -- promise construction ---------------------------------------------

    /// Create a fresh pending promise and its primary resolving capability
    /// (`new Promise(executor)` gives the executor this capability's
    /// resolve/reject).
    pub fn new_promise(&mut self) -> (PromiseId, Capability) {
        let id = self.promises.len();
        self.promises.push(PromiseRecord {
            state: PromiseState::Pending,
            fulfill_reactions: Vec::new(),
            reject_reactions: Vec::new(),
            handled: false,
        });
        (id, Capability::new(id))
    }

    /// A fresh resolving capability for an EXISTING promise, with its own guard
    /// (the spec's CreateResolvingFunctions, as PromiseResolveThenableJob mints).
    fn resolving_functions(&mut self, promise: PromiseId) -> Capability {
        Capability::new(promise)
    }

    // -- resolve / reject (the resolving functions) -----------------------

    /// The promise resolve function: `resolve(value)` with the already-resolved
    /// guard, self-resolution check, and thenable assimilation via a queued job.
    pub fn resolve<H: Host<Value = V, Fn = F>>(
        &mut self,
        host: &mut H,
        cap: &Capability,
        value: V,
    ) {
        if !cap.claim() {
            return;
        }
        if host.promise_of(&value) == Some(cap.promise) {
            let e = host.type_error("Chaining cycle detected for promise");
            self.reject_promise(host, cap.promise, e);
            return;
        }
        match host.get_then(self, &value) {
            ThenLookup::Threw(e) => self.reject_promise(host, cap.promise, e),
            ThenLookup::NotThenable => self.fulfill_promise(cap.promise, value),
            ThenLookup::Thenable(then) => self.microtasks.push_back(Job::ResolveThenable {
                promise: cap.promise,
                thenable: value,
                then,
            }),
        }
    }

    /// The promise reject function: `reject(reason)` with the already-resolved
    /// guard (RejectPromise, no thenable check).
    pub fn reject<H: Host<Value = V, Fn = F>>(&mut self, host: &mut H, cap: &Capability, reason: V) {
        if !cap.claim() {
            return;
        }
        self.reject_promise(host, cap.promise, reason);
    }

    /// FulfillPromise: settle `pid` fulfilled, enqueue its fulfill reactions.
    fn fulfill_promise(&mut self, pid: PromiseId, value: V) {
        let reactions = {
            let p = &mut self.promises[pid];
            if !matches!(p.state, PromiseState::Pending) {
                return;
            }
            p.reject_reactions.clear();
            p.state = PromiseState::Fulfilled(value.clone());
            std::mem::take(&mut p.fulfill_reactions)
        };
        for r in reactions {
            self.microtasks.push_back(Job::Reaction {
                handler: r.handler,
                arg: value.clone(),
                cap: r.cap,
            });
        }
    }

    /// RejectPromise: settle `pid` rejected, enqueue its reject reactions, and —
    /// if the promise was never handled — raise the unhandled-rejection signal.
    fn reject_promise<H: Host<Value = V, Fn = F>>(&mut self, host: &mut H, pid: PromiseId, reason: V) {
        let (reactions, handled) = {
            let p = &mut self.promises[pid];
            if !matches!(p.state, PromiseState::Pending) {
                return;
            }
            p.fulfill_reactions.clear();
            p.state = PromiseState::Rejected(reason.clone());
            (std::mem::take(&mut p.reject_reactions), p.handled)
        };
        for r in reactions {
            self.microtasks.push_back(Job::Reaction {
                handler: r.handler,
                arg: reason.clone(),
                cap: r.cap,
            });
        }
        if !handled {
            self.outstanding.insert(pid, reason.clone());
            host.on_rejection(RejectionEvent::Rejected {
                promise: pid,
                reason,
            });
        }
    }

    // -- then / catch ------------------------------------------------------

    /// PerformPromiseThen with a dependent promise: attach `on_fulfilled` /
    /// `on_rejected` (each `None` = the default identity/thrower) and return the
    /// dependent promise. This is `p.then(onF, onR)`.
    pub fn then<H: Host<Value = V, Fn = F>>(
        &mut self,
        host: &mut H,
        promise: PromiseId,
        on_fulfilled: Option<F>,
        on_rejected: Option<F>,
    ) -> PromiseId {
        let (result, cap) = self.new_promise();
        let fh = on_fulfilled.map_or(Handler::Identity, Handler::Host);
        let rh = on_rejected.map_or(Handler::Thrower, Handler::Host);
        self.perform_then(host, promise, fh, rh, Some(cap));
        result
    }

    /// `p.catch(onRejected)` == `p.then(undefined, onRejected)`.
    pub fn catch<H: Host<Value = V, Fn = F>>(
        &mut self,
        host: &mut H,
        promise: PromiseId,
        on_rejected: F,
    ) -> PromiseId {
        self.then(host, promise, None, Some(on_rejected))
    }

    /// PerformPromiseThen core: either register the reactions (pending) or
    /// enqueue a reaction job now (already settled). Marks the promise handled;
    /// if it was an outstanding unhandled rejection, raises the "handled" signal.
    fn perform_then<H: Host<Value = V, Fn = F>>(
        &mut self,
        host: &mut H,
        pid: PromiseId,
        fulfill_handler: Handler<V, F>,
        reject_handler: Handler<V, F>,
        cap: Option<Capability>,
    ) {
        let mut emit_handled = false;
        let job;
        {
            let p = &mut self.promises[pid];
            let already_handled = p.handled;
            p.handled = true;
            match &p.state {
                PromiseState::Pending => {
                    p.fulfill_reactions.push(ReactionRecord {
                        handler: fulfill_handler,
                        cap: cap.clone(),
                    });
                    p.reject_reactions.push(ReactionRecord {
                        handler: reject_handler,
                        cap,
                    });
                    return;
                }
                PromiseState::Fulfilled(v) => {
                    job = Job::Reaction {
                        handler: fulfill_handler,
                        arg: v.clone(),
                        cap,
                    };
                }
                PromiseState::Rejected(e) => {
                    emit_handled = !already_handled;
                    job = Job::Reaction {
                        handler: reject_handler,
                        arg: e.clone(),
                        cap,
                    };
                }
            }
        }
        if emit_handled {
            self.outstanding.shift_remove(&pid);
            host.on_rejection(RejectionEvent::Handled { promise: pid });
        }
        self.microtasks.push_back(job);
    }

    // -- Promise.resolve / reject ------------------------------------------

    /// `Promise.resolve(value)`: return `value` if it is already one of this
    /// reactor's promises, else a new promise resolved with `value`.
    pub fn promise_resolve<H: Host<Value = V, Fn = F>>(&mut self, host: &mut H, value: V) -> PromiseId {
        if let Some(pid) = host.promise_of(&value) {
            return pid;
        }
        let (p, cap) = self.new_promise();
        self.resolve(host, &cap, value);
        p
    }

    /// `Promise.reject(reason)`: a new promise rejected with `reason` (initially
    /// unhandled).
    pub fn promise_reject<H: Host<Value = V, Fn = F>>(&mut self, host: &mut H, reason: V) -> PromiseId {
        let (p, cap) = self.new_promise();
        self.reject(host, &cap, reason);
        p
    }

    // -- combinators -------------------------------------------------------

    /// `Promise.all(elements)` — fulfill with an ordered array of the elements'
    /// values, or reject with the first rejection. The consumer supplies the
    /// already-iterated element values; the reactor coerces each with
    /// `promise_resolve` and orchestrates the aggregation.
    pub fn promise_all<H: Host<Value = V, Fn = F>>(&mut self, host: &mut H, elements: Vec<V>) -> PromiseId {
        let (result, cap) = self.new_promise();
        let n = elements.len();
        if n == 0 {
            let arr = host.build_array(Vec::new());
            self.resolve(host, &cap, arr);
            return result;
        }
        let state = Rc::new(RefCell::new(AggState {
            slots: (0..n).map(|_| None).collect(),
            remaining: n,
            cap: cap.clone(),
            settled: false,
        }));
        for (index, v) in elements.into_iter().enumerate() {
            let ep = self.promise_resolve(host, v);
            self.perform_then(
                host,
                ep,
                Handler::Internal(Internal::AllFulfill {
                    state: state.clone(),
                    index,
                }),
                Handler::Internal(Internal::RejectMain { cap: cap.clone() }),
                None,
            );
        }
        result
    }

    /// `Promise.allSettled(elements)` — never rejects; fulfills with an ordered
    /// array of `{status,value}` / `{status,reason}` records.
    pub fn promise_all_settled<H: Host<Value = V, Fn = F>>(
        &mut self,
        host: &mut H,
        elements: Vec<V>,
    ) -> PromiseId {
        let (result, cap) = self.new_promise();
        let n = elements.len();
        if n == 0 {
            let arr = host.build_array(Vec::new());
            self.resolve(host, &cap, arr);
            return result;
        }
        let state = Rc::new(RefCell::new(AggState {
            slots: (0..n).map(|_| None).collect(),
            remaining: n,
            cap,
            settled: false,
        }));
        for (index, v) in elements.into_iter().enumerate() {
            let ep = self.promise_resolve(host, v);
            self.perform_then(
                host,
                ep,
                Handler::Internal(Internal::SettledFulfill {
                    state: state.clone(),
                    index,
                }),
                Handler::Internal(Internal::SettledReject {
                    state: state.clone(),
                    index,
                }),
                None,
            );
        }
        result
    }

    /// `Promise.race(elements)` — settle with the first element to settle
    /// (fulfill or reject). Empty input stays forever pending, per spec.
    pub fn promise_race<H: Host<Value = V, Fn = F>>(&mut self, host: &mut H, elements: Vec<V>) -> PromiseId {
        let (result, cap) = self.new_promise();
        for v in elements {
            let ep = self.promise_resolve(host, v);
            self.perform_then(
                host,
                ep,
                Handler::Internal(Internal::ResolveMain { cap: cap.clone() }),
                Handler::Internal(Internal::RejectMain { cap: cap.clone() }),
                None,
            );
        }
        result
    }

    /// `Promise.any(elements)` — fulfill with the first element to fulfill; if
    /// all reject, reject with an AggregateError of the ordered reasons. Empty
    /// input rejects with an AggregateError immediately, per spec.
    pub fn promise_any<H: Host<Value = V, Fn = F>>(&mut self, host: &mut H, elements: Vec<V>) -> PromiseId {
        let (result, cap) = self.new_promise();
        let n = elements.len();
        if n == 0 {
            let agg = host.build_aggregate_error(Vec::new());
            self.reject(host, &cap, agg);
            return result;
        }
        let state = Rc::new(RefCell::new(AggState {
            slots: (0..n).map(|_| None).collect(),
            remaining: n,
            cap: cap.clone(),
            settled: false,
        }));
        for (index, v) in elements.into_iter().enumerate() {
            let ep = self.promise_resolve(host, v);
            self.perform_then(
                host,
                ep,
                Handler::Internal(Internal::ResolveMain { cap: cap.clone() }),
                Handler::Internal(Internal::AnyReject {
                    state: state.clone(),
                    index,
                }),
                None,
            );
        }
        result
    }

    // -- the drain loop ----------------------------------------------------

    /// Drain to quiescence: all microtasks, then the earliest timer (advancing
    /// the virtual clock to its deadline), then all microtasks again — repeating
    /// until both queues are empty. Returns `Err(ReactorError::Budget)` if the
    /// step budget is exhausted first. This is exactly the M0 driver's
    /// `drainMicrotasks(); drainTimers()` discipline.
    pub fn drain<H: Host<Value = V, Fn = F>>(&mut self, host: &mut H) -> Result<(), ReactorError> {
        loop {
            self.drain_microtasks(host)?;
            let key = match self.timers.keys().next().copied() {
                Some(k) => k,
                None => break,
            };
            let entry = self.timers.remove(&key).expect("key just observed");
            self.id_to_key.remove(&entry.id);
            self.clock = key.0;
            if let Some(period) = entry.interval {
                // Re-arm at clock+period with a fresh ordering seq but the SAME
                // stable id, so clearInterval still finds it. A zero period
                // storm cannot advance the clock and is bounded by the budget.
                let s = self.next_seq();
                let nk: TimerKey = (self.clock.saturating_add(period), s);
                self.id_to_key.insert(entry.id, nk);
                self.timers.insert(
                    nk,
                    TimerEntry {
                        id: entry.id,
                        f: entry.f.clone(),
                        interval: Some(period),
                    },
                );
            }
            self.charge()?;
            host.run_callback(self, &entry.f);
        }
        Ok(())
    }

    /// Run all queued microtasks to empty (draining any they enqueue in turn).
    pub fn drain_microtasks<H: Host<Value = V, Fn = F>>(
        &mut self,
        host: &mut H,
    ) -> Result<(), ReactorError> {
        while let Some(job) = self.microtasks.pop_front() {
            self.charge()?;
            self.run_job(host, job);
        }
        Ok(())
    }

    fn run_job<H: Host<Value = V, Fn = F>>(&mut self, host: &mut H, job: Job<V, F>) {
        match job {
            Job::HostMicrotask(f) => host.run_callback(self, &f),
            Job::Reaction { handler, arg, cap } => self.run_reaction(host, handler, arg, cap),
            Job::ResolveThenable {
                promise,
                thenable,
                then,
            } => {
                let cap = self.resolving_functions(promise);
                match host.call_then(self, &then, &thenable, cap.clone(), cap.clone()) {
                    Completion::Normal(_) => {}
                    Completion::Throw(e) => self.reject(host, &cap, e),
                }
            }
        }
    }

    fn run_reaction<H: Host<Value = V, Fn = F>>(
        &mut self,
        host: &mut H,
        handler: Handler<V, F>,
        arg: V,
        cap: Option<Capability>,
    ) {
        match handler {
            Handler::Identity => {
                if let Some(c) = cap {
                    self.resolve(host, &c, arg);
                }
            }
            Handler::Thrower => {
                if let Some(c) = cap {
                    self.reject(host, &c, arg);
                }
            }
            Handler::Host(f) => match host.call(self, &f, arg) {
                Completion::Normal(x) => {
                    if let Some(c) = cap {
                        self.resolve(host, &c, x);
                    }
                }
                Completion::Throw(e) => {
                    if let Some(c) = cap {
                        self.reject(host, &c, e);
                    }
                }
            },
            Handler::Internal(ir) => self.run_internal(host, ir, arg),
        }
    }

    fn run_internal<H: Host<Value = V, Fn = F>>(&mut self, host: &mut H, ir: Internal<V>, arg: V) {
        match ir {
            Internal::ResolveMain { cap } => self.resolve(host, &cap, arg),
            Internal::RejectMain { cap } => self.reject(host, &cap, arg),
            Internal::AllFulfill { state, index } => {
                if let Some((vals, cap)) = collect(&state, index, arg) {
                    let arr = host.build_array(vals);
                    self.resolve(host, &cap, arr);
                }
            }
            Internal::SettledFulfill { state, index } => {
                let obj = host.build_settled_fulfilled(arg);
                if let Some((vals, cap)) = collect(&state, index, obj) {
                    let arr = host.build_array(vals);
                    self.resolve(host, &cap, arr);
                }
            }
            Internal::SettledReject { state, index } => {
                let obj = host.build_settled_rejected(arg);
                if let Some((vals, cap)) = collect(&state, index, obj) {
                    let arr = host.build_array(vals);
                    self.resolve(host, &cap, arr);
                }
            }
            Internal::AnyReject { state, index } => {
                if let Some((errs, cap)) = collect(&state, index, arg) {
                    let agg = host.build_aggregate_error(errs);
                    self.reject(host, &cap, agg);
                }
            }
        }
    }
}

/// Store `item` at `index` in the shared aggregation state, decrement the
/// remaining count, and — when it hits zero — take the ordered items out and
/// return them with the aggregate capability. `None` while more are pending or
/// if the aggregate already settled. The RefCell borrow is released before the
/// caller touches the host, so no borrow is held across a host call.
fn collect<V>(state: &Rc<RefCell<AggState<V>>>, index: usize, item: V) -> Option<(Vec<V>, Capability)> {
    let mut s = state.borrow_mut();
    if s.settled {
        return None;
    }
    s.slots[index] = Some(item);
    s.remaining -= 1;
    if s.remaining == 0 {
        s.settled = true;
        let vals = s.slots.drain(..).map(|o| o.expect("all slots filled")).collect();
        let cap = s.cap.clone();
        Some((vals, cap))
    } else {
        None
    }
}
