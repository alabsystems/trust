// Promises + the deterministic job model (ECMA-262 §9.5, §27.2): a microtask
// (Promise-job) FIFO queue and a virtual-timer queue drained after the script
// body, in the EXACT order the trace driver's drainMicrotasks/drainTimers
// define (microtasks to empty, then the earliest-deadline-then-insertion
// timer, repeat). This is an INDEPENDENT implementation written from the spec
// text and calibrated against the driver's algorithm — it shares no code with
// the faithful reactor tier, so the differential over async ordering is
// meaningful.
//
// SOUNDNESS. Every promise algorithm is the spec's; anything the slice cannot
// drive exactly (a patched intrinsic combinator path, a custom @@species /
// subclass, an out-of-slice iterable) is an `Abrupt::Fatal` refusal
// (NoCoverage), never a wrong trace. Runaway rescheduling (an unbounded
// microtask storm — which would hang the real driver) hits a budget cap and
// refuses; the virtual-timer drain honours the driver's TIMER_CAP with the
// same `timer-cap` host event.
//
// Author: Andrew Yates
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

use crate::interp::{Abrupt, ERes, Interp};
use crate::value::{
    units_from_str, GenId, NativeErrorKind, ObjId, ObjKind, Object, Prop, PromiseId, Value,
};
use std::cell::{Cell, RefCell};
use std::rc::Rc;

/// The driver's virtual-timer cap (TIMER_CAP): beyond it the drain records a
/// `timer-cap` host event and stops, exactly like the driver.
pub const TIMER_CAP: u64 = 10_000;

/// A hard cap on jobs run across one drain. The real driver hangs on an
/// unbounded microtask storm (V8's checkpoint drains to empty); we refuse
/// instead — both are "no verdict", never a wrong trace.
pub const JOB_BUDGET: u64 = 2_000_000;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum PromiseSt {
    Pending,
    Fulfilled,
    Rejected,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ReactionKind {
    Fulfill,
    Reject,
}

/// A promise reaction's [[Handler]] (27.2.1.2): empty (identity for a fulfill
/// reaction, thrower for a reject reaction) or a JobCallback function.
#[derive(Debug, Clone)]
pub(crate) enum Handler {
    Empty,
    Func(Value),
}

/// A PromiseCapability record (27.2.1.1): the promise plus its resolve/reject
/// functions.
#[derive(Debug, Clone)]
pub(crate) struct Capability {
    pub promise: Value,
    pub resolve: Value,
    pub reject: Value,
}

/// A PromiseReaction record (27.2.1.2). Its [[Type]] is implied by which list
/// (fulfill/reject) it lives in, so the kind is supplied at trigger time.
#[derive(Debug, Clone)]
pub(crate) struct Reaction {
    pub capability: Option<Capability>,
    pub handler: Handler,
}

/// The mutable state behind one Promise instance.
pub(crate) struct PromiseState {
    pub obj: ObjId,
    pub state: PromiseSt,
    pub result: Value,
    pub fulfill_reactions: Vec<Reaction>,
    pub reject_reactions: Vec<Reaction>,
    #[allow(dead_code)]
    pub is_handled: bool,
}

/// A dynamically-created internal function object with captured state.
#[derive(Debug, Clone)]
pub(crate) enum NativeClosure {
    /// A resolve function (27.2.1.3.2), sharing `already` with its reject.
    Resolve {
        pid: PromiseId,
        already: Rc<Cell<bool>>,
    },
    /// A reject function (27.2.1.3.1).
    Reject {
        pid: PromiseId,
        already: Rc<Cell<bool>>,
    },
    /// An async-function await resume handler (27.7.5.3 Await): resumes the
    /// suspended async execution with a normal (`is_throw` false) or throw
    /// completion.
    AsyncResume { gid: GenId, is_throw: bool },
    /// A Promise.all Resolve Element function (27.2.4.1.3).
    AllResolveElement {
        index: usize,
        values: Rc<RefCell<Vec<Value>>>,
        capability: Capability,
        remaining: Rc<Cell<usize>>,
        already: Rc<Cell<bool>>,
    },
    /// A Promise.allSettled Resolve/Reject Element function (27.2.4.2.3-4).
    AllSettledElement {
        is_reject: bool,
        index: usize,
        values: Rc<RefCell<Vec<Value>>>,
        capability: Capability,
        remaining: Rc<Cell<usize>>,
        already: Rc<Cell<bool>>,
    },
    /// A Promise.any Reject Element function (27.2.4.3.3).
    AnyRejectElement {
        index: usize,
        errors: Rc<RefCell<Vec<Value>>>,
        capability: Capability,
        remaining: Rc<Cell<usize>>,
        already: Rc<Cell<bool>>,
    },
    /// A `then` finally / `catch` finally function (27.2.5.3.1-2).
    ThenFinally { on_finally: Value },
    CatchFinally { on_finally: Value },
    /// The finally value-thunk (returns the captured value) / thrower.
    FinallyValueThunk(Value),
    FinallyThrower(Value),
    /// A Proxy Revocation Function (28.2.2.1.1): revokes `proxy` by clearing
    /// its [[ProxyTarget]]/[[ProxyHandler]] to null (idempotent).
    ProxyRevoke { proxy: ObjId },
}

/// One queued Promise-job / microtask.
pub(crate) enum Job {
    /// A PromiseReactionJob (27.2.2.1).
    Reaction {
        handler: Handler,
        capability: Option<Capability>,
        kind: ReactionKind,
        argument: Value,
    },
    /// A NewPromiseResolveThenableJob (27.2.2.2).
    Thenable {
        pid: PromiseId,
        thenable: Value,
        then: Value,
    },
    /// A `queueMicrotask(cb)` callback.
    Callback { func: Value },
}

/// One scheduled virtual timer.
pub(crate) struct Timer {
    /// Insertion order = the numeric id returned by setTimeout (the driver
    /// uses the same counter for both).
    pub seq: u64,
    pub time: f64,
    pub cb: Value,
    pub args: Vec<Value>,
    pub interval: Option<f64>,
}

impl Interp {
    // -- promise arena helpers ---------------------------------------------

    /// The `PromiseId` behind a value, if it is a Promise instance.
    pub(crate) fn as_promise(&self, v: &Value) -> Option<PromiseId> {
        match v {
            Value::Obj(o) => match self.obj(*o).kind {
                ObjKind::Promise(p) => Some(p),
                _ => None,
            },
            _ => None,
        }
    }

    /// Allocate a fresh pending Promise object with the given [[Prototype]].
    pub(crate) fn alloc_promise(&mut self, proto: ObjId) -> (PromiseId, ObjId) {
        let pid = PromiseId(u32::try_from(self.promises.len()).expect("promises bounded"));
        self.promises.push(PromiseState {
            obj: ObjId(0),
            state: PromiseSt::Pending,
            result: Value::Undefined,
            fulfill_reactions: Vec::new(),
            reject_reactions: Vec::new(),
            is_handled: false,
        });
        let oid = self.alloc(Object::new(ObjKind::Promise(pid), Some(proto)));
        self.promises[pid.0 as usize].obj = oid;
        (pid, oid)
    }

    /// CreateResolvingFunctions (27.2.1.3): the resolve/reject pair sharing an
    /// [[AlreadyResolved]] cell.
    pub(crate) fn create_resolving_functions(&mut self, pid: PromiseId) -> (Value, Value) {
        let already = Rc::new(Cell::new(false));
        let resolve = self.alloc_native(NativeClosure::Resolve {
            pid,
            already: Rc::clone(&already),
        });
        let reject = self.alloc_native(NativeClosure::Reject { pid, already });
        (resolve, reject)
    }

    /// Allocate a native-closure function object (length 1, name "", proto
    /// %Function.prototype%).
    pub(crate) fn alloc_native(&mut self, nc: NativeClosure) -> Value {
        // The finally value-thunk (returns the captured value) and thrower
        // (throws the captured reason) each have length 0; every other internal
        // closure has length 1.
        let len = if matches!(
            nc,
            NativeClosure::FinallyValueThunk(_)
                | NativeClosure::FinallyThrower(_)
                | NativeClosure::ProxyRevoke { .. }
        ) {
            0.0
        } else {
            1.0
        };
        let oid = self.alloc(Object::new(
            ObjKind::Function(crate::value::FnImpl::Native(Rc::new(nc))),
            Some(self.intr.function_proto),
        ));
        self.obj_mut(oid).props.insert(
            units_from_str("length"),
            Prop::with_attrs(Value::Num(len), false, false, true),
        );
        self.obj_mut(oid).props.insert(
            units_from_str("name"),
            Prop::with_attrs(Value::str_from(""), false, false, true),
        );
        Value::Obj(oid)
    }

    /// A default (%Promise%) PromiseCapability: a fresh pending promise plus
    /// its resolving functions. Observably identical to
    /// NewPromiseCapability(%Promise%) — used on the fast path where the
    /// constructor/@@species are the untampered intrinsics.
    pub(crate) fn new_promise_capability_default(&mut self) -> Capability {
        let (pid, oid) = self.alloc_promise(self.intr.promise_proto);
        let (resolve, reject) = self.create_resolving_functions(pid);
        Capability {
            promise: Value::Obj(oid),
            resolve,
            reject,
        }
    }

    // -- fulfil / reject / trigger -----------------------------------------

    /// FulfillPromise (27.2.1.4).
    pub(crate) fn fulfill_promise(&mut self, pid: PromiseId, value: Value) {
        let reactions = std::mem::take(&mut self.promises[pid.0 as usize].fulfill_reactions);
        {
            let ps = &mut self.promises[pid.0 as usize];
            ps.result = value.clone();
            ps.state = PromiseSt::Fulfilled;
            ps.reject_reactions.clear();
        }
        self.trigger_reactions(reactions, ReactionKind::Fulfill, value);
    }

    /// RejectPromise (27.2.1.7).
    pub(crate) fn reject_promise(&mut self, pid: PromiseId, reason: Value) {
        let reactions = std::mem::take(&mut self.promises[pid.0 as usize].reject_reactions);
        {
            let ps = &mut self.promises[pid.0 as usize];
            ps.result = reason.clone();
            ps.state = PromiseSt::Rejected;
            ps.fulfill_reactions.clear();
        }
        self.trigger_reactions(reactions, ReactionKind::Reject, reason);
    }

    /// TriggerPromiseReactions (27.2.1.8): enqueue a reaction job per reaction,
    /// in list (FIFO) order.
    fn trigger_reactions(&mut self, reactions: Vec<Reaction>, kind: ReactionKind, arg: Value) {
        for r in reactions {
            self.microtasks.push_back(Job::Reaction {
                handler: r.handler,
                capability: r.capability,
                kind,
                argument: arg.clone(),
            });
        }
    }

    // -- resolve function semantics ----------------------------------------

    /// The body of a resolve function (27.2.1.3.2).
    fn resolve_promise_with(
        &mut self,
        pid: PromiseId,
        already: &Rc<Cell<bool>>,
        resolution: Value,
    ) -> Result<(), Abrupt> {
        if already.get() {
            return Ok(());
        }
        already.set(true);
        // Self-resolution: reject with a TypeError.
        let self_obj = self.promises[pid.0 as usize].obj;
        if let Value::Obj(r) = &resolution {
            if *r == self_obj {
                let e = self.make_native_error(NativeErrorKind::TypeError, true);
                self.reject_promise(pid, Value::Obj(e));
                return Ok(());
            }
        }
        let Value::Obj(roid) = resolution else {
            self.fulfill_promise(pid, resolution);
            return Ok(());
        };
        // then = Get(resolution, "then") — may throw (→ reject).
        let then = match self.get_from_object(roid, &units_from_str("then")) {
            Ok(t) => t,
            Err(Abrupt::Throw(e)) => {
                self.reject_promise(pid, e);
                return Ok(());
            }
            Err(other) => return Err(other),
        };
        if !self.is_callable_value(&then) {
            self.fulfill_promise(pid, resolution);
            return Ok(());
        }
        // Schedule NewPromiseResolveThenableJob.
        self.microtasks.push_back(Job::Thenable {
            pid,
            thenable: resolution,
            then,
        });
        Ok(())
    }

    fn is_callable_value(&self, v: &Value) -> bool {
        matches!(v, Value::Obj(o) if self.obj(*o).is_callable())
    }

    // -- PromiseResolve abstract op (27.2.4.7.1, default %Promise%) ---------

    /// PromiseResolve(%Promise%, x): if x is already a %Promise% (untampered
    /// constructor) return it, else wrap it in a fresh resolved promise.
    pub(crate) fn promise_resolve_default(&mut self, x: Value) -> Result<Value, Abrupt> {
        if let Some(_pid) = self.as_promise(&x) {
            if let Value::Obj(xoid) = &x {
                // x.constructor === %Promise% ? (untampered fast path)
                let c = self.get_from_object(*xoid, &units_from_str("constructor"))?;
                if matches!(&c, Value::Obj(o) if *o == self.intr.promise_ctor) {
                    return Ok(x);
                }
                // A tampered constructor makes the exact identity check
                // observable in ways the slice does not model — refuse.
                return Err(Abrupt::Fatal(
                    "PromiseResolve with a non-default promise constructor (out of slice)"
                        .to_string(),
                ));
            }
        }
        let cap = self.new_promise_capability_default();
        let resolve = cap.resolve.clone();
        self.call_value(&resolve, Value::Undefined, vec![x])?;
        Ok(cap.promise)
    }

    // -- PerformPromiseThen (27.2.5.4.1) -----------------------------------

    /// on_fulfilled / on_rejected are raw values (callable → handler, else
    /// empty). `capability` None = the await/internal case. Returns the result
    /// promise (or undefined when there is no capability).
    pub(crate) fn perform_promise_then(
        &mut self,
        pid: PromiseId,
        on_fulfilled: Value,
        on_rejected: Value,
        capability: Option<Capability>,
    ) -> Value {
        let fulfill_handler = if self.is_callable_value(&on_fulfilled) {
            Handler::Func(on_fulfilled)
        } else {
            Handler::Empty
        };
        let reject_handler = if self.is_callable_value(&on_rejected) {
            Handler::Func(on_rejected)
        } else {
            Handler::Empty
        };
        let ret = capability
            .as_ref()
            .map_or(Value::Undefined, |c| c.promise.clone());
        let state = self.promises[pid.0 as usize].state;
        match state {
            PromiseSt::Pending => {
                self.promises[pid.0 as usize].fulfill_reactions.push(Reaction {
                    capability: capability.clone(),
                    handler: fulfill_handler,
                });
                self.promises[pid.0 as usize].reject_reactions.push(Reaction {
                    capability,
                    handler: reject_handler,
                });
            }
            PromiseSt::Fulfilled => {
                let value = self.promises[pid.0 as usize].result.clone();
                self.microtasks.push_back(Job::Reaction {
                    handler: fulfill_handler,
                    capability,
                    kind: ReactionKind::Fulfill,
                    argument: value,
                });
            }
            PromiseSt::Rejected => {
                let reason = self.promises[pid.0 as usize].result.clone();
                self.microtasks.push_back(Job::Reaction {
                    handler: reject_handler,
                    capability,
                    kind: ReactionKind::Reject,
                    argument: reason,
                });
            }
        }
        self.promises[pid.0 as usize].is_handled = true;
        ret
    }

    // -- job execution -----------------------------------------------------

    /// Run one queued job. A Fatal propagates (→ NoCoverage); throws inside a
    /// reaction handler are captured into the result promise's rejection.
    fn run_job(&mut self, job: Job) -> Result<(), Abrupt> {
        match job {
            Job::Reaction {
                handler,
                capability,
                kind,
                argument,
            } => self.run_reaction_job(&handler, capability.as_ref(), kind, argument),
            Job::Thenable {
                pid,
                thenable,
                then,
            } => self.run_thenable_job(pid, thenable, then),
            Job::Callback { func } => {
                // queueMicrotask(cb): a throw becomes an uncaught exception in
                // the real host (process termination) — refuse rather than
                // guess the observable.
                match self.call_value(&func, Value::Undefined, Vec::new()) {
                    Ok(_) => Ok(()),
                    Err(Abrupt::Throw(_)) => Err(Abrupt::Fatal(
                        "queueMicrotask callback threw (uncaught microtask, out of slice)"
                            .to_string(),
                    )),
                    Err(other) => Err(other),
                }
            }
        }
    }

    /// PromiseReactionJob (27.2.2.1).
    fn run_reaction_job(
        &mut self,
        handler: &Handler,
        capability: Option<&Capability>,
        kind: ReactionKind,
        argument: Value,
    ) -> Result<(), Abrupt> {
        // handler_result: Ok(value) = normal, Err(value) = thrown.
        let handler_result: Result<Value, Value> = match handler {
            Handler::Empty => match kind {
                ReactionKind::Fulfill => Ok(argument),
                ReactionKind::Reject => Err(argument),
            },
            Handler::Func(f) => match self.call_value(f, Value::Undefined, vec![argument]) {
                Ok(v) => Ok(v),
                Err(Abrupt::Throw(e)) => Err(e),
                Err(other) => return Err(other),
            },
        };
        match capability {
            // await / internal reaction: no result promise. The handler is one
            // of our resume closures, which never abruptly completes here.
            None => Ok(()),
            Some(cap) => match handler_result {
                Err(e) => {
                    let reject = cap.reject.clone();
                    self.call_value(&reject, Value::Undefined, vec![e]).map(|_| ())
                }
                Ok(v) => {
                    let resolve = cap.resolve.clone();
                    self.call_value(&resolve, Value::Undefined, vec![v]).map(|_| ())
                }
            },
        }
    }

    /// NewPromiseResolveThenableJob (27.2.2.2).
    fn run_thenable_job(
        &mut self,
        pid: PromiseId,
        thenable: Value,
        then: Value,
    ) -> Result<(), Abrupt> {
        let (resolve, reject) = self.create_resolving_functions(pid);
        match self.call_value(&then, thenable, vec![resolve, reject.clone()]) {
            Ok(_) => Ok(()),
            Err(Abrupt::Throw(e)) => {
                self.call_value(&reject, Value::Undefined, vec![e]).map(|_| ())
            }
            Err(other) => Err(other),
        }
    }

    // -- native-closure dispatch -------------------------------------------

    /// [[Call]] on a `FnImpl::Native` function object.
    pub(crate) fn call_native(
        &mut self,
        nc: &NativeClosure,
        _this: Value,
        args: Vec<Value>,
    ) -> ERes {
        let arg0 = args.first().cloned().unwrap_or(Value::Undefined);
        match nc {
            NativeClosure::Resolve { pid, already } => {
                let already = Rc::clone(already);
                self.resolve_promise_with(*pid, &already, arg0)?;
                Ok(Value::Undefined)
            }
            NativeClosure::Reject { pid, already } => {
                if !already.get() {
                    already.set(true);
                    self.reject_promise(*pid, arg0);
                }
                Ok(Value::Undefined)
            }
            NativeClosure::AsyncResume { gid, is_throw } => {
                let r = if *is_throw {
                    crate::generator::Resumption::Throw(arg0)
                } else {
                    crate::generator::Resumption::Normal(arg0)
                };
                self.async_resume(*gid, r)?;
                Ok(Value::Undefined)
            }
            NativeClosure::AllResolveElement {
                index,
                values,
                capability,
                remaining,
                already,
            } => {
                if already.get() {
                    return Ok(Value::Undefined);
                }
                already.set(true);
                values.borrow_mut()[*index] = arg0;
                self.combinator_countdown_resolve(remaining, values, capability)
            }
            NativeClosure::AllSettledElement {
                is_reject,
                index,
                values,
                capability,
                remaining,
                already,
            } => {
                if already.get() {
                    return Ok(Value::Undefined);
                }
                already.set(true);
                let obj = self.alloc(Object::new(ObjKind::Plain, Some(self.intr.object_proto)));
                if *is_reject {
                    self.obj_mut(obj)
                        .props
                        .insert(units_from_str("status"), Prop::data(Value::str_from("rejected")));
                    self.obj_mut(obj)
                        .props
                        .insert(units_from_str("reason"), Prop::data(arg0));
                } else {
                    self.obj_mut(obj).props.insert(
                        units_from_str("status"),
                        Prop::data(Value::str_from("fulfilled")),
                    );
                    self.obj_mut(obj)
                        .props
                        .insert(units_from_str("value"), Prop::data(arg0));
                }
                values.borrow_mut()[*index] = Value::Obj(obj);
                self.combinator_countdown_resolve(remaining, values, capability)
            }
            NativeClosure::AnyRejectElement {
                index,
                errors,
                capability,
                remaining,
                already,
            } => {
                if already.get() {
                    return Ok(Value::Undefined);
                }
                already.set(true);
                errors.borrow_mut()[*index] = arg0;
                let _ = capability;
                let n = remaining.get() - 1;
                remaining.set(n);
                if n == 0 {
                    // All inputs rejected: Promise.any rejects with an
                    // AggregateError, which the value model does not carry —
                    // refuse rather than fabricate one.
                    return Err(Abrupt::Fatal(
                        "Promise.any all-rejected → AggregateError (out of slice)".to_string(),
                    ));
                }
                Ok(Value::Undefined)
            }
            NativeClosure::ThenFinally { on_finally } => {
                self.finally_then(on_finally.clone(), arg0, false)
            }
            NativeClosure::CatchFinally { on_finally } => {
                self.finally_then(on_finally.clone(), arg0, true)
            }
            NativeClosure::FinallyValueThunk(v) => Ok(v.clone()),
            NativeClosure::FinallyThrower(v) => Err(Abrupt::Throw(v.clone())),
            NativeClosure::ProxyRevoke { proxy } => {
                // 28.2.2.1.1: set [[ProxyTarget]]/[[ProxyHandler]] to null; the
                // callable/constructor presence is fixed at creation and kept.
                if let ObjKind::Proxy { target, handler, .. } = &mut self.obj_mut(*proxy).kind {
                    *target = None;
                    *handler = None;
                }
                Ok(Value::Undefined)
            }
        }
    }

    /// The shared countdown for all/allSettled resolve-element closures: on the
    /// last element, resolve the capability with the collected values array.
    fn combinator_countdown_resolve(
        &mut self,
        remaining: &Rc<Cell<usize>>,
        values: &Rc<RefCell<Vec<Value>>>,
        capability: &Capability,
    ) -> ERes {
        let n = remaining.get() - 1;
        remaining.set(n);
        if n == 0 {
            let arr = self.array_from_values(&values.borrow());
            let resolve = capability.resolve.clone();
            self.call_value(&resolve, Value::Undefined, vec![arr])?;
        }
        Ok(Value::Undefined)
    }

    /// CreateArrayFromList over a snapshot of values.
    pub(crate) fn array_from_values(&mut self, values: &[Value]) -> Value {
        let arr = self.new_array(0);
        for (i, v) in values.iter().enumerate() {
            self.obj_mut(arr)
                .props
                .insert(units_from_str(&i.to_string()), Prop::data(v.clone()));
        }
        #[allow(clippy::cast_precision_loss)]
        self.set_array_length_raw(arr, values.len() as f64);
        Value::Obj(arr)
    }

    // -- finally wrappers ---------------------------------------------------

    /// thenFinally/catchFinally body (27.2.5.3.1-2): run onFinally, wrap its
    /// result in PromiseResolve, then thread the original value/reason through.
    fn finally_then(&mut self, on_finally: Value, arg: Value, is_catch: bool) -> ERes {
        let result = self.call_value(&on_finally, Value::Undefined, Vec::new())?;
        let promise = self.promise_resolve_default(result)?;
        let thunk = if is_catch {
            self.alloc_native(NativeClosure::FinallyThrower(arg))
        } else {
            self.alloc_native(NativeClosure::FinallyValueThunk(arg))
        };
        // Invoke(promise, "then", [thunk]).
        let Value::Obj(poid) = promise else {
            return Err(Abrupt::Fatal("finally: PromiseResolve result not a promise".into()));
        };
        let then = self.get_from_object(poid, &units_from_str("then"))?;
        self.call_value(&then, promise.clone(), vec![thunk])
    }

    // -- drain (post-body) --------------------------------------------------

    /// Drain the microtask FIFO to empty. A Fatal (out-of-slice / budget)
    /// refuses the whole case.
    pub(crate) fn drain_microtasks(&mut self) -> Result<(), Abrupt> {
        while let Some(job) = self.microtasks.pop_front() {
            self.job_steps += 1;
            if self.job_steps > JOB_BUDGET {
                return Err(Abrupt::Fatal(
                    "microtask/job budget exceeded (runaway rescheduling, out of slice)".to_string(),
                ));
            }
            self.run_job(job)?;
        }
        Ok(())
    }

    /// Drain jobs after the script body, in the driver's order: microtasks to
    /// empty, then the earliest-deadline-then-insertion timer with a microtask
    /// drain between each, honouring TIMER_CAP. Returns `Some(thrown)` when a
    /// timer callback threw (→ completion phase "timer"), else None.
    pub(crate) fn drain_jobs(&mut self) -> Result<Option<Value>, Abrupt> {
        self.drain_microtasks()?;
        let mut ran: u64 = 0;
        while !self.timers.is_empty() {
            if ran >= TIMER_CAP {
                self.events.push(trust_js_trace::HostEvent::Host {
                    v: "timer-cap".to_string(),
                });
                self.timers.clear();
                break;
            }
            // Earliest time, then earliest seq.
            let mut best = 0usize;
            for i in 1..self.timers.len() {
                let a = &self.timers[i];
                let b = &self.timers[best];
                if a.time < b.time || (a.time == b.time && a.seq < b.seq) {
                    best = i;
                }
            }
            let t = self.timers.remove(best);
            self.virtual_now = t.time;
            if let Some(iv) = t.interval {
                let seq = self.next_timer_seq();
                self.timers.push(Timer {
                    seq,
                    time: self.virtual_now + iv,
                    cb: t.cb.clone(),
                    args: t.args.clone(),
                    interval: Some(iv),
                });
            }
            ran += 1;
            match self.call_value(&t.cb, Value::Undefined, t.args) {
                Ok(_) => {}
                // A timer callback threw: the driver still performs a final
                // microtask checkpoint (draining any jobs the callback enqueued
                // before it threw) before reporting the fault.
                Err(Abrupt::Throw(e)) => {
                    self.drain_microtasks()?;
                    return Ok(Some(e));
                }
                Err(other) => return Err(other),
            }
            self.drain_microtasks()?;
        }
        Ok(None)
    }

    pub(crate) fn next_timer_seq(&mut self) -> u64 {
        self.timer_seq += 1;
        self.timer_seq
    }

    // -- builtin dispatch ---------------------------------------------------

    pub(crate) fn dispatch_promise_builtin(
        &mut self,
        b: crate::value::Builtin,
        this: Value,
        args: Vec<Value>,
        is_new: bool,
    ) -> ERes {
        use crate::value::Builtin;
        let arg = |i: usize| args.get(i).cloned().unwrap_or(Value::Undefined);
        match b {
            Builtin::PromiseCtor => self.promise_constructor(&args, is_new),
            Builtin::PromiseSpeciesGet => Ok(this),
            Builtin::PromiseResolveStatic => {
                // Promise.resolve(x): `this` must be an object (the constructor).
                if !matches!(this, Value::Obj(_)) {
                    return Err(self.throw_native(NativeErrorKind::TypeError));
                }
                if !matches!(&this, Value::Obj(o) if *o == self.intr.promise_ctor) {
                    return Err(Abrupt::Fatal(
                        "Promise.resolve on a non-default constructor (out of slice)".to_string(),
                    ));
                }
                self.promise_resolve_default(arg(0))
            }
            Builtin::PromiseRejectStatic => {
                if !matches!(&this, Value::Obj(o) if *o == self.intr.promise_ctor) {
                    return Err(Abrupt::Fatal(
                        "Promise.reject on a non-default constructor (out of slice)".to_string(),
                    ));
                }
                let cap = self.new_promise_capability_default();
                let reject = cap.reject.clone();
                self.call_value(&reject, Value::Undefined, vec![arg(0)])?;
                Ok(cap.promise)
            }
            Builtin::PromiseProtoThen => self.promise_proto_then(&this, arg(0), arg(1)),
            Builtin::PromiseProtoCatch => {
                // Invoke(this, "then", [undefined, onRejected]) — GetV coerces a
                // primitive `this` via ToObject (so `catch.call(true)` reads
                // Boolean.prototype.then), and undefined/null throws TypeError.
                let then = self.get_prop_value(&this, &units_from_str("then"))?;
                self.call_value(&then, this.clone(), vec![Value::Undefined, arg(0)])
            }
            Builtin::PromiseProtoFinally => self.promise_proto_finally(&this, arg(0)),
            Builtin::PromiseAll => self.promise_combinator(&this, arg(0), Combinator::All),
            Builtin::PromiseAllSettled => {
                self.promise_combinator(&this, arg(0), Combinator::AllSettled)
            }
            Builtin::PromiseRace => self.promise_combinator(&this, arg(0), Combinator::Race),
            Builtin::PromiseAny => self.promise_combinator(&this, arg(0), Combinator::Any),
            Builtin::SetTimeout | Builtin::SetInterval | Builtin::SetImmediate => {
                self.set_timer(b, &args)
            }
            Builtin::ClearTimer => {
                self.clear_timer(&arg(0));
                Ok(Value::Undefined)
            }
            Builtin::QueueMicrotask => {
                let cb = arg(0);
                if !self.is_callable_value(&cb) {
                    return Err(self.throw_native(NativeErrorKind::TypeError));
                }
                self.microtasks.push_back(Job::Callback { func: cb });
                Ok(Value::Undefined)
            }
            _ => Err(Abrupt::Fatal(format!("promise dispatch: unexpected {b:?}"))),
        }
    }

    /// `new Promise(executor)` (27.2.3.1).
    fn promise_constructor(&mut self, args: &[Value], is_new: bool) -> ERes {
        if !is_new {
            // Called without `new`: NewTarget is undefined → TypeError.
            return Err(self.throw_native(NativeErrorKind::TypeError));
        }
        let executor = args.first().cloned().unwrap_or(Value::Undefined);
        if !self.is_callable_value(&executor) {
            return Err(self.throw_native(NativeErrorKind::TypeError));
        }
        let proto = match self.pending_new_target.take() {
            Some(nt) => self.proto_from_new_target(nt, self.intr.promise_proto)?,
            None => self.intr.promise_proto,
        };
        let (pid, oid) = self.alloc_promise(proto);
        let (resolve, reject) = self.create_resolving_functions(pid);
        match self.call_value(&executor, Value::Undefined, vec![resolve, reject.clone()]) {
            Ok(_) => {}
            Err(Abrupt::Throw(e)) => {
                self.call_value(&reject, Value::Undefined, vec![e])?;
            }
            Err(other) => return Err(other),
        }
        Ok(Value::Obj(oid))
    }

    /// Promise.prototype.then (27.2.5.4) for the default %Promise%.
    pub(crate) fn promise_proto_then(
        &mut self,
        this: &Value,
        on_fulfilled: Value,
        on_rejected: Value,
    ) -> ERes {
        let Some(pid) = self.as_promise(this) else {
            return Err(self.throw_native(NativeErrorKind::TypeError));
        };
        let Value::Obj(oid) = this else { unreachable!() };
        if !self.promise_constructor_is_default(*oid)? {
            return Err(Abrupt::Fatal(
                "Promise.prototype.then with a custom @@species/constructor (out of slice)"
                    .to_string(),
            ));
        }
        let cap = self.new_promise_capability_default();
        Ok(self.perform_promise_then(pid, on_fulfilled, on_rejected, Some(cap)))
    }

    /// Is `this`'s SpeciesConstructor the default %Promise% (untampered
    /// constructor + @@species)? Ok(false) = custom (caller refuses); Err =
    /// the SpeciesConstructor TypeError.
    fn promise_constructor_is_default(&mut self, this_oid: ObjId) -> Result<bool, Abrupt> {
        let c = self.get_from_object(this_oid, &units_from_str("constructor"))?;
        match &c {
            Value::Undefined => return Ok(true),
            Value::Obj(cobj) if *cobj == self.intr.promise_ctor => {}
            Value::Obj(_) => return Ok(false),
            _ => return Err(self.throw_native(NativeErrorKind::TypeError)),
        }
        // c === %Promise%: confirm Promise[@@species] is the intrinsic getter.
        let sid = self.intr.wk(crate::builtins::WK_SPECIES);
        let ok = matches!(
            self.obj(self.intr.promise_ctor).sym_props.get(&sid),
            Some(crate::value::Prop {
                val: crate::value::PropVal::Accessor { get: Some(g), .. },
                ..
            }) if matches!(
                self.obj(*g).kind,
                ObjKind::Function(crate::value::FnImpl::Builtin(
                    crate::value::Builtin::PromiseSpeciesGet
                ))
            )
        );
        Ok(ok)
    }

    /// Promise.prototype.finally (27.2.5.3) for the default %Promise%.
    fn promise_proto_finally(&mut self, this: &Value, on_finally: Value) -> ERes {
        let Value::Obj(oid) = this else {
            return Err(self.throw_native(NativeErrorKind::TypeError));
        };
        if !self.promise_constructor_is_default(*oid)? {
            return Err(Abrupt::Fatal(
                "Promise.prototype.finally with a custom @@species/constructor (out of slice)"
                    .to_string(),
            ));
        }
        // finally's internal `Invoke(promise, "then", ...)` (and the wrappers'
        // own `then` calls during the drain) make the exact then-call protocol
        // observable when `then` is patched — refuse rather than risk a
        // mismatching call sequence / builtin-function shape.
        let then = self.get_from_object(*oid, &units_from_str("then"))?;
        if !matches!(
            &then,
            Value::Obj(f) if matches!(
                self.obj(*f).kind,
                ObjKind::Function(crate::value::FnImpl::Builtin(
                    crate::value::Builtin::PromiseProtoThen
                ))
            )
        ) {
            return Err(Abrupt::Fatal(
                "Promise.prototype.finally with a patched `then` (observable protocol out of slice)"
                    .to_string(),
            ));
        }
        let (then_finally, catch_finally) = if self.is_callable_value(&on_finally) {
            (
                self.alloc_native(NativeClosure::ThenFinally {
                    on_finally: on_finally.clone(),
                }),
                self.alloc_native(NativeClosure::CatchFinally { on_finally }),
            )
        } else {
            (on_finally.clone(), on_finally)
        };
        self.call_value(&then, this.clone(), vec![then_finally, catch_finally])
    }

    // -- combinators --------------------------------------------------------

    fn promise_combinator(&mut self, this: &Value, iterable: Value, kind: Combinator) -> ERes {
        if !matches!(this, Value::Obj(o) if *o == self.intr.promise_ctor) {
            return Err(Abrupt::Fatal(
                "Promise combinator on a non-default constructor (out of slice)".to_string(),
            ));
        }
        let cap = self.new_promise_capability_default();
        match self.perform_combinator(&iterable, &cap, kind) {
            Ok(()) => {}
            Err(Abrupt::Throw(e)) => {
                let reject = cap.reject.clone();
                self.call_value(&reject, Value::Undefined, vec![e])?;
            }
            Err(other) => return Err(other),
        }
        Ok(cap.promise)
    }

    fn perform_combinator(
        &mut self,
        iterable: &Value,
        cap: &Capability,
        kind: Combinator,
    ) -> Result<(), Abrupt> {
        let c = Value::Obj(self.intr.promise_ctor);
        // GetPromiseResolve (27.2.4.1.2): promiseResolve = Get(C, "resolve");
        // a non-callable value throws TypeError (→ the caller rejects the cap).
        let promise_resolve =
            self.get_from_object(self.intr.promise_ctor, &units_from_str("resolve"))?;
        if !self.is_callable_value(&promise_resolve) {
            return Err(self.throw_native(NativeErrorKind::TypeError));
        }
        let mut iter = self.slice_iterator_public(iterable)?;
        let values = Rc::new(RefCell::new(Vec::<Value>::new()));
        let remaining = Rc::new(Cell::new(1usize));
        let mut index = 0usize;
        loop {
            // IteratorStep: a fault here leaves the iterator done — no close.
            let next = self.slice_iter_next_public(&mut iter)?;
            let Some(next_value) = next else {
                // Iterator done.
                let n = remaining.get() - 1;
                remaining.set(n);
                if n == 0 {
                    match kind {
                        Combinator::All | Combinator::AllSettled => {
                            let arr = self.array_from_values(&values.borrow());
                            let resolve = cap.resolve.clone();
                            self.call_value(&resolve, Value::Undefined, vec![arr])?;
                        }
                        Combinator::Any => {
                            // Zero elements → reject with AggregateError (no
                            // element ever fulfilled): out of slice.
                            return Err(Abrupt::Fatal(
                                "Promise.any over an empty iterable → AggregateError (out of slice)"
                                    .to_string(),
                            ));
                        }
                        Combinator::Race => {} // race over empty never settles
                    }
                }
                break;
            };
            // Per PerformPromiseAll/AllSettled/Race/Any: any abrupt completion
            // from processing the element (Invoke resolve, Get "then", Invoke
            // "then") is IfAbruptCloseIterator — IteratorClose the (not-done)
            // iterator with the throw completion (best-effort, the original
            // throw wins) before the caller rejects the capability.
            if let Err(a) = self.combinator_element_step(
                next_value,
                &promise_resolve,
                &c,
                &values,
                &remaining,
                cap,
                kind,
                index,
            ) {
                let _ = self.slice_iterator_close(&mut iter);
                return Err(a);
            }
            index += 1;
        }
        Ok(())
    }

    /// One element of a Promise combinator (the loop body of PerformPromiseAll
    /// et al., 27.2.4.x): resolve the value through the constructor, install the
    /// per-element reactions, and Invoke "then". Any abrupt completion is
    /// returned so the caller can IteratorClose the iterator (IfAbruptClose).
    #[allow(clippy::too_many_arguments)]
    fn combinator_element_step(
        &mut self,
        next_value: Value,
        promise_resolve: &Value,
        c: &Value,
        values: &Rc<RefCell<Vec<Value>>>,
        remaining: &Rc<Cell<usize>>,
        cap: &Capability,
        kind: Combinator,
        index: usize,
    ) -> Result<(), Abrupt> {
        // nextPromise = Call(promiseResolve, C, [nextValue]).
        let next_promise = self.call_value(promise_resolve, c.clone(), vec![next_value])?;
        let (on_f, on_r) = match kind {
            Combinator::All => {
                values.borrow_mut().push(Value::Undefined);
                let already = Rc::new(Cell::new(false));
                let on_f = self.alloc_native(NativeClosure::AllResolveElement {
                    index,
                    values: Rc::clone(values),
                    capability: cap.clone(),
                    remaining: Rc::clone(remaining),
                    already,
                });
                remaining.set(remaining.get() + 1);
                (on_f, cap.reject.clone())
            }
            Combinator::AllSettled => {
                values.borrow_mut().push(Value::Undefined);
                let already = Rc::new(Cell::new(false));
                let on_f = self.alloc_native(NativeClosure::AllSettledElement {
                    is_reject: false,
                    index,
                    values: Rc::clone(values),
                    capability: cap.clone(),
                    remaining: Rc::clone(remaining),
                    already: Rc::clone(&already),
                });
                let on_r = self.alloc_native(NativeClosure::AllSettledElement {
                    is_reject: true,
                    index,
                    values: Rc::clone(values),
                    capability: cap.clone(),
                    remaining: Rc::clone(remaining),
                    already,
                });
                remaining.set(remaining.get() + 1);
                (on_f, on_r)
            }
            Combinator::Any => {
                values.borrow_mut().push(Value::Undefined);
                let already = Rc::new(Cell::new(false));
                let on_r = self.alloc_native(NativeClosure::AnyRejectElement {
                    index,
                    errors: Rc::clone(values),
                    capability: cap.clone(),
                    remaining: Rc::clone(remaining),
                    already,
                });
                remaining.set(remaining.get() + 1);
                (cap.resolve.clone(), on_r)
            }
            Combinator::Race => (cap.resolve.clone(), cap.reject.clone()),
        };
        // Invoke(nextPromise, "then", [onFulfilled, onRejected]).
        let Value::Obj(np_oid) = next_promise else {
            return Err(Abrupt::Fatal(
                "Promise combinator: resolve did not yield an object (out of slice)".to_string(),
            ));
        };
        let then = self.get_from_object(np_oid, &units_from_str("then"))?;
        self.call_value(&then, next_promise, vec![on_f, on_r])?;
        Ok(())
    }

    // -- timers -------------------------------------------------------------

    fn set_timer(&mut self, b: crate::value::Builtin, args: &[Value]) -> ERes {
        use crate::value::Builtin;
        let cb = args.first().cloned().unwrap_or(Value::Undefined);
        // The driver returns 0 (no timer) when the callback is not a function.
        if !self.is_callable_value(&cb) {
            return Ok(Value::Num(0.0));
        }
        // setImmediate(cb, ...args) == setTimeout(cb, 0, ...args); interval
        // delay defaults to 0.
        let (delay_val, extra_start) = match b {
            Builtin::SetImmediate => (Value::Num(0.0), 1usize),
            _ => (args.get(1).cloned().unwrap_or(Value::Undefined), 2usize),
        };
        // Number(delay) || 0.
        let n = self.to_number(&delay_val)?;
        let offset = if n == 0.0 || n.is_nan() { 0.0 } else { n };
        let extra: Vec<Value> = args.iter().skip(extra_start).cloned().collect();
        let interval = matches!(b, Builtin::SetInterval).then_some(offset);
        let seq = self.next_timer_seq();
        self.timers.push(Timer {
            seq,
            time: self.virtual_now + offset,
            cb,
            args: extra,
            interval,
        });
        #[allow(clippy::cast_precision_loss)]
        Ok(Value::Num(seq as f64))
    }

    fn clear_timer(&mut self, id: &Value) {
        // The driver filters by strict `t.id !== id`; a timer id is a number,
        // so only a numeric argument can match.
        if let Value::Num(n) = id {
            let n = *n;
            #[allow(clippy::cast_precision_loss)]
            self.timers.retain(|t| (t.seq as f64) != n);
        }
    }
}

#[derive(Debug, Clone, Copy)]
enum Combinator {
    All,
    AllSettled,
    Race,
    Any,
}
