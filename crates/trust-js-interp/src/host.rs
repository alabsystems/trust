// The reactor `Host` seam (M2 D1): plugs the tier-0 interpreter's `JsValue`
// and call machinery into trust-js-reactor. The reactor owns the promise state
// machine, the microtask/timer queues, and the virtual clock; this module owns
// everything that requires interpreting JS (invoking reaction handlers, the
// thenable check, running a thenable's `then`, building the combinator
// aggregate values, resuming async functions).
//
// Borrow discipline. The reactor is stored `Some` in `Interp::reactor` and
// `take`n out for every operation (`rx_op`), so `&mut Interp` (the Host) and
// `&mut Reactor` never alias. When the reactor calls back into a host method it
// hands over `&mut Reactor`; the method PARKS it into `self.reactor` (swapping a
// cheap empty placeholder into the reactor's own slot) so any reentrant JS run
// inside the callback reaches it through the same `rx_op` path, then restores
// it. No `unsafe`, no `Rc<RefCell>`, byte-deterministic — the reactor is moved
// by value between the drain's stack frame and `self.reactor`.
//
// Author: Andrew Yates
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

use crate::generators::{GenExec, ResumeInput};
use crate::interp::{Abrupt, Interp};
use std::rc::Rc;
use trust_js_reactor::{
    Capability, Completion, Host, PromiseId, Reactor, RejectionEvent, ThenLookup,
};
use trust_js_value::{ErrKind, JsValue, ObjId, ObjKind, PropKey};

/// An async-function execution id (index into `Interp::async_execs`).
pub type AsyncId = usize;

/// The reactor's callback handle (`F`). Cheap to clone.
#[derive(Clone)]
pub enum JobFn {
    /// Invoke a JS function value — with the reaction argument (a `.then`
    /// handler via `Host::call`) or with no argument (a `queueMicrotask` job
    /// via `Host::run_callback`).
    Call(JsValue),
    /// A timer callback: the JS function plus the trailing `setTimeout`/
    /// `setInterval` extra arguments.
    Timer(JsValue, Rc<Vec<JsValue>>),
    /// Resume async execution `id` with a fulfilled value (`await` → Next).
    AsyncNext(AsyncId),
    /// Resume async execution `id` with a rejection reason (`await` → Throw).
    AsyncThrow(AsyncId),
    /// Resume async generator `oid`'s body after an internal `await` (§27.6),
    /// with the fulfilled value / rejection reason.
    AsyncGenAwaitNext(ObjId),
    AsyncGenAwaitThrow(ObjId),
    /// A `finally` fulfill/reject reaction carrying the `onFinally` callback.
    FinallyFulfill(JsValue),
    FinallyReject(JsValue),
}

/// An async-function suspension record: the resumable frame stack (reusing the
/// generator machinery in `Await` mode) and the result promise's resolving
/// capability. The result Promise object is returned to the caller at creation
/// time; the reactions reference the execution by `AsyncId`, not the object.
pub(crate) struct AsyncExec {
    pub(crate) machine: GenExec,
    pub(crate) cap: Capability,
}

/// A CreateResolvingFunctions capability plus which side it drives.
pub(crate) struct ResolveEntry {
    pub(crate) cap: Capability,
    pub(crate) reject: bool,
}

impl Interp {
    /// Run a reactor operation from ordinary eval context: take the reactor
    /// out (so it and `&mut Interp` don't alias), run `f`, put it back.
    pub(crate) fn rx_op<R>(
        &mut self,
        f: impl FnOnce(&mut Interp, &mut Reactor<JsValue, JobFn>) -> R,
    ) -> R {
        let mut rx = self.reactor.take().expect("reactor available");
        let out = f(self, &mut rx);
        self.reactor = Some(rx);
        out
    }

    /// Drain the reactor to quiescence (microtasks, then earliest timer,
    /// repeat — the trace driver's `drainMicrotasks(); drainTimers()` order).
    /// Fails closed on the reactor step budget or a mid-drain refusal.
    pub(crate) fn run_reactor_drain(&mut self) -> Result<(), Abrupt> {
        let mut rx = self.reactor.take().expect("reactor available");
        let res = rx.drain(self);
        self.reactor = Some(rx);
        if let Some(fault) = self.drain_fault.take() {
            return Err(Abrupt::Fatal(fault));
        }
        res.map_err(|e| Abrupt::Fatal(format!("reactor drain: {e}")))
    }

    /// Any promise settled but never handled by the end of the drain: the
    /// driver does not surface unhandled rejections in the observable trace and
    /// the engines diverge on their host policy, so refuse (NoCoverage).
    pub(crate) fn reactor_unhandled_refusal(&mut self) -> Option<String> {
        let rx = self.reactor.as_ref().expect("reactor available");
        if rx.unhandled_rejections().is_empty() {
            None
        } else {
            Some("unhandled promise rejection (engine-divergent observability)".to_string())
        }
    }

    // -- reactor-callback parking ------------------------------------------

    fn host_park(&mut self, rx: &mut Reactor<JsValue, JobFn>) {
        let real = std::mem::replace(rx, Reactor::new(0));
        debug_assert!(self.reactor.is_none(), "reactor must be out during a callback");
        self.reactor = Some(real);
    }

    fn host_unpark(&mut self, rx: &mut Reactor<JsValue, JobFn>) {
        let real = self.reactor.take().expect("reactor parked");
        *rx = real;
    }

    /// Record the first mid-drain refusal and halt further observable work.
    pub(crate) fn note_drain_fault(&mut self, a: Abrupt) {
        if self.drain_fault.is_none() {
            self.drain_fault = Some(match a {
                Abrupt::Fatal(s) => s,
                Abrupt::Throw(_) => "throw escaped a raw microtask/timer callback \
                     (engine-divergent observability)"
                    .to_string(),
                other => format!("abrupt completion escaped a reactor callback: {other:?}"),
            });
        }
    }

    // -- host-side callback bodies -----------------------------------------

    /// A PromiseReactionJob handler applied to `arg`.
    fn run_reaction(&mut self, f: &JobFn, arg: JsValue) -> Result<JsValue, Abrupt> {
        if self.drain_fault.is_some() {
            return Ok(JsValue::Undefined);
        }
        match f {
            JobFn::Call(func) => self.call_value(func, JsValue::Undefined, vec![arg]),
            JobFn::AsyncNext(id) => {
                self.async_resume(*id, ResumeInput::Next(arg))?;
                Ok(JsValue::Undefined)
            }
            JobFn::AsyncThrow(id) => {
                self.async_resume(*id, ResumeInput::Throw(arg))?;
                Ok(JsValue::Undefined)
            }
            JobFn::AsyncGenAwaitNext(oid) => {
                self.async_gen_await_resume(*oid, ResumeInput::Next(arg))?;
                Ok(JsValue::Undefined)
            }
            JobFn::AsyncGenAwaitThrow(oid) => {
                self.async_gen_await_resume(*oid, ResumeInput::Throw(arg))?;
                Ok(JsValue::Undefined)
            }
            JobFn::FinallyFulfill(on_finally) => self.finally_reaction(on_finally, arg, false),
            JobFn::FinallyReject(on_finally) => self.finally_reaction(on_finally, arg, true),
            JobFn::Timer(cb, args) => self.call_value(cb, JsValue::Undefined, (**args).clone()),
        }
    }

    /// A no-argument job (a `queueMicrotask` callback or a timer callback).
    fn run_callback_job(&mut self, f: &JobFn) -> Result<(), Abrupt> {
        if self.drain_fault.is_some() {
            return Ok(());
        }
        match f {
            JobFn::Call(func) => {
                self.call_value(func, JsValue::Undefined, Vec::new())?;
                Ok(())
            }
            JobFn::Timer(cb, args) => {
                self.call_value(cb, JsValue::Undefined, (**args).clone())?;
                Ok(())
            }
            // Async resumes / finally reactions never enter the run_callback
            // (no-argument) lane; a reaction always carries its settled value.
            JobFn::AsyncNext(_)
            | JobFn::AsyncThrow(_)
            | JobFn::AsyncGenAwaitNext(_)
            | JobFn::AsyncGenAwaitThrow(_)
            | JobFn::FinallyFulfill(_)
            | JobFn::FinallyReject(_) => {
                Err(Abrupt::Fatal("reaction handle in a no-argument job".to_string()))
            }
        }
    }

    /// The resolve algorithm's `Get(resolution, "then")` + callable test.
    fn host_get_then(&mut self, value: &JsValue) -> ThenLookup<JsValue, JobFn> {
        if !value.is_object() {
            return ThenLookup::NotThenable;
        }
        match self.get_prop(value, &PropKey::from_str("then")) {
            Ok(then) => match &then {
                JsValue::Obj(o) if self.heap.obj(*o).is_callable() => {
                    ThenLookup::Thenable(JobFn::Call(then))
                }
                _ => ThenLookup::NotThenable,
            },
            Err(Abrupt::Throw(e)) => ThenLookup::Threw(e),
            Err(a) => {
                self.note_drain_fault(a);
                ThenLookup::Threw(JsValue::Undefined)
            }
        }
    }

    /// PromiseResolveThenableJob body: run `then.call(thenable, resolve, reject)`.
    fn host_call_then(
        &mut self,
        then: &JobFn,
        thenable: &JsValue,
        resolve: Capability,
        reject: Capability,
    ) -> Result<JsValue, Abrupt> {
        let JobFn::Call(then_fn) = then else {
            return Err(Abrupt::Fatal("call_then: non-Call thenable handle".to_string()));
        };
        let resolve_fn = self.make_resolving_fn(resolve, false)?;
        let reject_fn = self.make_resolving_fn(reject, true)?;
        self.call_value(
            then_fn,
            thenable.clone(),
            vec![JsValue::Obj(resolve_fn), JsValue::Obj(reject_fn)],
        )
    }

    fn host_type_error(&mut self) -> JsValue {
        match self.make_native_error(ErrKind::Type, false) {
            Ok(oid) => JsValue::Obj(oid),
            Err(a) => {
                self.note_drain_fault(a);
                JsValue::Undefined
            }
        }
    }
}

impl Host for Interp {
    type Value = JsValue;
    type Fn = JobFn;

    fn call(
        &mut self,
        rx: &mut Reactor<JsValue, JobFn>,
        f: &JobFn,
        argument: JsValue,
    ) -> Completion<JsValue> {
        self.host_park(rx);
        let r = self.run_reaction(f, argument);
        self.host_unpark(rx);
        match r {
            Ok(v) => Completion::Normal(v),
            Err(Abrupt::Throw(e)) => Completion::Throw(e),
            Err(a) => {
                self.note_drain_fault(a);
                Completion::Normal(JsValue::Undefined)
            }
        }
    }

    fn run_callback(&mut self, rx: &mut Reactor<JsValue, JobFn>, f: &JobFn) {
        self.host_park(rx);
        let r = self.run_callback_job(f);
        self.host_unpark(rx);
        if let Err(a) = r {
            self.note_drain_fault(a);
        }
    }

    fn get_then(
        &mut self,
        rx: &mut Reactor<JsValue, JobFn>,
        value: &JsValue,
    ) -> ThenLookup<JsValue, JobFn> {
        self.host_park(rx);
        let r = self.host_get_then(value);
        self.host_unpark(rx);
        r
    }

    fn call_then(
        &mut self,
        rx: &mut Reactor<JsValue, JobFn>,
        then: &JobFn,
        thenable: &JsValue,
        resolve: Capability,
        reject: Capability,
    ) -> Completion<JsValue> {
        self.host_park(rx);
        let r = self.host_call_then(then, thenable, resolve, reject);
        self.host_unpark(rx);
        match r {
            Ok(v) => Completion::Normal(v),
            Err(Abrupt::Throw(e)) => Completion::Throw(e),
            Err(a) => {
                self.note_drain_fault(a);
                Completion::Normal(JsValue::Undefined)
            }
        }
    }

    fn type_error(&mut self, _message: &str) -> JsValue {
        self.host_type_error()
    }

    fn promise_of(&mut self, value: &JsValue) -> Option<PromiseId> {
        if let JsValue::Obj(o) = value {
            if let ObjKind::Promise(pid) = self.heap.obj(*o).kind {
                return Some(pid);
            }
        }
        None
    }

    fn build_array(&mut self, elements: Vec<JsValue>) -> JsValue {
        match self.build_js_array(elements) {
            Ok(v) => v,
            Err(a) => {
                self.note_drain_fault(a);
                JsValue::Undefined
            }
        }
    }

    fn build_settled_fulfilled(&mut self, value: JsValue) -> JsValue {
        match self.build_settled_record(true, value) {
            Ok(v) => v,
            Err(a) => {
                self.note_drain_fault(a);
                JsValue::Undefined
            }
        }
    }

    fn build_settled_rejected(&mut self, reason: JsValue) -> JsValue {
        match self.build_settled_record(false, reason) {
            Ok(v) => v,
            Err(a) => {
                self.note_drain_fault(a);
                JsValue::Undefined
            }
        }
    }

    fn build_aggregate_error(&mut self, errors: Vec<JsValue>) -> JsValue {
        match self.build_agg_error(errors) {
            Ok(v) => v,
            Err(a) => {
                self.note_drain_fault(a);
                JsValue::Undefined
            }
        }
    }

    fn on_rejection(&mut self, _event: RejectionEvent<JsValue>) {
        // Unhandled-rejection detail is not in the observable trace; the
        // end-of-drain sweep (`reactor_unhandled_refusal`) refuses cases that
        // leave a rejection outstanding, so nothing to do live.
    }
}
