// Shared test harness: a concrete `Host` (TestHost) plus a `Rt` runtime that
// wraps a `Reactor<TestVal, TestFn>` with a compact DSL. This is what a future
// consumer plugs in miniature — `TestVal` stands in for the interp's JsValue,
// `TestFn` for its function-call closure — so the tests exercise the reactor
// exactly through the seam M2 will use, never through internals.
//
// Callbacks reenter the reactor the same way the real interp will: every host
// method receives `&mut Reactor`, and the closures stored in `TestFn` capture
// nothing but their marker/behaviour — they log through the `&mut TestHost` they
// are handed and schedule through the `&mut Reactor` they are handed.
//
// Author: Andrew Yates
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

#![allow(dead_code)]

use std::rc::Rc;
use trust_js_reactor::{
    Capability, Completion, Host, PromiseId, Reactor, ReactorError, RejectionEvent, ThenLookup,
    TimerId,
};

/// The M0 driver's pinned FIXED_EPOCH, so a reactor clock reads the same base.
pub const EPOCH: u64 = 1_700_000_000_000;

type Rx = Reactor<TestVal, TestFn>;

/// A stand-in host value (the interp's JsValue, in miniature).
#[derive(Clone, Debug, PartialEq)]
pub enum TestVal {
    Undefined,
    Bool(bool),
    Num(f64),
    Str(String),
    Arr(Vec<TestVal>),
    /// An allSettled result record.
    Settled { fulfilled: bool, payload: Box<TestVal> },
    /// An AggregateError's collected errors (Promise.any all-reject).
    Aggregate(Vec<TestVal>),
    /// A host error value (e.g. the self-resolution TypeError).
    Error(String),
    /// A value that IS one of this reactor's promises.
    Promise(PromiseId),
    /// A thenable object; the index selects its `then` behaviour in the host.
    Thenable(usize),
}

/// A stand-in host callback handle (the interp's function-call closure).
#[derive(Clone)]
#[allow(clippy::type_complexity)]
pub enum TestFn {
    /// A reaction handler: takes the settlement value, returns a completion.
    Reaction(Rc<dyn Fn(&mut Rx, &mut TestHost, TestVal) -> Completion<TestVal>>),
    /// A no-argument callback (queueMicrotask job / timer callback).
    Void(Rc<dyn Fn(&mut Rx, &mut TestHost)>),
    /// A thenable's `then` method: takes the reactor's resolve/reject caps.
    Then(Rc<dyn Fn(&mut Rx, &mut TestHost, Capability, Capability)>),
}

/// The concrete host: an ordered marker log + the thenable registry + the
/// observable unhandled-rejection signal log.
#[derive(Default)]
pub struct TestHost {
    /// Ordered console.log-equivalent markers — the observable trace.
    pub log: Vec<String>,
    /// `then` behaviours for `TestVal::Thenable(idx)`.
    pub thenables: Vec<TestFn>,
    /// The unhandled-rejection signal, as ordered "reject:<reason>" /
    /// "handle:<id>" strings.
    pub rejections: Vec<String>,
}

pub fn val_str(v: &TestVal) -> String {
    match v {
        TestVal::Undefined => "undefined".into(),
        TestVal::Bool(b) => b.to_string(),
        TestVal::Num(n) => n.to_string(),
        TestVal::Str(s) => s.clone(),
        TestVal::Error(e) => format!("Error({e})"),
        TestVal::Promise(p) => format!("Promise({p})"),
        TestVal::Arr(_) => "[array]".into(),
        TestVal::Settled { fulfilled, .. } => {
            if *fulfilled { "settled:fulfilled".into() } else { "settled:rejected".into() }
        }
        TestVal::Aggregate(_) => "AggregateError".into(),
        TestVal::Thenable(_) => "[thenable]".into(),
    }
}

impl Host for TestHost {
    type Value = TestVal;
    type Fn = TestFn;

    fn call(&mut self, rx: &mut Rx, f: &TestFn, arg: TestVal) -> Completion<TestVal> {
        match f {
            TestFn::Reaction(c) => c(rx, self, arg),
            TestFn::Void(c) => {
                c(rx, self);
                Completion::Normal(TestVal::Undefined)
            }
            TestFn::Then(_) => Completion::Normal(TestVal::Undefined),
        }
    }

    fn run_callback(&mut self, rx: &mut Rx, f: &TestFn) {
        match f {
            TestFn::Void(c) => c(rx, self),
            TestFn::Reaction(c) => {
                let _ = c(rx, self, TestVal::Undefined);
            }
            TestFn::Then(_) => {}
        }
    }

    fn get_then(&mut self, _rx: &mut Rx, value: &TestVal) -> ThenLookup<TestVal, TestFn> {
        match value {
            TestVal::Thenable(idx) => ThenLookup::Thenable(self.thenables[*idx].clone()),
            // A native promise is itself a thenable: assimilating it forwards its
            // settlement to the resolving capability through the job queue — the
            // spec behaviour (and the extra ticks that come with it).
            TestVal::Promise(id) => {
                let inner = *id;
                ThenLookup::Thenable(TestFn::Then(Rc::new(move |rx, host, res, rej| {
                    let rc = res.clone();
                    let on_f = TestFn::Reaction(Rc::new(move |rx, host, v| {
                        rx.resolve(host, &rc, v);
                        Completion::Normal(TestVal::Undefined)
                    }));
                    let rj = rej.clone();
                    let on_r = TestFn::Reaction(Rc::new(move |rx, host, e| {
                        rx.reject(host, &rj, e);
                        Completion::Normal(TestVal::Undefined)
                    }));
                    rx.then(host, inner, Some(on_f), Some(on_r));
                })))
            }
            _ => ThenLookup::NotThenable,
        }
    }

    fn call_then(
        &mut self,
        rx: &mut Rx,
        then: &TestFn,
        _thenable: &TestVal,
        resolve: Capability,
        reject: Capability,
    ) -> Completion<TestVal> {
        if let TestFn::Then(c) = then {
            c(rx, self, resolve, reject);
        }
        Completion::Normal(TestVal::Undefined)
    }

    fn type_error(&mut self, message: &str) -> TestVal {
        TestVal::Error(format!("TypeError: {message}"))
    }

    fn promise_of(&mut self, value: &TestVal) -> Option<PromiseId> {
        match value {
            TestVal::Promise(id) => Some(*id),
            _ => None,
        }
    }

    fn build_array(&mut self, elements: Vec<TestVal>) -> TestVal {
        TestVal::Arr(elements)
    }

    fn build_settled_fulfilled(&mut self, value: TestVal) -> TestVal {
        TestVal::Settled { fulfilled: true, payload: Box::new(value) }
    }

    fn build_settled_rejected(&mut self, reason: TestVal) -> TestVal {
        TestVal::Settled { fulfilled: false, payload: Box::new(reason) }
    }

    fn build_aggregate_error(&mut self, errors: Vec<TestVal>) -> TestVal {
        TestVal::Aggregate(errors)
    }

    fn on_rejection(&mut self, event: RejectionEvent<TestVal>) {
        match event {
            RejectionEvent::Rejected { promise, reason } => {
                self.rejections.push(format!("reject:{promise}:{}", val_str(&reason)));
            }
            RejectionEvent::Handled { promise } => {
                self.rejections.push(format!("handle:{promise}"));
            }
        }
    }
}

// --- free constructors ----------------------------------------------------

pub fn s(x: &str) -> TestVal {
    TestVal::Str(x.to_string())
}

pub fn void(f: impl Fn(&mut Rx, &mut TestHost) + 'static) -> TestFn {
    TestFn::Void(Rc::new(f))
}

pub fn reaction(f: impl Fn(&mut Rx, &mut TestHost, TestVal) -> Completion<TestVal> + 'static) -> TestFn {
    TestFn::Reaction(Rc::new(f))
}

/// Register a thenable in the host from inside a reaction (where only the host
/// is in scope), returning the `TestVal::Thenable` that names it. Mirrors a
/// handler `return { then(resolve, reject) { ... } }`.
pub fn register_thenable(
    host: &mut TestHost,
    body: impl Fn(&mut Reactor<TestVal, TestFn>, &mut TestHost, Capability, Capability) + 'static,
) -> TestVal {
    let idx = host.thenables.len();
    host.thenables.push(TestFn::Then(Rc::new(body)));
    TestVal::Thenable(idx)
}

/// A reaction that logs `marker` and passes its argument through (so it chains).
pub fn log_reaction(marker: &str) -> TestFn {
    let m = marker.to_string();
    TestFn::Reaction(Rc::new(move |_rx, host, arg| {
        host.log.push(m.clone());
        Completion::Normal(arg)
    }))
}

// --- the runtime DSL ------------------------------------------------------

/// A reactor + its host, with a compact DSL mirroring the JS surface a program
/// would use (console.log / queueMicrotask / setTimeout / Promise.*).
pub struct Rt {
    pub rx: Reactor<TestVal, TestFn>,
    pub host: TestHost,
}

impl Default for Rt {
    fn default() -> Self {
        Self::new()
    }
}

impl Rt {
    pub fn new() -> Self {
        Self { rx: Reactor::new(EPOCH), host: TestHost::default() }
    }

    pub fn with_budget(budget: u64) -> Self {
        Self { rx: Reactor::with_budget(EPOCH, budget), host: TestHost::default() }
    }

    // -- synchronous "script" effects --
    pub fn log(&mut self, marker: &str) {
        self.host.log.push(marker.to_string());
    }

    // -- queueMicrotask --
    pub fn micro(&mut self, marker: &str) {
        let m = marker.to_string();
        self.rx.queue_microtask(void(move |_rx, host| host.log.push(m.clone())));
    }
    pub fn micro_fn(&mut self, f: TestFn) {
        self.rx.queue_microtask(f);
    }

    // -- timers --
    pub fn timer(&mut self, delay: u64, marker: &str) -> TimerId {
        let m = marker.to_string();
        self.rx.set_timeout(void(move |_rx, host| host.log.push(m.clone())), delay)
    }
    pub fn timer_fn(&mut self, delay: u64, f: TestFn) -> TimerId {
        self.rx.set_timeout(f, delay)
    }
    pub fn interval(&mut self, delay: u64, marker: &str) -> TimerId {
        let m = marker.to_string();
        self.rx.set_interval(void(move |_rx, host| host.log.push(m.clone())), delay)
    }
    pub fn clear(&mut self, id: TimerId) {
        self.rx.clear_timer(id);
    }

    // -- promises --
    pub fn resolved(&mut self, v: TestVal) -> PromiseId {
        self.rx.promise_resolve(&mut self.host, v)
    }
    pub fn rejected(&mut self, v: TestVal) -> PromiseId {
        self.rx.promise_reject(&mut self.host, v)
    }
    pub fn new_promise(&mut self) -> (PromiseId, Capability) {
        self.rx.new_promise()
    }
    pub fn resolve(&mut self, cap: &Capability, v: TestVal) {
        self.rx.resolve(&mut self.host, cap, v);
    }
    pub fn reject(&mut self, cap: &Capability, v: TestVal) {
        self.rx.reject(&mut self.host, cap, v);
    }

    /// `p.then(onFulfilled?, onRejected?)` where each present handler logs its
    /// marker and passes the value through. Returns the dependent promise.
    pub fn then_log(&mut self, p: PromiseId, on_f: Option<&str>, on_r: Option<&str>) -> PromiseId {
        let f = on_f.map(log_reaction);
        let r = on_r.map(log_reaction);
        self.rx.then(&mut self.host, p, f, r)
    }
    /// `p.then(v => console.log(String(v)))` — logs the fulfilled value.
    pub fn then_val(&mut self, p: PromiseId) -> PromiseId {
        let f = reaction(|_rx, host, arg| {
            host.log.push(val_str(&arg));
            Completion::Normal(arg)
        });
        self.rx.then(&mut self.host, p, Some(f), None)
    }
    pub fn then_fn(&mut self, p: PromiseId, on_f: Option<TestFn>, on_r: Option<TestFn>) -> PromiseId {
        self.rx.then(&mut self.host, p, on_f, on_r)
    }
    pub fn catch_log(&mut self, p: PromiseId, marker: &str) -> PromiseId {
        let r = log_reaction(marker);
        self.rx.catch(&mut self.host, p, r)
    }

    // -- combinators --
    pub fn all(&mut self, els: Vec<TestVal>) -> PromiseId {
        self.rx.promise_all(&mut self.host, els)
    }
    pub fn all_settled(&mut self, els: Vec<TestVal>) -> PromiseId {
        self.rx.promise_all_settled(&mut self.host, els)
    }
    pub fn race(&mut self, els: Vec<TestVal>) -> PromiseId {
        self.rx.promise_race(&mut self.host, els)
    }
    pub fn any(&mut self, els: Vec<TestVal>) -> PromiseId {
        self.rx.promise_any(&mut self.host, els)
    }

    /// Register a thenable whose `then(resolve, reject)` runs `body`.
    pub fn thenable(
        &mut self,
        body: impl Fn(&mut Rx, &mut TestHost, Capability, Capability) + 'static,
    ) -> TestVal {
        let idx = self.host.thenables.len();
        self.host.thenables.push(TestFn::Then(Rc::new(body)));
        TestVal::Thenable(idx)
    }

    // -- drive --
    pub fn drain(&mut self) -> Result<(), ReactorError> {
        self.rx.drain(&mut self.host)
    }
    pub fn order(&self) -> Vec<String> {
        self.host.log.clone()
    }
}
