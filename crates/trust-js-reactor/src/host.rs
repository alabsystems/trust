// The `Host` trait: the seam between the engine-only reactor and a real JS
// front end. The reactor owns the state machine, queues, virtual clock, and job
// scheduling; the host owns everything that requires *interpreting JS*: invoking
// a function handler, deciding whether a value is a thenable (a property get
// that may run a user getter), running a thenable's `then`, and building the
// aggregate values the combinators fulfill with (arrays, {status,value}
// records, AggregateError). The reactor NEVER interprets JS — it calls back
// through this trait.
//
// Reentrancy is by design: every host method receives `&mut Reactor`, so JS
// running inside a callback can create promises, call `then`, `queueMicrotask`,
// and arm timers by calling straight back into the reactor. There is no
// ownership cycle and no `Rc<RefCell>` on the hot path — the reactor and host
// are threaded as `&mut` parameters through the reentrant call graph, the way a
// tree-walking interpreter threads a context.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

use crate::types::{Capability, PromiseId};
use crate::Reactor;

/// The completion of invoking a host callback: a normal return or a throw.
/// (The spec's normal vs abrupt completion, narrowed to what a reaction needs.)
pub enum Completion<V> {
    Normal(V),
    Throw(V),
}

/// The result of the resolve algorithm's `Get(resolution, "then")` step.
pub enum ThenLookup<V, F> {
    /// Not a thenable (or `then` not callable): fulfill with the value.
    NotThenable,
    /// A thenable — assimilate via a queued PromiseResolveThenableJob using this
    /// `then` method.
    Thenable(F),
    /// Reading `.then` threw (a hostile getter): reject with this value.
    Threw(V),
}

/// The observable unhandled-rejection signal, delivered live to the host as the
/// reactor settles/handles promises. The consumer reads this to drive
/// `process` 'unhandledRejection'/'rejectionHandled' (and the async
/// ObservableTrace's unhandled-rejection observable). The reactor ALSO retains
/// the currently-outstanding set (`Reactor::unhandled_rejections`) for an
/// end-of-drain sweep.
pub enum RejectionEvent<V> {
    /// A promise rejected with no handler attached at reject time.
    Rejected { promise: PromiseId, reason: V },
    /// A previously-signalled unhandled rejection later got a handler.
    Handled { promise: PromiseId },
}

/// The consumer plug-in. `Value` is the host's opaque JS value (the interp's
/// JsValue); `Fn` is its opaque callable handle (a function-call closure). The
/// reactor treats both as black boxes.
pub trait Host {
    /// The opaque host value type (e.g. the interp's `JsValue`).
    type Value: Clone;
    /// The opaque host callback handle (e.g. a JS function / bound closure).
    type Fn: Clone;

    /// Invoke a reaction handler `f` with one argument, returning its completion.
    /// (PromiseReactionJob: `Call(handler, undefined, « argument »)`.) JS run
    /// here may reenter `rx`.
    fn call(
        &mut self,
        rx: &mut Reactor<Self::Value, Self::Fn>,
        f: &Self::Fn,
        argument: Self::Value,
    ) -> Completion<Self::Value>;

    /// Invoke a no-argument callback (a `queueMicrotask` job or a timer
    /// callback). An abrupt completion here is an uncaught exception the host
    /// handles per its own policy (Node: process-level 'uncaughtException'); the
    /// reactor does not observe it, so drain order stays deterministic.
    fn run_callback(&mut self, rx: &mut Reactor<Self::Value, Self::Fn>, f: &Self::Fn);

    /// Perform the resolve algorithm's thenable check: `Get(resolution, "then")`
    /// and a callable test. May run a user getter (hence `&mut self` + `rx`).
    fn get_then(
        &mut self,
        rx: &mut Reactor<Self::Value, Self::Fn>,
        value: &Self::Value,
    ) -> ThenLookup<Self::Value, Self::Fn>;

    /// Run a thenable's `then` with the reactor's resolving functions
    /// (PromiseResolveThenableJob). The host wraps `resolve`/`reject` as JS
    /// functions (both share one guard, so the first call wins) and invokes
    /// `Call(then, thenable, « resolve, reject »)`. An abrupt completion is
    /// routed to `reject` by the reactor.
    fn call_then(
        &mut self,
        rx: &mut Reactor<Self::Value, Self::Fn>,
        then: &Self::Fn,
        thenable: &Self::Value,
        resolve: Capability,
        reject: Capability,
    ) -> Completion<Self::Value>;

    /// Build the host's `TypeError` value for the self-resolution guard
    /// (resolving a promise with itself). The reactor cannot fabricate a JS
    /// error, so the host supplies it.
    fn type_error(&mut self, message: &str) -> Self::Value;

    /// If `value` is one of THIS reactor's promises, return its id — used for the
    /// self-resolution `SameValue(resolution, promise)` check and the
    /// `Promise.resolve(nativePromise)` passthrough. Default: never a promise.
    fn promise_of(&mut self, _value: &Self::Value) -> Option<PromiseId> {
        None
    }

    /// Build the array a fulfilled `Promise.all` / `Promise.allSettled` produces
    /// (also the errors array inside an AggregateError). Engine collects the
    /// elements in order; host boxes them into a JS Array.
    fn build_array(&mut self, elements: Vec<Self::Value>) -> Self::Value;

    /// Build an allSettled `{ status: "fulfilled", value }` record.
    fn build_settled_fulfilled(&mut self, value: Self::Value) -> Self::Value;

    /// Build an allSettled `{ status: "rejected", reason }` record.
    fn build_settled_rejected(&mut self, reason: Self::Value) -> Self::Value;

    /// Build the `AggregateError` a fully-rejected `Promise.any` rejects with,
    /// wrapping the collected per-element errors (in order).
    fn build_aggregate_error(&mut self, errors: Vec<Self::Value>) -> Self::Value;

    /// The live unhandled-rejection signal. Default: ignore (the reactor still
    /// retains the outstanding set for an end-of-drain sweep).
    fn on_rejection(&mut self, _event: RejectionEvent<Self::Value>) {}
}
