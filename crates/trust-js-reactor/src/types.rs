// Internal reactor data types + the one public handle the consumer holds
// (`Capability`). Everything else here is `pub(crate)`: the promise record, the
// reaction records, the job variants, the combinator aggregation state, and the
// timer entry. Kept in insertion-ordered / index-keyed structures throughout so
// nothing observable depends on hash iteration order.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

use std::cell::{Cell, RefCell};
use std::rc::Rc;

/// A promise identity: a dense index into the reactor's promise table. Stable
/// for the reactor's lifetime; handed to and from the consumer opaquely.
pub type PromiseId = usize;

/// A timer identity: the monotonically-increasing sequence number assigned when
/// the timer was armed. `clear_timer` takes one of these. Stable across an
/// interval's re-arming (the id is fixed; only its ordering seq refreshes).
pub type TimerId = u64;

/// The observable status of a promise.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PromiseStatus {
    /// Not yet settled.
    Pending,
    /// Settled with a value.
    Fulfilled,
    /// Settled with a reason.
    Rejected,
}

/// A promise-resolving capability: the `{ [[Resolve]], [[Reject]] }` pair the
/// spec's CreateResolvingFunctions produces, condensed to the target promise
/// plus the *shared* already-resolved guard. Cloning shares the guard, so the
/// spec's "the first of resolve/reject wins, the rest are inert" invariant holds
/// across every clone of one capability — and a FRESH capability for the same
/// promise (as PromiseResolveThenableJob makes) gets its own guard, exactly as
/// the spec mints fresh resolving functions.
#[derive(Clone)]
pub struct Capability {
    /// The promise this capability resolves or rejects.
    pub promise: PromiseId,
    pub(crate) guard: Rc<Cell<bool>>,
}

impl Capability {
    pub(crate) fn new(promise: PromiseId) -> Self {
        Self {
            promise,
            guard: Rc::new(Cell::new(false)),
        }
    }

    /// Claim the capability (`alreadyResolved`). Returns true on the first call,
    /// false thereafter — the guard shared by every clone of this capability.
    pub(crate) fn claim(&self) -> bool {
        if self.guard.get() {
            return false;
        }
        self.guard.set(true);
        true
    }
}

pub(crate) enum PromiseState<V> {
    Pending,
    Fulfilled(V),
    Rejected(V),
}

pub(crate) struct PromiseRecord<V, F> {
    pub state: PromiseState<V>,
    pub fulfill_reactions: Vec<ReactionRecord<V, F>>,
    pub reject_reactions: Vec<ReactionRecord<V, F>>,
    /// `[[PromiseIsHandled]]`: set the first time a reaction is attached (via
    /// `then`), gating the unhandled-rejection signal.
    pub handled: bool,
}

pub(crate) struct ReactionRecord<V, F> {
    pub handler: Handler<V, F>,
    /// The dependent promise's capability, resolved/rejected with the reaction's
    /// outcome. `None` for engine-internal combinator reactions, which drive
    /// their own aggregate capability instead.
    pub cap: Option<Capability>,
}

/// What a reaction does when it fires.
pub(crate) enum Handler<V, F> {
    /// Default onFulfilled: pass the value through to the dependent (identity).
    Identity,
    /// Default onRejected: re-reject the dependent with the reason (thrower).
    Thrower,
    /// A host (JS) function handler, invoked through `Host::call`.
    Host(F),
    /// An engine-internal combinator element callback.
    Internal(Internal<V>),
}

/// Engine-internal reactions driving the combinator aggregation state machines.
pub(crate) enum Internal<V> {
    /// Promise.all element fulfilled: store at index, decrement, resolve on 0.
    AllFulfill {
        state: Rc<RefCell<AggState<V>>>,
        index: usize,
    },
    /// Promise.allSettled element fulfilled: store {fulfilled,value} result.
    SettledFulfill {
        state: Rc<RefCell<AggState<V>>>,
        index: usize,
    },
    /// Promise.allSettled element rejected: store {rejected,reason} result.
    SettledReject {
        state: Rc<RefCell<AggState<V>>>,
        index: usize,
    },
    /// Promise.any element rejected: store error, reject-aggregate on 0.
    AnyReject {
        state: Rc<RefCell<AggState<V>>>,
        index: usize,
    },
    /// Race/any element fulfilled, or race element rejected: settle the shared
    /// capability directly (first settle wins via the capability guard).
    ResolveMain { cap: Capability },
    RejectMain { cap: Capability },
}

/// Shared aggregation state for the collecting combinators (all / allSettled /
/// any). `slots` collects per-index results/errors in ORDER regardless of the
/// order elements settle in; `remaining` counts down; `cap` is the aggregate
/// promise's capability; `settled` guards a double-completion.
pub(crate) struct AggState<V> {
    pub slots: Vec<Option<V>>,
    pub remaining: usize,
    pub cap: Capability,
    pub settled: bool,
}

/// A queued job. Microtask queue entries are these; the FIFO discipline plus the
/// deterministic enqueue order make the drain byte-reproducible.
pub(crate) enum Job<V, F> {
    /// A `queueMicrotask` / host job: invoke `f` with no argument.
    HostMicrotask(F),
    /// A PromiseReactionJob: run `handler` with `arg`, settle `cap`.
    Reaction {
        handler: Handler<V, F>,
        arg: V,
        cap: Option<Capability>,
    },
    /// A PromiseResolveThenableJob: assimilate `thenable` into `promise` by
    /// invoking its `then` with a fresh capability's resolve/reject.
    ResolveThenable {
        promise: PromiseId,
        thenable: V,
        then: F,
    },
}

/// Timer ordering key: `(deadline, order_seq)`. `BTreeMap` over this yields the
/// spec/HTML order the M0 driver pins — earliest deadline first, ties broken by
/// insertion order (the monotonic seq). Total and insertion-independent.
pub(crate) type TimerKey = (u64, u64);

pub(crate) struct TimerEntry<F> {
    pub id: TimerId,
    pub f: F,
    /// `Some(period)` for `set_interval` (re-arms after firing); `None` for a
    /// one-shot `set_timeout`.
    pub interval: Option<u64>,
}
