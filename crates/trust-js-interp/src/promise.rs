// §27.2 Promise objects + the event-loop surface (`queueMicrotask`,
// `setTimeout`/`clearTimeout`), driven by the deterministic trust-js-reactor.
// The reactor owns the promise state machine, reaction records, microtask/timer
// queues, and the virtual clock; this module is the JS-facing glue: the
// constructor and its resolving functions, `then`/`catch`/`finally`, the static
// `resolve`/`reject`/`all`/`allSettled`/`race`/`any`, and the timer/microtask
// intrinsics. All reactor access goes through `rx_op` (see host.rs).
//
// Honesty: only the intrinsic `%Promise%` receiver is modeled. A Promise
// SUBCLASS receiver on any static combinator, and a non-default `@@species` on
// `then`/`catch`/`finally`, refuse (NoCoverage) rather than risk a wrong result.
// `setInterval` refuses: its re-arm ordering (the reactor mints a fresh order
// key per re-arm; the trace driver keeps the timer's original id) can diverge
// from the driver on a same-deadline collision — a sound refusal, never a wrong
// trace.
//
// Author: Andrew Yates
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

use crate::host::{JobFn, ResolveEntry};
use crate::interp::{Abrupt, ERes, Interp};
use std::cell::RefCell;
use std::rc::Rc;
use trust_js_reactor::{Capability, PromiseId};
use trust_js_value::{
    units_from_str, ErrKind, FnData, JsObject, JsValue, NativeFn, ObjId, ObjKind, PropKey, PropValue,
    Property, SymId, WkSym,
};

/// Cap on a combinator iterable's element count (totality bound).
const MAX_COMBINATOR_ELEMS: usize = 1_000_000;

#[derive(Clone, Copy, PartialEq, Eq)]
enum CombKind {
    All,
    AllSettled,
    Race,
    Any,
}

/// A NewPromiseCapability GetCapabilitiesExecutor's shared slot: the
/// `[[Resolve]]`/`[[Reject]]` the executor writes (each starts `undefined`; the
/// executor throws if a slot is already non-`undefined`, per 27.2.1.5.1).
pub(crate) struct CapRecord {
    pub(crate) resolve: JsValue,
    pub(crate) reject: JsValue,
}

/// A resolved PromiseCapability Record: the constructed promise plus its
/// resolve/reject functions (both validated callable).
struct PromiseCap {
    promise: JsValue,
    resolve: JsValue,
    reject: JsValue,
}

/// Aggregation state shared across one combinator call's element functions
/// (Promise.all / allSettled / any). `race` uses none.
struct CombShared {
    kind: CombKind,
    /// One slot per iterated element, filled as each settles; the final ordered
    /// array (all/allSettled) or AggregateError error list (any).
    values: Vec<JsValue>,
    /// `remainingElementsCount.[[Value]]` (starts 1 for the loop-hold guard).
    remaining: i64,
    /// `resultCapability.[[Resolve]]` / `[[Reject]]`.
    cap_resolve: JsValue,
    cap_reject: JsValue,
}

/// One combinator element closure's state (a Promise.all / allSettled resolve
/// element, an allSettled / any reject element). Cheap to clone (Rc handles).
#[derive(Clone)]
pub(crate) struct CombElement {
    /// `[[AlreadyCalled]]` — shared between an allSettled fulfill/reject pair.
    already_called: Rc<RefCell<bool>>,
    /// `[[Index]]` into the shared `values`.
    index: usize,
    /// True for an allSettled/any reject-side element (chooses the stored shape).
    is_reject: bool,
    shared: Rc<RefCell<CombShared>>,
}

impl Interp {
    /// Dispatch for every Promise / event-loop native.
    pub(crate) fn dispatch_promise(
        &mut self,
        nf: NativeFn,
        fid: ObjId,
        this: JsValue,
        args: Vec<JsValue>,
        new_target: Option<&JsValue>,
    ) -> ERes {
        let arg = |i: usize| args.get(i).cloned().unwrap_or(JsValue::Undefined);
        match nf {
            NativeFn::PromiseCtor => self.promise_construct(&args, new_target),
            NativeFn::PromiseResolveFn | NativeFn::PromiseRejectFn => {
                self.run_resolving_fn(fid, arg(0))
            }
            NativeFn::PromiseValueThunk | NativeFn::PromiseThrowThunk => self.run_value_thunk(fid),
            NativeFn::PromiseCapExecutor => self.run_cap_executor(fid, arg(0), arg(1)),
            NativeFn::PromiseAllResolveElement
            | NativeFn::PromiseAllSettledResolveElement
            | NativeFn::PromiseAllSettledRejectElement
            | NativeFn::PromiseAnyRejectElement => self.run_comb_element(fid, arg(0)),
            NativeFn::PromiseResolve => self.promise_static_resolve(&this, arg(0)),
            NativeFn::PromiseReject => self.promise_static_reject(&this, arg(0)),
            NativeFn::PromiseAll => self.run_combinator(&this, arg(0), CombKind::All),
            NativeFn::PromiseAllSettled => self.run_combinator(&this, arg(0), CombKind::AllSettled),
            NativeFn::PromiseRace => self.run_combinator(&this, arg(0), CombKind::Race),
            NativeFn::PromiseAny => self.run_combinator(&this, arg(0), CombKind::Any),
            NativeFn::PromiseTry => self.promise_try(&this, &args),
            NativeFn::PromiseWithResolvers => self.promise_with_resolvers(&this),
            NativeFn::PromiseProtoThen => self.promise_then(&this, arg(0), arg(1)),
            // `catch` is generic: `Invoke(this, "then", «undefined, onRejected»)`
            // — it brand-checks nothing, so it also works on thenables/primitives.
            NativeFn::PromiseProtoCatch => {
                let then = self.get_prop(&this, &PropKey::from_str("then"))?;
                self.call_value(&then, this.clone(), vec![JsValue::Undefined, arg(0)])
            }
            NativeFn::PromiseProtoFinally => self.promise_finally(&this, arg(0)),
            NativeFn::QueueMicrotask => self.queue_microtask(arg(0)),
            NativeFn::SetTimeout => self.set_timer(&args),
            NativeFn::SetInterval => Err(Abrupt::Fatal(
                "setInterval re-arm ordering (out of slice — sound refusal)".to_string(),
            )),
            NativeFn::ClearTimer => {
                self.clear_timer(arg(0));
                Ok(JsValue::Undefined)
            }
            _ => Err(Abrupt::Fatal("non-promise native in promise dispatch".to_string())),
        }
    }

    // -- constructor + resolving functions ---------------------------------

    fn promise_construct(&mut self, args: &[JsValue], new_target: Option<&JsValue>) -> ERes {
        // 27.2.3.1: `Promise()` without `new` throws; executor must be callable.
        let Some(nt) = new_target else {
            return Err(self.throw_type_error());
        };
        let executor = args.first().cloned().unwrap_or(JsValue::Undefined);
        if !self.is_callable_value(&executor) {
            return Err(self.throw_type_error());
        }
        let proto = self.get_prototype_from_constructor(nt, self.intr.promise_proto)?;
        let (pobj, _pid, cap) = self.new_promise_with_proto(proto)?;
        let resolve_fn = self.make_resolving_fn(cap.clone(), false)?;
        let reject_fn = self.make_resolving_fn(cap.clone(), true)?;
        let r = self.call_value(
            &executor,
            JsValue::Undefined,
            vec![JsValue::Obj(resolve_fn), JsValue::Obj(reject_fn)],
        );
        match r {
            Ok(_) => Ok(JsValue::Obj(pobj)),
            // An executor throw calls the reject function (shared guard).
            Err(Abrupt::Throw(e)) => {
                self.rx_op(|it, rx| rx.reject(it, &cap, e));
                Ok(JsValue::Obj(pobj))
            }
            Err(a) => Err(a),
        }
    }

    /// A resolve/reject function's [[Call]]: drive the reactor's capability.
    fn run_resolving_fn(&mut self, fid: ObjId, value: JsValue) -> ERes {
        let Some(ResolveEntry { cap, reject }) = self.resolve_caps.get(&fid) else {
            return Ok(JsValue::Undefined);
        };
        let cap = cap.clone();
        let reject = *reject;
        self.rx_op(|it, rx| {
            if reject {
                rx.reject(it, &cap, value);
            } else {
                rx.resolve(it, &cap, value);
            }
        });
        Ok(JsValue::Undefined)
    }

    /// A `finally` value-transform thunk: return (or throw) the captured value.
    fn run_value_thunk(&mut self, fid: ObjId) -> ERes {
        match self.thunk_values.get(&fid) {
            Some((v, throw)) => {
                let v = v.clone();
                if *throw {
                    Err(Abrupt::Throw(v))
                } else {
                    Ok(v)
                }
            }
            None => Ok(JsValue::Undefined),
        }
    }

    // -- static resolve / reject -------------------------------------------

    fn promise_static_resolve(&mut self, this: &JsValue, x: JsValue) -> ERes {
        // The intrinsic `%Promise%` receiver keeps the calibrated reactor
        // fast-path; a subclass / arbitrary constructor receiver C takes the
        // faithful PromiseResolve(C, x) path (27.2.4.7.1). Non-object → TypeError.
        if self.is_intrinsic_promise_ctor(this) {
            let obj = self.promise_resolve_obj(x)?;
            return Ok(JsValue::Obj(obj));
        }
        if !matches!(this, JsValue::Obj(_)) {
            return Err(self.throw_type_error());
        }
        self.promise_resolve_general(this, x)
    }

    fn promise_static_reject(&mut self, this: &JsValue, reason: JsValue) -> ERes {
        if self.is_intrinsic_promise_ctor(this) {
            let (obj, _pid, cap) = self.new_promise_object()?;
            self.rx_op(|it, rx| rx.reject(it, &cap, reason));
            return Ok(JsValue::Obj(obj));
        }
        // `Promise.reject` requires Type(C) is Object only via NewPromiseCapability
        // (IsConstructor false → TypeError), so a non-object receiver still throws.
        let cap = self.new_promise_capability(this)?;
        self.call_value(&cap.reject, JsValue::Undefined, vec![reason])?;
        Ok(cap.promise)
    }

    /// `Promise.try(callback, ...args)` — a new promise (via NewPromiseCapability
    /// on the `this` receiver C) resolved with the callback's result, or rejected
    /// with its thrown value.
    fn promise_try(&mut self, this: &JsValue, args: &[JsValue]) -> ERes {
        let callback = args.first().cloned().unwrap_or(JsValue::Undefined);
        let call_args: Vec<JsValue> = args.iter().skip(1).cloned().collect();
        if self.is_intrinsic_promise_ctor(this) {
            let (obj, _pid, cap) = self.new_promise_object()?;
            match self.call_value(&callback, JsValue::Undefined, call_args) {
                Ok(v) => self.rx_op(|it, rx| rx.resolve(it, &cap, v)),
                Err(Abrupt::Throw(e)) => self.rx_op(|it, rx| rx.reject(it, &cap, e)),
                Err(a) => return Err(a),
            }
            return Ok(JsValue::Obj(obj));
        }
        let cap = self.new_promise_capability(this)?;
        match self.call_value(&callback, JsValue::Undefined, call_args) {
            Ok(v) => self.call_value(&cap.resolve, JsValue::Undefined, vec![v])?,
            Err(Abrupt::Throw(e)) => self.call_value(&cap.reject, JsValue::Undefined, vec![e])?,
            Err(a) => return Err(a),
        };
        Ok(cap.promise)
    }

    /// `Promise.withResolvers()` — `{ promise, resolve, reject }` from
    /// NewPromiseCapability on the receiver C.
    fn promise_with_resolvers(&mut self, this: &JsValue) -> ERes {
        let (promise, resolve, reject) = if self.is_intrinsic_promise_ctor(this) {
            let (pobj, _pid, cap) = self.new_promise_object()?;
            let resolve = self.make_resolving_fn(cap.clone(), false)?;
            let reject = self.make_resolving_fn(cap, true)?;
            (JsValue::Obj(pobj), JsValue::Obj(resolve), JsValue::Obj(reject))
        } else {
            let cap = self.new_promise_capability(this)?;
            (cap.promise, cap.resolve, cap.reject)
        };
        let o = self.new_plain()?;
        for (key, val) in [("promise", promise), ("resolve", resolve), ("reject", reject)] {
            self.heap
                .obj_mut(o)
                .props
                .insert(PropKey::from_str(key), Property::data(val));
        }
        Ok(JsValue::Obj(o))
    }

    // -- then / catch / finally --------------------------------------------

    fn promise_then(&mut self, this: &JsValue, on_f: JsValue, on_r: JsValue) -> ERes {
        let pid = self.this_promise(this)?;
        self.require_default_species(this)?;
        let fh = self.callable_handle(&on_f);
        let rh = self.callable_handle(&on_r);
        let dep = self.rx_op(|it, rx| rx.then(it, pid, fh, rh));
        Ok(JsValue::Obj(self.wrap_promise(dep)?))
    }

    fn promise_finally(&mut self, this: &JsValue, on_finally: JsValue) -> ERes {
        // `finally` is generic (`Invoke(this, "then", …)`), so a thenable /
        // foreign this-value or a promise with a custom/poisoned `then` observes
        // its own `then` — which the reactor fast-path bypasses. Only a DIRECT
        // intrinsic `%Promise%` receiver (intrinsic `then`, intrinsic
        // constructor) is faithful; anything else refuses.
        if !self.is_direct_intrinsic_promise(this) {
            return Err(Abrupt::Fatal(
                "Promise.prototype.finally on a non-intrinsic-promise receiver (out of slice)"
                    .to_string(),
            ));
        }
        let pid = self.this_promise(this)?;
        self.require_default_species(this)?;
        let (fh, rh) = if self.is_callable_value(&on_finally) {
            (
                Some(JobFn::FinallyFulfill(on_finally.clone())),
                Some(JobFn::FinallyReject(on_finally)),
            )
        } else {
            // Non-callable onFinally: identity/thrower passthrough.
            (None, None)
        };
        let dep = self.rx_op(|it, rx| rx.then(it, pid, fh, rh));
        Ok(JsValue::Obj(self.wrap_promise(dep)?))
    }

    /// A `finally` reaction: `onFinally()`, then thread the original
    /// value/reason through `Promise.resolve(result).then(thunk)`.
    pub(crate) fn finally_reaction(
        &mut self,
        on_finally: &JsValue,
        original: JsValue,
        reject: bool,
    ) -> ERes {
        let result = self.call_value(on_finally, JsValue::Undefined, Vec::new())?;
        let inner = self.promise_resolve_obj(result)?;
        // Spec (Then/Catch Finally Functions): the thunk is attached via
        // `Invoke(promise, "then", « thunk »)`. The reactor fast-path attaches an
        // INTERNAL reaction instead of calling the JS `then`, so it is faithful
        // only when that `then` is the untouched intrinsic: `inner` a DIRECT
        // `%Promise%` (no shadowing own `then`/`constructor`) and
        // `%Promise.prototype%.then` unpatched. A promise carrying a spy `then`
        // (e.g. `p.then = function(){…}`), or a globally patched prototype
        // `then`, makes that invocation observable — refuse rather than silently
        // skip it (a sound no-coverage, never a wrong ordering trace).
        if !self.is_direct_intrinsic_promise(&JsValue::Obj(inner))
            || !self.own_native_is(self.intr.promise_proto, "then", NativeFn::PromiseProtoThen)
        {
            return Err(Abrupt::Fatal(
                "Promise.prototype.finally: observable `then` on the intermediate promise \
                 (out of slice)"
                    .to_string(),
            ));
        }
        let thunk = self.make_value_thunk(original, reject)?;
        let dep = self.promise_then_obj(inner, Some(JsValue::Obj(thunk)), None)?;
        Ok(JsValue::Obj(dep))
    }

    // -- combinators --------------------------------------------------------

    fn run_combinator(&mut self, this: &JsValue, iterable: JsValue, kind: CombKind) -> ERes {
        // A subclass / arbitrary constructor receiver C takes the faithful
        // JS-level protocol (NewPromiseCapability(C), GetPromiseResolve(C),
        // per-element `Call(C.resolve, ...)` + `Invoke(nextPromise, "then", ...)`).
        // The intrinsic `%Promise%` receiver keeps the calibrated reactor path.
        if !self.is_intrinsic_promise_ctor(this) {
            if !matches!(this, JsValue::Obj(_)) {
                return Err(self.throw_type_error());
            }
            return self.run_combinator_general(this, iterable, kind);
        }
        // The spec combinators are an OBSERVABLE protocol: they `Call(C.resolve,
        // ...)` per element and `Invoke(nextPromise, "then", ...)`. The reactor
        // fast-path reproduces the OUTCOME but not those method invocations, so
        // if a test has replaced `Promise.resolve` / `Promise.prototype.then`
        // (to spy on or alter them) the reactor path would diverge — refuse.
        if !self.combinator_protocol_intact() {
            return Err(Abrupt::Fatal(
                "Promise combinator with a patched resolve/then protocol (out of slice)".to_string(),
            ));
        }
        let elems = match self.iterate_to_vec(&iterable) {
            Ok(e) => e,
            // IfAbruptRejectPromise: an iteration throw rejects the result
            // promise (returned), not the combinator call.
            Err(Abrupt::Throw(e)) => {
                let (obj, _pid, cap) = self.new_promise_object()?;
                self.rx_op(|it, rx| rx.reject(it, &cap, e));
                return Ok(JsValue::Obj(obj));
            }
            Err(a) => return Err(a),
        };
        // The spec `Invoke(nextPromise, "then", …)` on each element is
        // observable. The reactor passes a native promise element through and
        // attaches an INTERNAL reaction (not its JS `then`), so a promise
        // element with a non-intrinsic `then` — or a subclass promise — would
        // diverge. Refuse those; plain promises / values / thenables stay exact.
        if elems.iter().any(|e| !self.combinator_safe_element(e)) {
            return Err(Abrupt::Fatal(
                "Promise combinator over an element with an observable custom `then` (out of slice)"
                    .to_string(),
            ));
        }
        let pid = self.rx_op(|it, rx| match kind {
            CombKind::All => rx.promise_all(it, elems),
            CombKind::AllSettled => rx.promise_all_settled(it, elems),
            CombKind::Race => rx.promise_race(it, elems),
            CombKind::Any => rx.promise_any(it, elems),
        });
        Ok(JsValue::Obj(self.wrap_promise(pid)?))
    }

    // -- queueMicrotask / timers -------------------------------------------

    fn queue_microtask(&mut self, cb: JsValue) -> ERes {
        if !self.is_callable_value(&cb) {
            return Err(self.throw_type_error());
        }
        self.rx_op(|_it, rx| rx.queue_microtask(JobFn::Call(cb)));
        Ok(JsValue::Undefined)
    }

    /// `setTimeout(cb, delay, ...args)` — matches the trace driver: a
    /// non-function `cb` returns 0 (no throw); the id is 1-based per call.
    fn set_timer(&mut self, args: &[JsValue]) -> ERes {
        let cb = args.first().cloned().unwrap_or(JsValue::Undefined);
        if !self.is_callable_value(&cb) {
            return Ok(JsValue::Num(0.0));
        }
        // Driver: `Number(delay) || 0`. Refuse fractional/negative delays whose
        // virtual ordering the reactor's u64 clock can't reproduce exactly.
        let delay = match args.get(1) {
            None | Some(JsValue::Undefined) => 0u64,
            Some(v) => {
                let d = self.to_number(v)?;
                if d.is_nan() || d == 0.0 {
                    0
                } else if d < 0.0 || d.fract() != 0.0 || d > 9.007_199_254_740_992e15 {
                    return Err(Abrupt::Fatal(
                        "setTimeout with a negative/fractional delay (out of slice)".to_string(),
                    ));
                } else {
                    d as u64
                }
            }
        };
        let extra: Vec<JsValue> = args.iter().skip(2).cloned().collect();
        let job = JobFn::Timer(cb, Rc::new(extra));
        let reactor_id = self.rx_op(|_it, rx| rx.set_timeout(job, delay));
        self.timer_seq += 1;
        let js_id = self.timer_seq;
        self.timer_map.insert(js_id, reactor_id);
        Ok(JsValue::Num(js_id as f64))
    }

    /// `clearTimeout(id)` — the driver filters by strict `!==`, so only a
    /// numeric id matching a live timer clears anything.
    fn clear_timer(&mut self, id: JsValue) {
        if let JsValue::Num(n) = id {
            if n.fract() == 0.0 && n >= 0.0 {
                #[allow(clippy::cast_sign_loss, clippy::cast_possible_truncation)]
                let js_id = n as u64;
                if let Some(reactor_id) = self.timer_map.get(&js_id).copied() {
                    self.rx_op(|_it, rx| rx.clear_timer(reactor_id));
                }
            }
        }
    }

    // -- shared builders (also the reactor `Host` aggregate builders) -------

    /// Allocate a fresh Promise object + reactor promise with the default
    /// `%Promise.prototype%`.
    pub(crate) fn new_promise_object(&mut self) -> Result<(ObjId, PromiseId, Capability), Abrupt> {
        let proto = self.intr.promise_proto;
        self.new_promise_with_proto(proto)
    }

    fn new_promise_with_proto(
        &mut self,
        proto: ObjId,
    ) -> Result<(ObjId, PromiseId, Capability), Abrupt> {
        let (pid, cap) = self.rx_op(|_it, rx| rx.new_promise());
        let obj = self.alloc_obj(JsObject::new(ObjKind::Promise(pid), Some(proto)))?;
        Ok((obj, pid, cap))
    }

    /// Wrap an existing reactor promise id in a fresh JS Promise object.
    pub(crate) fn wrap_promise(&mut self, pid: PromiseId) -> Result<ObjId, Abrupt> {
        let proto = self.intr.promise_proto;
        self.alloc_obj(JsObject::new(ObjKind::Promise(pid), Some(proto)))
    }

    /// `Promise.resolve(x)` (receiver `%Promise%`) returning the Promise object.
    /// Spec passes an existing promise through ONLY when its `constructor` is
    /// the receiver — a promise with a foreign/reassigned constructor is
    /// re-wrapped.
    pub(crate) fn promise_resolve_obj(&mut self, x: JsValue) -> Result<ObjId, Abrupt> {
        if let JsValue::Obj(o) = &x {
            if matches!(self.heap.obj(*o).kind, ObjKind::Promise(_)) {
                let obj = *o;
                let ctor = self.get_prop(&x, &PropKey::from_str("constructor"))?;
                if matches!(&ctor, JsValue::Obj(c) if *c == self.intr.promise_ctor) {
                    return Ok(obj);
                }
                // Foreign constructor: a NEW promise adopting `x` (the reactor's
                // `promise_resolve` would passthrough via `promise_of`, so drive
                // a fresh capability's resolve to assimilate `x` as a thenable).
                let (np, _pid, cap) = self.new_promise_object()?;
                self.rx_op(|it, rx| rx.resolve(it, &cap, x));
                return Ok(np);
            }
        }
        let pid = self.rx_op(|it, rx| rx.promise_resolve(it, x));
        self.wrap_promise(pid)
    }

    /// `promise.then(onFulfilled, onRejected)` at the reactor level, returning
    /// the dependent Promise object. `on_*` are already-callable JS functions.
    fn promise_then_obj(
        &mut self,
        promise_obj: ObjId,
        on_f: Option<JsValue>,
        on_r: Option<JsValue>,
    ) -> Result<ObjId, Abrupt> {
        let ObjKind::Promise(pid) = self.heap.obj(promise_obj).kind else {
            return Err(Abrupt::Fatal("then on a non-promise object".to_string()));
        };
        let fh = on_f.map(JobFn::Call);
        let rh = on_r.map(JobFn::Call);
        let dep = self.rx_op(|it, rx| rx.then(it, pid, fh, rh));
        self.wrap_promise(dep)
    }

    pub(crate) fn make_resolving_fn(&mut self, cap: Capability, reject: bool) -> Result<ObjId, Abrupt> {
        let nf = if reject {
            NativeFn::PromiseRejectFn
        } else {
            NativeFn::PromiseResolveFn
        };
        let f = self.alloc_obj(JsObject::new(
            ObjKind::Function(FnData::Native(nf)),
            Some(self.intr.function_proto),
        ))?;
        self.heap.obj_mut(f).props.insert(
            PropKey::from_str("length"),
            Property::with_attrs(JsValue::Num(1.0), false, false, true),
        );
        self.heap.obj_mut(f).props.insert(
            PropKey::from_str("name"),
            Property::with_attrs(JsValue::str_from(""), false, false, true),
        );
        self.resolve_caps.insert(f, ResolveEntry { cap, reject });
        Ok(f)
    }

    fn make_value_thunk(&mut self, value: JsValue, throw: bool) -> Result<ObjId, Abrupt> {
        let nf = if throw {
            NativeFn::PromiseThrowThunk
        } else {
            NativeFn::PromiseValueThunk
        };
        let f = self.alloc_obj(JsObject::new(
            ObjKind::Function(FnData::Native(nf)),
            Some(self.intr.function_proto),
        ))?;
        self.heap.obj_mut(f).props.insert(
            PropKey::from_str("length"),
            Property::with_attrs(JsValue::Num(0.0), false, false, true),
        );
        self.heap.obj_mut(f).props.insert(
            PropKey::from_str("name"),
            Property::with_attrs(JsValue::str_from(""), false, false, true),
        );
        self.thunk_values.insert(f, (value, throw));
        Ok(f)
    }

    pub(crate) fn build_js_array(&mut self, elements: Vec<JsValue>) -> ERes {
        let arr = self.new_array(0)?;
        #[allow(clippy::cast_precision_loss)]
        let len = elements.len() as f64;
        for (i, v) in elements.into_iter().enumerate() {
            self.heap
                .obj_mut(arr)
                .props
                .insert(PropKey::Str(units_from_str(&i.to_string())), Property::data(v));
        }
        self.set_array_length_raw(arr, len);
        Ok(JsValue::Obj(arr))
    }

    pub(crate) fn build_settled_record(&mut self, fulfilled: bool, v: JsValue) -> ERes {
        let o = self.new_plain()?;
        self.heap.obj_mut(o).props.insert(
            PropKey::from_str("status"),
            Property::data(JsValue::str_from(if fulfilled { "fulfilled" } else { "rejected" })),
        );
        self.heap.obj_mut(o).props.insert(
            PropKey::from_str(if fulfilled { "value" } else { "reason" }),
            Property::data(v),
        );
        Ok(JsValue::Obj(o))
    }

    pub(crate) fn build_agg_error(&mut self, errors: Vec<JsValue>) -> ERes {
        let errs = self.build_js_array(errors)?;
        let proto = self.intr.aggregate_error_proto;
        let oid = self.make_native_error_with_proto(ErrKind::Aggregate, false, proto)?;
        // [[AggregateErrors]] surfaces as the own data prop `errors`
        // {w:true, e:false, c:true}.
        self.heap.obj_mut(oid).props.insert(
            PropKey::from_str("errors"),
            Property::with_attrs(errs, true, false, true),
        );
        Ok(JsValue::Obj(oid))
    }

    // -- helpers ------------------------------------------------------------

    /// Collect an iterable into a Vec via the iterator protocol.
    fn iterate_to_vec(&mut self, iterable: &JsValue) -> Result<Vec<JsValue>, Abrupt> {
        let mut it = self.get_iterator_or_type_error(iterable)?;
        let mut out = Vec::new();
        loop {
            match self.fast_iter_next(&mut it) {
                Ok(Some(v)) => {
                    out.push(v);
                    if out.len() > MAX_COMBINATOR_ELEMS {
                        return Err(Abrupt::Fatal("combinator iterable too large".to_string()));
                    }
                }
                Ok(None) => return Ok(out),
                Err(a) => return Err(a),
            }
        }
    }

    fn is_callable_value(&self, v: &JsValue) -> bool {
        matches!(v, JsValue::Obj(o) if self.heap.obj(*o).is_callable())
    }

    /// Are `%Promise%.resolve` and `%Promise.prototype%.then` the untouched
    /// intrinsics? The combinators observe both, so a replacement means the
    /// reactor fast-path is no longer faithful.
    fn combinator_protocol_intact(&self) -> bool {
        self.own_native_is(self.intr.promise_ctor, "resolve", NativeFn::PromiseResolve)
            && self.own_native_is(self.intr.promise_proto, "then", NativeFn::PromiseProtoThen)
    }

    /// Is `v` an element the reactor combinator coerces faithfully? Primitives,
    /// non-promise objects (values / thenables — assimilated exactly by
    /// `promise_resolve`), and DIRECT `%Promise%` instances with the intrinsic
    /// `then` all are. A subclass promise, or a promise with a shadowing own
    /// `then`, is NOT (spec would `Invoke` a different `then`).
    fn combinator_safe_element(&self, v: &JsValue) -> bool {
        let JsValue::Obj(o) = v else {
            return true;
        };
        if matches!(self.heap.obj(*o).kind, ObjKind::Promise(_)) {
            return self.is_direct_intrinsic_promise(v);
        }
        true
    }

    /// Is `v` a DIRECT `%Promise%` instance — proto `%Promise.prototype%`, no
    /// own `then`, no own `constructor` — so its `then`/`constructor` are the
    /// untouched intrinsics and the reactor fast-path is faithful?
    fn is_direct_intrinsic_promise(&self, v: &JsValue) -> bool {
        let JsValue::Obj(o) = v else {
            return false;
        };
        matches!(self.heap.obj(*o).kind, ObjKind::Promise(_))
            && self.heap.obj(*o).proto == Some(self.intr.promise_proto)
            && !self.heap.obj(*o).props.contains_key(&PropKey::from_str("then"))
            && !self
                .heap
                .obj(*o)
                .props
                .contains_key(&PropKey::from_str("constructor"))
    }

    /// Is `obj`'s own data property `key` the given native function intrinsic?
    fn own_native_is(&self, obj: ObjId, key: &str, want: NativeFn) -> bool {
        match self.heap.obj(obj).props.get(&PropKey::from_str(key)).map(|p| &p.v) {
            Some(PropValue::Data { value: JsValue::Obj(o), .. }) => {
                matches!(self.heap.obj(*o).kind, ObjKind::Function(FnData::Native(nf)) if nf == want)
            }
            _ => false,
        }
    }

    fn callable_handle(&self, v: &JsValue) -> Option<JobFn> {
        if self.is_callable_value(v) {
            Some(JobFn::Call(v.clone()))
        } else {
            None
        }
    }

    /// `this` must be a Promise instance; return its reactor id.
    fn this_promise(&mut self, this: &JsValue) -> Result<PromiseId, Abrupt> {
        if let JsValue::Obj(o) = this {
            if let ObjKind::Promise(pid) = self.heap.obj(*o).kind {
                return Ok(pid);
            }
        }
        Err(self.throw_type_error())
    }

    /// Is `this` the intrinsic `%Promise%` constructor itself (the calibrated
    /// reactor fast-path receiver)?
    fn is_intrinsic_promise_ctor(&self, this: &JsValue) -> bool {
        matches!(this, JsValue::Obj(o) if *o == self.intr.promise_ctor)
    }

    // -- NewPromiseCapability + the general (receiver-C) static lane ---------

    /// A fresh anonymous built-in function of `ObjKind::Function(Native(nf))`
    /// with the standard `length` then `name` own data properties
    /// ({w:false,e:false,c:true}) and no `prototype` — the shape every Promise
    /// executor / resolve-element / reject-element function has.
    fn make_anon_native(&mut self, nf: NativeFn, length: f64) -> Result<ObjId, Abrupt> {
        let f = self.alloc_obj(JsObject::new(
            ObjKind::Function(FnData::Native(nf)),
            Some(self.intr.function_proto),
        ))?;
        self.heap.obj_mut(f).props.insert(
            PropKey::from_str("length"),
            Property::with_attrs(JsValue::Num(length), false, false, true),
        );
        self.heap.obj_mut(f).props.insert(
            PropKey::from_str("name"),
            Property::with_attrs(JsValue::str_from(""), false, false, true),
        );
        Ok(f)
    }

    /// NewPromiseCapability(C) (27.2.1.5): `Construct(C, «executor»)` where the
    /// executor captures the resolve/reject the constructor hands it, then
    /// validate both are callable. `C` must be a constructor (else TypeError).
    fn new_promise_capability(&mut self, c: &JsValue) -> Result<PromiseCap, Abrupt> {
        if !self.is_constructor(c) {
            return Err(self.throw_type_error());
        }
        let rec = Rc::new(RefCell::new(CapRecord {
            resolve: JsValue::Undefined,
            reject: JsValue::Undefined,
        }));
        let exec = self.make_anon_native(NativeFn::PromiseCapExecutor, 2.0)?;
        self.cap_states.insert(exec, rec.clone());
        // `Construct(C, «executor»)` — user code runs here and may throw
        // (propagated) or call the executor (synchronously, filling `rec`).
        let promise = self.construct(c, vec![JsValue::Obj(exec)], None);
        self.cap_states.remove(&exec);
        let promise = promise?;
        let (resolve, reject) = {
            let r = rec.borrow();
            (r.resolve.clone(), r.reject.clone())
        };
        if !self.is_callable_value(&resolve) || !self.is_callable_value(&reject) {
            return Err(self.throw_type_error());
        }
        Ok(PromiseCap { promise, resolve, reject })
    }

    /// GetCapabilitiesExecutor `[[Call]]` (27.2.1.5.1): store resolve/reject into
    /// the shared record, throwing a TypeError if either slot is already set to a
    /// non-`undefined` value.
    fn run_cap_executor(&mut self, fid: ObjId, resolve: JsValue, reject: JsValue) -> ERes {
        let Some(rec) = self.cap_states.get(&fid).cloned() else {
            return Ok(JsValue::Undefined);
        };
        let already = {
            let r = rec.borrow();
            !matches!(r.resolve, JsValue::Undefined) || !matches!(r.reject, JsValue::Undefined)
        };
        if already {
            return Err(self.throw_type_error());
        }
        {
            let mut r = rec.borrow_mut();
            r.resolve = resolve;
            r.reject = reject;
        }
        Ok(JsValue::Undefined)
    }

    /// PromiseResolve(C, x) (27.2.4.7.1) for a non-intrinsic constructor C: pass
    /// an existing promise through only when its `constructor` is C; otherwise
    /// NewPromiseCapability(C) and drive its resolve with `x`.
    fn promise_resolve_general(&mut self, c: &JsValue, x: JsValue) -> ERes {
        if let JsValue::Obj(o) = &x {
            if matches!(self.heap.obj(*o).kind, ObjKind::Promise(_)) {
                let ctor = self.get_prop(&x, &PropKey::from_str("constructor"))?;
                if crate::ops::same_value(&ctor, c) {
                    return Ok(x);
                }
            }
        }
        let cap = self.new_promise_capability(c)?;
        self.call_value(&cap.resolve, JsValue::Undefined, vec![x])?;
        Ok(cap.promise)
    }

    /// GetPromiseResolve(C) (27.2.4.2.1): `Get(C, "resolve")`, which must be
    /// callable.
    fn get_promise_resolve(&mut self, c: &JsValue) -> Result<JsValue, Abrupt> {
        let r = self.get_prop(c, &PropKey::from_str("resolve"))?;
        if !self.is_callable_value(&r) {
            return Err(self.throw_type_error());
        }
        Ok(r)
    }

    /// The faithful all / allSettled / race / any lane for a non-intrinsic
    /// receiver C: NewPromiseCapability(C), GetPromiseResolve(C) (with
    /// IfAbruptRejectPromise), GetIterator, then the per-kind Perform* iteration
    /// (with IteratorClose on a body abrupt). Any refusal inside (Fatal) makes
    /// the whole case NoCoverage — never a wrong trace.
    fn run_combinator_general(&mut self, c: &JsValue, iterable: JsValue, kind: CombKind) -> ERes {
        let cap = self.new_promise_capability(c)?;
        // GetPromiseResolve(C) — IfAbruptRejectPromise on throw.
        let promise_resolve = match self.get_promise_resolve(c) {
            Ok(v) => v,
            Err(Abrupt::Throw(e)) => {
                self.call_value(&cap.reject, JsValue::Undefined, vec![e])?;
                return Ok(cap.promise);
            }
            Err(a) => return Err(a),
        };
        // GetIterator(iterable, sync) — IfAbruptRejectPromise on throw.
        let mut iter = match self.get_iterator_or_type_error(&iterable) {
            Ok(it) => it,
            Err(Abrupt::Throw(e)) => {
                self.call_value(&cap.reject, JsValue::Undefined, vec![e])?;
                return Ok(cap.promise);
            }
            Err(a) => return Err(a),
        };
        let result = if kind == CombKind::Race {
            self.perform_race(c, &mut iter, &cap, &promise_resolve)
        } else {
            self.perform_combinator(c, &mut iter, &cap, &promise_resolve, kind)
        };
        match result {
            Ok(()) => Ok(cap.promise),
            Err(Abrupt::Throw(e)) => {
                // If iteration is not exhausted, IteratorClose (the original throw
                // wins over any close error); then IfAbruptRejectPromise.
                if self.iter_user_not_done(&iter) {
                    let _ = self.iterator_close(&iter, true);
                }
                self.call_value(&cap.reject, JsValue::Undefined, vec![e])?;
                Ok(cap.promise)
            }
            Err(a) => Err(a),
        }
    }

    /// One IteratorStep for a combinator iteration; on an abrupt step the
    /// iterator record is marked done (IteratorStepValue sets `[[Done]]`), so the
    /// caller skips IteratorClose — matching the spec's forward of a step throw.
    fn combinator_step(
        &mut self,
        iter: &mut crate::destr::FastIter,
    ) -> Result<Option<JsValue>, Abrupt> {
        match self.fast_iter_next(iter) {
            Ok(n) => Ok(n),
            Err(a) => {
                if let crate::destr::FastIter::User { done, .. } = iter {
                    *done = true;
                }
                Err(a)
            }
        }
    }

    /// PerformPromiseRace (27.2.4.5.1): each element's `nextPromise.then` wires
    /// the result capability's resolve/reject DIRECTLY (no element functions, no
    /// remaining count). Empty input leaves the result promise forever pending.
    fn perform_race(
        &mut self,
        c: &JsValue,
        iter: &mut crate::destr::FastIter,
        cap: &PromiseCap,
        promise_resolve: &JsValue,
    ) -> Result<(), Abrupt> {
        let mut count = 0usize;
        loop {
            let Some(next_value) = self.combinator_step(iter)? else {
                return Ok(());
            };
            if count >= MAX_COMBINATOR_ELEMS {
                return Err(Abrupt::Fatal("combinator iterable too large".to_string()));
            }
            count += 1;
            let next_promise = self.call_value(promise_resolve, c.clone(), vec![next_value])?;
            let then = self.get_prop(&next_promise, &PropKey::from_str("then"))?;
            self.call_value(
                &then,
                next_promise,
                vec![cap.resolve.clone(), cap.reject.clone()],
            )?;
        }
    }

    /// PerformPromiseAll / AllSettled / Any (27.2.4.{1,2,8}.1): iterate, coerce
    /// each element with `Call(promiseResolve, C, «value»)`, then
    /// `Invoke(nextPromise, "then", «onFulfilled, onRejected»)` with the per-kind
    /// element closures, threading the shared `remainingElementsCount`.
    fn perform_combinator(
        &mut self,
        c: &JsValue,
        iter: &mut crate::destr::FastIter,
        cap: &PromiseCap,
        promise_resolve: &JsValue,
        kind: CombKind,
    ) -> Result<(), Abrupt> {
        let shared = Rc::new(RefCell::new(CombShared {
            kind,
            values: Vec::new(),
            remaining: 1,
            cap_resolve: cap.resolve.clone(),
            cap_reject: cap.reject.clone(),
        }));
        let mut index = 0usize;
        loop {
            let Some(next_value) = self.combinator_step(iter)? else {
                let finished = {
                    let mut s = shared.borrow_mut();
                    s.remaining -= 1;
                    s.remaining == 0
                };
                if finished {
                    self.settle_on_zero(&shared)?;
                }
                return Ok(());
            };
            if index >= MAX_COMBINATOR_ELEMS {
                return Err(Abrupt::Fatal("combinator iterable too large".to_string()));
            }
            shared.borrow_mut().values.push(JsValue::Undefined);
            let next_promise = self.call_value(promise_resolve, c.clone(), vec![next_value])?;
            let (on_f, on_r) = self.build_comb_handlers(kind, index, &shared, cap)?;
            shared.borrow_mut().remaining += 1;
            let then = self.get_prop(&next_promise, &PropKey::from_str("then"))?;
            self.call_value(&then, next_promise, vec![on_f, on_r])?;
            index += 1;
        }
    }

    /// Build the `(onFulfilled, onRejected)` handlers `Invoke(nextPromise,
    /// "then", …)` passes for one element, per combinator kind:
    ///  * all — resolve element + the result cap's reject;
    ///  * allSettled — resolve element + reject element sharing one
    ///    `[[AlreadyCalled]]`;
    ///  * any — the result cap's resolve + reject element.
    fn build_comb_handlers(
        &mut self,
        kind: CombKind,
        index: usize,
        shared: &Rc<RefCell<CombShared>>,
        cap: &PromiseCap,
    ) -> Result<(JsValue, JsValue), Abrupt> {
        match kind {
            CombKind::All => {
                let f = self.make_comb_element(
                    NativeFn::PromiseAllResolveElement,
                    index,
                    false,
                    Rc::new(RefCell::new(false)),
                    shared,
                )?;
                Ok((JsValue::Obj(f), cap.reject.clone()))
            }
            CombKind::AllSettled => {
                let already = Rc::new(RefCell::new(false));
                let f = self.make_comb_element(
                    NativeFn::PromiseAllSettledResolveElement,
                    index,
                    false,
                    already.clone(),
                    shared,
                )?;
                let r = self.make_comb_element(
                    NativeFn::PromiseAllSettledRejectElement,
                    index,
                    true,
                    already,
                    shared,
                )?;
                Ok((JsValue::Obj(f), JsValue::Obj(r)))
            }
            CombKind::Any => {
                let r = self.make_comb_element(
                    NativeFn::PromiseAnyRejectElement,
                    index,
                    true,
                    Rc::new(RefCell::new(false)),
                    shared,
                )?;
                Ok((cap.resolve.clone(), JsValue::Obj(r)))
            }
            CombKind::Race => unreachable!("race uses perform_race"),
        }
    }

    /// Allocate one combinator element function object (anonymous, length 1) and
    /// register its aggregation state.
    fn make_comb_element(
        &mut self,
        nf: NativeFn,
        index: usize,
        is_reject: bool,
        already_called: Rc<RefCell<bool>>,
        shared: &Rc<RefCell<CombShared>>,
    ) -> Result<ObjId, Abrupt> {
        let f = self.make_anon_native(nf, 1.0)?;
        self.comb_elements.insert(
            f,
            CombElement {
                already_called,
                index,
                is_reject,
                shared: shared.clone(),
            },
        );
        Ok(f)
    }

    /// A combinator element function's `[[Call]]` (the all/allSettled resolve
    /// element, allSettled/any reject element): the `[[AlreadyCalled]]` guard,
    /// store the (possibly wrapped) settled value at `[[Index]]`, decrement the
    /// shared remaining count, and — when it reaches 0 — settle the result.
    fn run_comb_element(&mut self, fid: ObjId, x: JsValue) -> ERes {
        let Some(el) = self.comb_elements.get(&fid).cloned() else {
            return Ok(JsValue::Undefined);
        };
        if *el.already_called.borrow() {
            return Ok(JsValue::Undefined);
        }
        *el.already_called.borrow_mut() = true;
        let kind = el.shared.borrow().kind;
        let item = match (kind, el.is_reject) {
            (CombKind::AllSettled, false) => self.build_settled_record(true, x)?,
            (CombKind::AllSettled, true) => self.build_settled_record(false, x)?,
            // all resolve element / any reject element store the raw value.
            _ => x,
        };
        let finished = {
            let mut s = el.shared.borrow_mut();
            s.values[el.index] = item;
            s.remaining -= 1;
            s.remaining == 0
        };
        if finished {
            self.settle_on_zero(&el.shared)?;
        }
        Ok(JsValue::Undefined)
    }

    /// The final settlement once a combinator's remaining count hits zero:
    /// all/allSettled resolve with the ordered array; any rejects with an
    /// AggregateError of the ordered errors. (race never reaches here.)
    fn settle_on_zero(&mut self, shared: &Rc<RefCell<CombShared>>) -> Result<(), Abrupt> {
        let (kind, values, cap_resolve, cap_reject) = {
            let s = shared.borrow();
            (s.kind, s.values.clone(), s.cap_resolve.clone(), s.cap_reject.clone())
        };
        match kind {
            CombKind::All | CombKind::AllSettled => {
                let arr = self.build_js_array(values)?;
                self.call_value(&cap_resolve, JsValue::Undefined, vec![arr])?;
            }
            CombKind::Any => {
                let agg = self.build_agg_error(values)?;
                self.call_value(&cap_reject, JsValue::Undefined, vec![agg])?;
            }
            CombKind::Race => {}
        }
        Ok(())
    }

    /// `then`/`catch`/`finally` model only the default `@@species`
    /// (SpeciesConstructor resolving to `%Promise%`); anything else refuses.
    fn require_default_species(&mut self, this: &JsValue) -> Result<(), Abrupt> {
        let ctor = self.get_prop(this, &PropKey::from_str("constructor"))?;
        // SpeciesConstructor: an UNDEFINED constructor returns the default; any
        // other non-Object constructor (e.g. `null`) throws a TypeError.
        if matches!(ctor, JsValue::Undefined) {
            return Ok(());
        }
        if !matches!(&ctor, JsValue::Obj(_)) {
            return Err(self.throw_type_error());
        }
        let species = self.get_prop(&ctor, &PropKey::Sym(SymId::WellKnown(WkSym::Species)))?;
        if species.is_nullish() {
            return Ok(());
        }
        if matches!(&species, JsValue::Obj(o) if *o == self.intr.promise_ctor) {
            return Ok(());
        }
        if !self.is_constructor(&species) {
            return Err(self.throw_type_error());
        }
        Err(Abrupt::Fatal(
            "Promise subclass @@species (out of slice)".to_string(),
        ))
    }
}
