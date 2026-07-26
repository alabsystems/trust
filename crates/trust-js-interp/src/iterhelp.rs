// Iterator Helper methods (ECMA-262 §27.1.4): the lazy adapters
// map/filter/take/drop/flatMap (each returns an %IteratorHelperPrototype%
// object driven step-by-step) and the eager consumers reduce/toArray/forEach/
// some/every/find (which drive the iterator to completion or short-circuit).
//
// Every method performs GetIteratorDirect(this) — reading `next` off the
// receiver, NEVER calling @@iterator on it — so the underlying iterator is
// always driven through the general iterator protocol (FastIter::User): call
// `next`, read `done`, then `value`, exactly as the spec's IteratorStepValue
// prescribes. The counter argument (0-based), the IteratorClose choreography on
// early exit / callback throw (IfAbruptCloseIterator), and the argument-check
// order (O-is-Object, IsCallable, GetIteratorDirect; take/drop do ToNumber →
// RangeError BEFORE GetIteratorDirect — verified against Node and Bun) all match
// the engines.
//
// A lazy helper is an ordinary object (ObjKind::Iterator) over
// %IteratorHelperPrototype%; its generator-closure state lives in the
// interpreter's `helper_state` side table (removed for the duration of a step,
// so a reentrant next() finds no state and throws the spec's "already executing"
// TypeError). flatMap's .return() while suspended inside an inner iterator closes
// the inner then the outer iterator (§27.1.4.7 step viii.4.b), in that order.
// Everything this file cannot evaluate to an engine-identical trace refuses
// (Abrupt::Fatal → sound NoCoverage, never a wrong trace).
//
// Author: Andrew Yates
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

use crate::destr::FastIter;
use crate::interp::{Abrupt, ERes, Interp};
use trust_js_value::{
    to_integer_or_infinity, units_from_str, ErrKind, JsObject, JsValue, NativeFn, ObjId, ObjKind,
    PropKey, Property, SymId, WkSym,
};

/// Which lazy adapter a helper object drives.
#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) enum HelperKind {
    Map,
    Filter,
    Take,
    Drop,
    FlatMap,
}

/// The generator-closure phase of a helper object (CreateIteratorFromClosure's
/// [[GeneratorState]], minus `executing`, which is modeled by removing the state
/// from the side table for the duration of a step).
#[derive(Clone, Copy, PartialEq, Eq)]
enum Phase {
    /// suspended-start: next() never called.
    Start,
    /// suspended-yield: paused at a Yield.
    Yield,
    /// completed: drained, threw, or was returned — every later next() yields
    /// {undefined, true}.
    Completed,
}

/// The suspension state of one Iterator Helper object.
pub(crate) struct IterHelper {
    kind: HelperKind,
    /// The underlying iterator record from GetIteratorDirect(this): the iterator
    /// object, its captured `next` method, and the [[Done]] flag.
    under_iter: ObjId,
    under_next: JsValue,
    under_done: bool,
    /// The 0-based counter passed to the callback (map/filter/flatMap).
    counter: f64,
    /// The remaining budget for take/drop (may be +∞); unused otherwise.
    remaining: f64,
    /// drop: whether the initial dropping phase has completed.
    dropped: bool,
    /// The mapper/predicate callback (map/filter/flatMap); Undefined otherwise.
    fn_arg: JsValue,
    /// flatMap: the active inner iterator record (iterator, next, done), or None
    /// between inner iterations.
    inner: Option<(ObjId, JsValue, bool)>,
    phase: Phase,
}

/// The short-circuiting search consumers (some/every/find).
#[derive(Clone, Copy)]
enum PredKind {
    Some,
    Every,
    Find,
}

impl Interp {
    // -- dispatch ------------------------------------------------------------

    /// Dispatch for the eleven %Iterator.prototype% helper methods plus the two
    /// %IteratorHelperPrototype% methods (next/return).
    pub(crate) fn dispatch_iter_helper(
        &mut self,
        nf: NativeFn,
        this: JsValue,
        args: Vec<JsValue>,
    ) -> ERes {
        use NativeFn as N;
        match nf {
            N::IteratorProtoMap => self.iter_proto_lazy(HelperKind::Map, &this, &args),
            N::IteratorProtoFilter => self.iter_proto_lazy(HelperKind::Filter, &this, &args),
            N::IteratorProtoFlatMap => self.iter_proto_lazy(HelperKind::FlatMap, &this, &args),
            N::IteratorProtoTake => self.iter_proto_take_drop(HelperKind::Take, &this, &args),
            N::IteratorProtoDrop => self.iter_proto_take_drop(HelperKind::Drop, &this, &args),
            N::IteratorProtoReduce => self.iter_proto_reduce(&this, &args),
            N::IteratorProtoToArray => self.iter_proto_to_array(&this),
            N::IteratorProtoForEach => self.iter_proto_for_each(&this, &args),
            N::IteratorProtoSome => self.iter_proto_predicate(PredKind::Some, &this, &args),
            N::IteratorProtoEvery => self.iter_proto_predicate(PredKind::Every, &this, &args),
            N::IteratorProtoFind => self.iter_proto_predicate(PredKind::Find, &this, &args),
            N::IteratorHelperNext => self.iter_helper_next(&this),
            N::IteratorHelperReturn => self.iter_helper_return(&this),
            _ => Err(Abrupt::Fatal(format!("dispatch_iter_helper: unexpected {nf:?}"))),
        }
    }

    // -- shared primitives ---------------------------------------------------

    fn is_callable_val(&self, v: &JsValue) -> bool {
        matches!(v, JsValue::Obj(o) if self.heap.obj(*o).is_callable())
    }

    /// GetIteratorDirect(O): read `next` off the receiver (NO @@iterator call).
    fn get_iterator_direct(&mut self, o: ObjId) -> ERes {
        self.get_from_object(o, &PropKey::from_str("next"), JsValue::Obj(o))
    }

    /// IteratorStepValue over a direct iterator record: IteratorStep (call
    /// `next`, require an Object result, read `done`) then IteratorValue (read
    /// `value`). Any abrupt marks the record [[Done]] (matching the spec, so no
    /// IteratorClose follows). `Ok(None)` = the iterator is exhausted.
    fn direct_step_value(
        &mut self,
        iter: ObjId,
        next: &JsValue,
        done: &mut bool,
    ) -> Result<Option<JsValue>, Abrupt> {
        let mut fi = FastIter::User {
            iter,
            next: next.clone(),
            done: *done,
        };
        let r = self.iter_step_marking_done(&mut fi);
        if let FastIter::User { done: d, .. } = &fi {
            *done = *d;
        }
        r
    }

    fn under_record(h: &IterHelper) -> FastIter {
        FastIter::User {
            iter: h.under_iter,
            next: h.under_next.clone(),
            done: h.under_done,
        }
    }

    /// Argument validation failing after the O-is-Object check closes the
    /// underlying iterator (§27.1.4: the methods build an Iterator Record
    /// {[[Iterator]]: O, [[NextMethod]]: undefined} BEFORE validating `mapper` /
    /// `limit`, then IfAbruptCloseIterator / IteratorClose on failure — verified
    /// against Node and Bun, which call `return` yet never read `next`).
    /// IteratorClose with the throw swallows any `return` error; the original
    /// completion (the TypeError / RangeError / coercion throw) propagates.
    fn close_on_arg_failure(&mut self, o: ObjId, err: Abrupt) -> Abrupt {
        let fi = FastIter::User {
            iter: o,
            next: JsValue::Undefined,
            done: false,
        };
        self.close_after_body_abrupt(&fi, err)
    }

    fn make_iter_helper(
        &mut self,
        kind: HelperKind,
        under_iter: ObjId,
        under_next: JsValue,
        fn_arg: JsValue,
        remaining: f64,
    ) -> ERes {
        let proto = self.intr.iterator_helper_proto;
        let oid = self.alloc_obj(JsObject::new(ObjKind::Iterator, Some(proto)))?;
        self.helper_state.insert(
            oid,
            IterHelper {
                kind,
                under_iter,
                under_next,
                under_done: false,
                counter: 0.0,
                remaining,
                dropped: false,
                fn_arg,
                inner: None,
                phase: Phase::Start,
            },
        );
        Ok(JsValue::Obj(oid))
    }

    // -- lazy adapters (constructors) ----------------------------------------

    /// map / filter / flatMap: O-is-Object, then IsCallable(fn) (closing the
    /// underlying on failure), GetIteratorDirect, then build the helper.
    fn iter_proto_lazy(&mut self, kind: HelperKind, this: &JsValue, args: &[JsValue]) -> ERes {
        let JsValue::Obj(o) = this else {
            return Err(self.throw_type_error());
        };
        let o = *o;
        let fn_arg = args.first().cloned().unwrap_or(JsValue::Undefined);
        if !self.is_callable_val(&fn_arg) {
            let err = self.throw_type_error();
            return Err(self.close_on_arg_failure(o, err));
        }
        let next = self.get_iterator_direct(o)?;
        self.make_iter_helper(kind, o, next, fn_arg, 0.0)
    }

    /// take / drop: O-is-Object, then ToNumber(limit) → RangeError on NaN /
    /// negative — each failure (a throwing coercion, NaN, or a negative limit)
    /// closes the underlying iterator BEFORE reading `next`; only on success does
    /// GetIteratorDirect read `next` (the coercion precedes the `next` read —
    /// verified against Node and Bun).
    fn iter_proto_take_drop(&mut self, kind: HelperKind, this: &JsValue, args: &[JsValue]) -> ERes {
        let JsValue::Obj(o) = this else {
            return Err(self.throw_type_error());
        };
        let o = *o;
        let limit = args.first().cloned().unwrap_or(JsValue::Undefined);
        let num = match self.to_number(&limit) {
            Ok(n) => n,
            Err(a) => return Err(self.close_on_arg_failure(o, a)),
        };
        if num.is_nan() {
            let err = self.throw_native(ErrKind::Range);
            return Err(self.close_on_arg_failure(o, err));
        }
        let int_limit = to_integer_or_infinity(num);
        if int_limit < 0.0 {
            let err = self.throw_native(ErrKind::Range);
            return Err(self.close_on_arg_failure(o, err));
        }
        let next = self.get_iterator_direct(o)?;
        self.make_iter_helper(kind, o, next, JsValue::Undefined, int_limit)
    }

    // -- helper next / return ------------------------------------------------

    /// %IteratorHelperPrototype%.next: GeneratorResume over the captured closure.
    pub(crate) fn iter_helper_next(&mut self, this: &JsValue) -> ERes {
        let JsValue::Obj(oid) = this else {
            return Err(self.throw_type_error());
        };
        let oid = *oid;
        if !matches!(self.heap.obj(oid).kind, ObjKind::Iterator) {
            return Err(self.throw_type_error());
        }
        // Absent ⇒ not a helper, OR reentrant (state removed while executing):
        // the spec's "generator is already executing" TypeError, and the brand
        // check, both fall out of this.
        let Some(mut h) = self.helper_state.remove(&oid) else {
            return Err(self.throw_type_error());
        };
        if matches!(h.phase, Phase::Completed) {
            self.helper_state.insert(oid, h);
            return self.create_iter_result(JsValue::Undefined, true);
        }
        let result = self.helper_step(&mut h);
        match &result {
            Ok(_) => {
                if !matches!(h.phase, Phase::Completed) {
                    h.phase = Phase::Yield;
                }
            }
            // A throw completes the generator (subsequent next() ⇒ done). A Fatal
            // refusal fails the whole case, so its phase is irrelevant.
            Err(Abrupt::Throw(_)) => h.phase = Phase::Completed,
            _ => {}
        }
        self.helper_state.insert(oid, h);
        result
    }

    /// %IteratorHelperPrototype%.return: close the underlying iterator and
    /// complete with {undefined, true}.
    pub(crate) fn iter_helper_return(&mut self, this: &JsValue) -> ERes {
        let JsValue::Obj(oid) = this else {
            return Err(self.throw_type_error());
        };
        let oid = *oid;
        if !matches!(self.heap.obj(oid).kind, ObjKind::Iterator) {
            return Err(self.throw_type_error());
        }
        let Some(mut h) = self.helper_state.remove(&oid) else {
            return Err(self.throw_type_error());
        };
        if matches!(h.phase, Phase::Completed) {
            self.helper_state.insert(oid, h);
            return self.create_iter_result(JsValue::Undefined, true);
        }
        h.phase = Phase::Completed;
        // flatMap suspended inside an inner iterator (§27.1.4.7 step viii.4.b):
        // IteratorClose(inner) THEN IteratorClose(outer) — both closed, inner
        // first (verified against Node and Bun). A `return` throw from the inner
        // still closes the outer (swallowed) and propagates the inner throw.
        let result = if let (HelperKind::FlatMap, Some((in_iter, in_next, in_done))) =
            (h.kind, h.inner.take())
        {
            let inner_fi = FastIter::User {
                iter: in_iter,
                next: in_next,
                done: in_done,
            };
            let outer_fi = Self::under_record(&h);
            match self.iterator_close(&inner_fi, false) {
                Ok(()) => self.iterator_close(&outer_fi, false),
                Err(inner_err) => Err(self.close_after_body_abrupt(&outer_fi, inner_err)),
            }
        } else {
            // map/filter/take/drop (any phase) and flatMap at suspended-start:
            // IteratorClose(the single underlying iterator).
            let fi = Self::under_record(&h);
            self.iterator_close(&fi, false)
        };
        self.helper_state.insert(oid, h);
        result?;
        self.create_iter_result(JsValue::Undefined, true)
    }

    /// Run the captured closure for one next() step, producing the
    /// iterator-result object. Sets `h.phase = Completed` on the normal
    /// exhaustion / take-limit paths; a throw is completed by the caller.
    fn helper_step(&mut self, h: &mut IterHelper) -> ERes {
        match h.kind {
            HelperKind::Map => {
                let v = match self.direct_step_value(h.under_iter, &h.under_next, &mut h.under_done)?
                {
                    None => {
                        h.phase = Phase::Completed;
                        return self.create_iter_result(JsValue::Undefined, true);
                    }
                    Some(v) => v,
                };
                let mapped =
                    self.call_value(&h.fn_arg, JsValue::Undefined, vec![v, JsValue::Num(h.counter)]);
                let mapped = match mapped {
                    Ok(m) => m,
                    Err(a) => {
                        let fi = Self::under_record(h);
                        return Err(self.close_after_body_abrupt(&fi, a));
                    }
                };
                h.counter += 1.0;
                self.create_iter_result(mapped, false)
            }
            HelperKind::Filter => loop {
                self.charge_loop()?;
                let v = match self.direct_step_value(h.under_iter, &h.under_next, &mut h.under_done)?
                {
                    None => {
                        h.phase = Phase::Completed;
                        return self.create_iter_result(JsValue::Undefined, true);
                    }
                    Some(v) => v,
                };
                let selected = self.call_value(
                    &h.fn_arg,
                    JsValue::Undefined,
                    vec![v.clone(), JsValue::Num(h.counter)],
                );
                let selected = match selected {
                    Ok(s) => s,
                    Err(a) => {
                        let fi = Self::under_record(h);
                        return Err(self.close_after_body_abrupt(&fi, a));
                    }
                };
                h.counter += 1.0;
                if self.to_boolean(&selected) {
                    return self.create_iter_result(v, false);
                }
            },
            HelperKind::Take => {
                if h.remaining == 0.0 {
                    h.phase = Phase::Completed;
                    let fi = Self::under_record(h);
                    self.iterator_close(&fi, false)?;
                    return self.create_iter_result(JsValue::Undefined, true);
                }
                if h.remaining.is_finite() {
                    h.remaining -= 1.0;
                }
                match self.direct_step_value(h.under_iter, &h.under_next, &mut h.under_done)? {
                    None => {
                        h.phase = Phase::Completed;
                        self.create_iter_result(JsValue::Undefined, true)
                    }
                    Some(v) => self.create_iter_result(v, false),
                }
            }
            HelperKind::Drop => {
                if !h.dropped {
                    while h.remaining > 0.0 {
                        self.charge_loop()?;
                        if h.remaining.is_finite() {
                            h.remaining -= 1.0;
                        }
                        if self
                            .direct_step_value(h.under_iter, &h.under_next, &mut h.under_done)?
                            .is_none()
                        {
                            h.phase = Phase::Completed;
                            return self.create_iter_result(JsValue::Undefined, true);
                        }
                    }
                    h.dropped = true;
                }
                match self.direct_step_value(h.under_iter, &h.under_next, &mut h.under_done)? {
                    None => {
                        h.phase = Phase::Completed;
                        self.create_iter_result(JsValue::Undefined, true)
                    }
                    Some(v) => self.create_iter_result(v, false),
                }
            }
            HelperKind::FlatMap => self.flat_map_step(h),
        }
    }

    /// flatMap's closure: yield every value of the inner iterator obtained from
    /// mapping each outer value, in order; the counter increments once each
    /// inner iterator is exhausted (§27.1.4.7 step ix).
    fn flat_map_step(&mut self, h: &mut IterHelper) -> ERes {
        loop {
            self.charge_loop()?;
            if let Some((in_iter, in_next, mut in_done)) = h.inner.take() {
                match self.direct_step_value(in_iter, &in_next, &mut in_done) {
                    Ok(Some(v)) => {
                        h.inner = Some((in_iter, in_next, in_done));
                        return self.create_iter_result(v, false);
                    }
                    Ok(None) => {
                        // Inner exhausted: advance the counter, resume the outer.
                        h.counter += 1.0;
                    }
                    Err(a) => {
                        // IteratorStepValue(inner) abrupt ⇒ close the OUTER.
                        let fi = Self::under_record(h);
                        return Err(self.close_after_body_abrupt(&fi, a));
                    }
                }
            } else {
                let value =
                    match self.direct_step_value(h.under_iter, &h.under_next, &mut h.under_done)? {
                        None => {
                            h.phase = Phase::Completed;
                            return self.create_iter_result(JsValue::Undefined, true);
                        }
                        Some(v) => v,
                    };
                let mapped = self.call_value(
                    &h.fn_arg,
                    JsValue::Undefined,
                    vec![value, JsValue::Num(h.counter)],
                );
                let mapped = match mapped {
                    Ok(m) => m,
                    Err(a) => {
                        let fi = Self::under_record(h);
                        return Err(self.close_after_body_abrupt(&fi, a));
                    }
                };
                match self.get_iterator_flattenable_reject(&mapped) {
                    Ok(rec) => h.inner = Some(rec),
                    Err(a) => {
                        let fi = Self::under_record(h);
                        return Err(self.close_after_body_abrupt(&fi, a));
                    }
                }
            }
        }
    }

    /// GetIteratorFlattenable(obj, reject-primitives): a non-Object mapped value
    /// (including a primitive string) throws TypeError; an Object with no
    /// @@iterator is treated as already an iterator; otherwise @@iterator yields
    /// the inner iterator. Returns the inner iterator record (iterator, next).
    fn get_iterator_flattenable_reject(
        &mut self,
        mapped: &JsValue,
    ) -> Result<(ObjId, JsValue, bool), Abrupt> {
        let JsValue::Obj(o) = mapped else {
            return Err(self.throw_type_error());
        };
        let o = *o;
        let key = PropKey::Sym(SymId::WellKnown(WkSym::Iterator));
        let method = self.get_method(mapped, &key)?;
        let iterator = match method {
            None => o,
            Some(m) => {
                let it = self.call_value(&m, mapped.clone(), vec![])?;
                let JsValue::Obj(io) = it else {
                    return Err(self.throw_type_error());
                };
                io
            }
        };
        let next = self.get_from_object(iterator, &PropKey::from_str("next"), JsValue::Obj(iterator))?;
        Ok((iterator, next, false))
    }

    // -- eager consumers -----------------------------------------------------

    /// reduce(reducer [, initialValue]).
    fn iter_proto_reduce(&mut self, this: &JsValue, args: &[JsValue]) -> ERes {
        let JsValue::Obj(o) = this else {
            return Err(self.throw_type_error());
        };
        let o = *o;
        let reducer = args.first().cloned().unwrap_or(JsValue::Undefined);
        if !self.is_callable_val(&reducer) {
            let err = self.throw_type_error();
            return Err(self.close_on_arg_failure(o, err));
        }
        let next = self.get_iterator_direct(o)?;
        let mut done = false;
        let (mut acc, mut counter) = if args.len() > 1 {
            (args[1].clone(), 0.0f64)
        } else {
            match self.direct_step_value(o, &next, &mut done)? {
                // reduce of an empty iterator with no initial value is a TypeError.
                None => return Err(self.throw_type_error()),
                Some(v) => (v, 1.0f64),
            }
        };
        loop {
            self.charge_loop()?;
            let value = match self.direct_step_value(o, &next, &mut done)? {
                None => return Ok(acc),
                Some(v) => v,
            };
            let result = self.call_value(
                &reducer,
                JsValue::Undefined,
                vec![acc.clone(), value, JsValue::Num(counter)],
            );
            acc = match result {
                Ok(r) => r,
                Err(a) => {
                    let fi = FastIter::User {
                        iter: o,
                        next: next.clone(),
                        done,
                    };
                    return Err(self.close_after_body_abrupt(&fi, a));
                }
            };
            counter += 1.0;
        }
    }

    /// toArray().
    fn iter_proto_to_array(&mut self, this: &JsValue) -> ERes {
        let JsValue::Obj(o) = this else {
            return Err(self.throw_type_error());
        };
        let o = *o;
        let next = self.get_iterator_direct(o)?;
        let mut done = false;
        let arr = self.new_array(0)?;
        let mut n: u32 = 0;
        loop {
            self.charge_loop()?;
            let value = match self.direct_step_value(o, &next, &mut done)? {
                None => break,
                Some(v) => v,
            };
            self.heap
                .obj_mut(arr)
                .props
                .insert(PropKey::Str(units_from_str(&n.to_string())), Property::data(value));
            n = n
                .checked_add(1)
                .ok_or_else(|| Abrupt::Fatal("Iterator.prototype.toArray length overflow".to_string()))?;
        }
        self.set_array_length_raw(arr, f64::from(n));
        Ok(JsValue::Obj(arr))
    }

    /// forEach(fn).
    fn iter_proto_for_each(&mut self, this: &JsValue, args: &[JsValue]) -> ERes {
        let JsValue::Obj(o) = this else {
            return Err(self.throw_type_error());
        };
        let o = *o;
        let f = args.first().cloned().unwrap_or(JsValue::Undefined);
        if !self.is_callable_val(&f) {
            let err = self.throw_type_error();
            return Err(self.close_on_arg_failure(o, err));
        }
        let next = self.get_iterator_direct(o)?;
        let mut done = false;
        let mut counter = 0.0f64;
        loop {
            self.charge_loop()?;
            let value = match self.direct_step_value(o, &next, &mut done)? {
                None => return Ok(JsValue::Undefined),
                Some(v) => v,
            };
            let result =
                self.call_value(&f, JsValue::Undefined, vec![value, JsValue::Num(counter)]);
            if let Err(a) = result {
                let fi = FastIter::User {
                    iter: o,
                    next: next.clone(),
                    done,
                };
                return Err(self.close_after_body_abrupt(&fi, a));
            }
            counter += 1.0;
        }
    }

    /// some(fn) / every(fn) / find(fn): drive until the predicate short-circuits,
    /// then IteratorClose(iterated, NormalCompletion(result)).
    fn iter_proto_predicate(&mut self, kind: PredKind, this: &JsValue, args: &[JsValue]) -> ERes {
        let JsValue::Obj(o) = this else {
            return Err(self.throw_type_error());
        };
        let o = *o;
        let pred = args.first().cloned().unwrap_or(JsValue::Undefined);
        if !self.is_callable_val(&pred) {
            let err = self.throw_type_error();
            return Err(self.close_on_arg_failure(o, err));
        }
        let next = self.get_iterator_direct(o)?;
        let mut done = false;
        let mut counter = 0.0f64;
        loop {
            self.charge_loop()?;
            let value = match self.direct_step_value(o, &next, &mut done)? {
                None => {
                    return Ok(match kind {
                        PredKind::Some => JsValue::Bool(false),
                        PredKind::Every => JsValue::Bool(true),
                        PredKind::Find => JsValue::Undefined,
                    });
                }
                Some(v) => v,
            };
            let result = self.call_value(
                &pred,
                JsValue::Undefined,
                vec![value.clone(), JsValue::Num(counter)],
            );
            let result = match result {
                Ok(r) => r,
                Err(a) => {
                    let fi = FastIter::User {
                        iter: o,
                        next: next.clone(),
                        done,
                    };
                    return Err(self.close_after_body_abrupt(&fi, a));
                }
            };
            let b = self.to_boolean(&result);
            let short = match kind {
                PredKind::Some | PredKind::Find => b,
                PredKind::Every => !b,
            };
            if short {
                let ret = match kind {
                    PredKind::Some => JsValue::Bool(true),
                    PredKind::Every => JsValue::Bool(false),
                    PredKind::Find => value,
                };
                let fi = FastIter::User {
                    iter: o,
                    next: next.clone(),
                    done,
                };
                self.iterator_close(&fi, false)?;
                return Ok(ret);
            }
            counter += 1.0;
        }
    }
}
