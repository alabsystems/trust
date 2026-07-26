// Destructuring (binding and assignment patterns, defaults, rest) and the
// internal iteration fast paths. Iteration is modeled ONLY where the
// iterator protocol provably resolves to the untampered intrinsic
// array/string iterators (pristine prototype link AND no own @@iterator —
// user symbols can express own overrides now); non-iterables throw the
// exact TypeError; user-defined iterators refuse.
//
// Author: Andrew Yates
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

use crate::interp::{Abrupt, Ctx, Interp};
use std::rc::Rc;
use trust_js_parse::ast::{Expr, Pat};
use trust_js_value::{
    to_length_u64, units_from_str, EnvId, JsValue, ObjKind, PropKey, PropValue, Property, SymId,
    Units, WkSym,
};

/// An internal fast iterator (array-values semantics / string code points /
/// live Map-entries / live Set-values), or a general USER iterator driven
/// through the spec iterator protocol (GetIterator/IteratorStep/
/// IteratorValue/IteratorClose).
pub(crate) enum FastIter {
    Arr { oid: trust_js_value::ObjId, i: u64, done: bool },
    Str { units: Rc<Units>, i: usize },
    /// %MapIteratorPrototype% entries semantics over the live [[MapData]]
    /// (tombstones skipped, appended entries visited).
    MapIter { oid: trust_js_value::ObjId, i: usize },
    /// %SetIteratorPrototype% values semantics over the live [[SetData]].
    SetIter { oid: trust_js_value::ObjId, i: usize },
    /// %TypedArray%.prototype.values semantics: a buffer-witness re-read each
    /// step (a detached/out-of-bounds source throws TypeError mid-iteration).
    TypedArrayIter { oid: trust_js_value::ObjId, i: usize },
    /// A user-defined iterator: the iterator object and its `next` method
    /// (captured at GetIterator time), driven step-by-step. `done` records
    /// IteratorComplete so IteratorClose is only issued while still open.
    User { iter: trust_js_value::ObjId, next: JsValue, done: bool },
}

impl Interp {
    /// GetIterator, restricted to receivers whose @@iterator provably
    /// resolves to the untampered intrinsic (arrays with the pristine
    /// prototype link, arguments objects still carrying the intrinsic values
    /// function, string primitives).
    pub(crate) fn get_fast_iterator(&mut self, v: &JsValue) -> Result<FastIter, Abrupt> {
        match v {
            // Pristine string: fast path only while String.prototype[@@iterator]
            // AND %StringIteratorPrototype%.next are still the intrinsics (a
            // tampered override of either falls to the general user protocol,
            // which reads and drives the replacement).
            JsValue::Str(s)
                if self.proto_iter_is(self.intr.string_proto, self.intr.string_iterator_fn)
                    && self.proto_next_is(
                        self.intr.string_iterator_proto,
                        self.intr.string_iterator_next_fn,
                    ) =>
            {
                Ok(FastIter::Str {
                    units: Rc::clone(s),
                    i: 0,
                })
            }
            JsValue::Obj(oid) => {
                let obj = self.heap.obj(*oid);
                let iter_key = PropKey::Sym(SymId::WellKnown(WkSym::Iterator));
                match &obj.kind {
                    // Pristine-proto arrays WITHOUT an own @@iterator, while
                    // Array.prototype[@@iterator] AND %ArrayIteratorPrototype%.next
                    // are still the intrinsics (a tampered override of either
                    // falls to the user protocol, which drives the replacement).
                    ObjKind::Array
                        if obj.proto == Some(self.intr.array_proto)
                            && !obj.props.contains_key(&iter_key)
                            && self.proto_iter_is(self.intr.array_proto, self.intr.array_values_fn)
                            && self.proto_next_is(
                                self.intr.array_iterator_proto,
                                self.intr.array_iterator_next_fn,
                            ) =>
                    {
                        Ok(FastIter::Arr {
                            oid: *oid,
                            i: 0,
                            done: false,
                        })
                    }
                    ObjKind::Arguments(_) => {
                        let it_key = PropKey::Sym(SymId::WellKnown(WkSym::Iterator));
                        let ok = matches!(
                            obj.props.get(&it_key),
                            Some(Property {
                                v: PropValue::Data { value: JsValue::Obj(f), .. },
                                ..
                            }) if *f == self.intr.array_values_fn
                        ) && self.proto_next_is(
                            self.intr.array_iterator_proto,
                            self.intr.array_iterator_next_fn,
                        );
                        if ok {
                            Ok(FastIter::Arr {
                                oid: *oid,
                                i: 0,
                                done: false,
                            })
                        } else {
                            Err(Abrupt::Fatal(
                                "iteration of arguments with replaced @@iterator (out of slice)"
                                    .to_string(),
                            ))
                        }
                    }
                    // Pristine Map/Set instances: provably-untampered
                    // @@iterator (no own override; the prototype slot still
                    // holds the intrinsic entries/values identity).
                    ObjKind::MapObj(_)
                        if obj.proto == Some(self.intr.map_proto)
                            && !obj.props.contains_key(&iter_key)
                            && self.proto_iter_is(self.intr.map_proto, self.intr.map_entries_fn)
                            && self.proto_next_is(
                                self.intr.map_iterator_proto,
                                self.intr.map_iterator_next_fn,
                            ) =>
                    {
                        Ok(FastIter::MapIter { oid: *oid, i: 0 })
                    }
                    ObjKind::SetObj(_)
                        if obj.proto == Some(self.intr.set_proto)
                            && !obj.props.contains_key(&iter_key)
                            && self.proto_iter_is(self.intr.set_proto, self.intr.set_values_fn)
                            && self.proto_next_is(
                                self.intr.set_iterator_proto,
                                self.intr.set_iterator_next_fn,
                            ) =>
                    {
                        Ok(FastIter::SetIter { oid: *oid, i: 0 })
                    }
                    // Pristine typed array: no own @@iterator, and its concrete
                    // prototype's @@iterator is still the intrinsic
                    // %TypedArray%.prototype.values.
                    // Typed-array iterators share %ArrayIteratorPrototype%, so
                    // its `next` must also still be the intrinsic.
                    ObjKind::TypedArray(_)
                        if !obj.props.contains_key(&iter_key)
                            && obj.proto.is_some_and(|p| {
                                self.intr.ta_elem_by_proto(p).is_some()
                                    && self.proto_iter_is(
                                        self.intr.typed_array_proto,
                                        self.intr.ta_values_fn,
                                    )
                            })
                            && self.proto_next_is(
                                self.intr.array_iterator_proto,
                                self.intr.array_iterator_next_fn,
                            ) =>
                    {
                        Ok(FastIter::TypedArrayIter { oid: *oid, i: 0 })
                    }
                    _ => Err(Abrupt::Fatal(
                        "iteration of a non-array/non-string value (iterator protocol out of slice)"
                            .to_string(),
                    )),
                }
            }
            _ => Err(Abrupt::Fatal(
                "iteration of a non-iterable primitive (out of slice)".to_string(),
            )),
        }
    }

    /// Does `proto`'s @@iterator slot still hold the given intrinsic
    /// function identity (data property, untampered)?
    fn proto_iter_is(&self, proto: trust_js_value::ObjId, f: trust_js_value::ObjId) -> bool {
        self.proto_slot_is(proto, &PropKey::Sym(SymId::WellKnown(WkSym::Iterator)), f)
    }

    /// Does `proto`'s `next` slot still hold the given intrinsic function
    /// identity? A patched %ArrayIteratorPrototype%.next (etc.) — even under a
    /// pristine @@iterator — makes the fast path unsound: the spec drives the
    /// iterator object's (patched) `next`, so we must fall to the general
    /// protocol, which does exactly that.
    fn proto_next_is(&self, proto: trust_js_value::ObjId, f: trust_js_value::ObjId) -> bool {
        self.proto_slot_is(proto, &PropKey::from_str("next"), f)
    }

    /// Does `proto`'s own `key` slot still hold the given intrinsic function
    /// identity as an untampered data property?
    fn proto_slot_is(&self, proto: trust_js_value::ObjId, key: &PropKey, f: trust_js_value::ObjId) -> bool {
        matches!(
            self.heap.obj(proto).props.get(key),
            Some(Property {
                v: PropValue::Data { value: JsValue::Obj(g), .. },
                ..
            }) if *g == f
        )
    }

    /// GetIterator (7.4.4, sync) for spec contexts that THROW TypeError on
    /// non-iterables: a provably-untampered fast iterator where one applies,
    /// otherwise the general protocol — call @@iterator, validate the result
    /// is an Object, capture its `next` method. `Err(Throw)` = the exact
    /// TypeError (no @@iterator anywhere on a fully-modeled chain, or a
    /// non-object iterator); `Err(Fatal)` = out-of-slice (danger hops).
    pub(crate) fn get_iterator_or_type_error(&mut self, v: &JsValue) -> Result<FastIter, Abrupt> {
        if let Ok(it) = self.get_fast_iterator(v) {
            return Ok(it);
        }
        if v.is_nullish() {
            return Err(self.throw_type_error());
        }
        let key = PropKey::Sym(SymId::WellKnown(WkSym::Iterator));
        // Danger hops refuse inside; a modeled hit drives the user protocol.
        match self.get_method(v, &key)? {
            None => Err(self.throw_type_error()),
            Some(method) => {
                let iterator = self.call_value(&method, v.clone(), vec![])?;
                let JsValue::Obj(io) = iterator else {
                    return Err(self.throw_type_error());
                };
                let next = self.get_from_object(io, &PropKey::from_str("next"), iterator.clone())?;
                Ok(FastIter::User {
                    iter: io,
                    next,
                    done: false,
                })
            }
        }
    }

    /// IteratorClose (7.4.11) for the abrupt/early-exit completion of an
    /// iteration. Only USER iterators can carry an observable `return`; fast
    /// iterators are intrinsic and closing them is a no-op. `pending_throw`
    /// suppresses any error from `return` (the original throw wins).
    pub(crate) fn iterator_close(
        &mut self,
        it: &FastIter,
        pending_throw: bool,
    ) -> Result<(), Abrupt> {
        let FastIter::User { iter, .. } = it else {
            return Ok(());
        };
        let iter_val = JsValue::Obj(*iter);
        let ret = self.get_method(&iter_val, &PropKey::from_str("return"));
        match ret {
            Ok(None) => Ok(()),
            Ok(Some(f)) => {
                let called = self.call_value(&f, iter_val, vec![]);
                if pending_throw {
                    Ok(()) // swallow: the original throw is preserved
                } else {
                    match called {
                        Ok(r) => {
                            if r.is_object() {
                                Ok(())
                            } else {
                                Err(self.throw_type_error())
                            }
                        }
                        Err(a) => Err(a),
                    }
                }
            }
            Err(a) => {
                if pending_throw {
                    Ok(())
                } else {
                    Err(a)
                }
            }
        }
    }

    /// After a loop/pattern BODY completes abruptly (never the iterator step
    /// itself), run IteratorClose and return the completion to propagate.
    pub(crate) fn close_after_body_abrupt(&mut self, it: &FastIter, a: Abrupt) -> Abrupt {
        if matches!(a, Abrupt::Fatal(_)) {
            return a; // refusal: no trace, no observable close
        }
        let pending = matches!(a, Abrupt::Throw(_));
        match self.iterator_close(it, pending) {
            Ok(()) => a,
            Err(close_err) => {
                if pending {
                    a
                } else {
                    close_err
                }
            }
        }
    }

    /// Is this a user iterator still open (IteratorClose applies at an early
    /// exit)? Fast iterators never need closing.
    pub(crate) fn iter_user_not_done(&self, it: &FastIter) -> bool {
        matches!(it, FastIter::User { done: false, .. })
    }

    /// One IteratorStep+Value (array-values semantics re-reads length each
    /// step; string iteration is by code points).
    pub(crate) fn fast_iter_next(&mut self, it: &mut FastIter) -> Result<Option<JsValue>, Abrupt> {
        match it {
            FastIter::Arr { oid, i, done } => {
                if *done {
                    return Ok(None);
                }
                let len_v =
                    self.get_from_object(*oid, &PropKey::from_str("length"), JsValue::Obj(*oid))?;
                let len = to_length_u64(self.to_number(&len_v)?);
                if *i >= len {
                    *done = true;
                    return Ok(None);
                }
                let key = PropKey::Str(units_from_str(&i.to_string()));
                let v = self.get_from_object(*oid, &key, JsValue::Obj(*oid))?;
                *i += 1;
                Ok(Some(v))
            }
            FastIter::MapIter { oid, i } => {
                loop {
                    let entry = {
                        let ObjKind::MapObj(d) = &self.heap.obj(*oid).kind else {
                            return Err(Abrupt::Fatal(
                                "map iterator over a non-map (interpreter bug)".to_string(),
                            ));
                        };
                        if *i >= d.entries.len() {
                            return Ok(None);
                        }
                        d.entries[*i].clone()
                    };
                    *i += 1;
                    if let Some((k, v)) = entry {
                        // CreateArrayFromList(«key, value»): a fresh pair.
                        let arr = self.new_array(2)?;
                        self.heap.obj_mut(arr).props.insert(
                            PropKey::Str(units_from_str("0")),
                            Property::data(k),
                        );
                        self.heap.obj_mut(arr).props.insert(
                            PropKey::Str(units_from_str("1")),
                            Property::data(v),
                        );
                        // new_array pre-set length; reinsert to keep spec
                        // own-key order (indices sort first anyway).
                        return Ok(Some(JsValue::Obj(arr)));
                    }
                    self.charge_loop()?;
                }
            }
            FastIter::SetIter { oid, i } => {
                loop {
                    let entry = {
                        let ObjKind::SetObj(d) = &self.heap.obj(*oid).kind else {
                            return Err(Abrupt::Fatal(
                                "set iterator over a non-set (interpreter bug)".to_string(),
                            ));
                        };
                        if *i >= d.entries.len() {
                            return Ok(None);
                        }
                        d.entries[*i].clone()
                    };
                    *i += 1;
                    if let Some(v) = entry {
                        return Ok(Some(v));
                    }
                    self.charge_loop()?;
                }
            }
            FastIter::TypedArrayIter { oid, i } => {
                let oid = *oid;
                if self.ta_out_of_bounds(oid) {
                    return Err(self.throw_type_error());
                }
                let len = self.ta_current_length(oid);
                if *i >= len {
                    return Ok(None);
                }
                #[allow(clippy::cast_precision_loss)]
                let v = self.ta_element_get_pure(oid, *i as f64);
                *i += 1;
                Ok(Some(v))
            }
            FastIter::User { iter, next, done } => {
                if *done {
                    return Ok(None);
                }
                // IteratorStep = IteratorNext + IteratorComplete.
                let result = self.call_value(next, JsValue::Obj(*iter), vec![])?;
                let JsValue::Obj(ro) = result else {
                    return Err(self.throw_type_error());
                };
                // IteratorComplete reads `done` BEFORE IteratorValue reads
                // `value` (both are observable Gets).
                let done_v =
                    self.get_from_object(ro, &PropKey::from_str("done"), result.clone())?;
                if self.to_boolean(&done_v) {
                    *done = true;
                    return Ok(None);
                }
                let value = self.get_from_object(ro, &PropKey::from_str("value"), result)?;
                Ok(Some(value))
            }
            FastIter::Str { units, i } => {
                if *i >= units.len() {
                    return Ok(None);
                }
                let c0 = units[*i];
                let take_pair = (0xd800..=0xdbff).contains(&c0)
                    && units
                        .get(*i + 1)
                        .is_some_and(|c1| (0xdc00..=0xdfff).contains(c1));
                let s: Units = if take_pair {
                    let s = vec![c0, units[*i + 1]];
                    *i += 2;
                    s
                } else {
                    *i += 1;
                    vec![c0]
                };
                Ok(Some(JsValue::Str(Rc::new(s))))
            }
        }
    }

    // -- pattern binding -----------------------------------------------------

    /// BindingInitialization / DestructuringAssignmentEvaluation.
    /// `env: Some(e)` initializes pre-declared bindings (declarations,
    /// parameters, catch); `None` resolves-and-assigns (var declarators and
    /// destructuring assignment).
    pub(crate) fn bind_pattern(
        &mut self,
        pat: &Pat,
        v: JsValue,
        env: Option<EnvId>,
        ctx: &Ctx,
    ) -> Result<(), Abrupt> {
        match pat {
            Pat::Ident(name) => match env {
                Some(e) => self.initialize_binding(e, name, v),
                None => self.env_set(ctx, name, v),
            },
            Pat::Expr(m) => {
                let r = self.expr_ref(m, ctx)?;
                self.ref_set(&r, v, ctx)
            }
            Pat::Default(inner, dflt) => {
                let v = if matches!(v, JsValue::Undefined) {
                    self.eval_default(inner, dflt, ctx)?
                } else {
                    v
                };
                self.bind_pattern(inner, v, env, ctx)
            }
            Pat::Array { elems, rest } => self.bind_array_pattern(elems, rest.as_deref(), v, env, ctx),
            Pat::Object { props, rest } => self.bind_object_pattern(props, rest.as_deref(), v, env, ctx),
            Pat::Rest(_) => Err(Abrupt::Fatal(
                "rest pattern outside positional context (parser bug?)".to_string(),
            )),
        }
    }

    fn eval_default(&mut self, target: &Pat, dflt: &Expr, ctx: &Ctx) -> Result<JsValue, Abrupt> {
        if let Pat::Ident(name) = target {
            self.eval_expr_named(dflt, name, ctx)
        } else {
            self.eval_expr(dflt, ctx)
        }
    }

    fn bind_array_pattern(
        &mut self,
        elems: &[Option<Pat>],
        rest: Option<&Pat>,
        v: JsValue,
        env: Option<EnvId>,
        ctx: &Ctx,
    ) -> Result<(), Abrupt> {
        let mut it = self.get_iterator_or_type_error(&v)?;
        let r = self.bind_array_pattern_body(elems, rest, v, env, ctx, &mut it);
        // IteratorClose: a step error (`?` inside the body) already left the
        // iterator done; on any other abrupt, and on a normal completion that
        // did not exhaust the iterator, close while still open.
        match r {
            Ok(()) => {
                if self.iter_user_not_done(&it) {
                    self.iterator_close(&it, false)?;
                }
                Ok(())
            }
            Err(a) => {
                if self.iter_user_not_done(&it) {
                    Err(self.close_after_body_abrupt(&it, a))
                } else {
                    Err(a)
                }
            }
        }
    }

    /// The binding body of an array pattern. Iterator STEP errors are marked
    /// `done` before propagating (spec sets [[Done]] on a step throw, so no
    /// close follows); all other errors leave the iterator open for the
    /// caller's IteratorClose.
    fn bind_array_pattern_body(
        &mut self,
        elems: &[Option<Pat>],
        rest: Option<&Pat>,
        v: JsValue,
        env: Option<EnvId>,
        ctx: &Ctx,
        it: &mut FastIter,
    ) -> Result<(), Abrupt> {
        let _ = v;
        for el in elems {
            self.charge_loop()?;
            match el {
                None => {
                    // Elision: consume one iterator step.
                    self.iter_step_marking_done(it)?;
                }
                Some(p) => {
                    // Assignment-form member targets evaluate their
                    // reference BEFORE the iterator step (spec order).
                    let (target, dflt) = split_default(p);
                    let pre_ref = if let Pat::Expr(m) = target {
                        Some(self.expr_ref(m, ctx)?)
                    } else {
                        None
                    };
                    let mut nv = self.iter_step_marking_done(it)?.unwrap_or(JsValue::Undefined);
                    if let (JsValue::Undefined, Some(d)) = (&nv, dflt) {
                        nv = self.eval_default(target, d, ctx)?;
                    }
                    match pre_ref {
                        Some(r) => self.ref_set(&r, nv, ctx)?,
                        None => self.bind_pattern(target, nv, env, ctx)?,
                    }
                }
            }
        }
        if let Some(r) = rest {
            let pre_ref = if let Pat::Expr(m) = r {
                Some(self.expr_ref(m, ctx)?)
            } else {
                None
            };
            let arr = self.new_array(0)?;
            let mut n: u32 = 0;
            while let Some(nv) = self.iter_step_marking_done(it)? {
                self.charge_loop()?;
                self.heap.obj_mut(arr).props.insert(
                    PropKey::Str(units_from_str(&n.to_string())),
                    Property::data(nv),
                );
                n = n
                    .checked_add(1)
                    .ok_or_else(|| Abrupt::Fatal("rest element count overflow".to_string()))?;
            }
            self.set_array_length_raw(arr, f64::from(n));
            match pre_ref {
                Some(rf) => self.ref_set(&rf, JsValue::Obj(arr), ctx)?,
                None => self.bind_pattern(r, JsValue::Obj(arr), env, ctx)?,
            }
        }
        Ok(())
    }

    /// One IteratorStep that marks a USER iterator `done` if the step itself
    /// throws (spec: a `next` throw sets [[Done]] = true, so no IteratorClose
    /// is issued afterward).
    pub(crate) fn iter_step_marking_done(
        &mut self,
        it: &mut FastIter,
    ) -> Result<Option<JsValue>, Abrupt> {
        match self.fast_iter_next(it) {
            Ok(v) => Ok(v),
            Err(a) => {
                if let FastIter::User { done, .. } = it {
                    *done = true;
                }
                Err(a)
            }
        }
    }

    fn bind_object_pattern(
        &mut self,
        props: &[trust_js_parse::ast::ObjPatProp],
        rest: Option<&Pat>,
        v: JsValue,
        env: Option<EnvId>,
        ctx: &Ctx,
    ) -> Result<(), Abrupt> {
        self.require_object_coercible(&v)?;
        let mut seen: Vec<PropKey> = Vec::with_capacity(props.len());
        for p in props {
            let (key, _, _) = self.eval_prop_key(&p.key, ctx)?;
            seen.push(key.clone());
            let (target, dflt) = split_default(&p.value);
            let pre_ref = if let Pat::Expr(m) = target {
                Some(self.expr_ref(m, ctx)?)
            } else {
                None
            };
            let mut pv = self.get_prop(&v, &key)?;
            if let (JsValue::Undefined, Some(d)) = (&pv, dflt) {
                pv = self.eval_default(target, d, ctx)?;
            }
            match pre_ref {
                Some(r) => self.ref_set(&r, pv, ctx)?,
                None => self.bind_pattern(target, pv, env, ctx)?,
            }
        }
        if let Some(r) = rest {
            let target = self.new_plain()?;
            self.copy_data_properties(target, &v, &seen)?;
            self.bind_pattern(r, JsValue::Obj(target), env, ctx)?;
        }
        Ok(())
    }

    /// CopyDataProperties (7.3.26): own enumerable properties of `src`
    /// (excluding `excluded`) onto `target`. Sound only where the source's
    /// own surface is fully modeled.
    pub(crate) fn copy_data_properties(
        &mut self,
        target: trust_js_value::ObjId,
        src: &JsValue,
        excluded: &[PropKey],
    ) -> Result<(), Abrupt> {
        if src.is_nullish() {
            return Ok(());
        }
        let from = self.to_object(src)?;
        if !self.own_surface_complete(from) {
            return Err(Abrupt::Fatal(
                "spread/rest from an object with unmodeled own surface".to_string(),
            ));
        }
        for key in self.ordered_own_keys_of(from) {
            if excluded.contains(&key) {
                continue;
            }
            self.charge_loop()?;
            let Some(p) = self.own_prop(from, &key) else {
                continue;
            };
            if !p.enumerable {
                continue;
            }
            let v = match &p.v {
                PropValue::Data { .. } => {
                    if p.synthetic {
                        return Err(Abrupt::Fatal(
                            "spread of engine-specific synthetic text".to_string(),
                        ));
                    }
                    p.data_value().expect("data").clone()
                }
                PropValue::Accessor { .. } => self.get_from_object(from, &key, src.clone())?,
            };
            let ok = self.define_own(
                target,
                &key,
                crate::props::PartialDesc::full_data(v, true, true, true),
            )?;
            if !ok {
                return Err(self.throw_type_error());
            }
        }
        Ok(())
    }

    /// Is every own property of `oid` carried by the model (nothing an engine
    /// would add)?
    pub(crate) fn own_surface_complete(&self, oid: trust_js_value::ObjId) -> bool {
        if oid == self.global {
            return false;
        }
        if self.intr.danger.contains_key(&oid) {
            return false;
        }
        // A proxy's own surface is the ownKeys + getOwnPropertyDescriptor traps.
        // The trap-routed reflection paths intercept proxies BEFORE this check;
        // any path that only consults `own_surface_complete` (JSON.stringify,
        // object-spread CopyDataProperties) is not proxy-wired, so treat a
        // proxy as incomplete → those paths refuse (sound), never mis-read the
        // proxy's empty backing `props`.
        !matches!(
            self.heap.obj(oid).kind,
            ObjKind::IntrinsicHost | ObjKind::Error | ObjKind::Proxy(_)
        )
    }
}

/// Split a `Default` layer off a pattern.
fn split_default(p: &Pat) -> (&Pat, Option<&Expr>) {
    match p {
        Pat::Default(inner, e) => (inner, Some(e)),
        other => (other, None),
    }
}
