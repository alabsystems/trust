// Destructuring evaluation, written from the spec (8.6.2 binding
// initialization, 13.15.5 destructuring assignment): object patterns with
// RequireObjectCoercible-before-keys, per-property Get/default/put order and
// the target-reference-before-value rule for assignment leaves; array
// patterns over the SLICE ITERATORS (the same provably-untampered iterables
// for-of accepts: arrays on the pristine %Array.prototype% chain, the
// arguments exotic, string code points) — arbitrary user iterables refuse;
// rest elements/properties (CopyDataProperties over the sound enumerable-own
// surface); NamedEvaluation for anonymous defaults bound to name leaves.
//
// Author: Andrew Yates
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

use crate::ast::{ObjKey, PatElem, Pattern};
use crate::interp::{Abrupt, Ctx, ERes, Interp};
use crate::value::{
    units_from_str, NativeErrorKind, ObjId, ObjKind, Object, Prop, SymId, Units, Value,
};
use std::rc::Rc;

/// How a pattern leaf lands.
#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) enum BindMode {
    /// PutValue on an existing reference (assignment patterns).
    Assign,
    /// `var` semantics (SetMutableBinding through the scope chain).
    Var,
    /// Initialize a pre-declared binding (let/const/param/catch).
    Init,
}

/// One step of a slice iterator (shared with for-of).
pub(crate) enum SliceIter {
    /// %Array.prototype.values% semantics over an object receiver.
    ArrayLike(ObjId, u64),
    /// The String iterator: code points over an immutable snapshot.
    Str(Rc<Units>, usize),
    /// A provably-untampered own generator, driven via its `next`/`return`.
    Generator(crate::value::GenId),
    /// A provably-untampered Array Iterator OBJECT (from `.values()`/`.keys()`/
    /// `.entries()`), driven via the intrinsic next step. (For-of's
    /// `obj[@@iterator]()` self-return comes from %IteratorPrototype%, which is
    /// symbol-keyed and untamperable in-slice.)
    IterObj(ObjId),
    /// A provably-untampered %RegExpStringIterator% (from `@@matchAll`), driven
    /// via the intrinsic `next` step.
    RegExpStringIter(ObjId),
    /// A provably-untampered String Iterator OBJECT (from
    /// `str[Symbol.iterator]()`), driven via the intrinsic code-point step.
    StringIterObj(ObjId),
    /// The GENERAL iterator protocol (7.4) over an arbitrary iterable: the
    /// `@@iterator` method was called to produce `iterator`, and `next` is its
    /// (possibly user-defined) next method. Each step calls `next.[[Call]]` and
    /// reads `done`/`value` off the result; IteratorClose calls `return`. This
    /// covers user-defined iterables AND the Map/Set iterator objects (whose
    /// `next` is a modeled intrinsic). `done` gates a post-completion close.
    General {
        iterator: ObjId,
        next: Value,
        done: bool,
    },
}

impl Interp {
    /// GetIterator over the provably-untampered iterables; exact TypeErrors
    /// where the spec pins them, refusals where user iterables would need
    /// the symbol protocol.
    pub(crate) fn slice_iterator(&mut self, v: &Value) -> Result<SliceIter, Abrupt> {
        match v {
            Value::Obj(o) => match &self.obj(*o).kind {
                ObjKind::Arguments(_) => Ok(SliceIter::ArrayLike(*o, 0)),
                // A generator instance is iterable (its @@iterator returns
                // itself). Iterate it directly when provably untampered
                // (unmodified intrinsic slots); a tampered generator refuses.
                ObjKind::Generator(gid) => {
                    let gid = *gid;
                    if self.generator_untampered(*o) {
                        Ok(SliceIter::Generator(gid))
                    } else {
                        Err(Abrupt::Fatal(
                            "iteration over a tampered generator (out of slice)".to_string(),
                        ))
                    }
                }
                // An Array Iterator object is iterable (its @@iterator returns
                // itself via %IteratorPrototype%). Drive it directly when
                // provably untampered; a tampered one refuses.
                ObjKind::ArrayIterator { .. } => {
                    if self.array_iterator_untampered(*o) {
                        Ok(SliceIter::IterObj(*o))
                    } else {
                        Err(Abrupt::Fatal(
                            "iteration over a tampered array iterator (out of slice)".to_string(),
                        ))
                    }
                }
                // A String Iterator object is iterable (its @@iterator returns
                // itself via %IteratorPrototype%). Drive it directly when
                // provably untampered; a tampered one refuses.
                ObjKind::StringIterator { .. } => {
                    if self.string_iterator_untampered(*o) {
                        Ok(SliceIter::StringIterObj(*o))
                    } else {
                        Err(Abrupt::Fatal(
                            "iteration over a tampered string iterator (out of slice)".to_string(),
                        ))
                    }
                }
                // A RegExp String Iterator (from @@matchAll) is iterable (its
                // @@iterator returns itself via %IteratorPrototype%). Drive it
                // directly when provably untampered.
                ObjKind::RegExpStringIterator { .. } => {
                    if self.regexp_string_iterator_untampered(*o) {
                        Ok(SliceIter::RegExpStringIter(*o))
                    } else {
                        Err(Abrupt::Fatal(
                            "iteration over a tampered RegExp String Iterator (out of slice)"
                                .to_string(),
                        ))
                    }
                }
                // A typed array is iterable via %TypedArray%.prototype.values →
                // an Array Iterator over its element indices. Iterate array-like
                // (length + element get) when @@iterator is the untampered
                // intrinsic; a tampered typed array refuses.
                ObjKind::TypedArray { .. } => {
                    let sid = self.intr.wk(crate::builtins::WK_ITERATOR);
                    match self.get_method_symbol(v, sid)? {
                        Some(m)
                            if matches!(
                                self.obj(m).kind,
                                ObjKind::Function(crate::value::FnImpl::Builtin(
                                    crate::value::Builtin::TypedArrayMethod(
                                        crate::value::TAMethod::Values
                                    )
                                ))
                            ) && self.array_iterator_proto_pristine() =>
                        {
                            Ok(SliceIter::ArrayLike(*o, 0))
                        }
                        _ => Err(Abrupt::Fatal(
                            "iteration over a tampered typed array (out of slice)".to_string(),
                        )),
                    }
                }
                _ => {
                    // GetIterator: resolve @@iterator soundly. If it is exactly
                    // %Array.prototype.values% (the receiver iterates array-like,
                    // covering ordinary arrays, Object.create(Array.prototype),
                    // and objects that install `[].values` as @@iterator), use
                    // the array-like driver. Any other user iterator is out of
                    // slice; absent @@iterator is a pinned TypeError.
                    let sid = self.intr.wk(crate::builtins::WK_ITERATOR);
                    match self.get_method_symbol(v, sid)? {
                        None => Err(self.throw_native(NativeErrorKind::TypeError)),
                        Some(m)
                            if matches!(
                                self.obj(m).kind,
                                ObjKind::Function(crate::value::FnImpl::Builtin(
                                    crate::value::Builtin::ArrayProtoValues
                                ))
                            ) && self.array_iterator_proto_pristine() =>
                        {
                            Ok(SliceIter::ArrayLike(*o, 0))
                        }
                        // Any other @@iterator: the GENERAL protocol (7.4).
                        // GetIterator calls the method to get the iterator, then
                        // reads its `next`; each step/close is spec-exact user-
                        // observable behavior (covers user iterables + Map/Set
                        // iterators).
                        Some(m) => self.general_iterator(v.clone(), m),
                    }
                }
            },
            // A string primitive iterates its code points via
            // String.prototype[@@iterator] → a String Iterator whose `next`
            // steps code-point-wise. The fast path bypasses both the @@iterator
            // method and `next`, so it is sound only while both are the pristine
            // intrinsics; a tampered String iteration protocol refuses.
            Value::Str(s) => {
                if self.string_iteration_pristine() {
                    Ok(SliceIter::Str(Rc::clone(s), 0))
                } else {
                    Err(Abrupt::Fatal(
                        "string iteration with a tampered @@iterator/next (out of slice)"
                            .to_string(),
                    ))
                }
            }
            // Number/Boolean/Symbol/BigInt are not iterable unless user code
            // installed an @@iterator on their prototype (then: out of slice).
            Value::Num(_) | Value::Bool(_) | Value::Sym(_) | Value::BigInt(_) => {
                let sid = self.intr.wk(crate::builtins::WK_ITERATOR);
                match self.get_method_symbol(v, sid)? {
                    None => Err(self.throw_native(NativeErrorKind::TypeError)),
                    Some(_) => Err(Abrupt::Fatal(
                        "iteration over a primitive with a user @@iterator (out of slice)"
                            .to_string(),
                    )),
                }
            }
            Value::Undefined | Value::Null => Err(self.throw_native(NativeErrorKind::TypeError)),
        }
    }

    /// Is the WHOLE intrinsic array-iteration protocol globally pristine —
    /// Array.prototype's own @@iterator still %Array.prototype.values% AND
    /// %ArrayIteratorPrototype%.next still intrinsic? The frozen trace driver's
    /// `classTag` itself deep-prints via `for (… of INTRINSIC_PROTOS)`, so a
    /// globally-patched array-iteration protocol corrupts the DRIVER's own
    /// projection of every object (Node then reports `cls:null` for a plain
    /// array). In that state the oracle is unreliable, so the general protocol
    /// must refuse rather than match self-corrupted output.
    fn array_iteration_pristine(&self) -> bool {
        let sid = self.intr.wk(crate::builtins::WK_ITERATOR);
        let iter_ok = matches!(
            self.obj(self.intr.array_proto).sym_props.get(&sid).map(|pr| &pr.val),
            Some(crate::value::PropVal::Data { value: Value::Obj(f), .. })
                if matches!(
                    self.obj(*f).kind,
                    ObjKind::Function(crate::value::FnImpl::Builtin(
                        crate::value::Builtin::ArrayProtoValues
                    ))
                )
        );
        iter_ok && self.array_iterator_proto_pristine()
    }

    /// GetIterator's tail (7.4.4) for the general protocol: call the resolved
    /// `@@iterator` method with `iterable` as `this`, require an Object result,
    /// then read its `next` method. A non-object iterator is a TypeError.
    fn general_iterator(&mut self, iterable: Value, method: ObjId) -> Result<SliceIter, Abrupt> {
        // If the intrinsic array-iteration protocol is globally tampered, the
        // trace driver's own deep-print is corrupted — refuse (see above).
        if !self.array_iteration_pristine() {
            return Err(Abrupt::Fatal(
                "general iteration while the array-iteration protocol is globally tampered \
                 (driver projection unreliable)"
                    .to_string(),
            ));
        }
        let iter = self.call_function(method, iterable, Vec::new(), false)?;
        let Value::Obj(ioid) = iter else {
            return Err(self.throw_native(NativeErrorKind::TypeError));
        };
        let next = self.get_from_object(ioid, &units_from_str("next"))?;
        Ok(SliceIter::General {
            iterator: ioid,
            next,
            done: false,
        })
    }

    /// Is `oid` a generator whose iteration protocol is provably the intrinsic
    /// one (so driving it via `next` is exact)? True iff the instance has no
    /// own properties (no shadowing `next`/@@iterator), and its `.prototype`
    /// object neither shadows `next`/`return` nor has had its own [[Prototype]]
    /// swapped away from %GeneratorPrototype%.
    pub(crate) fn generator_untampered(&self, oid: ObjId) -> bool {
        let obj = self.obj(oid);
        if !obj.props.is_empty() {
            return false;
        }
        let Some(p) = obj.proto else { return false };
        let pobj = self.obj(p);
        if pobj.props.contains_key(&units_from_str("next"))
            || pobj.props.contains_key(&units_from_str("return"))
        {
            return false;
        }
        pobj.proto == Some(self.intr.generator_proto)
    }

    /// Is the shared %ArrayIteratorPrototype%.next still the pristine intrinsic
    /// builtin? The array-like iteration fast path bypasses `next` entirely, so
    /// a user-replaced `next` (observable through the real iterator protocol)
    /// makes that path unsound — the caller must refuse instead.
    pub(crate) fn array_iterator_proto_pristine(&self) -> bool {
        matches!(
            self.obj(self.intr.array_iterator_proto)
                .props
                .get(&units_from_str("next"))
                .map(|pr| &pr.val),
            Some(crate::value::PropVal::Data {
                value: Value::Obj(f),
                ..
            }) if matches!(
                self.obj(*f).kind,
                ObjKind::Function(crate::value::FnImpl::Builtin(
                    crate::value::Builtin::ArrayIteratorNext
                ))
            )
        )
    }

    /// Is `oid` an Array Iterator whose iteration protocol is provably the
    /// intrinsic one? True iff it has no own properties (no shadowing `next`),
    /// its [[Prototype]] is the pristine %ArrayIteratorPrototype% (own
    /// `next` still the intrinsic builtin, proto still %IteratorPrototype%).
    pub(crate) fn array_iterator_untampered(&self, oid: ObjId) -> bool {
        let obj = self.obj(oid);
        if !obj.props.is_empty() {
            return false;
        }
        if obj.proto != Some(self.intr.array_iterator_proto) {
            return false;
        }
        let p = self.intr.array_iterator_proto;
        let pobj = self.obj(p);
        if pobj.proto != Some(self.intr.iterator_proto) {
            return false;
        }
        matches!(
            pobj.props.get(&units_from_str("next")).map(|pr| &pr.val),
            Some(crate::value::PropVal::Data {
                value: Value::Obj(f),
                ..
            }) if matches!(
                self.obj(*f).kind,
                ObjKind::Function(crate::value::FnImpl::Builtin(
                    crate::value::Builtin::ArrayIteratorNext
                ))
            )
        )
    }

    /// Is `oid` a String Iterator whose iteration protocol is provably the
    /// intrinsic one? True iff it has no own properties (no shadowing `next`),
    /// its [[Prototype]] is the pristine %StringIteratorPrototype% (own `next`
    /// still the intrinsic builtin, proto still %IteratorPrototype%).
    pub(crate) fn string_iterator_untampered(&self, oid: ObjId) -> bool {
        let obj = self.obj(oid);
        if !obj.props.is_empty() {
            return false;
        }
        if obj.proto != Some(self.intr.string_iterator_proto) {
            return false;
        }
        self.string_iterator_proto_pristine()
    }

    /// Is %StringIteratorPrototype% pristine: proto still %IteratorPrototype%
    /// and its own `next` still the intrinsic `StringIteratorNext` builtin?
    pub(crate) fn string_iterator_proto_pristine(&self) -> bool {
        let p = self.intr.string_iterator_proto;
        let pobj = self.obj(p);
        if pobj.proto != Some(self.intr.iterator_proto) {
            return false;
        }
        matches!(
            pobj.props.get(&units_from_str("next")).map(|pr| &pr.val),
            Some(crate::value::PropVal::Data {
                value: Value::Obj(f),
                ..
            }) if matches!(
                self.obj(*f).kind,
                ObjKind::Function(crate::value::FnImpl::Builtin(
                    crate::value::Builtin::StringIteratorNext
                ))
            )
        )
    }

    /// Is the whole String iteration protocol pristine — String.prototype's own
    /// @@iterator still the intrinsic `StringProtoIterator`, and
    /// %StringIteratorPrototype%.next still intrinsic? Guards the raw-string
    /// for-of/spread fast path (which bypasses both).
    pub(crate) fn string_iteration_pristine(&self) -> bool {
        let sid = self.intr.wk(crate::builtins::WK_ITERATOR);
        let intrinsic_at_iterator = matches!(
            self.obj(self.intr.string_proto).sym_props.get(&sid).map(|pr| &pr.val),
            Some(crate::value::PropVal::Data {
                value: Value::Obj(f),
                ..
            }) if matches!(
                self.obj(*f).kind,
                ObjKind::Function(crate::value::FnImpl::Builtin(
                    crate::value::Builtin::StringProtoIterator
                ))
            )
        );
        intrinsic_at_iterator && self.string_iterator_proto_pristine()
    }

    /// Is `oid` a RegExp String Iterator whose iteration protocol is provably
    /// the intrinsic one? True iff it has no own properties (no shadowing
    /// `next`) and its [[Prototype]] is the pristine
    /// %RegExpStringIteratorPrototype% (own `next` still the intrinsic builtin,
    /// proto still %IteratorPrototype%).
    pub(crate) fn regexp_string_iterator_untampered(&self, oid: ObjId) -> bool {
        let obj = self.obj(oid);
        if !obj.props.is_empty() {
            return false;
        }
        if obj.proto != Some(self.intr.regexp_string_iterator_proto) {
            return false;
        }
        let p = self.intr.regexp_string_iterator_proto;
        let pobj = self.obj(p);
        if pobj.proto != Some(self.intr.iterator_proto) {
            return false;
        }
        matches!(
            pobj.props.get(&units_from_str("next")).map(|pr| &pr.val),
            Some(crate::value::PropVal::Data {
                value: Value::Obj(f),
                ..
            }) if matches!(
                self.obj(*f).kind,
                ObjKind::Function(crate::value::FnImpl::Builtin(
                    crate::value::Builtin::RegExpStringIteratorNext
                ))
            )
        )
    }

    /// The next iterator value; None = done.
    pub(crate) fn slice_iter_next(&mut self, it: &mut SliceIter) -> Result<Option<Value>, Abrupt> {
        match it {
            SliceIter::Generator(gid) => {
                let gid = *gid;
                let res = self.generator_resume(gid, crate::generator::Resumption::Normal(Value::Undefined))?;
                let Value::Obj(roid) = res else {
                    return Err(Abrupt::Fatal("generator result not an object".to_string()));
                };
                let done = self.get_from_object(roid, &units_from_str("done"))?;
                if self.to_boolean(&done) {
                    Ok(None)
                } else {
                    Ok(Some(self.get_from_object(roid, &units_from_str("value"))?))
                }
            }
            SliceIter::ArrayLike(o, idx) => {
                let o = *o;
                let len_v = self.get_from_object(o, &units_from_str("length"))?;
                let len = crate::builtins::to_length_u64(self.to_number(&len_v)?);
                if *idx >= len {
                    Ok(None)
                } else {
                    let key = units_from_str(&idx.to_string());
                    let el = self.get_from_object(o, &key)?;
                    *idx += 1;
                    Ok(Some(el))
                }
            }
            SliceIter::Str(s, i) => {
                if *i >= s.len() {
                    Ok(None)
                } else {
                    let c = s[*i];
                    let mut out = vec![c];
                    if (0xd800..=0xdbff).contains(&c)
                        && *i + 1 < s.len()
                        && (0xdc00..=0xdfff).contains(&s[*i + 1])
                    {
                        out.push(s[*i + 1]);
                    }
                    *i += out.len();
                    Ok(Some(Value::Str(Rc::new(out))))
                }
            }
            SliceIter::IterObj(oid) => {
                let oid = *oid;
                let (value, done) = self.array_iterator_step(oid)?;
                Ok(if done { None } else { Some(value) })
            }
            SliceIter::StringIterObj(oid) => {
                let oid = *oid;
                let (value, done) = self.string_iterator_step(oid);
                Ok(if done { None } else { Some(value) })
            }
            SliceIter::RegExpStringIter(oid) => {
                let oid = *oid;
                let res = self.regexp_string_iterator_next(&Value::Obj(oid))?;
                let Value::Obj(roid) = res else {
                    return Err(Abrupt::Fatal(
                        "RegExp String Iterator result not an object".to_string(),
                    ));
                };
                let done = self.get_from_object(roid, &units_from_str("done"))?;
                if self.to_boolean(&done) {
                    Ok(None)
                } else {
                    Ok(Some(self.get_from_object(roid, &units_from_str("value"))?))
                }
            }
            // The general protocol (7.4.6 IteratorStep + 7.4.7 IteratorValue):
            // Call(next, iterator); the result must be an Object; read `done`
            // then (if not done) `value`.
            SliceIter::General { iterator, next, done } => {
                if *done {
                    return Ok(None);
                }
                let iterator = *iterator;
                let next = next.clone();
                let res = self.call_value(&next, Value::Obj(iterator), Vec::new())?;
                let Value::Obj(roid) = res else {
                    return Err(self.throw_native(NativeErrorKind::TypeError));
                };
                let done_v = self.get_from_object(roid, &units_from_str("done"))?;
                if self.to_boolean(&done_v) {
                    if let SliceIter::General { done, .. } = it {
                        *done = true;
                    }
                    Ok(None)
                } else {
                    Ok(Some(self.get_from_object(roid, &units_from_str("value"))?))
                }
            }
        }
    }

    /// IteratorClose (7.4.11) on a slice iterator during an early for-of exit.
    /// The array/string/arguments iterators have no `return` method, so this
    /// is a no-op; generator-backed iterators route through the generator's
    /// `return` (added with the own-generator fast path).
    pub(crate) fn slice_iterator_close(
        &mut self,
        it: &mut SliceIter,
    ) -> Result<(), Abrupt> {
        match it {
            // Array/string iterators, Array Iterator objects, and RegExp
            // String Iterators have no `return` method — IteratorClose is a
            // no-op.
            SliceIter::ArrayLike(..)
            | SliceIter::Str(..)
            | SliceIter::IterObj(..)
            | SliceIter::StringIterObj(..)
            | SliceIter::RegExpStringIter(..) => Ok(()),
            // IteratorClose routes through the generator's `return`, running
            // any pending finally blocks; a completed generator is a no-op.
            SliceIter::Generator(gid) => {
                let gid = *gid;
                self.generator_resume(gid, crate::generator::Resumption::Return(Value::Undefined))?;
                Ok(())
            }
            // IteratorClose (7.4.11) for the general protocol: GetMethod(
            // iterator, "return"); a nullish return is a no-op, else call it
            // and (on a normal completion) require an Object result. A done
            // iterator is never closed.
            SliceIter::General { iterator, done, .. } => {
                if *done {
                    return Ok(());
                }
                let iterator = *iterator;
                let sid_return = units_from_str("return");
                let ret = self.get_from_object(iterator, &sid_return)?;
                match ret {
                    Value::Undefined | Value::Null => Ok(()),
                    Value::Obj(f) if self.obj(f).is_callable() => {
                        let r = self.call_function(f, Value::Obj(iterator), Vec::new(), false)?;
                        if matches!(r, Value::Obj(_)) {
                            Ok(())
                        } else {
                            Err(self.throw_native(NativeErrorKind::TypeError))
                        }
                    }
                    _ => Err(self.throw_native(NativeErrorKind::TypeError)),
                }
            }
        }
    }

    /// Destructure `v` per `pat` in the given mode.
    pub(crate) fn destructure(
        &mut self,
        pat: &Pattern,
        v: &Value,
        ctx: &Ctx,
        mode: BindMode,
    ) -> Result<(), Abrupt> {
        match pat {
            Pattern::Ident(name) => self.bind_pattern_leaf(name, v.clone(), ctx, mode),
            Pattern::Target(e) => {
                if mode != BindMode::Assign {
                    return Err(Abrupt::Fatal(
                        "member target in a binding pattern (parser invariant)".to_string(),
                    ));
                }
                let r = self.eval_ref_assign(e, ctx)?;
                self.ref_set(&r, v.clone(), ctx)
            }
            Pattern::Object { props, rest } => self.destructure_object(props, rest, v, ctx, mode),
            Pattern::Array { elems, rest } => self.destructure_array(elems, rest, v, ctx, mode),
        }
    }

    fn bind_pattern_leaf(
        &mut self,
        name: &str,
        v: Value,
        ctx: &Ctx,
        mode: BindMode,
    ) -> Result<(), Abrupt> {
        match mode {
            BindMode::Assign | BindMode::Var => self.env_set(ctx, name, v),
            BindMode::Init => {
                self.initialize_binding_public(ctx.env, name, v);
                Ok(())
            }
        }
    }

    /// The default-initializer step, with NamedEvaluation for anonymous
    /// function/class defaults landing on a NAME leaf.
    fn apply_default(
        &mut self,
        v: Value,
        elem: &PatElem,
        ctx: &Ctx,
    ) -> ERes {
        if !matches!(v, Value::Undefined) {
            return Ok(v);
        }
        let Some(d) = &elem.default else {
            return Ok(v);
        };
        if let Pattern::Ident(name) = &elem.pat {
            return self.eval_named(d, ctx, &units_from_str(name));
        }
        self.eval_expr(d, ctx)
    }

    fn destructure_object(
        &mut self,
        props: &[(ObjKey, PatElem)],
        rest: &Option<Box<Pattern>>,
        src: &Value,
        ctx: &Ctx,
        mode: BindMode,
    ) -> Result<(), Abrupt> {
        // RequireObjectCoercible BEFORE any key evaluation.
        if matches!(src, Value::Undefined | Value::Null) {
            return Err(self.throw_native(NativeErrorKind::TypeError));
        }
        let mut consumed: Vec<Units> = Vec::new();
        for (key_ast, elem) in props {
            // Leaf targets resolve BEFORE the value is fetched (13.15.5.3),
            // but AFTER the key evaluates.
            let key = match key_ast {
                ObjKey::Fixed(u) => u.clone(),
                ObjKey::Computed(e) => {
                    let kv = self.eval_expr(e, ctx)?;
                    // Symbol-keyed destructuring targets (`{ [sym]: x } = o`) are
                    // out of the current slice (the rest-exclusion set would need
                    // symbol keys too) — refuse rather than mis-key.
                    match self.to_property_key(&kv)? {
                        crate::value::PropertyKey::Str(u) => u,
                        crate::value::PropertyKey::Sym(_) => {
                            return Err(Abrupt::Fatal(
                                "symbol-keyed destructuring target (out of slice)".to_string(),
                            ))
                        }
                    }
                }
            };
            consumed.push(key.clone());
            match &elem.pat {
                Pattern::Target(te) if mode == BindMode::Assign => {
                    let r = self.eval_ref_assign(te, ctx)?;
                    let v = self.get_prop_value(src, &key)?;
                    let v = self.apply_default(v, elem, ctx)?;
                    self.ref_set(&r, v, ctx)?;
                }
                _ => {
                    let v = self.get_prop_value(src, &key)?;
                    let v = self.apply_default(v, elem, ctx)?;
                    match &elem.pat {
                        Pattern::Ident(name) => {
                            self.bind_pattern_leaf(name, v, ctx, mode)?;
                        }
                        nested => self.destructure(nested, &v, ctx, mode)?,
                    }
                }
            }
        }
        if let Some(rest_pat) = rest {
            let robj = self.copy_data_properties_excluding(src, &consumed)?;
            match rest_pat.as_ref() {
                Pattern::Ident(name) => {
                    self.bind_pattern_leaf(name, Value::Obj(robj), ctx, mode)?;
                }
                Pattern::Target(te) if mode == BindMode::Assign => {
                    let r = self.eval_ref_assign(te, ctx)?;
                    self.ref_set(&r, Value::Obj(robj), ctx)?;
                }
                _ => {
                    return Err(Abrupt::Fatal(
                        "object rest target shape (parser invariant)".to_string(),
                    ))
                }
            }
        }
        Ok(())
    }

    /// CopyDataProperties(target, source, excluded): a fresh object from the
    /// sound enumerable-own surface of the source.
    fn copy_data_properties_excluding(
        &mut self,
        src: &Value,
        excluded: &[Units],
    ) -> Result<ObjId, Abrupt> {
        let out = self.alloc(Object::new(ObjKind::Plain, Some(self.intr.object_proto)));
        // A proxy source: CopyDataProperties drives [[OwnPropertyKeys]] then
        // [[GetOwnProperty]] + [[Get]] per key, in trap order (7.3.25).
        if let Value::Obj(o) = src {
            if matches!(self.obj(*o).kind, crate::value::ObjKind::Proxy { .. }) {
                for key in self.mop_own_keys(*o)? {
                    if let crate::value::PropertyKey::Str(u) = &key {
                        if excluded.contains(u) {
                            continue;
                        }
                    }
                    let Some(desc) = self.mop_get_own_property(*o, &key)? else {
                        continue;
                    };
                    if !desc.enumerable {
                        continue;
                    }
                    let v = self.get_prop_value_pk(src, &key)?;
                    match key {
                        crate::value::PropertyKey::Str(u) => {
                            self.obj_mut(out).props.insert(u, Prop::data(v));
                        }
                        crate::value::PropertyKey::Sym(s) => {
                            self.obj_mut(out).sym_props.insert(s, Prop::data(v));
                        }
                    }
                }
                return Ok(out);
            }
        }
        let keys: Vec<Units> = match src {
            Value::Obj(o) => self
                .enumerable_own_keys_sound(*o)
                .map_err(|e| Abrupt::Fatal(format!("object rest: {e}")))?,
            Value::Str(s) => (0..s.len()).map(|i| units_from_str(&i.to_string())).collect(),
            _ => Vec::new(), // number/boolean wrappers: no own enumerables
        };
        for k in keys {
            if excluded.contains(&k) {
                continue;
            }
            let v = self.get_prop_value(src, &k)?;
            self.obj_mut(out).props.insert(k, Prop::data(v));
        }
        // CopyDataProperties (7.3.25) visits every own key of
        // [[OwnPropertyKeys]] — so enumerable SYMBOL keys follow the strings,
        // in insertion order. (Symbol-keyed rest EXCLUSION targets are out of
        // slice, so `excluded` is string-only; no symbol is ever excluded.)
        // Soundness: `enumerable_own_keys_sound` above already refused the
        // wildcard hosts (global/console/Error instances); for every remaining
        // object the enumerable own-symbol set is fully captured by `sym_props`
        // — user objects are complete, and every intrinsic's well-known symbol
        // is spec-non-enumerable, so none are copied.
        if let Value::Obj(o) = src {
            let sym_keys: Vec<SymId> = self
                .obj(*o)
                .sym_props
                .iter()
                .filter(|(_, p)| p.enumerable)
                .map(|(s, _)| *s)
                .collect();
            for s in sym_keys {
                let v = self.get_prop_value_sym(src, s)?;
                self.obj_mut(out).sym_props.insert(s, Prop::data(v));
            }
        }
        Ok(out)
    }

    fn destructure_array(
        &mut self,
        elems: &[Option<PatElem>],
        rest: &Option<Box<Pattern>>,
        src: &Value,
        ctx: &Ctx,
        mode: BindMode,
    ) -> Result<(), Abrupt> {
        let mut it = self.slice_iterator(src)?;
        // Track iterator exhaustion: IteratorClose (8.6.2 / 13.15.5.5) runs on
        // completion ONLY while the iterator is not done. A step that returns
        // done — or itself throws (IteratorStep abrupt sets [[Done]]) — leaves
        // no iterator to close.
        let mut done = false;
        let result = self.destructure_array_body(&mut it, &mut done, elems, rest, ctx, mode);
        match result {
            Ok(()) => {
                if !done && rest.is_none() {
                    // Normal completion with an un-exhausted iterator: close it
                    // (a no-op for array/string; a generator's/user `return`
                    // runs, and a non-object `return` result throws TypeError).
                    self.slice_iterator_close(&mut it)?;
                }
                Ok(())
            }
            Err(a) => {
                // Abrupt completion: IteratorClose with a throw completion is
                // best-effort — the original throw always wins (7.4.11 step 4),
                // so a faulting/non-object `return` is swallowed here.
                if !done {
                    let _ = self.slice_iterator_close(&mut it);
                }
                Err(a)
            }
        }
    }

    /// One iterator step for array destructuring, tracking exhaustion. Once
    /// `done`, further elements bind `undefined` without touching the iterator.
    fn array_dstr_step(
        &mut self,
        it: &mut SliceIter,
        done: &mut bool,
    ) -> Result<Value, Abrupt> {
        if *done {
            return Ok(Value::Undefined);
        }
        match self.slice_iter_next(it) {
            Ok(Some(v)) => Ok(v),
            Ok(None) => {
                *done = true;
                Ok(Value::Undefined)
            }
            Err(a) => {
                // IteratorStep abrupt: the iterator record is now done.
                *done = true;
                Err(a)
            }
        }
    }

    fn destructure_array_body(
        &mut self,
        it: &mut SliceIter,
        done: &mut bool,
        elems: &[Option<PatElem>],
        rest: &Option<Box<Pattern>>,
        ctx: &Ctx,
        mode: BindMode,
    ) -> Result<(), Abrupt> {
        for elem in elems {
            match elem {
                None => {
                    // Elision consumes one iterator step.
                    self.charge_loop()?;
                    self.array_dstr_step(it, done)?;
                }
                Some(elem) => {
                    self.charge_loop()?;
                    match &elem.pat {
                        // Leaf target references resolve BEFORE the iterator
                        // steps (13.15.5.5).
                        Pattern::Target(te) if mode == BindMode::Assign => {
                            let r = self.eval_ref_assign(te, ctx)?;
                            let v = self.array_dstr_step(it, done)?;
                            let v = self.apply_default(v, elem, ctx)?;
                            self.ref_set(&r, v, ctx)?;
                        }
                        Pattern::Ident(name) => {
                            // Same rule: name leaves resolve their reference
                            // first (observable only through env exotics —
                            // identical here).
                            let v = self.array_dstr_step(it, done)?;
                            let v = self.apply_default(v, elem, ctx)?;
                            self.bind_pattern_leaf(name, v, ctx, mode)?;
                        }
                        nested => {
                            let v = self.array_dstr_step(it, done)?;
                            let v = self.apply_default(v, elem, ctx)?;
                            self.destructure(nested, &v, ctx, mode)?;
                        }
                    }
                }
            }
        }
        if let Some(rest_pat) = rest {
            // The rest-target reference resolves BEFORE the drain (13.15.5.5).
            let rest_ref = match rest_pat.as_ref() {
                Pattern::Target(te) if mode == BindMode::Assign => {
                    Some(self.eval_ref_assign(te, ctx)?)
                }
                _ => None,
            };
            let arr = self.new_array(0);
            let mut n: u64 = 0;
            loop {
                self.charge_loop()?;
                if *done {
                    break;
                }
                match self.slice_iter_next(it) {
                    Ok(Some(v)) => {
                        self.obj_mut(arr)
                            .props
                            .insert(units_from_str(&n.to_string()), Prop::data(v));
                        n += 1;
                    }
                    Ok(None) => {
                        *done = true;
                        break;
                    }
                    Err(a) => {
                        *done = true;
                        return Err(a);
                    }
                }
            }
            #[allow(clippy::cast_precision_loss)]
            self.set_array_length_raw(arr, n as f64);
            match rest_pat.as_ref() {
                Pattern::Ident(name) => {
                    self.bind_pattern_leaf(name, Value::Obj(arr), ctx, mode)?;
                }
                Pattern::Target(_) if mode == BindMode::Assign => {
                    let r = rest_ref.expect("rest target reference resolved above");
                    self.ref_set(&r, Value::Obj(arr), ctx)?;
                }
                nested => self.destructure(nested, &Value::Obj(arr), ctx, mode)?,
            }
        }
        Ok(())
    }
}
