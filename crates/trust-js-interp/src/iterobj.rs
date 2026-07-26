// Built-in iterator objects: %ArrayIteratorPrototype% / %StringIteratorPrototype%
// / %MapIteratorPrototype% / %SetIteratorPrototype% instances, written from
// ECMA-262 (23.1.5 / 22.1.5 / 24.1.5 / 24.2.5). Each is an ordinary object
// (ObjKind::Iterator) whose iteration state lives in the interpreter's
// `iter_state` side table (like a generator's internal slots); `.next()`
// produces exact {value,done} iterator-result objects, re-reading the live
// source each step. Array and TypedArray iterators share %ArrayIteratorPrototype%
// (@@toStringTag "Array Iterator") exactly as the spec prescribes.
//
// The object itself carries NO own properties, so it projects as an ordinary
// empty object `{cls:'Object', props:[]}` (its @@toStringTag lives on the
// prototype, matching the deep-print driver, which tags by intrinsic-prototype
// identity and never sees the iterator prototypes).
//
// Author: Andrew Yates
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

use crate::builtins_regexp::advance_string_index;
use crate::interp::{Abrupt, ERes, Interp};
use std::rc::Rc;
use trust_js_value::{
    to_length_u64, units_from_str, JsObject, JsValue, ObjId, ObjKind, PropKey, Property, Units,
};

/// Which projection each `next` step yields ([[ArrayLikeIterationKind]] /
/// [[MapIterationKind]] / [[SetIterationKind]]).
#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) enum IterKind {
    Key,
    Value,
    KeyValue,
}

/// The iteration state of one built-in iterator object (an internal-slots
/// record kept out of the heap object).
pub(crate) enum IterObj {
    /// Array Iterator over an array-like object (23.1.5): `length` and elements
    /// are re-read each step through observable [[Get]]s. `target` = None once
    /// completed ([[IteratedArrayLike]] set to undefined).
    Array {
        target: Option<ObjId>,
        kind: IterKind,
        index: u64,
    },
    /// Array Iterator over a TypedArray (shares %ArrayIteratorPrototype%): the
    /// backing buffer is validated each step; a detached/out-of-bounds source
    /// throws TypeError mid-iteration.
    TypedArray {
        target: Option<ObjId>,
        kind: IterKind,
        index: usize,
    },
    /// String Iterator (22.1.5): by code point.
    Str { units: Rc<Units>, pos: usize },
    /// Map Iterator over the live [[MapData]] (24.1.5): tombstones skipped,
    /// appended entries visited. `target` = None latches completion even if the
    /// map later grows.
    Map {
        target: Option<ObjId>,
        kind: IterKind,
        index: usize,
    },
    /// Set Iterator over the live [[SetData]] (24.2.5); keys === values.
    Set {
        target: Option<ObjId>,
        kind: IterKind,
        index: usize,
    },
    /// RegExp String Iterator (22.2.9.2.1 %RegExpStringIteratorPrototype%.next).
    /// `matcher` = R, the [[IteratingRegExp]] (None latches [[Done]]). Each step
    /// runs one RegExpExec(R, S); a global empty match performs the
    /// ToLength(lastIndex) → AdvanceStringIndex → Set SYNCHRONOUSLY within the
    /// same step (the modern spec's next is an ordinary method, not a suspended
    /// closure — the advance is observable via a custom exec before the next
    /// step).
    RegExpString {
        matcher: Option<ObjId>,
        s: Rc<Units>,
        global: bool,
        full_unicode: bool,
    },
}

/// The family a `.next` brand-check requires.
#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) enum IterBrand {
    /// Array Iterator (Array OR TypedArray — they share the prototype/next).
    Array,
    String,
    Map,
    Set,
    RegExpString,
}

impl IterObj {
    fn brand(&self) -> IterBrand {
        match self {
            IterObj::Array { .. } | IterObj::TypedArray { .. } => IterBrand::Array,
            IterObj::Str { .. } => IterBrand::String,
            IterObj::Map { .. } => IterBrand::Map,
            IterObj::Set { .. } => IterBrand::Set,
            IterObj::RegExpString { .. } => IterBrand::RegExpString,
        }
    }

    /// Mark the iterator completed (after a step throw): subsequent `next`
    /// yields {undefined, true}.
    fn complete(&mut self) {
        match self {
            IterObj::Array { target, .. } | IterObj::TypedArray { target, .. } => *target = None,
            IterObj::Map { target, .. } | IterObj::Set { target, .. } => *target = None,
            IterObj::RegExpString { matcher, .. } => *matcher = None,
            IterObj::Str { units, pos } => *pos = units.len(),
        }
    }
}

impl Interp {
    // -- construction --------------------------------------------------------

    fn alloc_iterator(&mut self, proto: ObjId, st: IterObj) -> ERes {
        let oid = self.alloc_obj(JsObject::new(ObjKind::Iterator, Some(proto)))?;
        self.iter_state.insert(oid, st);
        Ok(JsValue::Obj(oid))
    }

    /// CreateArrayIterator(O, kind) (23.1.5.1) over an array-like object.
    pub(crate) fn make_array_iterator(&mut self, target: ObjId, kind: IterKind) -> ERes {
        self.alloc_iterator(
            self.intr.array_iterator_proto,
            IterObj::Array {
                target: Some(target),
                kind,
                index: 0,
            },
        )
    }

    /// CreateArrayIterator over a TypedArray (23.2.3.x): same prototype, but the
    /// buffer is validated each step.
    pub(crate) fn make_typed_array_iterator(&mut self, target: ObjId, kind: IterKind) -> ERes {
        self.alloc_iterator(
            self.intr.array_iterator_proto,
            IterObj::TypedArray {
                target: Some(target),
                kind,
                index: 0,
            },
        )
    }

    /// CreateStringIterator(S) (22.1.5.1).
    pub(crate) fn make_string_iterator(&mut self, units: Rc<Units>) -> ERes {
        self.alloc_iterator(self.intr.string_iterator_proto, IterObj::Str { units, pos: 0 })
    }

    /// CreateMapIterator(map, kind) (24.1.5.1).
    pub(crate) fn make_map_iterator(&mut self, target: ObjId, kind: IterKind) -> ERes {
        self.alloc_iterator(
            self.intr.map_iterator_proto,
            IterObj::Map {
                target: Some(target),
                kind,
                index: 0,
            },
        )
    }

    /// CreateSetIterator(set, kind) (24.2.5.1).
    pub(crate) fn make_set_iterator(&mut self, target: ObjId, kind: IterKind) -> ERes {
        self.alloc_iterator(
            self.intr.set_iterator_proto,
            IterObj::Set {
                target: Some(target),
                kind,
                index: 0,
            },
        )
    }

    /// CreateRegExpStringIterator(R, S, global, fullUnicode) (22.2.9.1).
    pub(crate) fn make_regexp_string_iterator(
        &mut self,
        matcher: ObjId,
        s: Rc<Units>,
        global: bool,
        full_unicode: bool,
    ) -> ERes {
        self.alloc_iterator(
            self.intr.regexp_string_iterator_proto,
            IterObj::RegExpString {
                matcher: Some(matcher),
                s,
                global,
                full_unicode,
            },
        )
    }

    // -- next ----------------------------------------------------------------

    /// The `.next()` of a built-in iterator prototype: brand-check `this`
    /// against `brand`, then run one IteratorNext step, returning the
    /// iterator-result object. The iteration state is taken OUT for the step so
    /// a reentrant `next()` (an array-like index getter / proxy re-entering the
    /// same iterator) finds no live state and throws — matching the spec's
    /// "generator is already executing" TypeError.
    pub(crate) fn builtin_iter_next(&mut self, this: &JsValue, brand: IterBrand) -> ERes {
        let JsValue::Obj(oid) = this else {
            return Err(self.throw_type_error());
        };
        let oid = *oid;
        if !matches!(self.heap.obj(oid).kind, ObjKind::Iterator) {
            return Err(self.throw_type_error());
        }
        let Some(mut st) = self.iter_state.remove(&oid) else {
            return Err(self.throw_type_error());
        };
        if st.brand() != brand {
            self.iter_state.insert(oid, st);
            return Err(self.throw_type_error());
        }
        let result = self.iter_step(&mut st);
        // A throw from a step completes the iterator (the generator closure
        // returns abruptly); a later next() then yields {undefined, true}.
        // Everything else (Ok, or a Fatal refusal that fails the whole case)
        // restores the state unchanged.
        if matches!(&result, Err(Abrupt::Throw(_))) {
            st.complete();
        }
        self.iter_state.insert(oid, st);
        result
    }

    fn iter_step(&mut self, st: &mut IterObj) -> ERes {
        match st {
            IterObj::Array { target, kind, index } => {
                let Some(arr) = *target else {
                    return self.create_iter_result(JsValue::Undefined, true);
                };
                let kind = *kind;
                let arrv = JsValue::Obj(arr);
                let len_v =
                    self.get_from_object(arr, &PropKey::from_str("length"), arrv.clone())?;
                let len = to_length_u64(self.to_number(&len_v)?);
                if *index >= len {
                    *target = None;
                    return self.create_iter_result(JsValue::Undefined, true);
                }
                let i = *index;
                #[allow(clippy::cast_precision_loss)]
                let result = match kind {
                    IterKind::Key => JsValue::Num(i as f64),
                    IterKind::Value => {
                        let key = PropKey::Str(units_from_str(&i.to_string()));
                        self.get_from_object(arr, &key, arrv)?
                    }
                    IterKind::KeyValue => {
                        let key = PropKey::Str(units_from_str(&i.to_string()));
                        let v = self.get_from_object(arr, &key, arrv)?;
                        self.iter_pair(JsValue::Num(i as f64), v)?
                    }
                };
                *index = i + 1;
                self.create_iter_result(result, false)
            }
            IterObj::TypedArray { target, kind, index } => {
                let Some(ta) = *target else {
                    return self.create_iter_result(JsValue::Undefined, true);
                };
                let kind = *kind;
                // IsValidIntegerIndex / typed-array validation: a detached or
                // out-of-bounds backing buffer throws TypeError mid-iteration.
                if self.ta_out_of_bounds(ta) {
                    return Err(self.throw_type_error());
                }
                let len = self.ta_current_length(ta);
                if *index >= len {
                    *target = None;
                    return self.create_iter_result(JsValue::Undefined, true);
                }
                let i = *index;
                #[allow(clippy::cast_precision_loss)]
                let result = match kind {
                    IterKind::Key => JsValue::Num(i as f64),
                    IterKind::Value => self.ta_element_get_pure(ta, i as f64),
                    IterKind::KeyValue => {
                        let v = self.ta_element_get_pure(ta, i as f64);
                        self.iter_pair(JsValue::Num(i as f64), v)?
                    }
                };
                *index = i + 1;
                self.create_iter_result(result, false)
            }
            IterObj::Str { units, pos } => {
                if *pos >= units.len() {
                    return self.create_iter_result(JsValue::Undefined, true);
                }
                let c0 = units[*pos];
                let take_pair = (0xd800..=0xdbff).contains(&c0)
                    && units
                        .get(*pos + 1)
                        .is_some_and(|c1| (0xdc00..=0xdfff).contains(c1));
                let s: Units = if take_pair {
                    let s = vec![c0, units[*pos + 1]];
                    *pos += 2;
                    s
                } else {
                    *pos += 1;
                    vec![c0]
                };
                self.create_iter_result(JsValue::Str(Rc::new(s)), false)
            }
            IterObj::Map { target, kind, index } => {
                let kind = *kind;
                loop {
                    let Some(m) = *target else {
                        return self.create_iter_result(JsValue::Undefined, true);
                    };
                    let slot = {
                        let ObjKind::MapObj(d) = &self.heap.obj(m).kind else {
                            return Err(Abrupt::Fatal(
                                "map iterator over a non-map (interpreter bug)".to_string(),
                            ));
                        };
                        if *index >= d.entries.len() {
                            None
                        } else {
                            Some(d.entries[*index].clone())
                        }
                    };
                    match slot {
                        None => {
                            *target = None;
                            return self.create_iter_result(JsValue::Undefined, true);
                        }
                        Some(entry) => {
                            *index += 1;
                            if let Some((k, v)) = entry {
                                let result = match kind {
                                    IterKind::Key => k,
                                    IterKind::Value => v,
                                    IterKind::KeyValue => self.iter_pair(k, v)?,
                                };
                                return self.create_iter_result(result, false);
                            }
                            self.charge_loop()?;
                        }
                    }
                }
            }
            IterObj::Set { target, kind, index } => {
                let kind = *kind;
                loop {
                    let Some(s) = *target else {
                        return self.create_iter_result(JsValue::Undefined, true);
                    };
                    let slot = {
                        let ObjKind::SetObj(d) = &self.heap.obj(s).kind else {
                            return Err(Abrupt::Fatal(
                                "set iterator over a non-set (interpreter bug)".to_string(),
                            ));
                        };
                        if *index >= d.entries.len() {
                            None
                        } else {
                            Some(d.entries[*index].clone())
                        }
                    };
                    match slot {
                        None => {
                            *target = None;
                            return self.create_iter_result(JsValue::Undefined, true);
                        }
                        Some(entry) => {
                            *index += 1;
                            if let Some(v) = entry {
                                let result = match kind {
                                    // Set keys === values; entries → [v, v].
                                    IterKind::Key | IterKind::Value => v,
                                    IterKind::KeyValue => self.iter_pair(v.clone(), v)?,
                                };
                                return self.create_iter_result(result, false);
                            }
                            self.charge_loop()?;
                        }
                    }
                }
            }
            IterObj::RegExpString {
                matcher,
                s,
                global,
                full_unicode,
            } => {
                // Step 4: [[Done]] latched.
                let Some(r) = *matcher else {
                    return self.create_iter_result(JsValue::Undefined, true);
                };
                let global = *global;
                let full_unicode = *full_unicode;
                let s_units = Rc::clone(s);
                let rv = JsValue::Obj(r);
                // Step 9: match ← RegExpExec(R, S).
                let m = self.regexp_exec(&rv, &s_units)?;
                // Step 10: null → set [[Done]], return {undefined, true}.
                if matches!(m, JsValue::Null) {
                    *matcher = None;
                    return self.create_iter_result(JsValue::Undefined, true);
                }
                let JsValue::Obj(res) = m else {
                    return Err(self.throw_type_error());
                };
                // Step 11.b: non-global → set [[Done]] after this single match.
                if !global {
                    *matcher = None;
                    return self.create_iter_result(JsValue::Obj(res), false);
                }
                // Step 11.a: global — an empty matchStr advances lastIndex NOW
                // (synchronously, before returning), observably via a custom exec.
                let m0 = self.get_from_object(res, &PropKey::from_str("0"), JsValue::Obj(res))?;
                let match_str = self.to_string_units(&m0)?;
                if match_str.is_empty() {
                    let li = self.get_prop(&rv, &PropKey::from_str("lastIndex"))?;
                    let this_index = to_length_u64(self.to_number(&li)?);
                    let next = advance_string_index(&s_units, this_index, full_unicode);
                    self.set_prop(
                        &rv,
                        &PropKey::from_str("lastIndex"),
                        JsValue::Num(next as f64),
                        true,
                    )?;
                }
                self.create_iter_result(JsValue::Obj(res), false)
            }
        }
    }

    /// CreateArrayFromList(« a, b »): a fresh two-element array.
    fn iter_pair(&mut self, a: JsValue, b: JsValue) -> ERes {
        let arr = self.new_array(2)?;
        self.heap
            .obj_mut(arr)
            .props
            .insert(PropKey::Str(units_from_str("0")), Property::data(a));
        self.heap
            .obj_mut(arr)
            .props
            .insert(PropKey::Str(units_from_str("1")), Property::data(b));
        Ok(JsValue::Obj(arr))
    }
}
