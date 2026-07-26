// Array statics (from/of) and the S1b prototype surface: at/copyWithin/
// every/some/fill/filter/find*/flat*/includes/lastIndexOf/reduce*/reverse/
// shift/unshift/sort/splice/toReversed/toSorted/toSpliced/with — written
// from ECMA-262 with the exact HasProperty/Get/Set/Delete choreography
// (holes are observables) and exact ArraySpeciesCreate.
//
// Sort discipline: the spec fixes the RESULT of sorting under a consistent
// comparator but not the comparison SEQUENCE, which is engine-specific and
// observable through impure comparators. Sorting therefore runs only when
// the comparator is PROVABLY pure (a static AST scan over a conservative
// expression whitelist) and every element is a primitive (so coercions run
// no user code); consistency is verified over a full comparison matrix and
// the result is the unique stable order. Anything else refuses.
//
// Author: Andrew Yates
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

use crate::interp::{Abrupt, ERes, Interp};
use std::rc::Rc;
use trust_js_parse::ast::{DeclKind, Expr, ForInit, Func, Pat, Stmt};
use trust_js_value::{
    to_integer_or_infinity, units_from_str, ErrKind, FnData, JsValue, NativeFn, ObjId, ObjKind,
    PropKey, Units,
};

const MAX_SAFE: u64 = 9_007_199_254_740_991;
/// Comparator-sort element cap (the consistency matrix is O(n²) calls).
const SORT_MATRIX_CAP: usize = 128;

fn key_u64(k: u64) -> PropKey {
    PropKey::Str(units_from_str(&k.to_string()))
}

fn key_f64(k: f64) -> PropKey {
    PropKey::Str(units_from_str(&trust_js_value::js_number_to_string(k)))
}

#[allow(clippy::cast_precision_loss)]
fn u2f(n: u64) -> f64 {
    n as f64
}

impl Interp {
    fn require_callable(&mut self, v: &JsValue) -> Result<(), Abrupt> {
        match v {
            JsValue::Obj(o) if self.heap.obj(*o).is_callable() => Ok(()),
            _ => Err(self.throw_type_error()),
        }
    }

    fn arr_get(&mut self, oid: ObjId, k: u64) -> ERes {
        self.get_from_object(oid, &key_u64(k), JsValue::Obj(oid))
    }

    fn arr_has(&mut self, oid: ObjId, k: u64) -> Result<bool, Abrupt> {
        self.has_property(oid, &key_u64(k))
    }

    fn arr_set(&mut self, oid: ObjId, k: u64, v: JsValue) -> Result<(), Abrupt> {
        self.set_on_object(oid, &key_u64(k), v, true)
    }

    fn set_len(&mut self, oid: ObjId, len: u64) -> Result<(), Abrupt> {
        self.set_on_object(oid, &PropKey::from_str("length"), JsValue::Num(u2f(len)), true)
    }

    fn delete_property_or_throw(&mut self, oid: ObjId, key: &PropKey) -> Result<(), Abrupt> {
        let ok = self.delete_prop(oid, key)?;
        if ok {
            Ok(())
        } else {
            Err(self.throw_type_error())
        }
    }

    /// Relative index clamp (slice family): -∞→0, negative→len+n (≥0),
    /// else min(n, len).
    fn rel_index(&self, t: f64, len: u64) -> u64 {
        if t == f64::NEG_INFINITY {
            0
        } else if t < 0.0 {
            let adjusted = u2f(len) + t;
            if adjusted < 0.0 {
                0
            } else {
                #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
                {
                    adjusted as u64
                }
            }
        } else if t >= u2f(len) {
            len
        } else {
            #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
            {
                t as u64
            }
        }
    }

    #[allow(clippy::too_many_lines)]
    pub(crate) fn dispatch_array(
        &mut self,
        nf: NativeFn,
        this: JsValue,
        args: Vec<JsValue>,
    ) -> ERes {
        let arg = |i: usize| args.get(i).cloned().unwrap_or(JsValue::Undefined);
        use NativeFn as N;
        match nf {
            N::ArrayFrom => self.array_from(&this, &args),
            N::ArrayOf => self.array_of(&this, &args),
            N::ArrayAt => {
                let oid = self.to_object(&this)?;
                let len = self.length_of_array_like(oid)?;
                let rel = to_integer_or_infinity(self.to_number(&arg(0))?);
                let k = if rel >= 0.0 { rel } else { u2f(len) + rel };
                if k < 0.0 || k >= u2f(len) {
                    return Ok(JsValue::Undefined);
                }
                self.get_from_object(oid, &key_f64(k), JsValue::Obj(oid))
            }
            N::ArrayIncludes => {
                let oid = self.to_object(&this)?;
                let len = self.length_of_array_like(oid)?;
                if len == 0 {
                    return Ok(JsValue::Bool(false));
                }
                let target = arg(0);
                let n = to_integer_or_infinity(self.to_number(&arg(1))?);
                if n == f64::INFINITY {
                    return Ok(JsValue::Bool(false));
                }
                let mut k = self.rel_index(n, len);
                while k < len {
                    self.charge_loop()?;
                    let v = self.arr_get(oid, k)?;
                    if crate::ops::same_value_zero(&target, &v) {
                        return Ok(JsValue::Bool(true));
                    }
                    k += 1;
                }
                Ok(JsValue::Bool(false))
            }
            N::ArrayLastIndexOf => {
                let oid = self.to_object(&this)?;
                let len = self.length_of_array_like(oid)?;
                if len == 0 {
                    return Ok(JsValue::Num(-1.0));
                }
                let target = arg(0);
                let n = if args.len() > 1 {
                    to_integer_or_infinity(self.to_number(&arg(1))?)
                } else {
                    u2f(len) - 1.0
                };
                if n == f64::NEG_INFINITY {
                    return Ok(JsValue::Num(-1.0));
                }
                let mut k = if n >= 0.0 {
                    n.min(u2f(len) - 1.0)
                } else {
                    u2f(len) + n
                };
                while k >= 0.0 {
                    self.charge_loop()?;
                    let key = key_f64(k);
                    if self.has_property(oid, &key)? {
                        let v = self.get_from_object(oid, &key, JsValue::Obj(oid))?;
                        if crate::ops::strict_eq(&v, &target) {
                            return Ok(JsValue::Num(k));
                        }
                    }
                    k -= 1.0;
                }
                Ok(JsValue::Num(-1.0))
            }
            N::ArrayEvery | N::ArraySome => {
                let every = matches!(nf, N::ArrayEvery);
                let oid = self.to_object(&this)?;
                let len = self.length_of_array_like(oid)?;
                let cb = arg(0);
                self.require_callable(&cb)?;
                let this_arg = arg(1);
                for k in 0..len {
                    self.charge_loop()?;
                    if !self.arr_has(oid, k)? {
                        continue;
                    }
                    let v = self.arr_get(oid, k)?;
                    let r = self.call_value(
                        &cb,
                        this_arg.clone(),
                        vec![v, JsValue::Num(u2f(k)), JsValue::Obj(oid)],
                    )?;
                    let b = self.to_boolean(&r);
                    if every && !b {
                        return Ok(JsValue::Bool(false));
                    }
                    if !every && b {
                        return Ok(JsValue::Bool(true));
                    }
                }
                Ok(JsValue::Bool(every))
            }
            N::ArrayFilter => {
                let oid = self.to_object(&this)?;
                let len = self.length_of_array_like(oid)?;
                let cb = arg(0);
                self.require_callable(&cb)?;
                let this_arg = arg(1);
                let out = self.array_species_create(oid, 0)?;
                let mut to: u64 = 0;
                for k in 0..len {
                    self.charge_loop()?;
                    if !self.arr_has(oid, k)? {
                        continue;
                    }
                    let v = self.arr_get(oid, k)?;
                    let r = self.call_value(
                        &cb,
                        this_arg.clone(),
                        vec![v.clone(), JsValue::Num(u2f(k)), JsValue::Obj(oid)],
                    )?;
                    if self.to_boolean(&r) {
                        self.create_data_property_or_throw(out, &to.to_string(), v)?;
                        to += 1;
                    }
                }
                Ok(JsValue::Obj(out))
            }
            N::ArrayFind { last, index } => {
                let oid = self.to_object(&this)?;
                let len = self.length_of_array_like(oid)?;
                let cb = arg(0);
                self.require_callable(&cb)?;
                let this_arg = arg(1);
                let order: Box<dyn Iterator<Item = u64>> = if last {
                    Box::new((0..len).rev())
                } else {
                    Box::new(0..len)
                };
                for k in order {
                    self.charge_loop()?;
                    let v = self.arr_get(oid, k)?;
                    let r = self.call_value(
                        &cb,
                        this_arg.clone(),
                        vec![v.clone(), JsValue::Num(u2f(k)), JsValue::Obj(oid)],
                    )?;
                    if self.to_boolean(&r) {
                        return Ok(if index { JsValue::Num(u2f(k)) } else { v });
                    }
                }
                Ok(if index {
                    JsValue::Num(-1.0)
                } else {
                    JsValue::Undefined
                })
            }
            N::ArrayFill => {
                let oid = self.to_object(&this)?;
                let len = self.length_of_array_like(oid)?;
                let value = arg(0);
                let start = {
                    let n = to_integer_or_infinity(self.to_number(&arg(1))?);
                    self.rel_index(n, len)
                };
                let end = if matches!(arg(2), JsValue::Undefined) {
                    len
                } else {
                    let n = to_integer_or_infinity(self.to_number(&arg(2))?);
                    self.rel_index(n, len)
                };
                let mut k = start;
                while k < end {
                    self.charge_loop()?;
                    self.arr_set(oid, k, value.clone())?;
                    k += 1;
                }
                Ok(JsValue::Obj(oid))
            }
            N::ArrayCopyWithin => {
                let oid = self.to_object(&this)?;
                let len = self.length_of_array_like(oid)?;
                let to = {
                    let n = to_integer_or_infinity(self.to_number(&arg(0))?);
                    self.rel_index(n, len)
                };
                let from = {
                    let n = to_integer_or_infinity(self.to_number(&arg(1))?);
                    self.rel_index(n, len)
                };
                let fin = if matches!(arg(2), JsValue::Undefined) {
                    len
                } else {
                    let n = to_integer_or_infinity(self.to_number(&arg(2))?);
                    self.rel_index(n, len)
                };
                let count = (fin.saturating_sub(from)).min(len - to);
                if count > 0 {
                    if from < to && to < from + count {
                        // Copy backwards.
                        let mut i = count;
                        while i > 0 {
                            self.charge_loop()?;
                            i -= 1;
                            let f = from + i;
                            let t = to + i;
                            if self.arr_has(oid, f)? {
                                let v = self.arr_get(oid, f)?;
                                self.arr_set(oid, t, v)?;
                            } else {
                                self.delete_property_or_throw(oid, &key_u64(t))?;
                            }
                        }
                    } else {
                        for i in 0..count {
                            self.charge_loop()?;
                            let f = from + i;
                            let t = to + i;
                            if self.arr_has(oid, f)? {
                                let v = self.arr_get(oid, f)?;
                                self.arr_set(oid, t, v)?;
                            } else {
                                self.delete_property_or_throw(oid, &key_u64(t))?;
                            }
                        }
                    }
                }
                Ok(JsValue::Obj(oid))
            }
            N::ArrayFlat => {
                let oid = self.to_object(&this)?;
                let len = self.length_of_array_like(oid)?;
                let depth = if matches!(arg(0), JsValue::Undefined) {
                    1.0
                } else {
                    to_integer_or_infinity(self.to_number(&arg(0))?)
                };
                let out = self.array_species_create(oid, 0)?;
                self.flatten_into_array(out, oid, len, 0.0, depth, None)?;
                Ok(JsValue::Obj(out))
            }
            N::ArrayFlatMap => {
                let oid = self.to_object(&this)?;
                let len = self.length_of_array_like(oid)?;
                let cb = arg(0);
                self.require_callable(&cb)?;
                let this_arg = arg(1);
                let out = self.array_species_create(oid, 0)?;
                self.flatten_into_array(out, oid, len, 0.0, 1.0, Some((&cb, &this_arg)))?;
                Ok(JsValue::Obj(out))
            }
            N::ArrayReduce { right } => {
                let oid = self.to_object(&this)?;
                let len = self.length_of_array_like(oid)?;
                let cb = arg(0);
                self.require_callable(&cb)?;
                let has_init = args.len() > 1;
                if len == 0 && !has_init {
                    return Err(self.throw_type_error());
                }
                let order: Box<dyn Iterator<Item = u64>> = if right {
                    Box::new((0..len).rev())
                } else {
                    Box::new(0..len)
                };
                let mut iter = order;
                let mut acc = if has_init {
                    arg(1)
                } else {
                    // First present element, or TypeError.
                    let mut found: Option<JsValue> = None;
                    for k in iter.by_ref() {
                        self.charge_loop()?;
                        if self.arr_has(oid, k)? {
                            found = Some(self.arr_get(oid, k)?);
                            break;
                        }
                    }
                    match found {
                        Some(v) => v,
                        None => return Err(self.throw_type_error()),
                    }
                };
                for k in iter {
                    self.charge_loop()?;
                    if !self.arr_has(oid, k)? {
                        continue;
                    }
                    let v = self.arr_get(oid, k)?;
                    acc = self.call_value(
                        &cb,
                        JsValue::Undefined,
                        vec![acc, v, JsValue::Num(u2f(k)), JsValue::Obj(oid)],
                    )?;
                }
                Ok(acc)
            }
            N::ArrayReverse => {
                let oid = self.to_object(&this)?;
                let len = self.length_of_array_like(oid)?;
                let middle = len / 2;
                let mut lower: u64 = 0;
                while lower != middle {
                    self.charge_loop()?;
                    let upper = len - lower - 1;
                    let lower_exists = self.arr_has(oid, lower)?;
                    let lower_value = if lower_exists {
                        Some(self.arr_get(oid, lower)?)
                    } else {
                        None
                    };
                    let upper_exists = self.arr_has(oid, upper)?;
                    let upper_value = if upper_exists {
                        Some(self.arr_get(oid, upper)?)
                    } else {
                        None
                    };
                    match (lower_value, upper_value) {
                        (Some(lv), Some(uv)) => {
                            self.arr_set(oid, lower, uv)?;
                            self.arr_set(oid, upper, lv)?;
                        }
                        (None, Some(uv)) => {
                            self.arr_set(oid, lower, uv)?;
                            self.delete_property_or_throw(oid, &key_u64(upper))?;
                        }
                        (Some(lv), None) => {
                            self.delete_property_or_throw(oid, &key_u64(lower))?;
                            self.arr_set(oid, upper, lv)?;
                        }
                        (None, None) => {}
                    }
                    lower += 1;
                }
                Ok(JsValue::Obj(oid))
            }
            N::ArrayShift => {
                let oid = self.to_object(&this)?;
                let len = self.length_of_array_like(oid)?;
                if len == 0 {
                    self.set_len(oid, 0)?;
                    return Ok(JsValue::Undefined);
                }
                let first = self.arr_get(oid, 0)?;
                for k in 1..len {
                    self.charge_loop()?;
                    if self.arr_has(oid, k)? {
                        let v = self.arr_get(oid, k)?;
                        self.arr_set(oid, k - 1, v)?;
                    } else {
                        self.delete_property_or_throw(oid, &key_u64(k - 1))?;
                    }
                }
                self.delete_property_or_throw(oid, &key_u64(len - 1))?;
                self.set_len(oid, len - 1)?;
                Ok(first)
            }
            N::ArrayUnshift => {
                let oid = self.to_object(&this)?;
                let len = self.length_of_array_like(oid)?;
                let argc = args.len() as u64;
                if argc > 0 {
                    if len + argc > MAX_SAFE {
                        return Err(self.throw_type_error());
                    }
                    let mut k = len;
                    while k > 0 {
                        self.charge_loop()?;
                        let from = k - 1;
                        let to = k + argc - 1;
                        if self.arr_has(oid, from)? {
                            let v = self.arr_get(oid, from)?;
                            self.arr_set(oid, to, v)?;
                        } else {
                            self.delete_property_or_throw(oid, &key_u64(to))?;
                        }
                        k -= 1;
                    }
                    for (j, v) in args.iter().enumerate() {
                        self.arr_set(oid, j as u64, v.clone())?;
                    }
                }
                self.set_len(oid, len + argc)?;
                Ok(JsValue::Num(u2f(len + argc)))
            }
            N::ArraySplice => self.array_splice(&this, &args),
            N::ArraySort => self.array_sort(&this, &arg(0)),
            N::ArrayToSorted => self.array_to_sorted(&this, &arg(0)),
            N::ArrayToReversed => {
                let oid = self.to_object(&this)?;
                let len = self.length_of_array_like(oid)?;
                let out = self.array_create_checked(len)?;
                for k in 0..len {
                    self.charge_loop()?;
                    let v = self.arr_get(oid, len - k - 1)?;
                    self.create_data_property_or_throw(out, &k.to_string(), v)?;
                }
                Ok(JsValue::Obj(out))
            }
            N::ArrayWith => {
                let oid = self.to_object(&this)?;
                let len = self.length_of_array_like(oid)?;
                let rel = to_integer_or_infinity(self.to_number(&arg(0))?);
                let actual = if rel >= 0.0 { rel } else { u2f(len) + rel };
                if actual >= u2f(len) || actual < 0.0 {
                    return Err(self.throw_native(ErrKind::Range));
                }
                let value = arg(1);
                let out = self.array_create_checked(len)?;
                for k in 0..len {
                    self.charge_loop()?;
                    let v = if u2f(k) == actual {
                        value.clone()
                    } else {
                        self.arr_get(oid, k)?
                    };
                    self.create_data_property_or_throw(out, &k.to_string(), v)?;
                }
                Ok(JsValue::Obj(out))
            }
            N::ArrayToSpliced => self.array_to_spliced(&this, &args),
            _ => Err(Abrupt::Fatal("unrouted Array native (interpreter bug)".to_string())),
        }
    }

    fn array_create_checked(&mut self, len: u64) -> Result<ObjId, Abrupt> {
        let Ok(len32) = u32::try_from(len) else {
            return Err(self.throw_native(ErrKind::Range));
        };
        self.new_array(len32)
    }

    /// The Array.from target A: `Construct(C)` for a non-%Array% constructor,
    /// else `ArrayCreate(0)`.
    fn array_from_new_target(&mut self, c: &JsValue) -> Result<ObjId, Abrupt> {
        if self.is_constructor(c) && !matches!(c, JsValue::Obj(o) if *o == self.intr.array_ctor) {
            let av = self.construct(c, vec![], None)?;
            let JsValue::Obj(ao) = av else {
                return Err(Abrupt::Fatal("constructor returned non-object".to_string()));
            };
            Ok(ao)
        } else {
            self.new_array(0)
        }
    }

    /// The Array.from iterate loop (fast or user iterator). A step throw
    /// propagates without close; a throw from the mapping call or the property
    /// definition runs IteratorClose.
    fn array_from_iterate(
        &mut self,
        mut it: crate::destr::FastIter,
        a: ObjId,
        mapping: bool,
        mapfn: &JsValue,
        this_arg: &JsValue,
    ) -> ERes {
        let mut k: u64 = 0;
        loop {
            self.charge_loop()?;
            let v = match self.fast_iter_next(&mut it) {
                Ok(Some(v)) => v,
                Ok(None) => break,
                Err(a) => return Err(a),
            };
            let body = (|s: &mut Self| -> Result<(), Abrupt> {
                let mapped = if mapping {
                    s.call_value(mapfn, this_arg.clone(), vec![v, JsValue::Num(u2f(k))])?
                } else {
                    v
                };
                s.create_data_property_or_throw(a, &k.to_string(), mapped)?;
                Ok(())
            })(self);
            if let Err(e) = body {
                return Err(self.close_after_body_abrupt(&it, e));
            }
            k += 1;
        }
        self.set_len(a, k)?;
        Ok(JsValue::Obj(a))
    }

    /// Array.from (23.1.2.1): fast-iterator path for provably-untampered
    /// iterables; the full iterator protocol for user iterables; array-like
    /// path otherwise.
    fn array_from(&mut self, c: &JsValue, args: &[JsValue]) -> ERes {
        let items = args.first().cloned().unwrap_or(JsValue::Undefined);
        let mapfn = args.get(1).cloned().unwrap_or(JsValue::Undefined);
        let mapping = if matches!(mapfn, JsValue::Undefined) {
            false
        } else {
            self.require_callable(&mapfn)?;
            true
        };
        let this_arg = args.get(2).cloned().unwrap_or(JsValue::Undefined);
        // Fast-iterator eligibility (pristine arrays/arguments/strings) — the
        // @@iterator GetMethod and its intrinsic result have no observable
        // side effect, so the provably-untampered fast path is exact.
        if let Ok(it) = self.get_fast_iterator(&items) {
            let a = self.array_from_new_target(c)?;
            return self.array_from_iterate(it, a, mapping, &mapfn, &this_arg);
        }
        // Otherwise GetMethod(items, @@iterator): a modeled hit drives the
        // full iterator protocol (S1e); a danger hop refuses inside get_method.
        let ikey = PropKey::Sym(trust_js_value::SymId::WellKnown(
            trust_js_value::WkSym::Iterator,
        ));
        if let Some(using) = self.get_method(&items, &ikey)? {
            let a = self.array_from_new_target(c)?;
            let iterator = self.call_value(&using, items.clone(), vec![])?;
            let JsValue::Obj(io) = iterator else {
                return Err(self.throw_type_error());
            };
            let next = self.get_from_object(io, &PropKey::from_str("next"), iterator.clone())?;
            let it = crate::destr::FastIter::User {
                iter: io,
                next,
                done: false,
            };
            return self.array_from_iterate(it, a, mapping, &mapfn, &this_arg);
        }
        // Array-like path (no @@iterator anywhere on a modeled chain).
        if items.is_nullish() {
            return Err(self.throw_type_error());
        }
        let array_like = self.to_object(&items)?;
        let len = self.length_of_array_like(array_like)?;
        let a = if self.is_constructor(c) && !matches!(c, JsValue::Obj(o) if *o == self.intr.array_ctor)
        {
            let av = self.construct(c, vec![JsValue::Num(u2f(len))], None)?;
            let JsValue::Obj(ao) = av else {
                return Err(Abrupt::Fatal("constructor returned non-object".to_string()));
            };
            ao
        } else {
            self.array_create_checked(len)?
        };
        for k in 0..len {
            self.charge_loop()?;
            let v = self.arr_get(array_like, k)?;
            let mapped = if mapping {
                self.call_value(&mapfn, this_arg.clone(), vec![v, JsValue::Num(u2f(k))])?
            } else {
                v
            };
            self.create_data_property_or_throw(a, &k.to_string(), mapped)?;
        }
        self.set_len(a, len)?;
        Ok(JsValue::Obj(a))
    }

    /// Array.of (23.1.2.3).
    fn array_of(&mut self, c: &JsValue, args: &[JsValue]) -> ERes {
        let len = args.len() as u64;
        let a = if self.is_constructor(c) && !matches!(c, JsValue::Obj(o) if *o == self.intr.array_ctor)
        {
            let av = self.construct(c, vec![JsValue::Num(u2f(len))], None)?;
            let JsValue::Obj(ao) = av else {
                return Err(Abrupt::Fatal("constructor returned non-object".to_string()));
            };
            ao
        } else {
            self.array_create_checked(len)?
        };
        for (k, v) in args.iter().enumerate() {
            self.charge_loop()?;
            self.create_data_property_or_throw(a, &k.to_string(), v.clone())?;
        }
        self.set_len(a, len)?;
        Ok(JsValue::Obj(a))
    }

    /// FlattenIntoArray (23.1.3.13.1).
    #[allow(clippy::too_many_arguments)]
    fn flatten_into_array(
        &mut self,
        target: ObjId,
        source: ObjId,
        source_len: u64,
        start: f64,
        depth: f64,
        mapper: Option<(&JsValue, &JsValue)>,
    ) -> Result<f64, Abrupt> {
        let mut target_index = start;
        for k in 0..source_len {
            self.charge_loop()?;
            if !self.arr_has(source, k)? {
                continue;
            }
            let mut element = self.arr_get(source, k)?;
            if let Some((cb, this_arg)) = mapper {
                element = self.call_value(
                    cb,
                    (*this_arg).clone(),
                    vec![element, JsValue::Num(u2f(k)), JsValue::Obj(source)],
                )?;
            }
            let should_flatten = if depth > 0.0 {
                // IsArray recurses through a proxy target (revoked → TypeError).
                match &element {
                    JsValue::Obj(o) => self.is_array_exotic(*o)?,
                    _ => false,
                }
            } else {
                false
            };
            if should_flatten {
                let JsValue::Obj(eo) = element else { unreachable!() };
                let elen = self.length_of_array_like(eo)?;
                let new_depth = if depth == f64::INFINITY { depth } else { depth - 1.0 };
                target_index =
                    self.flatten_into_array(target, eo, elen, target_index, new_depth, None)?;
            } else {
                if target_index >= u2f(MAX_SAFE) {
                    return Err(self.throw_type_error());
                }
                let key = trust_js_value::js_number_to_string(target_index);
                self.create_data_property_or_throw(target, &key, element)?;
                target_index += 1.0;
            }
        }
        Ok(target_index)
    }

    /// Array.prototype.splice (23.1.3.31).
    fn array_splice(&mut self, this: &JsValue, args: &[JsValue]) -> ERes {
        let oid = self.to_object(this)?;
        let len = self.length_of_array_like(oid)?;
        let rel_start = if args.is_empty() {
            0.0
        } else {
            to_integer_or_infinity(self.to_number(&args[0])?)
        };
        let actual_start = self.rel_index(rel_start, len);
        let (insert_count, actual_delete): (u64, u64) = if args.is_empty() {
            (0, 0)
        } else if args.len() == 1 {
            (0, len - actual_start)
        } else {
            let ic = (args.len() - 2) as u64;
            let dc = to_integer_or_infinity(self.to_number(&args[1])?);
            let max_del = len - actual_start;
            let dc = if dc <= 0.0 {
                0
            } else if dc >= u2f(max_del) {
                max_del
            } else {
                #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
                {
                    dc as u64
                }
            };
            (ic, dc)
        };
        if len + insert_count - actual_delete > MAX_SAFE {
            return Err(self.throw_type_error());
        }
        let a = self.array_species_create(oid, actual_delete)?;
        for k in 0..actual_delete {
            self.charge_loop()?;
            let from = actual_start + k;
            if self.arr_has(oid, from)? {
                let v = self.arr_get(oid, from)?;
                self.create_data_property_or_throw(a, &k.to_string(), v)?;
            }
        }
        self.set_len(a, actual_delete)?;
        let items: Vec<JsValue> = if args.len() > 2 {
            args[2..].to_vec()
        } else {
            Vec::new()
        };
        let item_count = items.len() as u64;
        if item_count < actual_delete {
            let mut k = actual_start;
            while k < len - actual_delete {
                self.charge_loop()?;
                let from = k + actual_delete;
                let to = k + item_count;
                if self.arr_has(oid, from)? {
                    let v = self.arr_get(oid, from)?;
                    self.arr_set(oid, to, v)?;
                } else {
                    self.delete_property_or_throw(oid, &key_u64(to))?;
                }
                k += 1;
            }
            let mut k = len;
            while k > len - actual_delete + item_count {
                self.charge_loop()?;
                self.delete_property_or_throw(oid, &key_u64(k - 1))?;
                k -= 1;
            }
        } else if item_count > actual_delete {
            let mut k = len - actual_delete;
            while k > actual_start {
                self.charge_loop()?;
                let from = k + actual_delete - 1;
                let to = k + item_count - 1;
                if self.arr_has(oid, from)? {
                    let v = self.arr_get(oid, from)?;
                    self.arr_set(oid, to, v)?;
                } else {
                    self.delete_property_or_throw(oid, &key_u64(to))?;
                }
                k -= 1;
            }
        }
        let mut k = actual_start;
        for item in items {
            self.arr_set(oid, k, item)?;
            k += 1;
        }
        self.set_len(oid, len - actual_delete + item_count)?;
        Ok(JsValue::Obj(a))
    }

    /// Array.prototype.toSpliced (23.1.3.35).
    fn array_to_spliced(&mut self, this: &JsValue, args: &[JsValue]) -> ERes {
        let oid = self.to_object(this)?;
        let len = self.length_of_array_like(oid)?;
        let rel_start = if args.is_empty() {
            0.0
        } else {
            to_integer_or_infinity(self.to_number(&args[0])?)
        };
        let actual_start = self.rel_index(rel_start, len);
        let (insert_count, actual_skip): (u64, u64) = if args.is_empty() {
            (0, 0)
        } else if args.len() == 1 {
            (0, len - actual_start)
        } else {
            let ic = (args.len() - 2) as u64;
            let sc = to_integer_or_infinity(self.to_number(&args[1])?);
            let max_skip = len - actual_start;
            let sc = if sc <= 0.0 {
                0
            } else if sc >= u2f(max_skip) {
                max_skip
            } else {
                #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
                {
                    sc as u64
                }
            };
            (ic, sc)
        };
        let new_len = len + insert_count - actual_skip;
        if new_len > MAX_SAFE {
            return Err(self.throw_type_error());
        }
        let a = self.array_create_checked(new_len)?;
        let mut i: u64 = 0;
        let mut r = actual_start + actual_skip;
        while i < actual_start {
            self.charge_loop()?;
            let v = self.arr_get(oid, i)?;
            self.create_data_property_or_throw(a, &i.to_string(), v)?;
            i += 1;
        }
        if args.len() > 2 {
            for item in &args[2..] {
                self.create_data_property_or_throw(a, &i.to_string(), item.clone())?;
                i += 1;
            }
        }
        while i < new_len {
            self.charge_loop()?;
            let v = self.arr_get(oid, r)?;
            self.create_data_property_or_throw(a, &i.to_string(), v)?;
            i += 1;
            r += 1;
        }
        Ok(JsValue::Obj(a))
    }

    // -- sort ----------------------------------------------------------------

    /// Array.prototype.sort (23.1.3.30).
    fn array_sort(&mut self, this: &JsValue, comparator: &JsValue) -> ERes {
        if !matches!(comparator, JsValue::Undefined) {
            self.require_callable(comparator)?;
        }
        let oid = self.to_object(this)?;
        let len = self.length_of_array_like(oid)?;
        // SortIndexedProperties: read phase, holes skipped.
        let mut items: Vec<JsValue> = Vec::new();
        for k in 0..len {
            self.charge_loop()?;
            if self.arr_has(oid, k)? {
                items.push(self.arr_get(oid, k)?);
            }
        }
        let sorted = self.sort_items(items, comparator)?;
        let item_count = sorted.len() as u64;
        for (j, v) in sorted.into_iter().enumerate() {
            self.charge_loop()?;
            self.arr_set(oid, j as u64, v)?;
        }
        for j in item_count..len {
            self.charge_loop()?;
            self.delete_property_or_throw(oid, &key_u64(j))?;
        }
        Ok(JsValue::Obj(oid))
    }

    /// Array.prototype.toSorted (23.1.3.34): holes read through as
    /// undefined; result is a plain array (no species).
    fn array_to_sorted(&mut self, this: &JsValue, comparator: &JsValue) -> ERes {
        if !matches!(comparator, JsValue::Undefined) {
            self.require_callable(comparator)?;
        }
        let oid = self.to_object(this)?;
        let len = self.length_of_array_like(oid)?;
        let out = self.array_create_checked(len)?;
        let mut items: Vec<JsValue> = Vec::with_capacity(usize::try_from(len).unwrap_or(0));
        for k in 0..len {
            self.charge_loop()?;
            items.push(self.arr_get(oid, k)?);
        }
        let sorted = self.sort_items(items, comparator)?;
        for (j, v) in sorted.into_iter().enumerate() {
            self.charge_loop()?;
            self.create_data_property_or_throw(out, &j.to_string(), v)?;
        }
        Ok(JsValue::Obj(out))
    }

    /// The exactness-gated sort core (see the module header).
    fn sort_items(&mut self, items: Vec<JsValue>, comparator: &JsValue) -> Result<Vec<JsValue>, Abrupt> {
        if items.len() <= 1 {
            return Ok(items);
        }
        if matches!(comparator, JsValue::Undefined) {
            return self.sort_default(items);
        }
        // User comparator: provably-pure comparator + primitive elements.
        if items
            .iter()
            .any(|v| matches!(v, JsValue::Obj(_) | JsValue::Sym(_) | JsValue::BigInt(_)))
        {
            return Err(Abrupt::Fatal(
                "comparator sort over non-primitive elements (coercion order engine-specific)"
                    .to_string(),
            ));
        }
        if !comparator_provably_pure(self, comparator) {
            return Err(Abrupt::Fatal(
                "comparator with potentially observable effects (call sequence engine-specific)"
                    .to_string(),
            ));
        }
        if items.len() > SORT_MATRIX_CAP {
            return Err(Abrupt::Fatal(
                "comparator sort beyond the consistency-matrix cap".to_string(),
            ));
        }
        let n = items.len();
        // Full comparison matrix (extra calls are unobservable: pure).
        let mut sign = vec![vec![0i8; n]; n];
        for i in 0..n {
            for j in 0..n {
                if i == j {
                    continue;
                }
                self.charge_loop()?;
                let r = match self.call_value(
                    comparator,
                    JsValue::Undefined,
                    vec![items[i].clone(), items[j].clone()],
                ) {
                    Ok(r) => r,
                    Err(Abrupt::Throw(_)) => {
                        return Err(Abrupt::Fatal(
                            "throwing comparator (pair coverage engine-specific)".to_string(),
                        ))
                    }
                    Err(e) => return Err(e),
                };
                let x = self.to_number(&r)?;
                sign[i][j] = if x.is_nan() || x == 0.0 {
                    0
                } else if x < 0.0 {
                    -1
                } else {
                    1
                };
            }
        }
        // Consistency: antisymmetry + transitivity of ≤ ⇒ a total preorder,
        // under which the stable sort result is unique.
        for i in 0..n {
            for j in 0..n {
                if i != j && sign[i][j] != -sign[j][i] {
                    return Err(Abrupt::Fatal(
                        "inconsistent comparator (result implementation-defined)".to_string(),
                    ));
                }
            }
        }
        for i in 0..n {
            for j in 0..n {
                for k in 0..n {
                    if sign[i][j] <= 0 && sign[j][k] <= 0 && sign[i][k] > 0 {
                        return Err(Abrupt::Fatal(
                            "inconsistent comparator (result implementation-defined)".to_string(),
                        ));
                    }
                }
            }
        }
        let mut idx: Vec<usize> = (0..n).collect();
        idx.sort_by(|&a, &b| sign[a][b].cmp(&0));
        Ok(idx.into_iter().map(|i| items[i].clone()).collect())
    }

    /// Default SortCompare: undefined last; ToString + code-unit order.
    /// Object elements refuse (their ToString may run user code whose call
    /// count is engine-specific); a symbol among ≥2 non-undefined elements
    /// throws TypeError exactly.
    fn sort_default(&mut self, items: Vec<JsValue>) -> Result<Vec<JsValue>, Abrupt> {
        if items.iter().any(|v| matches!(v, JsValue::Obj(_))) {
            return Err(Abrupt::Fatal(
                "default sort over object elements (ToString call count engine-specific)"
                    .to_string(),
            ));
        }
        let non_undef: Vec<&JsValue> = items
            .iter()
            .filter(|v| !matches!(v, JsValue::Undefined))
            .collect();
        if non_undef.len() >= 2 && non_undef.iter().any(|v| matches!(v, JsValue::Sym(_))) {
            // Any comparison involving a symbol runs ToString(symbol).
            return Err(self.throw_type_error());
        }
        let mut keyed: Vec<(Units, JsValue)> = Vec::new();
        let mut undef_count = 0usize;
        for v in items {
            if matches!(v, JsValue::Undefined) {
                undef_count += 1;
            } else {
                let key = self.to_string_units(&v)?;
                keyed.push((key, v));
            }
        }
        keyed.sort_by(|a, b| a.0.cmp(&b.0));
        let mut out: Vec<JsValue> = keyed.into_iter().map(|(_, v)| v).collect();
        out.extend(std::iter::repeat_n(JsValue::Undefined, undef_count));
        Ok(out)
    }
}

// ---------------------------------------------------------------------------
// Comparator purity: a conservative static whitelist over the AST.
// ---------------------------------------------------------------------------

/// True iff the comparator is a user function whose every evaluation is
/// provably free of observable effects over PRIMITIVE arguments: parameters
/// are plain identifiers, all referenced names are locals/parameters, and
/// only effect-free expression forms occur (no calls, member access,
/// assignments to non-locals, `this`, object/array/function literals, ...).
fn comparator_provably_pure(it: &Interp, comparator: &JsValue) -> bool {
    let JsValue::Obj(o) = comparator else {
        return false;
    };
    let ObjKind::Function(FnData::User(uf)) = &it.heap.obj(*o).kind else {
        return false;
    };
    let f: &Rc<Func> = &uf.func;
    if f.is_async || f.is_gen {
        return false;
    }
    let mut locals: Vec<String> = Vec::new();
    for p in &f.params {
        match p {
            Pat::Ident(n) => locals.push(n.clone()),
            _ => return false,
        }
    }
    if let Some(e) = &f.expr_body {
        collect_locals_ok(&[], &mut locals) && pure_expr(e, &locals)
    } else {
        let mut ls = locals;
        if !collect_locals_ok(&f.body, &mut ls) {
            return false;
        }
        f.body.iter().all(|s| pure_stmt(s, &ls))
    }
}

/// Collect all identifier declarations (var/let/const, any nesting we
/// accept); false = an unsupported declaration shape appears.
fn collect_locals_ok(stmts: &[Stmt], out: &mut Vec<String>) -> bool {
    for s in stmts {
        match s {
            Stmt::Decl { decls, kind } => {
                // `var` only: let/const reads can hit a TDZ (a conditional
                // ReferenceError whose pair coverage is engine-specific).
                if !matches!(kind, DeclKind::Var) {
                    return false;
                }
                for (pat, _) in decls {
                    match pat {
                        Pat::Ident(n) => out.push(n.clone()),
                        _ => return false,
                    }
                }
            }
            Stmt::Block(b) => {
                if !collect_locals_ok(b, out) {
                    return false;
                }
            }
            Stmt::If { cons, alt, .. } => {
                if !collect_locals_ok(std::slice::from_ref(cons), out) {
                    return false;
                }
                if let Some(a) = alt {
                    if !collect_locals_ok(std::slice::from_ref(a), out) {
                        return false;
                    }
                }
            }
            Stmt::While { body, .. } | Stmt::DoWhile { body, .. } => {
                if !collect_locals_ok(std::slice::from_ref(body), out) {
                    return false;
                }
            }
            Stmt::For { init, body, .. } => {
                if let Some(ForInit::Decl(kind, decls)) = init {
                    if !matches!(kind, DeclKind::Var) {
                        return false;
                    }
                    for (pat, _) in decls {
                        match pat {
                            Pat::Ident(n) => out.push(n.clone()),
                            _ => return false,
                        }
                    }
                }
                if !collect_locals_ok(std::slice::from_ref(body), out) {
                    return false;
                }
            }
            Stmt::Expr(_) | Stmt::Return(_) | Stmt::Empty | Stmt::Break(_) | Stmt::Continue(_) => {}
            _ => return false,
        }
    }
    true
}

fn pure_stmt(s: &Stmt, locals: &[String]) -> bool {
    match s {
        Stmt::Expr(e) => pure_expr(e, locals),
        Stmt::Return(e) => e.as_ref().is_none_or(|e| pure_expr(e, locals)),
        Stmt::Empty | Stmt::Break(None) | Stmt::Continue(None) => true,
        Stmt::Block(b) => b.iter().all(|st| pure_stmt(st, locals)),
        Stmt::If { test, cons, alt } => {
            pure_expr(test, locals)
                && pure_stmt(cons, locals)
                && alt.as_ref().is_none_or(|a| pure_stmt(a, locals))
        }
        Stmt::While { test, body } | Stmt::DoWhile { body, test } => {
            pure_expr(test, locals) && pure_stmt(body, locals)
        }
        Stmt::For {
            init,
            test,
            update,
            body,
        } => {
            let init_ok = match init {
                None => true,
                Some(ForInit::Expr(e)) => pure_expr(e, locals),
                Some(ForInit::Decl(_, decls)) => decls
                    .iter()
                    .all(|(_, e)| e.as_ref().is_none_or(|e| pure_expr(e, locals))),
            };
            init_ok
                && test.as_ref().is_none_or(|e| pure_expr(e, locals))
                && update.as_ref().is_none_or(|e| pure_expr(e, locals))
                && pure_stmt(body, locals)
        }
        Stmt::Decl { decls, .. } => decls
            .iter()
            .all(|(_, e)| e.as_ref().is_none_or(|e| pure_expr(e, locals))),
        _ => false,
    }
}

fn pure_expr(e: &Expr, locals: &[String]) -> bool {
    match e {
        Expr::Ident(n) => locals.contains(n),
        Expr::Num(_) | Expr::Str { .. } | Expr::Bool(_) | Expr::Null => true,
        Expr::Paren(inner) => pure_expr(inner, locals),
        Expr::Unary { op, arg } => {
            matches!(*op, "!" | "-" | "+" | "~" | "typeof" | "void") && pure_expr(arg, locals)
        }
        Expr::Binary { op, left, right } => {
            !matches!(*op, "in" | "instanceof")
                && pure_expr(left, locals)
                && pure_expr(right, locals)
        }
        Expr::Logical { left, right, .. } => pure_expr(left, locals) && pure_expr(right, locals),
        Expr::Cond { test, cons, alt } => {
            pure_expr(test, locals) && pure_expr(cons, locals) && pure_expr(alt, locals)
        }
        Expr::Seq(es) => es.iter().all(|e| pure_expr(e, locals)),
        // Assignment/update only to locals (invisible outside the call).
        Expr::Assign { op: _, target, value } => {
            matches!(target.as_ref(), Pat::Ident(n) if locals.contains(n))
                && pure_expr(value, locals)
        }
        Expr::Update { arg, .. } => {
            matches!(arg.as_ref(), Expr::Ident(n) if locals.contains(n))
        }
        _ => false,
    }
}
