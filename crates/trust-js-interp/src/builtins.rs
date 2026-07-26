// Native builtin dispatch: the modeled standard-library surface, written
// from the spec algorithms (argument coercion order is observable and
// preserved). Anything outside the modeled surface refuses via the danger
// tables before it can dispatch.
//
// Author: Andrew Yates
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

use crate::interp::{Abrupt, ERes, Interp, MAX_STRING_UNITS};
use crate::props::PartialDesc;
use std::rc::Rc;
use trust_js_trace::HostEvent;
use trust_js_value::{
    exact_uint32, js_number_to_string, to_integer_or_infinity, to_length_u64, units_from_str,
    ErrKind, JsValue, NativeFn, ObjId, ObjKind, PropKey, PropValue, Property, SymId, Units, WkSym,
    WrapperPrim,
};

impl Interp {
    /// Refuse an output recording the trace driver could not perform. The
    /// driver records every `console.*`/`print` effect into JS arrays
    /// (`vs.push(project(arg))` per argument, then `events.push({k, v})`), so a
    /// user-installed poisoning INDEXED property on `Array.prototype` /
    /// `Object.prototype` — an accessor, or a non-writable data property, at an
    /// index one of those pushes would write — makes the driver throw and DROP
    /// the event on BOTH engines (a projection artifact, not a JS semantic).
    /// The Rust-Vec recorder here does not share that artifact, so recording
    /// the event would diverge: refuse instead (a sound no-coverage). A fresh
    /// `[].push` writes indices `0..n_args` for the per-event array and the
    /// current event count for the shared array; a WRITABLE inherited data
    /// property is fine (Set makes an own array property and shadows it).
    fn guard_driver_output_recording(&self, n_args: usize) -> Result<(), Abrupt> {
        let event_idx = self.events.len() as u64;
        let poisoned = (0..n_args as u64)
            .chain(std::iter::once(event_idx))
            .any(|i| self.array_push_index_poisoned(i));
        if poisoned {
            return Err(Abrupt::Fatal(
                "output recording while Array/Object.prototype carries a poisoning indexed \
                 property (trace-driver projection artifact; out of slice)"
                    .to_string(),
            ));
        }
        Ok(())
    }

    /// Would a fresh array's `push` writing own index `i` throw because a
    /// prototype on the chain (`Array.prototype`, then `Object.prototype`)
    /// carries a poisoning own property at that index — an accessor (setter
    /// call / unwritable), or a non-writable data property? The FIRST prototype
    /// with an own `i` decides (a writable data property shadows and succeeds).
    fn array_push_index_poisoned(&self, i: u64) -> bool {
        let key = PropKey::from_str(&i.to_string());
        for proto in [self.intr.array_proto, self.intr.object_proto] {
            if let Some(p) = self.heap.obj(proto).props.get(&key) {
                return match &p.v {
                    PropValue::Accessor { .. } => true,
                    PropValue::Data { writable, .. } => !writable,
                };
            }
        }
        false
    }

    #[allow(clippy::too_many_lines)]
    pub(crate) fn dispatch_native(
        &mut self,
        nf: NativeFn,
        fid: ObjId,
        this: JsValue,
        args: Vec<JsValue>,
        new_target: Option<JsValue>,
    ) -> ERes {
        let arg = |i: usize| args.get(i).cloned().unwrap_or(JsValue::Undefined);
        match nf {
            NativeFn::FunctionProtoSelf => Ok(JsValue::Undefined),
            NativeFn::FunProtoCall => {
                let rest: Vec<JsValue> = args.iter().skip(1).cloned().collect();
                self.call_value(&this, arg(0), rest)
            }
            NativeFn::FunProtoApply => {
                let arg_array = arg(1);
                let list = if arg_array.is_nullish() {
                    Vec::new()
                } else {
                    let JsValue::Obj(ao) = arg_array else {
                        return Err(self.throw_type_error());
                    };
                    self.create_list_from_array_like(ao)?
                };
                self.call_value(&this, arg(0), list)
            }
            NativeFn::FunProtoBind => {
                let JsValue::Obj(target) = this else {
                    return Err(self.throw_type_error());
                };
                if !self.heap.obj(target).is_callable() {
                    return Err(self.throw_type_error());
                }
                let bound_args: Vec<JsValue> = args.iter().skip(1).cloned().collect();
                let bf = self.make_bound_function(target, arg(0), bound_args)?;
                Ok(JsValue::Obj(bf))
            }
            NativeFn::FunctionCtor => self.create_dynamic_function(&args, new_target.as_ref()),
            NativeFn::AsyncFunctionCtor => {
                self.create_dynamic_function_kind(&args, new_target.as_ref(), true)
            }
            NativeFn::FunProtoHasInstance => {
                // %Function.prototype[Symbol.hasInstance]% (20.2.3.6):
                // OrdinaryHasInstance(this, V).
                let JsValue::Obj(c) = this else {
                    return Ok(JsValue::Bool(false));
                };
                Ok(JsValue::Bool(self.ordinary_has_instance(c, &arg(0))?))
            }
            NativeFn::EvalFn => self.eval_indirect(arg(0)),
            NativeFn::SpeciesGetter => Ok(this),
            NativeFn::ObjectCtor => {
                // 20.1.1.1: subclass path when NewTarget is another ctor.
                if let Some(ntv) = &new_target {
                    if !matches!(ntv, JsValue::Obj(o) if *o == fid) {
                        let proto =
                            self.get_prototype_from_constructor(ntv, self.intr.object_proto)?;
                        let oid = self
                            .alloc_obj(trust_js_value::JsObject::new(ObjKind::Plain, Some(proto)))?;
                        return Ok(JsValue::Obj(oid));
                    }
                }
                match arg(0) {
                    JsValue::Undefined | JsValue::Null => Ok(JsValue::Obj(self.new_plain()?)),
                    JsValue::Obj(oid) => Ok(JsValue::Obj(oid)),
                    prim => Ok(JsValue::Obj(self.to_object(&prim)?)),
                }
            }
            NativeFn::ObjectKeys => {
                let a0 = arg(0);
                let oid = self.to_object(&a0)?;
                let keys = self.enumerable_own_string_keys(oid)?;
                let arr = self.new_array(0)?;
                let mut n: u32 = 0;
                for k in keys {
                    self.heap.obj_mut(arr).props.insert(
                        PropKey::Str(units_from_str(&n.to_string())),
                        Property::data(JsValue::Str(Rc::new(k))),
                    );
                    n += 1;
                }
                self.set_array_length_raw(arr, f64::from(n));
                Ok(JsValue::Obj(arr))
            }
            NativeFn::ObjectGetOwnPropertyNames => {
                let a0 = arg(0);
                let oid = self.to_object(&a0)?;
                let all_keys = if matches!(self.heap.obj(oid).kind, ObjKind::Proxy(_)) {
                    self.proxy_own_property_keys(oid)?
                } else {
                    if !self.own_surface_complete(oid) {
                        return Err(Abrupt::Fatal(
                            "getOwnPropertyNames of an object with unmodeled own surface"
                                .to_string(),
                        ));
                    }
                    self.ordered_own_keys_of(oid)
                };
                let arr = self.new_array(0)?;
                let mut n: u32 = 0;
                for key in all_keys {
                    let PropKey::Str(u) = key else { continue };
                    self.heap.obj_mut(arr).props.insert(
                        PropKey::Str(units_from_str(&n.to_string())),
                        Property::data(JsValue::Str(Rc::new(u))),
                    );
                    n += 1;
                }
                self.set_array_length_raw(arr, f64::from(n));
                Ok(JsValue::Obj(arr))
            }
            NativeFn::ObjectDefineProperty => {
                let JsValue::Obj(oid) = arg(0) else {
                    return Err(self.throw_type_error());
                };
                let key = {
                    let k = arg(1);
                    self.to_property_key(&k)?
                };
                let desc = self.to_property_descriptor(&arg(2))?;
                if oid == self.global {
                    return Err(Abrupt::Fatal(
                        "defineProperty on the global object (attribute surface unmodeled)"
                            .to_string(),
                    ));
                }
                let ok = self.define_own(oid, &key, desc)?;
                if !ok {
                    return Err(self.throw_type_error());
                }
                Ok(JsValue::Obj(oid))
            }
            NativeFn::ObjectGetOwnPropertyDescriptor => {
                let a0 = arg(0);
                let oid = self.to_object(&a0)?;
                let key = {
                    let k = arg(1);
                    self.to_property_key(&k)?
                };
                match self.im_get_own_property(oid, &key)? {
                    None => Ok(JsValue::Undefined),
                    Some(p) => self.from_property_descriptor(&p),
                }
            }
            NativeFn::ObjectGetPrototypeOf => {
                let a0 = arg(0);
                let oid = self.to_object(&a0)?;
                Ok(match self.im_get_prototype_of(oid)? {
                    Some(p) => JsValue::Obj(p),
                    None => JsValue::Null,
                })
            }
            NativeFn::ObjectCreate => {
                let proto = match arg(0) {
                    JsValue::Obj(p) => Some(p),
                    JsValue::Null => None,
                    _ => return Err(self.throw_type_error()),
                };
                let oid = self.alloc_obj(trust_js_value::JsObject::new(ObjKind::Plain, proto))?;
                if !matches!(arg(1), JsValue::Undefined) {
                    self.object_define_properties(oid, &arg(1))?;
                }
                Ok(JsValue::Obj(oid))
            }
            NativeFn::ObjectIs => Ok(JsValue::Bool(crate::ops::same_value(&arg(0), &arg(1)))),
            NativeFn::ObjectPreventExtensions => {
                if let JsValue::Obj(oid) = arg(0) {
                    // Object.preventExtensions: a false [[PreventExtensions]]
                    // result is a TypeError (unlike Reflect.preventExtensions).
                    if !self.im_prevent_extensions(oid)? {
                        return Err(self.throw_type_error());
                    }
                }
                Ok(arg(0))
            }
            NativeFn::ObjectIsExtensible => Ok(JsValue::Bool(match arg(0) {
                JsValue::Obj(oid) => self.im_is_extensible(oid)?,
                _ => false,
            })),
            NativeFn::ObjProtoToString => self.object_proto_to_string(&this),
            NativeFn::ObjProtoToLocaleString => {
                let m = self.get_prop(&this, &PropKey::from_str("toString"))?;
                self.call_value(&m, this, Vec::new())
            }
            NativeFn::ObjProtoValueOf => Ok(JsValue::Obj(self.to_object(&this)?)),
            NativeFn::ObjProtoHasOwnProperty => {
                let key = {
                    let k = arg(0);
                    self.to_property_key(&k)?
                };
                let oid = self.to_object(&this)?;
                Ok(JsValue::Bool(self.im_get_own_property(oid, &key)?.is_some()))
            }
            NativeFn::ObjProtoIsPrototypeOf => {
                let JsValue::Obj(vo) = arg(0) else {
                    return Ok(JsValue::Bool(false));
                };
                let t = self.to_object(&this)?;
                // V.[[GetPrototypeOf]]() per hop — a proxy in the chain traps.
                let mut cur = self.im_get_prototype_of(vo)?;
                let mut hops = 0;
                while let Some(p) = cur {
                    if p == t {
                        return Ok(JsValue::Bool(true));
                    }
                    cur = self.im_get_prototype_of(p)?;
                    hops += 1;
                    if hops >= 128 {
                        return Err(Abrupt::Fatal("prototype chain too deep".to_string()));
                    }
                }
                Ok(JsValue::Bool(false))
            }
            NativeFn::ObjProtoPropertyIsEnumerable => {
                let key = {
                    let k = arg(0);
                    self.to_property_key(&k)?
                };
                let oid = self.to_object(&this)?;
                if oid == self.global {
                    return Err(Abrupt::Fatal(
                        "propertyIsEnumerable on the global object (attribute surface unmodeled)"
                            .to_string(),
                    ));
                }
                Ok(JsValue::Bool(
                    self.im_get_own_property(oid, &key)?.is_some_and(|p| p.enumerable),
                ))
            }
            NativeFn::ArrayCtor => {
                let proto = match &new_target {
                    Some(ntv) => self.get_prototype_from_constructor(ntv, self.intr.array_proto)?,
                    None => self.intr.array_proto,
                };
                if args.len() == 1 {
                    if let JsValue::Num(n) = arg(0) {
                        let Some(len) = exact_uint32(n) else {
                            return Err(self.throw_native(ErrKind::Range));
                        };
                        return Ok(JsValue::Obj(self.new_array_with_proto(len, proto)?));
                    }
                }
                let arr = self.new_array_with_proto(0, proto)?;
                for (i, v) in args.iter().enumerate() {
                    self.heap.obj_mut(arr).props.insert(
                        PropKey::Str(units_from_str(&i.to_string())),
                        Property::data(v.clone()),
                    );
                }
                #[allow(clippy::cast_precision_loss)]
                self.set_array_length_raw(arr, args.len() as f64);
                Ok(JsValue::Obj(arr))
            }
            NativeFn::ArrayIsArray => Ok(JsValue::Bool(match arg(0) {
                // IsArray recurses through a proxy target (revoked → TypeError).
                JsValue::Obj(o) => self.is_array_exotic(o)?,
                _ => false,
            })),
            NativeFn::ArrayJoin => self.array_join(&this, &arg(0)),
            NativeFn::ArrayToString => {
                let oid = self.to_object(&this)?;
                let func = self.get_from_object(oid, &PropKey::from_str("join"), JsValue::Obj(oid))?;
                if let JsValue::Obj(f) = &func {
                    if self.heap.obj(*f).is_callable() {
                        return self.call_value(&func, JsValue::Obj(oid), Vec::new());
                    }
                }
                self.object_proto_to_string(&JsValue::Obj(oid))
            }
            NativeFn::ArrayPush => {
                let oid = self.to_object(&this)?;
                let mut len = self.length_of_array_like(oid)?;
                if len + args.len() as u64 > 9_007_199_254_740_991 {
                    return Err(self.throw_type_error());
                }
                for v in args {
                    self.set_on_object(oid, &PropKey::Str(units_from_str(&len.to_string())), v, true)?;
                    len += 1;
                }
                #[allow(clippy::cast_precision_loss)]
                let len_f = len as f64;
                self.set_on_object(oid, &PropKey::from_str("length"), JsValue::Num(len_f), true)?;
                Ok(JsValue::Num(len_f))
            }
            NativeFn::ArrayPop => {
                let oid = self.to_object(&this)?;
                let len = self.length_of_array_like(oid)?;
                if len == 0 {
                    self.set_on_object(oid, &PropKey::from_str("length"), JsValue::Num(0.0), true)?;
                    return Ok(JsValue::Undefined);
                }
                let new_len = len - 1;
                let key = PropKey::Str(units_from_str(&new_len.to_string()));
                let element = self.get_from_object(oid, &key, JsValue::Obj(oid))?;
                let deleted = self.delete_prop(oid, &key)?;
                if !deleted {
                    return Err(self.throw_type_error());
                }
                #[allow(clippy::cast_precision_loss)]
                self.set_on_object(
                    oid,
                    &PropKey::from_str("length"),
                    JsValue::Num(new_len as f64),
                    true,
                )?;
                Ok(element)
            }
            NativeFn::ArrayIndexOf => {
                let oid = self.to_object(&this)?;
                let len = i64::try_from(self.length_of_array_like(oid)?).unwrap_or(i64::MAX);
                if len == 0 {
                    return Ok(JsValue::Num(-1.0));
                }
                let target = arg(0);
                let n = if args.len() > 1 {
                    let raw = self.to_number(&arg(1))?;
                    let t = to_integer_or_infinity(raw);
                    if t == f64::INFINITY {
                        return Ok(JsValue::Num(-1.0));
                    }
                    clamp_i64(t)
                } else {
                    0
                };
                let mut k = if n >= 0 { n } else { (len + n).max(0) };
                while k < len {
                    self.charge_loop()?;
                    let key = PropKey::Str(units_from_str(&k.to_string()));
                    if self.has_property(oid, &key)? {
                        let v = self.get_from_object(oid, &key, JsValue::Obj(oid))?;
                        if crate::ops::strict_eq(&v, &target) {
                            #[allow(clippy::cast_precision_loss)]
                            return Ok(JsValue::Num(k as f64));
                        }
                    }
                    k += 1;
                }
                Ok(JsValue::Num(-1.0))
            }
            NativeFn::ArraySlice => {
                let oid = self.to_object(&this)?;
                let len = i64::try_from(self.length_of_array_like(oid)?).unwrap_or(i64::MAX);
                let rel = |t: f64| -> i64 {
                    if t == f64::NEG_INFINITY {
                        0
                    } else if t < 0.0 {
                        (len + clamp_i64(t)).max(0)
                    } else {
                        clamp_i64(t).min(len)
                    }
                };
                let start = if args.is_empty() {
                    0
                } else {
                    let n = self.to_number(&arg(0))?;
                    rel(to_integer_or_infinity(n))
                };
                let end = if args.len() < 2 || matches!(arg(1), JsValue::Undefined) {
                    len
                } else {
                    let n = self.to_number(&arg(1))?;
                    rel(to_integer_or_infinity(n))
                };
                let count = u64::try_from((end - start).max(0)).expect("non-negative");
                let out = self.array_species_create(oid, count)?;
                let mut n: u64 = 0;
                let mut k = start;
                while k < end {
                    self.charge_loop()?;
                    let key = PropKey::Str(units_from_str(&k.to_string()));
                    if self.has_property(oid, &key)? {
                        let v = self.get_from_object(oid, &key, JsValue::Obj(oid))?;
                        self.create_data_property_or_throw(out, &n.to_string(), v)?;
                    }
                    n += 1;
                    k += 1;
                }
                #[allow(clippy::cast_precision_loss)]
                self.set_on_object(out, &PropKey::from_str("length"), JsValue::Num(n as f64), true)?;
                Ok(JsValue::Obj(out))
            }
            NativeFn::ArrayMap | NativeFn::ArrayForEach => {
                let map = matches!(nf, NativeFn::ArrayMap);
                let oid = self.to_object(&this)?;
                let len = self.length_of_array_like(oid)?;
                let cb = arg(0);
                match &cb {
                    JsValue::Obj(c) if self.heap.obj(*c).is_callable() => {}
                    _ => return Err(self.throw_type_error()),
                }
                let this_arg = arg(1);
                let result = if map {
                    Some(self.array_species_create(oid, len)?)
                } else {
                    None
                };
                for k in 0..len {
                    self.charge_loop()?;
                    let key = PropKey::Str(units_from_str(&k.to_string()));
                    if !self.has_property(oid, &key)? {
                        continue;
                    }
                    let v = self.get_from_object(oid, &key, JsValue::Obj(oid))?;
                    #[allow(clippy::cast_precision_loss)]
                    let r = self.call_value(
                        &cb,
                        this_arg.clone(),
                        vec![v, JsValue::Num(k as f64), JsValue::Obj(oid)],
                    )?;
                    if let Some(res) = result {
                        self.create_data_property_or_throw(res, &k.to_string(), r)?;
                    }
                }
                match result {
                    Some(res) => Ok(JsValue::Obj(res)),
                    None => Ok(JsValue::Undefined),
                }
            }
            NativeFn::ArrayConcat => {
                let oid = self.to_object(&this)?;
                let out = self.array_species_create(oid, 0)?;
                let mut n: u64 = 0;
                let mut items: Vec<JsValue> = vec![JsValue::Obj(oid)];
                items.extend(args);
                for e in items {
                    let spreadable = self.is_concat_spreadable(&e)?;
                    if spreadable {
                        let JsValue::Obj(eo) = e else { unreachable!("spreadable is an object") };
                        let elen = self.length_of_array_like(eo)?;
                        if elen > 4_294_967_295 {
                            // Engines deviate from the spec loop above the
                            // array-index range (V8 short-circuits): the
                            // consensus is not the spec here — refuse.
                            return Err(Abrupt::Fatal(
                                "concat spreadable length beyond the array-index range \
                                 (engine behavior deviates from spec)"
                                    .to_string(),
                            ));
                        }
                        if n + elen > 9_007_199_254_740_991 {
                            return Err(self.throw_type_error());
                        }
                        for k in 0..elen {
                            self.charge_loop()?;
                            let key = PropKey::Str(units_from_str(&k.to_string()));
                            if self.has_property(eo, &key)? {
                                let v = self.get_from_object(eo, &key, JsValue::Obj(eo))?;
                                self.create_data_property_or_throw(out, &n.to_string(), v)?;
                            }
                            n += 1;
                        }
                    } else {
                        self.create_data_property_or_throw(out, &n.to_string(), e)?;
                        n += 1;
                    }
                }
                #[allow(clippy::cast_precision_loss)]
                self.set_on_object(out, &PropKey::from_str("length"), JsValue::Num(n as f64), true)?;
                Ok(JsValue::Obj(out))
            }
            NativeFn::ArrayValues | NativeFn::ArrayKeys | NativeFn::ArrayEntries => {
                // 23.1.3.{36,17,5}: O = ? ToObject(this); CreateArrayIterator(O, kind).
                let o = self.to_object(&this)?;
                let kind = match nf {
                    NativeFn::ArrayKeys => crate::iterobj::IterKind::Key,
                    NativeFn::ArrayEntries => crate::iterobj::IterKind::KeyValue,
                    _ => crate::iterobj::IterKind::Value,
                };
                self.make_array_iterator(o, kind)
            }
            NativeFn::StringCtor => {
                if let Some(ntv) = new_target {
                    // 22.1.1.1 with NewTarget: NO symbol special case.
                    let s = if args.is_empty() {
                        Vec::new()
                    } else {
                        self.to_string_units(&arg(0))?
                    };
                    let proto =
                        self.get_prototype_from_constructor(&ntv, self.intr.string_proto)?;
                    let oid = self.make_string_wrapper(&Rc::new(s), proto)?;
                    Ok(JsValue::Obj(oid))
                } else {
                    if args.is_empty() {
                        return Ok(JsValue::str_from(""));
                    }
                    // String(symbol) is the SymbolDescriptiveString.
                    if let JsValue::Sym(s) = arg(0) {
                        return Ok(JsValue::Str(Rc::new(self.symbol_descriptive_string(s))));
                    }
                    let u = self.to_string_units(&arg(0))?;
                    Ok(JsValue::Str(Rc::new(u)))
                }
            }
            NativeFn::StringProtoToString | NativeFn::StringProtoValueOf => {
                self.this_string_value(&this).map(|u| JsValue::Str(Rc::new(u)))
            }
            NativeFn::StringCharAt => {
                self.require_object_coercible(&this)?;
                let s = self.to_string_units(&this)?;
                let pos = {
                    let n = self.to_number(&arg(0))?;
                    to_integer_or_infinity(n)
                };
                if pos < 0.0 || pos >= s.len() as f64 {
                    return Ok(JsValue::str_from(""));
                }
                #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
                let i = pos as usize;
                Ok(JsValue::Str(Rc::new(vec![s[i]])))
            }
            NativeFn::StringCharCodeAt => {
                self.require_object_coercible(&this)?;
                let s = self.to_string_units(&this)?;
                let pos = {
                    let n = self.to_number(&arg(0))?;
                    to_integer_or_infinity(n)
                };
                if pos < 0.0 || pos >= s.len() as f64 {
                    return Ok(JsValue::Num(f64::NAN));
                }
                #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
                let i = pos as usize;
                Ok(JsValue::Num(f64::from(s[i])))
            }
            NativeFn::StringIndexOf => {
                self.require_object_coercible(&this)?;
                let s = self.to_string_units(&this)?;
                let search = self.to_string_units(&arg(0))?;
                let pos = {
                    let n = self.to_number(&arg(1))?;
                    to_integer_or_infinity(n)
                };
                let start = if pos < 0.0 {
                    0
                } else if pos > s.len() as f64 {
                    s.len()
                } else {
                    #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
                    {
                        pos as usize
                    }
                };
                Ok(JsValue::Num(string_index_of(&s, &search, start)))
            }
            NativeFn::NumberCtor => {
                // Number(value): ToNumeric, then map a BigInt to its closest
                // Number (21.1.1.1) — NOT ToNumber (which would throw).
                let n = if args.is_empty() {
                    0.0
                } else {
                    match self.to_numeric(&arg(0))? {
                        crate::ops::Numeric::N(x) => x,
                        crate::ops::Numeric::B(b) => trust_js_value::bigint_to_f64(&b),
                    }
                };
                if let Some(ntv) = new_target {
                    let proto =
                        self.get_prototype_from_constructor(&ntv, self.intr.number_proto)?;
                    let oid = self.alloc_obj(trust_js_value::JsObject::new(
                        ObjKind::Wrapper(WrapperPrim::Num(n)),
                        Some(proto),
                    ))?;
                    Ok(JsValue::Obj(oid))
                } else {
                    Ok(JsValue::Num(n))
                }
            }
            NativeFn::NumberProtoToString => {
                let n = self.this_number_value(&this)?;
                match arg(0) {
                    JsValue::Undefined => Ok(JsValue::str_from(&js_number_to_string(n))),
                    rv => {
                        let r = to_integer_or_infinity(self.to_number(&rv)?);
                        if !(2.0..=36.0).contains(&r) {
                            return Err(self.throw_native(ErrKind::Range));
                        }
                        if (r - 10.0).abs() < f64::EPSILON {
                            return Ok(JsValue::str_from(&js_number_to_string(n)));
                        }
                        // Non-decimal radix: exact for integral values
                        // (digit expansion); fractional digits are
                        // shortest-form territory — refuse.
                        if n.is_nan() || n.is_infinite() {
                            return Ok(JsValue::str_from(&js_number_to_string(n)));
                        }
                        if n.trunc() != n {
                            return Err(Abrupt::Fatal(
                                "Number.prototype.toString fractional non-decimal radix (out of slice)"
                                    .to_string(),
                            ));
                        }
                        if n.abs() >= 340_282_366_920_938_463_463_374_607_431_768_211_456.0 {
                            return Err(Abrupt::Fatal(
                                "Number.prototype.toString radix beyond exact 128-bit expansion"
                                    .to_string(),
                            ));
                        }
                        #[allow(clippy::cast_possible_truncation)]
                        let radix = r as u32;
                        Ok(JsValue::str_from(&integer_to_radix_string(n, radix)))
                    }
                }
            }
            NativeFn::NumberProtoValueOf => Ok(JsValue::Num(self.this_number_value(&this)?)),
            NativeFn::BooleanCtor => {
                let b = self.to_boolean(&arg(0));
                if let Some(ntv) = new_target {
                    let proto =
                        self.get_prototype_from_constructor(&ntv, self.intr.boolean_proto)?;
                    let oid = self.alloc_obj(trust_js_value::JsObject::new(
                        ObjKind::Wrapper(WrapperPrim::Bool(b)),
                        Some(proto),
                    ))?;
                    Ok(JsValue::Obj(oid))
                } else {
                    Ok(JsValue::Bool(b))
                }
            }
            NativeFn::BooleanProtoToString => {
                let b = self.this_boolean_value(&this)?;
                Ok(JsValue::str_from(if b { "true" } else { "false" }))
            }
            NativeFn::BooleanProtoValueOf => Ok(JsValue::Bool(self.this_boolean_value(&this)?)),
            NativeFn::ErrorCtor(kind) => {
                let default_proto = self.intr.error_proto_for(kind);
                let proto = match &new_target {
                    Some(ntv) => self.get_prototype_from_constructor(ntv, default_proto)?,
                    None => default_proto,
                };
                let oid = self.make_native_error_with_proto(kind, false, proto)?;
                if !matches!(arg(0), JsValue::Undefined) {
                    let msg = self.to_string_units(&arg(0))?;
                    self.heap.obj_mut(oid).props.insert(
                        PropKey::from_str("message"),
                        Property::with_attrs(JsValue::Str(Rc::new(msg)), true, false, true),
                    );
                }
                // InstallErrorCause: only when options is an Object with a
                // `cause` property.
                self.install_error_cause(oid, &arg(1))?;
                Ok(JsValue::Obj(oid))
            }
            NativeFn::AggregateErrorCtor => self.aggregate_error_ctor(&args, new_target.as_ref()),
            NativeFn::SuppressedErrorCtor => {
                self.suppressed_error_construct(&args, new_target.as_ref())
            }
            NativeFn::DisposableStackCtor => {
                self.disposable_stack_construct(new_target.as_ref())
            }
            NativeFn::DisposableStackUse => self.ds_use(&this, arg(0)),
            NativeFn::DisposableStackAdopt => self.ds_adopt(&this, arg(0), arg(1)),
            NativeFn::DisposableStackDefer => self.ds_defer(&this, arg(0)),
            NativeFn::DisposableStackMove => self.ds_move(&this),
            NativeFn::DisposableStackDispose => self.ds_dispose(&this),
            NativeFn::DisposableStackDisposedGetter => self.ds_disposed_getter(&this),
            NativeFn::ErrorProtoToString => {
                if !matches!(this, JsValue::Obj(_)) {
                    return Err(self.throw_type_error());
                }
                let name_v = self.get_prop(&this, &PropKey::from_str("name"))?;
                let name = match name_v {
                    JsValue::Undefined => units_from_str("Error"),
                    v => self.to_string_units(&v)?,
                };
                let msg_v = self.get_prop(&this, &PropKey::from_str("message"))?;
                let msg = match msg_v {
                    JsValue::Undefined => Vec::new(),
                    v => self.to_string_units(&v)?,
                };
                let out: Units = if name.is_empty() {
                    msg
                } else if msg.is_empty() {
                    name
                } else {
                    let mut o = name;
                    o.extend_from_slice(&units_from_str(": "));
                    o.extend_from_slice(&msg);
                    o
                };
                Ok(JsValue::Str(Rc::new(out)))
            }
            NativeFn::JsonStringify => self.json_stringify(&args),
            NativeFn::JsonParse => self.json_parse(&args),
            NativeFn::EncodeUri { component } => self.dispatch_uri(true, component, &arg(0)),
            NativeFn::DecodeUri { component } => self.dispatch_uri(false, component, &arg(0)),
            NativeFn::IsNaN => Ok(JsValue::Bool(self.to_number(&arg(0))?.is_nan())),
            NativeFn::IsFinite => Ok(JsValue::Bool(self.to_number(&arg(0))?.is_finite())),
            NativeFn::MathFloor => {
                let n = self.to_number(&arg(0))?;
                Ok(JsValue::Num(n.floor()))
            }
            NativeFn::MathCeil => {
                let n = self.to_number(&arg(0))?;
                Ok(JsValue::Num(n.ceil()))
            }
            NativeFn::MathTrunc => {
                let n = self.to_number(&arg(0))?;
                Ok(JsValue::Num(n.trunc()))
            }
            NativeFn::MathAbs => {
                let n = self.to_number(&arg(0))?;
                Ok(JsValue::Num(n.abs()))
            }
            NativeFn::MathPow => {
                let b = self.to_number(&arg(0))?;
                let e = self.to_number(&arg(1))?;
                Ok(JsValue::Num(crate::ops::js_exponentiate(b, e)))
            }
            NativeFn::MathMax | NativeFn::MathMin => {
                let max = matches!(nf, NativeFn::MathMax);
                let mut coerced = Vec::with_capacity(args.len());
                for a in &args {
                    coerced.push(self.to_number(a)?);
                }
                let mut best = if max { f64::NEG_INFINITY } else { f64::INFINITY };
                let mut nan = false;
                for x in coerced {
                    if x.is_nan() {
                        nan = true;
                        continue;
                    }
                    if max {
                        if x > best || (x == 0.0 && best == 0.0 && !x.is_sign_negative()) {
                            best = x;
                        }
                    } else if x < best || (x == 0.0 && best == 0.0 && x.is_sign_negative()) {
                        best = x;
                    }
                }
                Ok(JsValue::Num(if nan { f64::NAN } else { best }))
            }
            // -- S1b family routing -----------------------------------------
            NativeFn::ObjectAssign => self.object_assign(&args),
            NativeFn::ObjectValues => {
                let a0 = arg(0);
                self.object_entries_values(&a0, true)
            }
            NativeFn::ObjectEntries => {
                let a0 = arg(0);
                self.object_entries_values(&a0, false)
            }
            NativeFn::ObjectFromEntries => {
                let a0 = arg(0);
                self.object_from_entries(&a0)
            }
            NativeFn::ObjectGetOwnPropertyDescriptors => {
                let a0 = arg(0);
                self.object_get_own_property_descriptors(&a0)
            }
            NativeFn::ObjectGetOwnPropertySymbols => {
                let a0 = arg(0);
                self.object_get_own_property_symbols(&a0)
            }
            NativeFn::ObjectDefineProperties => {
                let JsValue::Obj(oid) = arg(0) else {
                    return Err(self.throw_type_error());
                };
                self.object_define_properties(oid, &arg(1))?;
                Ok(JsValue::Obj(oid))
            }
            NativeFn::ObjectFreeze => {
                let a0 = arg(0);
                self.object_set_integrity(&a0, true)
            }
            NativeFn::ObjectSeal => {
                let a0 = arg(0);
                self.object_set_integrity(&a0, false)
            }
            NativeFn::ObjectIsFrozen => {
                let a0 = arg(0);
                self.object_test_integrity(&a0, true)
            }
            NativeFn::ObjectIsSealed => {
                let a0 = arg(0);
                self.object_test_integrity(&a0, false)
            }
            NativeFn::ObjectSetPrototypeOf => {
                let o = arg(0);
                self.require_object_coercible(&o)?;
                let proto = match arg(1) {
                    JsValue::Obj(p) => Some(p),
                    JsValue::Null => None,
                    _ => return Err(self.throw_type_error()),
                };
                let JsValue::Obj(oid) = o else {
                    return Ok(o);
                };
                let ok = self.im_set_prototype_of(oid, proto)?;
                if !ok {
                    return Err(self.throw_type_error());
                }
                Ok(JsValue::Obj(oid))
            }
            NativeFn::ObjectHasOwn => {
                let a0 = arg(0);
                let oid = self.to_object(&a0)?;
                let key = {
                    let k = arg(1);
                    self.to_property_key(&k)?
                };
                Ok(JsValue::Bool(self.im_get_own_property(oid, &key)?.is_some()))
            }
            NativeFn::ReflectApply
            | NativeFn::ReflectConstruct
            | NativeFn::ReflectDefineProperty
            | NativeFn::ReflectDeleteProperty
            | NativeFn::ReflectGet
            | NativeFn::ReflectGetOwnPropertyDescriptor
            | NativeFn::ReflectGetPrototypeOf
            | NativeFn::ReflectHas
            | NativeFn::ReflectIsExtensible
            | NativeFn::ReflectOwnKeys
            | NativeFn::ReflectPreventExtensions
            | NativeFn::ReflectSet
            | NativeFn::ReflectSetPrototypeOf => self.dispatch_reflect(nf, &args),
            NativeFn::ArrayFrom
            | NativeFn::ArrayOf
            | NativeFn::ArrayAt
            | NativeFn::ArrayIncludes
            | NativeFn::ArrayLastIndexOf
            | NativeFn::ArrayEvery
            | NativeFn::ArraySome
            | NativeFn::ArrayFilter
            | NativeFn::ArrayFind { .. }
            | NativeFn::ArrayFill
            | NativeFn::ArrayCopyWithin
            | NativeFn::ArrayFlat
            | NativeFn::ArrayFlatMap
            | NativeFn::ArrayReduce { .. }
            | NativeFn::ArrayReverse
            | NativeFn::ArrayShift
            | NativeFn::ArrayUnshift
            | NativeFn::ArraySplice
            | NativeFn::ArraySort
            | NativeFn::ArrayToSorted
            | NativeFn::ArrayToReversed
            | NativeFn::ArrayToSpliced
            | NativeFn::ArrayWith => self.dispatch_array(nf, this, args),
            NativeFn::StringFromCharCode
            | NativeFn::StringFromCodePoint
            | NativeFn::StringRaw
            | NativeFn::StringAt
            | NativeFn::StringCodePointAt
            | NativeFn::StringLastIndexOf
            | NativeFn::StringIncludes
            | NativeFn::StringStartsWith
            | NativeFn::StringEndsWith
            | NativeFn::StringSlice
            | NativeFn::StringSubstring
            | NativeFn::StringSplit
            | NativeFn::StringMatch
            | NativeFn::StringMatchAll
            | NativeFn::StringSearch
            | NativeFn::StringCase { .. }
            | NativeFn::StringTrim { .. }
            | NativeFn::StringRepeat
            | NativeFn::StringPad { .. }
            | NativeFn::StringConcat
            | NativeFn::StringReplace { .. }
            | NativeFn::StringIsWellFormed
            | NativeFn::StringToWellFormed => self.dispatch_string(nf, this, args),
            NativeFn::SymbolCtor
            | NativeFn::SymbolFor
            | NativeFn::SymbolKeyFor
            | NativeFn::SymbolProtoToString
            | NativeFn::SymbolProtoValueOf
            | NativeFn::SymbolProtoDescription
            | NativeFn::SymbolToPrimitive
            | NativeFn::BigIntCtor
            | NativeFn::BigIntAsIntN
            | NativeFn::BigIntAsUintN
            | NativeFn::BigIntProtoToString
            | NativeFn::BigIntProtoValueOf
            | NativeFn::NumberIsFinite
            | NativeFn::NumberIsInteger
            | NativeFn::NumberIsNaN
            | NativeFn::NumberIsSafeInteger
            | NativeFn::ParseInt
            | NativeFn::ParseFloat
            | NativeFn::MathRound
            | NativeFn::MathSign
            | NativeFn::MathSqrt
            | NativeFn::MathImul
            | NativeFn::MathClz32
            | NativeFn::MathFround => self.dispatch_misc(nf, this, args, new_target.as_ref()),
            NativeFn::MapCtor => self.map_like_ctor(false, &args, new_target.as_ref()),
            NativeFn::WeakMapCtor => self.map_like_ctor(true, &args, new_target.as_ref()),
            NativeFn::SetCtor => self.set_like_ctor(false, &args, new_target.as_ref()),
            NativeFn::WeakSetCtor => self.set_like_ctor(true, &args, new_target.as_ref()),
            NativeFn::MapGet
            | NativeFn::MapSet
            | NativeFn::MapHas
            | NativeFn::MapDelete
            | NativeFn::MapClear
            | NativeFn::MapForEach
            | NativeFn::MapSizeGetter
            | NativeFn::MapGetOrInsert
            | NativeFn::MapGetOrInsertComputed
            | NativeFn::MapEntries
            | NativeFn::MapKeys
            | NativeFn::MapValues
            | NativeFn::SetAdd
            | NativeFn::SetHas
            | NativeFn::SetDelete
            | NativeFn::SetClear
            | NativeFn::SetForEach
            | NativeFn::SetSizeGetter
            | NativeFn::SetValues
            | NativeFn::SetEntries
            | NativeFn::WeakMapGet
            | NativeFn::WeakMapSet
            | NativeFn::WeakMapHas
            | NativeFn::WeakMapDelete
            | NativeFn::WeakMapGetOrInsert
            | NativeFn::WeakMapGetOrInsertComputed
            | NativeFn::WeakSetAdd
            | NativeFn::WeakSetHas
            | NativeFn::WeakSetDelete => self.dispatch_collections(nf, this, args),
            NativeFn::WeakRefCtor
            | NativeFn::WeakRefDeref
            | NativeFn::FinalizationRegistryCtor
            | NativeFn::FinRegRegister
            | NativeFn::FinRegUnregister
            | NativeFn::IteratorCtor
            | NativeFn::IteratorProtoCtorGet
            | NativeFn::IteratorProtoCtorSet
            | NativeFn::IteratorProtoTagGet
            | NativeFn::IteratorProtoTagSet => self.dispatch_weak(nf, this, args),
            // §27.1.4 Iterator Helper methods + %IteratorHelperPrototype%.next/return.
            NativeFn::IteratorProtoMap
            | NativeFn::IteratorProtoFilter
            | NativeFn::IteratorProtoTake
            | NativeFn::IteratorProtoDrop
            | NativeFn::IteratorProtoFlatMap
            | NativeFn::IteratorProtoReduce
            | NativeFn::IteratorProtoToArray
            | NativeFn::IteratorProtoForEach
            | NativeFn::IteratorProtoSome
            | NativeFn::IteratorProtoEvery
            | NativeFn::IteratorProtoFind
            | NativeFn::IteratorHelperNext
            | NativeFn::IteratorHelperReturn => self.dispatch_iter_helper(nf, this, args),
            NativeFn::DateWrapperCtor
            | NativeFn::DateRealCtor
            | NativeFn::DateNow
            | NativeFn::DateRealNow
            | NativeFn::DateParse
            | NativeFn::DateUtc
            | NativeFn::DateGetField { .. }
            | NativeFn::DateSetField { .. }
            | NativeFn::DateGetTime
            | NativeFn::DateSetTime
            | NativeFn::DateGetTimezoneOffset
            | NativeFn::DateValueOf
            | NativeFn::DateToIsoString
            | NativeFn::DateToJson
            | NativeFn::DateToUtcString
            | NativeFn::DateToString
            | NativeFn::DateToDateString
            | NativeFn::DateToTimeString
            | NativeFn::DateToPrimitive
            | NativeFn::DateGetYear
            | NativeFn::DateSetYear => self.dispatch_date(nf, this, args, new_target.as_ref()),
            NativeFn::ProxyCtor => {
                // 28.2.1.1 Proxy(target, handler): `Proxy(...)` without new is a
                // TypeError; otherwise ProxyCreate.
                if new_target.is_none() {
                    return Err(self.throw_type_error());
                }
                let target = arg(0);
                let handler = arg(1);
                Ok(JsValue::Obj(self.proxy_create(&target, &handler)?))
            }
            NativeFn::ProxyRevocable => {
                let target = arg(0);
                let handler = arg(1);
                self.proxy_revocable(&target, &handler)
            }
            NativeFn::ProxyRevoke => self.proxy_revoke(fid),
            NativeFn::RegExpCtor
            | NativeFn::RegexSourceGetter
            | NativeFn::RegexFlagsGetter
            | NativeFn::RegexFlagGetter(_)
            | NativeFn::RegexToString
            | NativeFn::RegexProtoMethod(_) => self.dispatch_regexp(nf, this, args, new_target),
            NativeFn::ConsoleWrite { stderr } => {
                self.guard_driver_output_recording(args.len())?;
                let mut vs = Vec::with_capacity(args.len());
                for a in &args {
                    vs.push(crate::project::project(self, a).map_err(Abrupt::Fatal)?);
                }
                self.events.push(if stderr {
                    HostEvent::Stderr { v: vs }
                } else {
                    HostEvent::Stdout { v: vs }
                });
                Ok(JsValue::Undefined)
            }
            NativeFn::Print => {
                self.guard_driver_output_recording(args.len())?;
                let mut vs = Vec::with_capacity(args.len());
                for a in &args {
                    vs.push(crate::project::project(self, a).map_err(Abrupt::Fatal)?);
                }
                self.events.push(HostEvent::Stdout { v: vs });
                Ok(JsValue::Undefined)
            }
            NativeFn::ThrowTypeError => Err(self.throw_type_error()),
            // -- generators / iterators (S1e) -------------------------------
            NativeFn::IteratorProtoIterator => Ok(this),
            NativeFn::ArrayIteratorNext => {
                self.builtin_iter_next(&this, crate::iterobj::IterBrand::Array)
            }
            NativeFn::StringIteratorNext => {
                self.builtin_iter_next(&this, crate::iterobj::IterBrand::String)
            }
            NativeFn::MapIteratorNext => {
                self.builtin_iter_next(&this, crate::iterobj::IterBrand::Map)
            }
            NativeFn::SetIteratorNext => {
                self.builtin_iter_next(&this, crate::iterobj::IterBrand::Set)
            }
            NativeFn::RegExpStringIteratorNext => {
                self.builtin_iter_next(&this, crate::iterobj::IterBrand::RegExpString)
            }
            NativeFn::StringProtoIterator => {
                // 22.1.3.34: RequireObjectCoercible + ToString + CreateStringIterator.
                self.require_object_coercible(&this)?;
                let units = self.to_string_units(&this)?;
                self.make_string_iterator(Rc::new(units))
            }
            NativeFn::GeneratorNext => {
                let oid = self.this_generator(&this)?;
                self.gen_resume(oid, crate::generators::ResumeInput::Next(arg(0)))
            }
            NativeFn::GeneratorReturn => {
                let oid = self.this_generator(&this)?;
                self.gen_resume(oid, crate::generators::ResumeInput::Return(arg(0)))
            }
            NativeFn::GeneratorThrow => {
                let oid = self.this_generator(&this)?;
                self.gen_resume(oid, crate::generators::ResumeInput::Throw(arg(0)))
            }
            NativeFn::GeneratorFunctionCtor => Err(Abrupt::Fatal(
                "GeneratorFunction constructor (eval-like, out of slice)".to_string(),
            )),
            // -- §27.6 async generators -------------------------------------
            NativeFn::AsyncGeneratorNext => {
                self.async_gen_method(&this, crate::generators::AsyncGenReq::Next(arg(0)))
            }
            NativeFn::AsyncGeneratorReturn => {
                self.async_gen_method(&this, crate::generators::AsyncGenReq::Return(arg(0)))
            }
            NativeFn::AsyncGeneratorThrow => {
                self.async_gen_method(&this, crate::generators::AsyncGenReq::Throw(arg(0)))
            }
            // %AsyncIteratorPrototype%[@@asyncIterator] returns `this`.
            NativeFn::AsyncIteratorProtoSelf => Ok(this),
            NativeFn::AsyncGeneratorFunctionCtor => Err(Abrupt::Fatal(
                "AsyncGeneratorFunction constructor (eval-like, out of slice)".to_string(),
            )),
            // -- §27.2 Promise + the event loop (M2 D1) ---------------------
            NativeFn::PromiseCtor
            | NativeFn::PromiseResolve
            | NativeFn::PromiseReject
            | NativeFn::PromiseAll
            | NativeFn::PromiseAllSettled
            | NativeFn::PromiseRace
            | NativeFn::PromiseAny
            | NativeFn::PromiseProtoThen
            | NativeFn::PromiseProtoCatch
            | NativeFn::PromiseProtoFinally
            | NativeFn::PromiseTry
            | NativeFn::PromiseWithResolvers
            | NativeFn::PromiseResolveFn
            | NativeFn::PromiseRejectFn
            | NativeFn::PromiseValueThunk
            | NativeFn::PromiseThrowThunk
            | NativeFn::PromiseCapExecutor
            | NativeFn::PromiseAllResolveElement
            | NativeFn::PromiseAllSettledResolveElement
            | NativeFn::PromiseAllSettledRejectElement
            | NativeFn::PromiseAnyRejectElement
            | NativeFn::QueueMicrotask
            | NativeFn::SetTimeout
            | NativeFn::SetInterval
            | NativeFn::ClearTimer => {
                self.dispatch_promise(nf, fid, this, args, new_target.as_ref())
            }
            // -- binary data (§23.2 / §25) ----------------------------------
            NativeFn::ArrayBufferCtor
            | NativeFn::ArrayBufferIsView
            | NativeFn::ArrayBufferByteLengthGetter
            | NativeFn::ArrayBufferMaxByteLengthGetter
            | NativeFn::ArrayBufferResizableGetter
            | NativeFn::ArrayBufferDetachedGetter
            | NativeFn::ArrayBufferSlice
            | NativeFn::ArrayBufferResize
            | NativeFn::ArrayBufferTransfer { .. }
            | NativeFn::DataViewCtor
            | NativeFn::DataViewBufferGetter
            | NativeFn::DataViewByteLengthGetter
            | NativeFn::DataViewByteOffsetGetter
            | NativeFn::DataViewGet(_)
            | NativeFn::DataViewSet(_)
            | NativeFn::TypedArrayBaseCtor
            | NativeFn::TypedArrayCtor(_)
            | NativeFn::TypedArrayFrom
            | NativeFn::TypedArrayOf
            | NativeFn::TaBufferGetter
            | NativeFn::TaByteLengthGetter
            | NativeFn::TaByteOffsetGetter
            | NativeFn::TaLengthGetter
            | NativeFn::TaToStringTagGetter
            | NativeFn::TaProtoMethod(_) => {
                self.dispatch_binary(nf, this, args, new_target.as_ref())
            }
        }
    }

    // -- shared helpers ------------------------------------------------------

    pub(crate) fn length_of_array_like(&mut self, oid: ObjId) -> Result<u64, Abrupt> {
        let v = self.get_from_object(oid, &PropKey::from_str("length"), JsValue::Obj(oid))?;
        Ok(to_length_u64(self.to_number(&v)?))
    }

    pub(crate) fn create_list_from_array_like(&mut self, oid: ObjId) -> Result<Vec<JsValue>, Abrupt> {
        let len = self.length_of_array_like(oid)?;
        if len > 1_000_000 {
            return Err(Abrupt::Fatal("array-like argument list cap exceeded".to_string()));
        }
        let mut out = Vec::with_capacity(usize::try_from(len).expect("capped"));
        for i in 0..len {
            self.charge_loop()?;
            let key = PropKey::Str(units_from_str(&i.to_string()));
            out.push(self.get_from_object(oid, &key, JsValue::Obj(oid))?);
        }
        Ok(out)
    }

    pub(crate) fn create_data_property_or_throw(
        &mut self,
        oid: ObjId,
        key: &str,
        v: JsValue,
    ) -> Result<(), Abrupt> {
        let ok = self.define_own(
            oid,
            &PropKey::Str(units_from_str(key)),
            PartialDesc::full_data(v, true, true, true),
        )?;
        if ok {
            Ok(())
        } else {
            Err(self.throw_type_error())
        }
    }

    /// ArraySpeciesCreate (10.4.2.3), exact: Get(O, "constructor") →
    /// Get(C, @@species) → Construct(C, [len]) (subclass-aware).
    pub(crate) fn array_species_create(&mut self, origin: ObjId, len: u64) -> Result<ObjId, Abrupt> {
        let array_create = |it: &mut Interp, len: u64| -> Result<ObjId, Abrupt> {
            let Ok(len32) = u32::try_from(len) else {
                return Err(it.throw_native(ErrKind::Range));
            };
            it.new_array(len32)
        };
        // IsArray recurses through a proxy target (revoked → TypeError).
        if !self.is_array_exotic(origin)? {
            return array_create(self, len);
        }
        let mut c =
            self.get_from_object(origin, &PropKey::from_str("constructor"), JsValue::Obj(origin))?;
        if let JsValue::Obj(_) = &c {
            let key = PropKey::Sym(SymId::WellKnown(WkSym::Species));
            let s = self.get_prop(&c, &key)?;
            c = match s {
                JsValue::Null => JsValue::Undefined,
                other => other,
            };
        }
        if matches!(c, JsValue::Undefined) {
            return array_create(self, len);
        }
        if !self.is_constructor(&c) {
            return Err(self.throw_type_error());
        }
        #[allow(clippy::cast_precision_loss)]
        let r = self.construct(&c, vec![JsValue::Num(len as f64)], None)?;
        match r {
            JsValue::Obj(o) => Ok(o),
            _ => Err(Abrupt::Fatal("constructor returned non-object".to_string())),
        }
    }

    /// IsConcatSpreadable (23.1.3.1.1), exact: Get(O, @@isConcatSpreadable)
    /// → ToBoolean when defined, else IsArray.
    fn is_concat_spreadable(&mut self, v: &JsValue) -> Result<bool, Abrupt> {
        let JsValue::Obj(oid) = v else {
            return Ok(false);
        };
        let key = PropKey::Sym(SymId::WellKnown(WkSym::IsConcatSpreadable));
        let s = self.get_from_object(*oid, &key, v.clone())?;
        if !matches!(s, JsValue::Undefined) {
            return Ok(self.to_boolean(&s));
        }
        // IsArray recurses through a proxy target (revoked → TypeError).
        self.is_array_exotic(*oid)
    }

    fn array_join(&mut self, this: &JsValue, sep: &JsValue) -> ERes {
        let oid = self.to_object(this)?;
        let len = self.length_of_array_like(oid)?;
        let sep_u = match sep {
            JsValue::Undefined => units_from_str(","),
            v => self.to_string_units(v)?,
        };
        let mut out: Units = Vec::new();
        for k in 0..len {
            self.charge_loop()?;
            if k > 0 {
                out.extend_from_slice(&sep_u);
            }
            let key = PropKey::Str(units_from_str(&k.to_string()));
            let el = self.get_from_object(oid, &key, JsValue::Obj(oid))?;
            if !el.is_nullish() {
                let u = self.to_string_units(&el)?;
                out.extend_from_slice(&u);
            }
            if out.len() > MAX_STRING_UNITS {
                return Err(Abrupt::Fatal("join result cap exceeded".to_string()));
            }
        }
        Ok(JsValue::Str(Rc::new(out)))
    }

    /// Object.prototype.toString (20.1.3.6) with exact builtin tags and an
    /// exact Get(O, @@toStringTag) (modeled data props and user handlers
    /// alike; misses on danger-listed intrinsic hops still refuse).
    fn object_proto_to_string(&mut self, this: &JsValue) -> ERes {
        let tag: &str = match this {
            JsValue::Undefined => return Ok(JsValue::str_from("[object Undefined]")),
            JsValue::Null => return Ok(JsValue::str_from("[object Null]")),
            JsValue::Bool(_) => "Boolean",
            JsValue::Num(_) => "Number",
            JsValue::Str(_) => "String",
            JsValue::Sym(_) | JsValue::BigInt(_) => "Object",
            JsValue::Obj(oid) => {
                let oid = *oid;
                if matches!(self.heap.obj(oid).kind, ObjKind::Proxy(_)) {
                    // 20.1.3.6: builtinTag is Array (IsArray, recursing the
                    // target — revoked → TypeError) / Function (callable) /
                    // Object; then @@toStringTag (via the get trap) overrides.
                    if self.is_array_exotic(oid)? {
                        "Array"
                    } else if self.heap.obj(oid).is_callable() {
                        "Function"
                    } else {
                        "Object"
                    }
                } else if oid == self.intr.number_proto {
                    "Number"
                } else if oid == self.intr.string_proto {
                    "String"
                } else if oid == self.intr.boolean_proto {
                    "Boolean"
                } else {
                    match &self.heap.obj(oid).kind {
                        ObjKind::Array => "Array",
                        ObjKind::Arguments(_) => "Arguments",
                        ObjKind::Function(_) => "Function",
                        ObjKind::Error => "Error",
                        ObjKind::Wrapper(WrapperPrim::Bool(_)) => "Boolean",
                        ObjKind::Wrapper(WrapperPrim::Num(_)) => "Number",
                        ObjKind::Wrapper(WrapperPrim::Str(_)) => "String",
                        ObjKind::Date(_) => "Date",
                        ObjKind::Regex(_) => "RegExp",
                        ObjKind::Wrapper(WrapperPrim::Sym(_))
                        | ObjKind::Wrapper(WrapperPrim::BigInt(_))
                        | ObjKind::Plain
                        | ObjKind::MapObj(_)
                        | ObjKind::SetObj(_)
                        | ObjKind::WeakMapObj(_)
                        | ObjKind::WeakSetObj(_)
                        | ObjKind::Generator
                        // An async generator's builtin tag is "Object"; its
                        // @@toStringTag ("AsyncGenerator") on the prototype
                        // overrides below.
                        | ObjKind::AsyncGenerator
                        // An iterator object's builtin tag is "Object"; its
                        // @@toStringTag ("Array Iterator" / …) on the prototype
                        // overrides below, giving "[object Array Iterator]".
                        | ObjKind::Iterator
                        // Promise's builtin tag is "Object"; its @@toStringTag
                        // ("Promise") overrides below, giving "[object Promise]".
                        | ObjKind::Promise(_)
                        | ObjKind::ArrayBuffer(_)
                        | ObjKind::DataView(_)
                        | ObjKind::TypedArray(_)
                        // A module namespace's builtin tag is "Object"; its
                        // frozen @@toStringTag ("Module") overrides below,
                        // giving "[object Module]".
                        | ObjKind::ModuleNamespace
                        // Proxy handled above (never reaches here).
                        | ObjKind::Proxy(_)
                        | ObjKind::IntrinsicHost => "Object",
                    }
                }
            }
        };
        // Get(O, @@toStringTag): a string value overrides the builtin tag
        // (primitive receivers resolve against their wrapper proto chains —
        // observably identical to the spec's ToObject + Get).
        let key = PropKey::Sym(SymId::WellKnown(WkSym::ToStringTag));
        let tag_v = self.get_prop(this, &key)?;
        if let JsValue::Str(s) = tag_v {
            let mut out = units_from_str("[object ");
            out.extend_from_slice(&s);
            out.extend_from_slice(&units_from_str("]"));
            return Ok(JsValue::Str(Rc::new(out)));
        }
        Ok(JsValue::str_from(&format!("[object {tag}]")))
    }

    // -- thisXxxValue --------------------------------------------------------

    fn this_string_value(&mut self, this: &JsValue) -> Result<Units, Abrupt> {
        match this {
            JsValue::Str(s) => Ok(s.as_ref().clone()),
            JsValue::Obj(oid) => {
                if *oid == self.intr.string_proto {
                    return Ok(Vec::new()); // [[StringData]] = ""
                }
                match &self.heap.obj(*oid).kind {
                    ObjKind::Wrapper(WrapperPrim::Str(s)) => Ok(s.as_ref().clone()),
                    _ => Err(self.throw_type_error()),
                }
            }
            _ => Err(self.throw_type_error()),
        }
    }

    fn this_number_value(&mut self, this: &JsValue) -> Result<f64, Abrupt> {
        match this {
            JsValue::Num(n) => Ok(*n),
            JsValue::Obj(oid) => {
                if *oid == self.intr.number_proto {
                    return Ok(0.0); // [[NumberData]] = +0
                }
                match &self.heap.obj(*oid).kind {
                    ObjKind::Wrapper(WrapperPrim::Num(n)) => Ok(*n),
                    _ => Err(self.throw_type_error()),
                }
            }
            _ => Err(self.throw_type_error()),
        }
    }

    fn this_boolean_value(&mut self, this: &JsValue) -> Result<bool, Abrupt> {
        match this {
            JsValue::Bool(b) => Ok(*b),
            JsValue::Obj(oid) => {
                if *oid == self.intr.boolean_proto {
                    return Ok(false); // [[BooleanData]] = false
                }
                match &self.heap.obj(*oid).kind {
                    ObjKind::Wrapper(WrapperPrim::Bool(b)) => Ok(*b),
                    _ => Err(self.throw_type_error()),
                }
            }
            _ => Err(self.throw_type_error()),
        }
    }

    /// EnumerableOwnProperties(O, key) for fully-modeled own surfaces.
    fn enumerable_own_string_keys(&mut self, oid: ObjId) -> Result<Vec<Units>, Abrupt> {
        // A proxy routes [[OwnPropertyKeys]] + per-key [[GetOwnProperty]]
        // through its traps (EnumerableOwnProperties over a proxy).
        if matches!(self.heap.obj(oid).kind, ObjKind::Proxy(_)) {
            let mut out = Vec::new();
            for key in self.proxy_own_property_keys(oid)? {
                self.charge_loop()?;
                let PropKey::Str(u) = key else { continue };
                if let Some(d) = self.im_get_own_property(oid, &PropKey::Str(u.clone()))? {
                    if d.enumerable {
                        out.push(u);
                    }
                }
            }
            return Ok(out);
        }
        if !self.own_surface_complete(oid) {
            return Err(Abrupt::Fatal(
                "Object.keys of an object with unmodeled own surface".to_string(),
            ));
        }
        let mut out = Vec::new();
        for key in self.ordered_own_keys_of(oid) {
            let PropKey::Str(u) = key else { continue };
            let enumerable = match self.heap.obj(oid).props.get(&PropKey::Str(u.clone())) {
                Some(p) => p.enumerable,
                // A synthesized typed-array index is enumerable.
                None => matches!(self.heap.obj(oid).kind, ObjKind::TypedArray(_)),
            };
            if enumerable {
                out.push(u);
            }
        }
        Ok(out)
    }

    // -- property descriptors ------------------------------------------------

    /// ToPropertyDescriptor (6.2.5.5), field order per spec.
    pub(crate) fn to_property_descriptor(&mut self, v: &JsValue) -> Result<PartialDesc, Abrupt> {
        let JsValue::Obj(oid) = v else {
            return Err(self.throw_type_error());
        };
        let oid = *oid;
        let mut d = PartialDesc::default();
        let fields: [&str; 6] = ["enumerable", "configurable", "value", "writable", "get", "set"];
        for f in fields {
            let key = PropKey::from_str(f);
            if !self.has_property(oid, &key)? {
                continue;
            }
            let fv = self.get_from_object(oid, &key, v.clone())?;
            match f {
                "enumerable" => d.enumerable = Some(self.to_boolean(&fv)),
                "configurable" => d.configurable = Some(self.to_boolean(&fv)),
                "value" => d.value = Some(fv),
                "writable" => d.writable = Some(self.to_boolean(&fv)),
                "get" | "set" => {
                    let fo = match fv {
                        JsValue::Undefined => None,
                        JsValue::Obj(f2) if self.heap.obj(f2).is_callable() => Some(f2),
                        _ => return Err(self.throw_type_error()),
                    };
                    if f == "get" {
                        d.get = Some(fo);
                    } else {
                        d.set = Some(fo);
                    }
                }
                _ => unreachable!(),
            }
        }
        if d.is_accessor() && d.is_data() {
            return Err(self.throw_type_error());
        }
        Ok(d)
    }

    /// FromPropertyDescriptor (6.2.5.4).
    pub(crate) fn from_property_descriptor(&mut self, p: &Property) -> ERes {
        let oid = self.new_plain()?;
        match &p.v {
            PropValue::Data { value, writable } => {
                if p.synthetic {
                    return Err(Abrupt::Fatal(
                        "descriptor of engine-specific synthetic text".to_string(),
                    ));
                }
                self.heap
                    .obj_mut(oid)
                    .props
                    .insert(PropKey::from_str("value"), Property::data(value.clone()));
                self.heap.obj_mut(oid).props.insert(
                    PropKey::from_str("writable"),
                    Property::data(JsValue::Bool(*writable)),
                );
            }
            PropValue::Accessor { get, set } => {
                let g = get.map_or(JsValue::Undefined, JsValue::Obj);
                let s = set.map_or(JsValue::Undefined, JsValue::Obj);
                self.heap
                    .obj_mut(oid)
                    .props
                    .insert(PropKey::from_str("get"), Property::data(g));
                self.heap
                    .obj_mut(oid)
                    .props
                    .insert(PropKey::from_str("set"), Property::data(s));
            }
        }
        self.heap.obj_mut(oid).props.insert(
            PropKey::from_str("enumerable"),
            Property::data(JsValue::Bool(p.enumerable)),
        );
        self.heap.obj_mut(oid).props.insert(
            PropKey::from_str("configurable"),
            Property::data(JsValue::Bool(p.configurable)),
        );
        Ok(JsValue::Obj(oid))
    }
}

/// Number::toString(x, radix≠10) for integral x: exact digit expansion
/// (lowercase a-z), matching engines for the whole safe-integer range and
/// beyond up to i128 magnitude.
fn integer_to_radix_string(n: f64, radix: u32) -> String {
    if n == 0.0 {
        return "0".to_string();
    }
    let neg = n < 0.0;
    let mag = n.abs();
    #[allow(clippy::cast_possible_truncation)]
    let mut v = mag as u128;
    let mut digits: Vec<char> = Vec::new();
    while v > 0 {
        let d = (v % u128::from(radix)) as u32;
        digits.push(char::from_digit(d, radix).expect("digit below radix"));
        v /= u128::from(radix);
    }
    let body: String = digits.into_iter().rev().collect();
    if neg {
        format!("-{body}")
    } else {
        body
    }
}

fn clamp_i64(t: f64) -> i64 {
    if t <= -9_007_199_254_740_992.0 {
        i64::MIN / 4
    } else if t >= 9_007_199_254_740_992.0 {
        i64::MAX / 4
    } else {
        #[allow(clippy::cast_possible_truncation)]
        {
            t as i64
        }
    }
}

/// StringIndexOf (6.1.4.1-adjacent helper) over code units; -1 when absent.
fn string_index_of(s: &[u16], search: &[u16], start: usize) -> f64 {
    if search.is_empty() {
        #[allow(clippy::cast_precision_loss)]
        return start.min(s.len()) as f64;
    }
    if search.len() > s.len() {
        return -1.0;
    }
    let last = s.len() - search.len();
    let mut i = start;
    while i <= last {
        if &s[i..i + search.len()] == search {
            #[allow(clippy::cast_precision_loss)]
            return i as f64;
        }
        i += 1;
    }
    -1.0
}

/// QuoteJSONString (25.5.2.2), well-formed, as code units.
pub(crate) fn json_quote_units(s: &[u16]) -> Units {
    let mut out: Units = Vec::with_capacity(s.len() + 2);
    out.push(u16::from(b'"'));
    let mut i = 0;
    while i < s.len() {
        let c = s[i];
        match c {
            0x22 => out.extend_from_slice(&units_from_str("\\\"")),
            0x5c => out.extend_from_slice(&units_from_str("\\\\")),
            0x08 => out.extend_from_slice(&units_from_str("\\b")),
            0x0c => out.extend_from_slice(&units_from_str("\\f")),
            0x0a => out.extend_from_slice(&units_from_str("\\n")),
            0x0d => out.extend_from_slice(&units_from_str("\\r")),
            0x09 => out.extend_from_slice(&units_from_str("\\t")),
            c if c < 0x20 => out.extend_from_slice(&units_from_str(&format!("\\u{c:04x}"))),
            c if (0xd800..=0xdbff).contains(&c) => {
                if i + 1 < s.len() && (0xdc00..=0xdfff).contains(&s[i + 1]) {
                    out.push(c);
                    out.push(s[i + 1]);
                    i += 1;
                } else {
                    out.extend_from_slice(&units_from_str(&format!("\\u{c:04x}")));
                }
            }
            c if (0xdc00..=0xdfff).contains(&c) => {
                out.extend_from_slice(&units_from_str(&format!("\\u{c:04x}")));
            }
            c => out.push(c),
        }
        i += 1;
    }
    out.push(u16::from(b'"'));
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_js_value::units_to_lossy;

    #[test]
    fn json_quote_vectors() {
        let q = |s: &str| units_to_lossy(&json_quote_units(&units_from_str(s)));
        assert_eq!(q("ab"), "\"ab\"");
        assert_eq!(q("a\"b"), "\"a\\\"b\"");
        assert_eq!(q("a\nb"), "\"a\\nb\"");
        assert_eq!(q("\u{1}"), "\"\\u0001\"");
        assert_eq!(q("é"), "\"é\"");
        // Lone surrogate escapes.
        assert_eq!(units_to_lossy(&json_quote_units(&[0xd800])), "\"\\ud800\"");
    }

    #[test]
    fn string_index_of_vectors() {
        let u = units_from_str;
        assert_eq!(string_index_of(&u("hello"), &u("ll"), 0), 2.0);
        assert_eq!(string_index_of(&u("hello"), &u("z"), 0), -1.0);
        assert_eq!(string_index_of(&u("hello"), &u(""), 3), 3.0);
        assert_eq!(string_index_of(&u("aaa"), &u("a"), 2), 2.0);
        assert_eq!(string_index_of(&u("abc"), &u("abcd"), 0), -1.0);
    }
}
