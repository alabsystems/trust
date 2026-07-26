// Property access algorithms with the per-hop miss-danger discipline: an
// unimplemented-but-engine-real intrinsic property can never be mis-read as
// `undefined`, mis-reported as absent, or silently fallen-through — it
// refuses. Implements ordinary [[Get]]/[[Set]]/[[Delete]]/[[HasProperty]]/
// [[DefineOwnProperty]] (full ValidateAndApplyPropertyDescriptor), the Array
// exotic length semantics (ArraySetLength), the arguments exotic parameter
// map, primitive wrappers (ToObject), and for-in key enumeration.
//
// Author: Andrew Yates
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

use crate::interp::{Abrupt, ERes, Interp};
use std::rc::Rc;
use trust_js_value::{
    array_index_of, exact_uint32, js_number_to_string, to_number_str, to_uint32, units_eq_ascii,
    units_from_str, units_to_lossy, ErrKind, JsObject, JsValue, ObjId, ObjKind, PropKey, PropValue,
    Property, Units, WrapperPrim, ERROR_INSTANCE_DANGER,
};

/// CanonicalNumericIndexString (7.1.21): `Some(n)` iff `u` is the canonical
/// string form of the Number `n` (including `"-0"` → -0, `"NaN"`, `"Infinity"`,
/// negatives, and fractionals). Non-canonical forms (`"01"`, `"1e3"`, `" 1"`)
/// are plain string keys.
#[must_use]
pub(crate) fn canonical_numeric_index(u: &Units) -> Option<f64> {
    if units_eq_ascii(u, "-0") {
        return Some(-0.0);
    }
    let s = units_to_lossy(u);
    let n = to_number_str(&s).ok()?;
    if units_from_str(&js_number_to_string(n)) == *u {
        Some(n)
    } else {
        None
    }
}

/// A partial property descriptor (spec Property Descriptor record).
#[derive(Debug, Clone, Default)]
pub struct PartialDesc {
    pub value: Option<JsValue>,
    pub writable: Option<bool>,
    pub get: Option<Option<ObjId>>,
    pub set: Option<Option<ObjId>>,
    pub enumerable: Option<bool>,
    pub configurable: Option<bool>,
}

impl PartialDesc {
    #[must_use]
    pub fn value_only(v: JsValue) -> PartialDesc {
        PartialDesc {
            value: Some(v),
            ..PartialDesc::default()
        }
    }

    #[must_use]
    pub fn full_data(v: JsValue, w: bool, e: bool, c: bool) -> PartialDesc {
        PartialDesc {
            value: Some(v),
            writable: Some(w),
            enumerable: Some(e),
            configurable: Some(c),
            get: None,
            set: None,
        }
    }

    #[must_use]
    pub fn is_accessor(&self) -> bool {
        self.get.is_some() || self.set.is_some()
    }

    #[must_use]
    pub fn is_data(&self) -> bool {
        self.value.is_some() || self.writable.is_some()
    }

    #[must_use]
    pub fn is_generic(&self) -> bool {
        !self.is_accessor() && !self.is_data()
    }
}

impl Interp {
    // -- own-property access with the danger discipline ----------------------

    /// The refusal reason when a MISS of `key` on `oid` is unsound to answer
    /// (a real engine may hold an unmodeled own property here).
    pub(crate) fn own_miss_gap(&self, oid: ObjId, key: &PropKey) -> Option<String> {
        if oid == self.global {
            return Some(format!(
                "global-object property miss `{}` (engine global surface unmodeled)",
                key.describe()
            ));
        }
        if matches!(self.heap.obj(oid).kind, ObjKind::Error) {
            if let PropKey::Str(u) = key {
                let name = trust_js_value::units_to_lossy(u);
                if ERROR_INSTANCE_DANGER.contains(&name.as_str()) {
                    return Some(format!("error-instance `{name}` (engine-specific own surface)"));
                }
            }
        }
        // Non-strict user functions carry engine legacy `arguments`/`caller`
        // magic own slots (V8): any own miss — reads AND defines — refuses.
        if let ObjKind::Function(trust_js_value::FnData::User(uf)) = &self.heap.obj(oid).kind {
            if !uf.func.strict {
                if let PropKey::Str(u) = key {
                    if units_eq_ascii(u, "arguments") || units_eq_ascii(u, "caller") {
                        return Some(format!(
                            "sloppy-function legacy `{}` own surface (engine magic slots)",
                            trust_js_value::units_to_lossy(u)
                        ));
                    }
                }
            }
        }
        self.intr.miss_danger(oid, key)
    }

    /// Raw own property, with the arguments-object parameter map merged in
    /// (mapped indices read through their parameter binding).
    pub(crate) fn own_prop(&self, oid: ObjId, key: &PropKey) -> Option<Property> {
        let obj = self.heap.obj(oid);
        // Integer-indexed exotic [[GetOwnProperty]]: a valid index yields a
        // fresh {w:true,e:true,c:true} data descriptor; any other canonical
        // numeric index is absent.
        if let ObjKind::TypedArray(_) = obj.kind {
            if let PropKey::Str(u) = key {
                if let Some(idx) = canonical_numeric_index(u) {
                    if self.ta_is_valid_index(oid, idx) {
                        let v = self.ta_element_get_pure(oid, idx);
                        return Some(Property::with_attrs(v, true, true, true));
                    }
                    return None;
                }
            }
        }
        let p = obj.props.get(key)?.clone();
        if let ObjKind::Arguments(args) = &obj.kind {
            if let Some(name) = mapped_name(args, key) {
                if let Some(v) = self.lookup_env_binding(args.env, name) {
                    let mut merged = p;
                    if let PropValue::Data { writable, .. } = merged.v {
                        merged.v = PropValue::Data { value: v, writable };
                    }
                    return Some(merged);
                }
            }
        }
        Some(p)
    }

    /// Own property with the miss-danger check: `Ok(None)` only where the
    /// own-surface model is complete for this key.
    pub(crate) fn own_prop_checked(
        &self,
        oid: ObjId,
        key: &PropKey,
    ) -> Result<Option<Property>, Abrupt> {
        // A proxy's [[GetOwnProperty]] is the handler trap (mutable, may run
        // arbitrary JS): it can never be answered on this pure `&self` path.
        // Callers reach a proxy through `im_get_own_property`; a miss here is
        // an unwired path, so refuse (sound) rather than mis-report absence.
        if matches!(self.heap.obj(oid).kind, ObjKind::Proxy(_)) {
            return Err(Abrupt::Fatal(
                "[[GetOwnProperty]] on a proxy off the trap-routed path".to_string(),
            ));
        }
        if let Some(p) = self.own_prop(oid, key) {
            return Ok(Some(p));
        }
        if let Some(gap) = self.own_miss_gap(oid, key) {
            return Err(Abrupt::Fatal(gap));
        }
        Ok(None)
    }

    fn lookup_env_binding(&self, env: trust_js_value::EnvId, name: &str) -> Option<JsValue> {
        let mut cur = Some(env);
        while let Some(e) = cur {
            if let Some(b) = self.heap.env(e).bindings.get(name) {
                return Some(b.value.clone());
            }
            cur = self.heap.env(e).parent;
        }
        None
    }

    /// Read a data property's value (refusing engine-specific synthetic
    /// text), or invoke its getter with `receiver` as this.
    fn prop_read(&mut self, p: &Property, receiver: &JsValue) -> ERes {
        match &p.v {
            PropValue::Data { value, .. } => {
                if p.synthetic {
                    return Err(Abrupt::Fatal(
                        "read of engine-specific synthetic message text".to_string(),
                    ));
                }
                Ok(value.clone())
            }
            PropValue::Accessor { get, .. } => match get {
                None => Ok(JsValue::Undefined),
                Some(g) => {
                    let gv = JsValue::Obj(*g);
                    self.call_value(&gv, receiver.clone(), vec![])
                }
            },
        }
    }

    // -- GetV ----------------------------------------------------------------

    /// GetV(base, key): property read off any base value, with primitive
    /// bases resolved against the wrapper prototype chains (no allocation).
    pub(crate) fn get_prop(&mut self, base: &JsValue, key: &PropKey) -> ERes {
        match base {
            JsValue::Obj(oid) => self.get_from_object(*oid, key, base.clone()),
            JsValue::Str(s) => {
                if let PropKey::Str(u) = key {
                    if units_eq_ascii(u, "length") {
                        #[allow(clippy::cast_precision_loss)]
                        return Ok(JsValue::Num(s.len() as f64));
                    }
                    if let Some(i) = array_index_of(u) {
                        let i = i as usize;
                        if i < s.len() {
                            return Ok(JsValue::Str(Rc::new(vec![s[i]])));
                        }
                        return Ok(JsValue::Undefined);
                    }
                }
                self.get_from_object(self.intr.string_proto, key, base.clone())
            }
            JsValue::Num(_) => self.get_from_object(self.intr.number_proto, key, base.clone()),
            JsValue::Bool(_) => self.get_from_object(self.intr.boolean_proto, key, base.clone()),
            JsValue::Sym(_) => self.get_from_object(self.intr.symbol_proto, key, base.clone()),
            JsValue::BigInt(_) => self.get_from_object(self.intr.bigint_proto, key, base.clone()),
            JsValue::Undefined | JsValue::Null => Err(self.throw_type_error()),
        }
    }

    pub(crate) fn get_from_object(&mut self, oid: ObjId, key: &PropKey, receiver: JsValue) -> ERes {
        // Integer-indexed exotic [[Get]] (10.4.5.4): a canonical numeric index
        // on a typed array reads the element (undefined when out of range) and
        // NEVER consults the prototype chain.
        if let ObjKind::TypedArray(_) = self.heap.obj(oid).kind {
            if let PropKey::Str(u) = key {
                if let Some(idx) = canonical_numeric_index(u) {
                    return Ok(self.ta_element_get_pure(oid, idx));
                }
            }
        }
        let mut cur = Some(oid);
        let mut hops = 0;
        while let Some(o) = cur {
            if hops >= 128 {
                return Err(Abrupt::Fatal("prototype chain too deep".to_string()));
            }
            // A proxy reached anywhere in the chain (as the base or as a
            // prototype) routes its [[Get]] through the handler trap, keeping
            // the same Receiver.
            if matches!(self.heap.obj(o).kind, ObjKind::Proxy(_)) {
                return self.proxy_get(o, key, receiver);
            }
            if let Some(p) = self.own_prop_checked(o, key)? {
                return self.prop_read(&p, &receiver);
            }
            cur = self.heap.obj(o).proto;
            hops += 1;
        }
        Ok(JsValue::Undefined)
    }

    /// HasProperty (7.3.12) with the per-hop miss discipline.
    pub(crate) fn has_property(&mut self, oid: ObjId, key: &PropKey) -> Result<bool, Abrupt> {
        // Integer-indexed exotic [[HasProperty]]: a canonical numeric index on
        // a typed array is present iff it is a valid integer index.
        if let ObjKind::TypedArray(_) = self.heap.obj(oid).kind {
            if let PropKey::Str(u) = key {
                if let Some(idx) = canonical_numeric_index(u) {
                    return Ok(self.ta_is_valid_index(oid, idx));
                }
            }
        }
        let mut cur = Some(oid);
        let mut hops = 0;
        while let Some(o) = cur {
            if hops >= 128 {
                return Err(Abrupt::Fatal("prototype chain too deep".to_string()));
            }
            // A proxy in the chain routes [[HasProperty]] through its trap.
            if matches!(self.heap.obj(o).kind, ObjKind::Proxy(_)) {
                return self.proxy_has(o, key);
            }
            if self.own_prop_checked(o, key)?.is_some() {
                return Ok(true);
            }
            cur = self.heap.obj(o).proto;
            hops += 1;
        }
        Ok(false)
    }

    // -- Set -----------------------------------------------------------------

    /// PutValue's object half: OrdinarySet with receiver == base.
    pub(crate) fn set_prop(
        &mut self,
        base: &JsValue,
        key: &PropKey,
        v: JsValue,
        strict: bool,
    ) -> Result<(), Abrupt> {
        match base {
            JsValue::Obj(oid) => self.set_on_object(*oid, key, v, strict),
            JsValue::Str(s) => {
                // Own virtual index/length props are non-writable.
                if let PropKey::Str(u) = key {
                    let is_own = units_eq_ascii(u, "length")
                        || array_index_of(u).is_some_and(|i| (i as usize) < s.len());
                    if is_own {
                        return if strict {
                            Err(self.throw_type_error())
                        } else {
                            Ok(())
                        };
                    }
                }
                let proto = self.intr.string_proto;
                self.set_on_primitive_chain(proto, base, key, v, strict)
            }
            JsValue::Num(_) => {
                let proto = self.intr.number_proto;
                self.set_on_primitive_chain(proto, base, key, v, strict)
            }
            JsValue::Bool(_) => {
                let proto = self.intr.boolean_proto;
                self.set_on_primitive_chain(proto, base, key, v, strict)
            }
            JsValue::Sym(_) => {
                let proto = self.intr.symbol_proto;
                self.set_on_primitive_chain(proto, base, key, v, strict)
            }
            JsValue::BigInt(_) => {
                let proto = self.intr.bigint_proto;
                self.set_on_primitive_chain(proto, base, key, v, strict)
            }
            JsValue::Undefined | JsValue::Null => Err(self.throw_type_error()),
        }
    }

    /// Set with a primitive receiver: chain accessors still run; data lands
    /// nowhere (strict TypeError / sloppy no-op).
    fn set_on_primitive_chain(
        &mut self,
        start_proto: ObjId,
        receiver: &JsValue,
        key: &PropKey,
        v: JsValue,
        strict: bool,
    ) -> Result<(), Abrupt> {
        let mut cur = Some(start_proto);
        let mut hops = 0;
        while let Some(o) = cur {
            if hops >= 128 {
                return Err(Abrupt::Fatal("prototype chain too deep".to_string()));
            }
            if let Some(p) = self.own_prop_checked(o, key)? {
                match &p.v {
                    PropValue::Accessor { set, .. } => {
                        return match set {
                            Some(s) => {
                                let sv = JsValue::Obj(*s);
                                self.call_value(&sv, receiver.clone(), vec![v])?;
                                Ok(())
                            }
                            None => {
                                if strict {
                                    Err(self.throw_type_error())
                                } else {
                                    Ok(())
                                }
                            }
                        };
                    }
                    PropValue::Data { .. } => break,
                }
            }
            cur = self.heap.obj(o).proto;
            hops += 1;
        }
        // Data property (or nothing) found: CreateDataProperty on a
        // primitive receiver fails.
        if strict {
            Err(self.throw_type_error())
        } else {
            Ok(())
        }
    }

    /// OrdinarySet(O, P, V, Receiver=O) with exotic define routing.
    pub(crate) fn set_on_object(
        &mut self,
        start: ObjId,
        key: &PropKey,
        v: JsValue,
        strict: bool,
    ) -> Result<(), Abrupt> {
        let receiver = JsValue::Obj(start);
        let ok = self.set_obj_with_receiver(start, key, v, &receiver)?;
        if !ok && strict {
            return Err(self.throw_type_error());
        }
        Ok(())
    }

    /// OrdinarySet / OrdinarySetWithOwnDescriptor (10.1.9.2) with an explicit
    /// receiver (super.x assignment, Reflect.set). Returns spec true/false.
    pub(crate) fn set_obj_with_receiver(
        &mut self,
        start: ObjId,
        key: &PropKey,
        v: JsValue,
        receiver: &JsValue,
    ) -> Result<bool, Abrupt> {
        // Find the own descriptor along the chain, honoring the integer-indexed
        // exotic [[Set]] (10.4.5.5) of ANY typed array reached by the walk —
        // not only `start`. Per OrdinarySetWithOwnDescriptor, when the current
        // object O carries no own descriptor its [[Set]] delegates to the
        // parent's [[Set]]; for a typed-array parent that is the exotic method,
        // which must be dispatched rather than flattened into an ordinary walk.
        let mut holder: Option<Property> = None;
        let mut o = start;
        let mut hops = 0;
        loop {
            if hops >= 128 {
                return Err(Abrupt::Fatal("prototype chain too deep".to_string()));
            }
            // A proxy reached in the walk (as O or as a prototype) routes its
            // [[Set]] through the handler trap, keeping the same Receiver.
            if matches!(self.heap.obj(o).kind, ObjKind::Proxy(_)) {
                return self.proxy_set(o, key, v, receiver.clone());
            }
            // Module Namespace exotic [[Set]] (10.4.6.9): always returns false,
            // regardless of the descriptor reported by [[GetOwnProperty]]
            // (writable:true). Reached as the direct target of a `ns.x = v`, or
            // as a null-proto parent that an ordinary child delegates its
            // [[Set]] to — both are the namespace's own [[Set]].
            if matches!(self.heap.obj(o).kind, ObjKind::ModuleNamespace) {
                return Ok(false);
            }
            // Integer-indexed exotic [[Set]] (10.4.5.5), applied at the object
            // `o` whose [[Set]] we are (recursively) invoking with this
            // Receiver. A canonical numeric index P:
            //   i.  SameValue(O, Receiver) → TypedArraySetElement (ToNumber is
            //       always observable; an out-of-range index discards the
            //       write), return true.
            //   ii. Otherwise, if IsValidIntegerIndex(O, P) is false, return
            //       true with no write (a foreign receiver never sees the
            //       canonical index materialize on the typed array).
            //   otherwise (valid index, foreign receiver) → step 2:
            //       OrdinarySet(O, P, V, Receiver). We fall through: the walk
            //       below finds O's own element descriptor (writable data) and
            //       the receiver-side branch creates the ordinary property on
            //       Receiver — exactly OrdinarySet starting at O.
            if let ObjKind::TypedArray(_) = self.heap.obj(o).kind {
                if let PropKey::Str(u) = key {
                    if let Some(idx) = canonical_numeric_index(u) {
                        if matches!(receiver, JsValue::Obj(r) if *r == o) {
                            self.ta_set_element(o, idx, v)?;
                            return Ok(true);
                        }
                        if !self.ta_is_valid_index(o, idx) {
                            return Ok(true);
                        }
                        // valid index + foreign receiver: fall through to
                        // OrdinarySet(O, …).
                    }
                }
            }
            // The global object takes fresh data properties like the sloppy
            // assignment fallback; its unmodeled surface stays refused at
            // every read. Only the receiver-is-global hop is exempted.
            let found = if o == self.global {
                self.own_prop(o, key)
            } else {
                self.own_prop_checked(o, key)?
            };
            if let Some(p) = found {
                holder = Some(p);
                break;
            }
            match self.heap.obj(o).proto {
                Some(p) => o = p,
                None => break,
            }
            hops += 1;
        }
        // ownDesc defaults to { w: true } when the chain carried nothing.
        if let Some(p) = &holder {
            if let PropValue::Accessor { set, .. } = &p.v {
                return match set {
                    Some(s) => {
                        let sv = JsValue::Obj(*s);
                        self.call_value(&sv, receiver.clone(), vec![v])?;
                        Ok(true)
                    }
                    None => Ok(false),
                };
            }
        }
        if let Some(Property {
            v: PropValue::Data { writable: false, .. },
            ..
        }) = &holder
        {
            return Ok(false);
        }
        let JsValue::Obj(rec) = receiver else {
            return Ok(false);
        };
        let rec = *rec;
        // Receiver-side: existing own → value-only define; otherwise
        // CreateDataProperty (full default attrs). Receiver.[[GetOwnProperty]]
        // routes through a proxy receiver's trap.
        let existing = if rec == self.global {
            self.own_prop(rec, key)
        } else {
            self.im_get_own_property(rec, key)?
        };
        match existing {
            Some(ex) => match &ex.v {
                PropValue::Accessor { .. } => Ok(false),
                PropValue::Data { writable: rw, .. } => {
                    if !rw {
                        return Ok(false);
                    }
                    self.define_own(rec, key, PartialDesc::value_only(v))
                }
            },
            None => self.define_own(rec, key, PartialDesc::full_data(v, true, true, true)),
        }
    }

    // -- DefineOwnProperty ---------------------------------------------------

    /// [[DefineOwnProperty]] with exotic routing. Returns spec true/false.
    pub(crate) fn define_own(
        &mut self,
        oid: ObjId,
        key: &PropKey,
        desc: PartialDesc,
    ) -> Result<bool, Abrupt> {
        if matches!(self.heap.obj(oid).kind, ObjKind::Proxy(_)) {
            return self.proxy_define_own(oid, key, desc);
        }
        // Module Namespace exotic [[DefineOwnProperty]] (10.4.6.7). A Symbol key
        // (only @@toStringTag exists) follows OrdinaryDefineOwnProperty over the
        // stored frozen property. A String key succeeds ONLY as a no-op redefine
        // of an existing export with a matching non-configurable, enumerable,
        // writable, same-valued data descriptor; anything else returns false.
        if matches!(self.heap.obj(oid).kind, ObjKind::ModuleNamespace) {
            if matches!(key, PropKey::Sym(_)) {
                return self.ordinary_define(oid, key, desc);
            }
            let Some(current) = self.own_prop(oid, key) else {
                return Ok(false); // not an export
            };
            if desc.configurable == Some(true) {
                return Ok(false);
            }
            if desc.enumerable == Some(false) {
                return Ok(false);
            }
            if desc.is_accessor() {
                return Ok(false);
            }
            if desc.writable == Some(false) {
                return Ok(false);
            }
            if let Some(v) = &desc.value {
                let cur_v = current.data_value().cloned().unwrap_or(JsValue::Undefined);
                return Ok(crate::ops::same_value(v, &cur_v));
            }
            return Ok(true);
        }
        // Integer-indexed exotic [[DefineOwnProperty]] (10.4.5.3).
        if let ObjKind::TypedArray(_) = self.heap.obj(oid).kind {
            if let PropKey::Str(u) = key {
                if let Some(idx) = canonical_numeric_index(u) {
                    return self.ta_define_index(oid, idx, desc);
                }
            }
        }
        match &self.heap.obj(oid).kind {
            ObjKind::Array => {
                if let PropKey::Str(u) = key {
                    if units_eq_ascii(u, "length") {
                        return self.array_set_length(oid, desc);
                    }
                    if let Some(idx) = array_index_of(u) {
                        return self.array_index_define(oid, key, idx, desc);
                    }
                }
                self.ordinary_define(oid, key, desc)
            }
            ObjKind::Arguments(args) => {
                let mapped = mapped_name(args, key).map(str::to_string);
                let env = args.env;
                // 10.4.4.2 step 4: defining {writable:false} WITHOUT a value
                // over a mapped index materializes the CURRENT map value into
                // the stored property (newArgDesc).
                let mut applied = desc.clone();
                if mapped.is_some()
                    && !desc.is_accessor()
                    && desc.value.is_none()
                    && desc.writable == Some(false)
                {
                    if let Some(name) = &mapped {
                        if let Some(v) = self.lookup_env_binding(env, name) {
                            applied.value = Some(v);
                        }
                    }
                }
                let ok = self.ordinary_define(oid, key, applied)?;
                if !ok {
                    return Ok(false);
                }
                if let Some(name) = mapped {
                    if desc.is_accessor() {
                        self.unmap_argument(oid, key);
                    } else {
                        if let Some(v) = desc.value {
                            // Keep the parameter binding aliased.
                            let mut cur = Some(env);
                            while let Some(e) = cur {
                                if let Some(b) = self.heap.env_mut(e).bindings.get_mut(&name) {
                                    b.value = v;
                                    break;
                                }
                                cur = self.heap.env(e).parent;
                            }
                        }
                        if desc.writable == Some(false) {
                            self.unmap_argument(oid, key);
                        }
                    }
                }
                Ok(true)
            }
            _ => self.ordinary_define(oid, key, desc),
        }
    }

    fn unmap_argument(&mut self, oid: ObjId, key: &PropKey) {
        if let PropKey::Str(u) = key {
            if let Some(i) = array_index_of(u) {
                if let ObjKind::Arguments(args) = &mut self.heap.obj_mut(oid).kind {
                    if let Some(slot) = args.map.get_mut(i as usize) {
                        *slot = None;
                    }
                }
            }
        }
    }

    /// OrdinaryDefineOwnProperty = ValidateAndApplyPropertyDescriptor.
    fn ordinary_define(
        &mut self,
        oid: ObjId,
        key: &PropKey,
        desc: PartialDesc,
    ) -> Result<bool, Abrupt> {
        let current = self.own_prop_checked(oid, key)?;
        match current {
            None => {
                if !self.heap.obj(oid).extensible {
                    return Ok(false);
                }
                let p = if desc.is_accessor() {
                    Property {
                        v: PropValue::Accessor {
                            get: desc.get.unwrap_or(None),
                            set: desc.set.unwrap_or(None),
                        },
                        enumerable: desc.enumerable.unwrap_or(false),
                        configurable: desc.configurable.unwrap_or(false),
                        synthetic: false,
                    }
                } else {
                    Property {
                        v: PropValue::Data {
                            value: desc.value.unwrap_or(JsValue::Undefined),
                            writable: desc.writable.unwrap_or(false),
                        },
                        enumerable: desc.enumerable.unwrap_or(false),
                        configurable: desc.configurable.unwrap_or(false),
                        synthetic: false,
                    }
                };
                self.heap.obj_mut(oid).props.insert(key.clone(), p);
                Ok(true)
            }
            Some(c) => {
                if desc.value.is_none()
                    && desc.writable.is_none()
                    && desc.get.is_none()
                    && desc.set.is_none()
                    && desc.enumerable.is_none()
                    && desc.configurable.is_none()
                {
                    return Ok(true);
                }
                if !c.configurable {
                    if desc.configurable == Some(true) {
                        return Ok(false);
                    }
                    if let Some(e) = desc.enumerable {
                        if e != c.enumerable {
                            return Ok(false);
                        }
                    }
                    if !desc.is_generic() && desc.is_accessor() != !c.is_data() {
                        return Ok(false);
                    }
                    match &c.v {
                        PropValue::Data { value, writable } => {
                            if !writable {
                                if desc.writable == Some(true) {
                                    return Ok(false);
                                }
                                if let Some(nv) = &desc.value {
                                    if c.synthetic {
                                        return Err(Abrupt::Fatal(
                                            "SameValue against engine-specific synthetic text"
                                                .to_string(),
                                        ));
                                    }
                                    if !crate::ops::same_value(nv, value) {
                                        return Ok(false);
                                    }
                                }
                            }
                        }
                        PropValue::Accessor { get, set } => {
                            if let Some(ng) = &desc.get {
                                if ng != get {
                                    return Ok(false);
                                }
                            }
                            if let Some(ns) = &desc.set {
                                if ns != set {
                                    return Ok(false);
                                }
                            }
                        }
                    }
                }
                // Apply: kind change or field merge, preserving slot order.
                let p = self
                    .heap
                    .obj_mut(oid)
                    .props
                    .get_mut(key)
                    .expect("own prop present");
                if desc.is_accessor() && c.is_data() {
                    p.v = PropValue::Accessor {
                        get: desc.get.unwrap_or(None),
                        set: desc.set.unwrap_or(None),
                    };
                    p.synthetic = false;
                } else if desc.is_data() && !c.is_data() {
                    p.v = PropValue::Data {
                        value: desc.value.unwrap_or(JsValue::Undefined),
                        writable: desc.writable.unwrap_or(false),
                    };
                    p.synthetic = false;
                } else {
                    match &mut p.v {
                        PropValue::Data { value, writable } => {
                            if let Some(nv) = desc.value {
                                *value = nv;
                                p.synthetic = false;
                            }
                            if let Some(nw) = desc.writable {
                                *writable = nw;
                            }
                        }
                        PropValue::Accessor { get, set } => {
                            if let Some(ng) = desc.get {
                                *get = ng;
                            }
                            if let Some(ns) = desc.set {
                                *set = ns;
                            }
                        }
                    }
                }
                if let Some(e) = desc.enumerable {
                    p.enumerable = e;
                }
                if let Some(cfg) = desc.configurable {
                    p.configurable = cfg;
                }
                Ok(true)
            }
        }
    }

    // -- Array exotic --------------------------------------------------------

    pub(crate) fn array_length(&self, oid: ObjId) -> u32 {
        match self
            .heap
            .obj(oid)
            .props
            .get(&PropKey::from_str("length"))
            .and_then(Property::data_value)
        {
            Some(JsValue::Num(n)) => exact_uint32(*n).unwrap_or(0),
            _ => 0,
        }
    }

    fn array_length_writable(&self, oid: ObjId) -> bool {
        match &self.heap.obj(oid).props.get(&PropKey::from_str("length")) {
            Some(Property {
                v: PropValue::Data { writable, .. },
                ..
            }) => *writable,
            _ => true,
        }
    }

    pub(crate) fn set_array_length_raw(&mut self, oid: ObjId, len: f64) {
        let key = PropKey::from_str("length");
        if let Some(p) = self.heap.obj_mut(oid).props.get_mut(&key) {
            if let PropValue::Data { value, .. } = &mut p.v {
                *value = JsValue::Num(len);
            }
        } else {
            self.heap
                .obj_mut(oid)
                .props
                .insert(key, Property::with_attrs(JsValue::Num(len), true, false, false));
        }
    }

    /// ArraySetLength (10.4.2.4).
    fn array_set_length(&mut self, oid: ObjId, desc: PartialDesc) -> Result<bool, Abrupt> {
        let Some(v) = desc.value.clone() else {
            // No value: ordinary validate/apply against the length prop.
            return self.ordinary_define(oid, &PropKey::from_str("length"), desc);
        };
        // Both conversions run (observably) per spec steps 3-4.
        let new_len_u = to_uint32(self.to_number(&v)?);
        let number_len = self.to_number(&v)?;
        if f64::from(new_len_u) != number_len {
            return Err(self.throw_native(ErrKind::Range));
        }
        let old_len = self.array_length(oid);
        let writable = self.array_length_writable(oid);
        if new_len_u >= old_len {
            let d = PartialDesc {
                value: Some(JsValue::Num(f64::from(new_len_u))),
                writable: desc.writable,
                enumerable: desc.enumerable,
                configurable: desc.configurable,
                get: None,
                set: None,
            };
            return self.ordinary_define(oid, &PropKey::from_str("length"), d);
        }
        if !writable {
            return Ok(false);
        }
        // Shrink: delete doomed indices from high to low, stopping at a
        // non-configurable element.
        let mut doomed: Vec<(u32, Units)> = self
            .heap
            .obj(oid)
            .props
            .keys()
            .filter_map(|k| match k {
                PropKey::Str(u) => array_index_of(u)
                    .filter(|i| *i >= new_len_u)
                    .map(|i| (i, u.clone())),
                PropKey::Sym(_) => None,
            })
            .collect();
        doomed.sort_by(|a, b| b.0.cmp(&a.0));
        let mut final_len = new_len_u;
        let mut ok = true;
        for (i, u) in doomed {
            let key = PropKey::Str(u);
            let configurable = self
                .heap
                .obj(oid)
                .props
                .get(&key)
                .is_some_and(|p| p.configurable);
            if configurable {
                self.heap.obj_mut(oid).props.shift_remove(&key);
            } else {
                final_len = i + 1;
                ok = false;
                break;
            }
        }
        self.set_array_length_raw(oid, f64::from(final_len));
        if desc.writable == Some(false) {
            let key = PropKey::from_str("length");
            if let Some(p) = self.heap.obj_mut(oid).props.get_mut(&key) {
                if let PropValue::Data { writable, .. } = &mut p.v {
                    *writable = false;
                }
            }
        }
        Ok(ok)
    }

    fn array_index_define(
        &mut self,
        oid: ObjId,
        key: &PropKey,
        idx: u32,
        desc: PartialDesc,
    ) -> Result<bool, Abrupt> {
        let old_len = self.array_length(oid);
        if idx >= old_len && !self.array_length_writable(oid) {
            return Ok(false);
        }
        let ok = self.ordinary_define(oid, key, desc)?;
        if ok && idx >= old_len {
            self.set_array_length_raw(oid, f64::from(idx) + 1.0);
        }
        Ok(ok)
    }

    // -- Delete --------------------------------------------------------------

    /// [[Delete]] with the danger discipline. Returns spec true/false.
    pub(crate) fn delete_prop(&mut self, oid: ObjId, key: &PropKey) -> Result<bool, Abrupt> {
        if oid == self.global {
            return Err(Abrupt::Fatal(
                "delete on the global object (attribute surface unmodeled)".to_string(),
            ));
        }
        if matches!(self.heap.obj(oid).kind, ObjKind::Proxy(_)) {
            return self.proxy_delete(oid, key);
        }
        // Integer-indexed exotic [[Delete]] (10.4.5.6): a valid index cannot be
        // deleted; any other canonical numeric index deletes vacuously.
        if let ObjKind::TypedArray(_) = self.heap.obj(oid).kind {
            if let PropKey::Str(u) = key {
                if let Some(idx) = canonical_numeric_index(u) {
                    return Ok(!self.ta_is_valid_index(oid, idx));
                }
            }
        }
        let Some(p) = self.own_prop_checked(oid, key)? else {
            return Ok(true);
        };
        if !p.configurable {
            return Ok(false);
        }
        self.unmap_argument(oid, key);
        self.heap.obj_mut(oid).props.shift_remove(key);
        Ok(true)
    }

    // -- ToObject / wrappers -------------------------------------------------

    /// ToObject (7.1.18). Wrapper allocations materialize String index
    /// properties with exact exotic attributes.
    pub(crate) fn to_object(&mut self, v: &JsValue) -> Result<ObjId, Abrupt> {
        match v {
            JsValue::Obj(oid) => Ok(*oid),
            JsValue::Bool(b) => {
                let proto = self.intr.boolean_proto;
                self.alloc_obj(JsObject::new(ObjKind::Wrapper(WrapperPrim::Bool(*b)), Some(proto)))
            }
            JsValue::Num(n) => {
                let proto = self.intr.number_proto;
                self.alloc_obj(JsObject::new(ObjKind::Wrapper(WrapperPrim::Num(*n)), Some(proto)))
            }
            JsValue::Str(s) => {
                let s = Rc::clone(s);
                let proto = self.intr.string_proto;
                self.make_string_wrapper(&s, proto)
            }
            JsValue::Sym(s) => {
                let proto = self.intr.symbol_proto;
                self.alloc_obj(JsObject::new(ObjKind::Wrapper(WrapperPrim::Sym(*s)), Some(proto)))
            }
            JsValue::BigInt(b) => {
                let b = Rc::clone(b);
                let proto = self.intr.bigint_proto;
                self.alloc_obj(JsObject::new(ObjKind::Wrapper(WrapperPrim::BigInt(b)), Some(proto)))
            }
            JsValue::Undefined | JsValue::Null => Err(self.throw_type_error()),
        }
    }

    /// A String exotic wrapper with the given prototype (subclass-aware).
    pub(crate) fn make_string_wrapper(
        &mut self,
        s: &Rc<Units>,
        proto: ObjId,
    ) -> Result<ObjId, Abrupt> {
        if s.len() > 4096 {
            return Err(Abrupt::Fatal(
                "ToObject on a >4096-unit string (wrapper materialization cap)".to_string(),
            ));
        }
        let mut o = JsObject::new(ObjKind::Wrapper(WrapperPrim::Str(Rc::clone(s))), Some(proto));
        for (i, unit) in s.iter().enumerate() {
            o.props.insert(
                PropKey::Str(units_from_str(&i.to_string())),
                Property::with_attrs(JsValue::Str(Rc::new(vec![*unit])), false, true, false),
            );
        }
        #[allow(clippy::cast_precision_loss)]
        o.props.insert(
            PropKey::from_str("length"),
            Property::with_attrs(JsValue::Num(s.len() as f64), false, false, false),
        );
        self.alloc_obj(o)
    }

    // -- enumeration ---------------------------------------------------------

    /// Is `oid` admissible as a hop in for-in / own-key reflection? Fully
    /// modeled kinds are; intrinsic prototypes are admissible for for-in
    /// specifically because every engine own property on them is
    /// non-enumerable (their danger names shadow as visited-non-enumerable).
    fn enum_safe_hop(&self, oid: ObjId) -> bool {
        if oid == self.global {
            return false;
        }
        match self.heap.obj(oid).kind {
            ObjKind::Plain
            | ObjKind::Array
            | ObjKind::Function(_)
            | ObjKind::Arguments(_)
            | ObjKind::Wrapper(_)
            | ObjKind::Date(_)
            | ObjKind::Regex(_)
            | ObjKind::MapObj(_)
            | ObjKind::SetObj(_)
            | ObjKind::WeakMapObj(_)
            | ObjKind::WeakSetObj(_)
            | ObjKind::ArrayBuffer(_)
            | ObjKind::DataView(_)
            | ObjKind::TypedArray(_)
            // A Promise instance has no engine-incidental own surface (its
            // state lives in the reactor), so it is a safe reflection hop.
            | ObjKind::Promise(_)
            // An iterator object's state lives in the side table, never as own
            // properties — a safe reflection hop with an empty own surface.
            | ObjKind::Iterator
            | ObjKind::Generator
            // A module namespace's own surface is fully modeled (the sorted
            // string exports + @@toStringTag), so it is a safe reflection hop.
            | ObjKind::ModuleNamespace
            | ObjKind::AsyncGenerator => true,
            // for-in over a proxy would invoke the ownKeys + getOwnPropertyDescriptor
            // traps per hop (EnumerateObjectProperties); that is not modeled on
            // this snapshot walk, so refuse (sound).
            ObjKind::Proxy(_) => false,
            ObjKind::Error => false,
            ObjKind::IntrinsicHost => {
                // Every engine own property on these prototypes is
                // non-enumerable, so they are admissible for-in hops (their
                // danger names shadow as visited-non-enumerable).
                let i = &self.intr;
                let base = [
                    i.object_proto,
                    i.string_proto,
                    i.number_proto,
                    i.boolean_proto,
                    i.symbol_proto,
                    // BigInt.prototype + the namespace intrinsics Math / JSON /
                    // Reflect + the §26 weak prototypes: every own property on
                    // each is NON-ENUMERABLE (built-in method / @@toStringTag),
                    // so their for-in surface is empty and their danger names
                    // shadow as visited-non-enumerable — a safe reflection hop.
                    // Verified empty vs Node 24 / Bun.
                    i.bigint_proto,
                    i.math,
                    i.json,
                    i.reflect,
                    i.weakref_proto,
                    i.finreg_proto,
                    i.error_proto,
                    i.type_error_proto,
                    i.range_error_proto,
                    i.reference_error_proto,
                    i.syntax_error_proto,
                    i.eval_error_proto,
                    i.uri_error_proto,
                    i.aggregate_error_proto,
                    i.map_proto,
                    i.set_proto,
                    i.weakmap_proto,
                    i.weakset_proto,
                    i.date_proto,
                    i.regexp_proto,
                    i.array_buffer_proto,
                    i.data_view_proto,
                    i.typed_array_proto,
                    // The iterator / generator / promise / async-function
                    // prototypes carry ONLY non-enumerable own properties
                    // (next/return/throw/then/catch/finally/constructor + the
                    // Iterator Helper danger names + @@toStringTag), so their
                    // enumerable for-in surface is empty and their danger names
                    // shadow as visited-non-enumerable — exactly the `base`
                    // property. Calibrated empty vs Node and Bun (for-in over a
                    // built-in iterator / generator instance or a
                    // generator/async FUNCTION yields nothing but own/inherited
                    // enumerables).
                    i.iterator_proto,
                    i.array_iterator_proto,
                    i.string_iterator_proto,
                    i.map_iterator_proto,
                    i.set_iterator_proto,
                    i.regexp_string_iterator_proto,
                    i.generator_proto,
                    i.generator_function_proto,
                    i.promise_proto,
                    i.async_function_proto,
                ]
                .contains(&oid);
                base || i.ta_protos.contains(&oid)
            }
        }
    }

    /// EnumerateObjectProperties: the for-in key snapshot (string keys only),
    /// receiver-to-prototype, integer-ascending-then-insertion per object,
    /// shadowed names (including danger-listed engine non-enumerables)
    /// skipped.
    pub(crate) fn for_in_keys(&mut self, receiver: ObjId) -> Result<Vec<Units>, Abrupt> {
        let mut visited: std::collections::HashSet<Units> = std::collections::HashSet::new();
        let mut out: Vec<Units> = Vec::new();
        let mut cur = Some(receiver);
        let mut hops = 0;
        while let Some(o) = cur {
            if hops >= 128 {
                return Err(Abrupt::Fatal("prototype chain too deep".to_string()));
            }
            if !self.enum_safe_hop(o) {
                return Err(Abrupt::Fatal(
                    "for-in over an object with unmodeled enumerable surface".to_string(),
                ));
            }
            let is_ta = matches!(self.heap.obj(o).kind, ObjKind::TypedArray(_));
            for key in self.ordered_own_keys_of(o) {
                let PropKey::Str(u) = key else { continue };
                if !visited.insert(u.clone()) {
                    continue;
                }
                let enumerable = match self.heap.obj(o).props.get(&PropKey::Str(u.clone())) {
                    Some(p) => p.enumerable,
                    None => is_ta && canonical_numeric_index(&u).is_some(),
                };
                if enumerable {
                    out.push(u);
                }
            }
            // Danger-listed engine names on this hop are real own
            // NON-ENUMERABLE properties: mark them visited so they shadow.
            if let Some(trust_js_value::Danger::Listed { names, .. }) = self.intr.danger.get(&o) {
                for n in *names {
                    visited.insert(units_from_str(n));
                }
            }
            cur = self.heap.obj(o).proto;
            hops += 1;
        }
        Ok(out)
    }

    // -- allocation helpers --------------------------------------------------

    pub(crate) fn new_plain(&mut self) -> Result<ObjId, Abrupt> {
        let proto = self.intr.object_proto;
        self.alloc_obj(JsObject::new(ObjKind::Plain, Some(proto)))
    }

    /// ArrayCreate with length `len` (< 2^32).
    pub(crate) fn new_array(&mut self, len: u32) -> Result<ObjId, Abrupt> {
        let proto = self.intr.array_proto;
        self.new_array_with_proto(len, proto)
    }

    /// ArrayCreate with an explicit prototype (subclass-aware).
    pub(crate) fn new_array_with_proto(&mut self, len: u32, proto: ObjId) -> Result<ObjId, Abrupt> {
        let oid = self.alloc_obj(JsObject::new(ObjKind::Array, Some(proto)))?;
        self.heap.obj_mut(oid).props.insert(
            PropKey::from_str("length"),
            Property::with_attrs(JsValue::Num(f64::from(len)), true, false, false),
        );
        Ok(oid)
    }

    /// Allocate a native error instance. `synthetic` marks an
    /// interpreter-raised error whose message text is engine-specific.
    pub(crate) fn make_native_error(
        &mut self,
        kind: ErrKind,
        synthetic: bool,
    ) -> Result<ObjId, Abrupt> {
        let proto = self.intr.error_proto_for(kind);
        self.make_native_error_with_proto(kind, synthetic, proto)
    }

    /// Native error instance with an explicit prototype (subclass-aware).
    pub(crate) fn make_native_error_with_proto(
        &mut self,
        _kind: ErrKind,
        synthetic: bool,
        proto: ObjId,
    ) -> Result<ObjId, Abrupt> {
        let oid = self.alloc_obj(JsObject::new(ObjKind::Error, Some(proto)))?;
        if synthetic {
            let mut p = Property::with_attrs(
                JsValue::str_from("[trust-js-interp synthetic message]"),
                true,
                false,
                true,
            );
            p.synthetic = true;
            self.heap
                .obj_mut(oid)
                .props
                .insert(PropKey::from_str("message"), p);
        }
        Ok(oid)
    }
}

/// The mapped parameter name for an arguments-object key, if still mapped.
fn mapped_name<'a>(args: &'a trust_js_value::ArgsData, key: &PropKey) -> Option<&'a str> {
    let PropKey::Str(u) = key else { return None };
    let i = array_index_of(u)? as usize;
    args.map.get(i)?.as_deref()
}
