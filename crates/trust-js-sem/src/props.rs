// The property-descriptor machinery, written from the spec: OrdinaryDefine-
// OwnProperty / ValidateAndApplyPropertyDescriptor (10.1.6.3), the Array
// exotic [[DefineOwnProperty]] + ArraySetLength (10.4.2), the arguments
// exotic hooks (10.4.4), [[Delete]], ToPropertyDescriptor /
// FromPropertyDescriptor (6.2.6), and the own-surface soundness gates that
// keep every operation over a partially-modeled intrinsic a refusal instead
// of a guess.
//
// Author: Andrew Yates
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

use crate::interp::{strict_eq, Abrupt, Interp};
use crate::value::{
    array_index_of, units_eq_ascii, units_from_str, units_to_lossy, ObjId, ObjKind, Object, Prop,
    PropDesc, PropVal, Units, Value,
};

/// ECMA-262 ToUint32 (7.1.7) on an already-ToNumber'd value: total, exact.
#[must_use]
pub fn to_uint32(n: f64) -> u32 {
    if !n.is_finite() || n == 0.0 {
        return 0;
    }
    let t = n.trunc();
    // fmod is exact for f64, so the modulo below is the spec's real-number
    // modulo whenever |t| has integral value (it does: trunc).
    let m = t % 4_294_967_296.0;
    let m = if m < 0.0 { m + 4_294_967_296.0 } else { m };
    #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
    {
        m as u32
    }
}

impl Interp {
    // -- arguments-object mapping helpers ------------------------------------

    /// The (env, param-name) a still-mapped arguments index aliases.
    pub(crate) fn args_mapped_name(&self, oid: ObjId, key: &Units) -> Option<(crate::value::EnvId, String)> {
        let ObjKind::Arguments(am) = &self.obj(oid).kind else {
            return None;
        };
        let i = array_index_of(key)? as usize;
        am.map.get(i).cloned().flatten().map(|n| (am.env, n))
    }

    fn args_unmap(&mut self, oid: ObjId, key: &Units) {
        let Some(i) = array_index_of(key) else { return };
        if let ObjKind::Arguments(am) = &mut self.obj_mut(oid).kind {
            if let Some(slot) = am.map.get_mut(i as usize) {
                *slot = None;
            }
        }
    }

    /// Read a binding value by name, walking from `env` upward.
    pub(crate) fn binding_value_lookup(&self, env: crate::value::EnvId, name: &str) -> Value {
        let mut cur = Some(env);
        while let Some(e) = cur {
            if let Some(b) = self.envs[e.0 as usize].bindings.get(name) {
                return b.value.clone();
            }
            cur = self.envs[e.0 as usize].parent;
        }
        Value::Undefined
    }

    pub(crate) fn set_binding_value(&mut self, env: crate::value::EnvId, name: &str, v: Value) {
        let mut cur = Some(env);
        while let Some(e) = cur {
            if let Some(b) = self.envs[e.0 as usize].bindings.get_mut(name) {
                b.value = v;
                return;
            }
            cur = self.envs[e.0 as usize].parent;
        }
    }

    /// The own property with any arguments-map alias resolved into the value.
    pub(crate) fn own_prop_resolved(&self, oid: ObjId, key: &Units) -> Option<Prop> {
        // A typed array's canonical-numeric-index keys are integer-indexed
        // exotic own properties synthesized over the buffer bytes (writable,
        // enumerable, configurable data). An out-of-range canonical index has
        // no own property; a non-numeric key is an ordinary own property.
        if matches!(self.obj(oid).kind, ObjKind::TypedArray { .. }) {
            if let Some(n) = crate::typedarray::canonical_numeric_index(key) {
                let f = self.ta_fields(oid).expect("typed array");
                return self.ta_valid_index(f, n).map(|_| Prop {
                    val: PropVal::Data {
                        value: self.ta_element_get(oid, n),
                        writable: true,
                    },
                    enumerable: true,
                    configurable: true,
                    synthetic: false,
                });
            }
        }
        let p = self.obj(oid).props.get(key)?.clone();
        if p.is_data() {
            if let Some((env, name)) = self.args_mapped_name(oid, key) {
                let mut p = p;
                if let PropVal::Data { value, .. } = &mut p.val {
                    *value = self.binding_value_lookup(env, &name);
                }
                return Some(p);
            }
        }
        Some(p)
    }

    // -- soundness gates -----------------------------------------------------

    /// Is our model of this object's OWN surface complete (every own property
    /// a real engine has is in `props`, string-keyed)? Required by define/
    /// getOwnPropertyNames/keys/freeze/seal walk operations.
    pub(crate) fn own_surface_complete(&self, oid: ObjId) -> Result<(), String> {
        if oid == self.global {
            return Err("global object own surface unmodeled".to_string());
        }
        if self.intr.opaque_hosts.contains(&oid) {
            return Err("intrinsic host-object own surface unmodeled".to_string());
        }
        if self.intr.host_statics_danger.contains_key(&oid) {
            return Err("intrinsic constructor own-key order is engine latitude".to_string());
        }
        if oid == self.intr.object_proto
            || oid == self.intr.function_proto
            || oid == self.intr.array_proto
            || oid == self.intr.string_proto
            || oid == self.intr.number_proto
            || oid == self.intr.boolean_proto
            || oid == self.intr.symbol_proto
            || oid == self.intr.regexp_proto
            || oid == self.intr.regexp_string_iterator_proto
            || oid == self.intr.promise_proto
            || oid == self.intr.async_function_proto
            || oid == self.intr.map_proto
            || oid == self.intr.set_proto
            || oid == self.intr.weakmap_proto
            || oid == self.intr.weakset_proto
            || oid == self.intr.map_iterator_proto
            || oid == self.intr.set_iterator_proto
            || self.intr.is_binary_proto(oid)
            || self.intr.error_protos().contains(&oid)
        {
            // Intrinsic prototype own-key ORDER (and full surface) is engine
            // latitude even where every property is modeled.
            return Err("intrinsic prototype own surface partially modeled".to_string());
        }
        match &self.obj(oid).kind {
            ObjKind::Plain
            | ObjKind::Array
            | ObjKind::Arguments(_)
            | ObjKind::StringObj(_)
            | ObjKind::NumberObj(_)
            | ObjKind::BoolObj(_)
            // A Symbol wrapper / Date object has no own string properties: its
            // enumerable-own surface is soundly empty.
            | ObjKind::SymbolObj(_)
            | ObjKind::BigIntObj(_)
            | ObjKind::DateObj(_)
            // A RegExp object's only own property is `lastIndex` (fully
            // modeled); a RegExp String Iterator has none.
            | ObjKind::RegExpObj(_)
            | ObjKind::RegExpStringIterator { .. }
            // A generator instance / array iterator / string iterator has no
            // own properties: its enumerable-own surface is soundly empty.
            | ObjKind::Generator(_)
            | ObjKind::ArrayIterator { .. }
            | ObjKind::StringIterator { .. }
            // ArrayBuffer/DataView instances have no own string properties; a
            // typed array's own surface (element indices + string props) is
            // fully modeled.
            | ObjKind::ArrayBuffer(_)
            | ObjKind::DataView { .. }
            | ObjKind::TypedArray { .. }
            // Map/Set/WeakMap/WeakSet instances and their iterators keep their
            // state in internal slots: no own string properties, soundly empty.
            | ObjKind::Map(_)
            | ObjKind::Set(_)
            | ObjKind::WeakMap(_)
            | ObjKind::WeakSet(_)
            | ObjKind::MapIterator { .. }
            | ObjKind::SetIterator { .. }
            // A Promise instance has no own properties: soundly empty.
            | ObjKind::Promise(_) => Ok(()),
            // Sloppy-mode user functions carry legacy own `caller`/
            // `arguments` in real engines (non-spec surface): incomplete.
            // Method-class functions (accessors) do not.
            ObjKind::Function(crate::value::FnImpl::User { lit, .. })
                if !lit.strict && !lit.is_method =>
            {
                Err("sloppy function legacy own caller/arguments (engine surface)".to_string())
            }
            ObjKind::Function(_) => Ok(()),
            ObjKind::Error => {
                Err("error instance carries engine-incidental own properties".to_string())
            }
            ObjKind::IntrinsicOpaque => Err("intrinsic own surface unmodeled".to_string()),
            // A proxy has no ordinary own surface: whole-surface walks must
            // route through its [[OwnPropertyKeys]] trap instead of here.
            ObjKind::Proxy { .. } => {
                Err("proxy own surface is trap-defined (route through [[OwnPropertyKeys]])".to_string())
            }
        }
    }

    /// Own string keys in exact spec order, gated on surface completeness.
    /// (Intrinsic own-key ORDER is engine latitude even where the SET is
    /// known, so intrinsics always refuse here.)
    pub(crate) fn own_keys_exact(&self, oid: ObjId) -> Result<Vec<Units>, String> {
        self.own_surface_complete(oid)?;
        Ok(self.ordered_own_keys_full(oid))
    }

    // -- [[DefineOwnProperty]] ----------------------------------------------

    /// The full [[DefineOwnProperty]] dispatcher. Ok(false) = rejected
    /// (caller turns it into TypeError or a silent failure); Err = throw or
    /// refusal.
    pub(crate) fn define_own_property(
        &mut self,
        oid: ObjId,
        key: &Units,
        desc: &PropDesc,
    ) -> Result<bool, Abrupt> {
        // A proxy receiver routes [[DefineOwnProperty]] through its trap.
        if matches!(self.obj(oid).kind, ObjKind::Proxy { .. }) {
            return self.mop_define_own(oid, &crate::value::PropertyKey::Str(key.clone()), desc);
        }
        // Sound-model gate: an own MISS where the real engine may hold an
        // unmodeled own property makes the current-descriptor input to
        // ValidateAndApply unknown.
        if oid == self.global {
            return Err(Abrupt::Fatal(
                "defineProperty on the global object (attribute surface unmodeled)".to_string(),
            ));
        }
        let name = units_to_lossy(key);
        if !self.obj(oid).props.contains_key(key) {
            if let Some(gap) = self.own_miss_gap(oid, &name) {
                return Err(Abrupt::Fatal(format!("defineProperty: {gap}")));
            }
        }
        match &self.obj(oid).kind {
            ObjKind::Array => self.array_define_own(oid, key, desc),
            ObjKind::Arguments(_) => self.args_define_own(oid, key, desc),
            ObjKind::TypedArray { .. } => self.ta_define_own(oid, key, desc),
            _ => self.ordinary_define_own(oid, key, desc),
        }
    }

    /// OrdinaryDefineOwnProperty + ValidateAndApplyPropertyDescriptor.
    pub(crate) fn ordinary_define_own(
        &mut self,
        oid: ObjId,
        key: &Units,
        desc: &PropDesc,
    ) -> Result<bool, Abrupt> {
        let current = self.own_prop_resolved(oid, key);
        let Some(current) = current else {
            if !self.obj(oid).extensible {
                return Ok(false);
            }
            let prop = if desc.is_accessor() {
                Prop {
                    val: PropVal::Accessor {
                        get: desc.get.flatten(),
                        set: desc.set.flatten(),
                    },
                    enumerable: desc.enumerable.unwrap_or(false),
                    configurable: desc.configurable.unwrap_or(false),
                    synthetic: false,
                }
            } else {
                Prop {
                    val: PropVal::Data {
                        value: desc.value.clone().unwrap_or(Value::Undefined),
                        writable: desc.writable.unwrap_or(false),
                    },
                    enumerable: desc.enumerable.unwrap_or(false),
                    configurable: desc.configurable.unwrap_or(false),
                    synthetic: false,
                }
            };
            self.obj_mut(oid).props.insert(key.clone(), prop);
            return Ok(true);
        };

        // Step 2 of ValidateAndApply: every field absent → true.
        if desc.value.is_none()
            && desc.writable.is_none()
            && desc.get.is_none()
            && desc.set.is_none()
            && desc.enumerable.is_none()
            && desc.configurable.is_none()
        {
            return Ok(true);
        }

        let cur_is_data = current.is_data();
        if !current.configurable {
            if desc.configurable == Some(true) {
                return Ok(false);
            }
            if let Some(e) = desc.enumerable {
                if e != current.enumerable {
                    return Ok(false);
                }
            }
            if !desc.is_generic() && desc.is_accessor() == cur_is_data {
                return Ok(false);
            }
            match &current.val {
                PropVal::Accessor { get, set } => {
                    if let Some(g) = &desc.get {
                        if *g != *get {
                            return Ok(false);
                        }
                    }
                    if let Some(s) = &desc.set {
                        if *s != *set {
                            return Ok(false);
                        }
                    }
                }
                PropVal::Data { value, writable } => {
                    if !writable {
                        if desc.writable == Some(true) {
                            return Ok(false);
                        }
                        if let Some(v) = &desc.value {
                            if current.synthetic {
                                return Err(Abrupt::Fatal(
                                    "defineProperty compares an engine-specific value".to_string(),
                                ));
                            }
                            if !same_value(self, v, value) {
                                return Ok(false);
                            }
                        }
                    }
                }
            }
        }

        // Apply.
        let is_args_mapped = self.args_mapped_name(oid, key);
        let p = self
            .obj_mut(oid)
            .props
            .get_mut(key)
            .expect("current exists");
        if desc.is_accessor() && p.is_data() {
            p.val = PropVal::Accessor {
                get: desc.get.clone().flatten(),
                set: desc.set.clone().flatten(),
            };
            p.synthetic = false;
        } else if desc.is_data() && !p.is_data() {
            p.val = PropVal::Data {
                value: desc.value.clone().unwrap_or(Value::Undefined),
                writable: desc.writable.unwrap_or(false),
            };
            p.synthetic = false;
        } else {
            match &mut p.val {
                PropVal::Data { value, writable } => {
                    if let Some(v) = &desc.value {
                        *value = v.clone();
                        p.synthetic = false;
                    }
                    if let Some(w) = desc.writable {
                        *writable = w;
                    }
                }
                PropVal::Accessor { get, set } => {
                    if let Some(g) = &desc.get {
                        *get = *g;
                    }
                    if let Some(s) = &desc.set {
                        *set = *s;
                    }
                }
            }
        }
        if let Some(e) = desc.enumerable {
            p.enumerable = e;
        }
        if let Some(c) = desc.configurable {
            p.configurable = c;
        }
        // Keep a mapped arguments slot's ordinary prop mirror in sync (the
        // exotic-level binding write happens in args_define_own).
        let _ = is_args_mapped;
        Ok(true)
    }

    /// Arguments exotic [[DefineOwnProperty]] (10.4.4.2).
    fn args_define_own(&mut self, oid: ObjId, key: &Units, desc: &PropDesc) -> Result<bool, Abrupt> {
        let mapped = self.args_mapped_name(oid, key);
        let mut new_desc = desc.clone();
        if let Some((env, name)) = &mapped {
            if new_desc.is_data() && new_desc.value.is_none() && new_desc.writable == Some(false) {
                new_desc.value = Some(self.binding_value_lookup(*env, name));
            }
        }
        let allowed = self.ordinary_define_own(oid, key, &new_desc)?;
        if !allowed {
            return Ok(false);
        }
        if let Some((env, name)) = mapped {
            if desc.is_accessor() {
                self.args_unmap(oid, key);
            } else {
                if let Some(v) = &desc.value {
                    self.set_binding_value(env, &name, v.clone());
                }
                if desc.writable == Some(false) {
                    self.args_unmap(oid, key);
                }
            }
        }
        Ok(true)
    }

    /// Array exotic [[DefineOwnProperty]] (10.4.2.1).
    fn array_define_own(&mut self, oid: ObjId, key: &Units, desc: &PropDesc) -> Result<bool, Abrupt> {
        if units_eq_ascii(key, "length") {
            return self.array_set_length(oid, desc);
        }
        if let Some(i) = array_index_of(key) {
            let (old_len, len_writable) = self.array_length_state(oid);
            if i >= old_len && !len_writable {
                return Ok(false);
            }
            let succeeded = self.ordinary_define_own(oid, key, desc)?;
            if !succeeded {
                return Ok(false);
            }
            if i >= old_len {
                self.array_write_length_value(oid, f64::from(i) + 1.0);
            }
            return Ok(true);
        }
        self.ordinary_define_own(oid, key, desc)
    }

    /// The array's (length value, length writable) pair.
    pub(crate) fn array_length_state(&self, oid: ObjId) -> (u32, bool) {
        match self.obj(oid).props.get(&units_from_str("length")) {
            Some(Prop {
                val: PropVal::Data { value: Value::Num(n), writable },
                ..
            }) => (crate::number::exact_uint32(*n).unwrap_or(0), *writable),
            _ => (0, true),
        }
    }

    fn array_write_length_value(&mut self, oid: ObjId, len: f64) {
        if let Some(p) = self.obj_mut(oid).props.get_mut(&units_from_str("length")) {
            if let PropVal::Data { value, .. } = &mut p.val {
                *value = Value::Num(len);
            }
        }
    }

    fn array_write_length_writable(&mut self, oid: ObjId, w: bool) {
        if let Some(p) = self.obj_mut(oid).props.get_mut(&units_from_str("length")) {
            if let PropVal::Data { writable, .. } = &mut p.val {
                *writable = w;
            }
        }
    }

    /// ArraySetLength (10.4.2.4).
    pub(crate) fn array_set_length(&mut self, oid: ObjId, desc: &PropDesc) -> Result<bool, Abrupt> {
        let Some(v) = desc.value.clone() else {
            return self.ordinary_define_own(oid, &units_from_str("length"), desc);
        };
        // Steps 3-4: ToUint32 and ToNumber are SEPARATE coercions — an
        // impure valueOf observably runs twice.
        let n1 = self.to_number(&v)?;
        let new_len = to_uint32(n1);
        let n2 = self.to_number(&v)?;
        let matches = if n2.is_nan() {
            false
        } else {
            f64::from(new_len) == n2
        };
        if !matches {
            return Err(self.throw_native(crate::value::NativeErrorKind::RangeError));
        }
        let mut new_len_desc = desc.clone();
        new_len_desc.value = Some(Value::Num(f64::from(new_len)));
        let (old_len, len_writable) = self.array_length_state(oid);
        if new_len >= old_len {
            return self.ordinary_define_own(oid, &units_from_str("length"), &new_len_desc);
        }
        if !len_writable {
            return Ok(false);
        }
        let new_writable = new_len_desc.writable != Some(false);
        if !new_writable {
            new_len_desc.writable = Some(true); // deferred per step 12
        }
        let succeeded =
            self.ordinary_define_own(oid, &units_from_str("length"), &new_len_desc)?;
        if !succeeded {
            return Ok(false);
        }
        // Delete indices >= newLen, highest first; stop at a non-configurable
        // element.
        let mut doomed: Vec<(u32, Units)> = self
            .obj(oid)
            .props
            .iter()
            .filter_map(|(k, _)| array_index_of(k).filter(|i| *i >= new_len).map(|i| (i, k.clone())))
            .collect();
        doomed.sort_by(|a, b| b.0.cmp(&a.0));
        for (i, k) in doomed {
            let configurable = self
                .obj(oid)
                .props
                .get(&k)
                .map_or(true, |p| p.configurable);
            if !configurable {
                self.array_write_length_value(oid, f64::from(i) + 1.0);
                if !new_writable {
                    self.array_write_length_writable(oid, false);
                }
                return Ok(false);
            }
            self.obj_mut(oid).props.shift_remove(&k);
        }
        if !new_writable {
            self.array_write_length_writable(oid, false);
        }
        Ok(true)
    }

    // -- [[Delete]] ----------------------------------------------------------

    /// [[Delete]] with the miss-danger discipline. Ok(bool) per spec.
    pub(crate) fn delete_property(&mut self, oid: ObjId, key: &Units) -> Result<bool, Abrupt> {
        if matches!(self.obj(oid).kind, ObjKind::Proxy { .. }) {
            return self.mop_delete(oid, &crate::value::PropertyKey::Str(key.clone()));
        }
        // Typed-array integer-indexed [[Delete]] (23.2.3.x): a valid in-bounds
        // index cannot be deleted (false); an out-of-range canonical index
        // "succeeds" (true).
        if matches!(self.obj(oid).kind, ObjKind::TypedArray { .. }) {
            if let Some(n) = crate::typedarray::canonical_numeric_index(key) {
                let f = self.ta_fields(oid).expect("typed array");
                return Ok(self.ta_valid_index(f, n).is_none());
            }
        }
        match self.obj(oid).props.get(key) {
            None => {
                let name = units_to_lossy(key);
                if let Some(gap) = self.own_miss_gap(oid, &name) {
                    return Err(Abrupt::Fatal(format!("delete: {gap}")));
                }
                Ok(true)
            }
            Some(p) => {
                if !p.configurable {
                    return Ok(false);
                }
                self.obj_mut(oid).props.shift_remove(key);
                self.args_unmap(oid, key);
                Ok(true)
            }
        }
    }

    // -- descriptor <-> object conversions ----------------------------------

    /// ToPropertyDescriptor (6.2.6.5): reads fields via HasProperty + Get in
    /// spec order.
    pub(crate) fn to_property_descriptor(&mut self, v: &Value) -> Result<PropDesc, Abrupt> {
        let Value::Obj(oid) = v else {
            return Err(self.throw_native(crate::value::NativeErrorKind::TypeError));
        };
        let oid = *oid;
        let mut d = PropDesc::default();
        // enumerable
        if self.has_property_checked(oid, &units_from_str("enumerable"))? {
            let x = self.get_from_object(oid, &units_from_str("enumerable"))?;
            d.enumerable = Some(self.to_boolean(&x));
        }
        // configurable
        if self.has_property_checked(oid, &units_from_str("configurable"))? {
            let x = self.get_from_object(oid, &units_from_str("configurable"))?;
            d.configurable = Some(self.to_boolean(&x));
        }
        // value
        if self.has_property_checked(oid, &units_from_str("value"))? {
            let x = self.get_from_object(oid, &units_from_str("value"))?;
            d.value = Some(x);
        }
        // writable
        if self.has_property_checked(oid, &units_from_str("writable"))? {
            let x = self.get_from_object(oid, &units_from_str("writable"))?;
            d.writable = Some(self.to_boolean(&x));
        }
        // get
        if self.has_property_checked(oid, &units_from_str("get"))? {
            let x = self.get_from_object(oid, &units_from_str("get"))?;
            d.get = Some(match x {
                Value::Undefined => None,
                Value::Obj(f) if self.obj(f).is_callable() => Some(f),
                _ => return Err(self.throw_native(crate::value::NativeErrorKind::TypeError)),
            });
        }
        // set
        if self.has_property_checked(oid, &units_from_str("set"))? {
            let x = self.get_from_object(oid, &units_from_str("set"))?;
            d.set = Some(match x {
                Value::Undefined => None,
                Value::Obj(f) if self.obj(f).is_callable() => Some(f),
                _ => return Err(self.throw_native(crate::value::NativeErrorKind::TypeError)),
            });
        }
        if (d.get.is_some() || d.set.is_some()) && (d.value.is_some() || d.writable.is_some()) {
            return Err(self.throw_native(crate::value::NativeErrorKind::TypeError));
        }
        Ok(d)
    }

    /// FromPropertyDescriptor (6.2.6.4) on a resolved own property.
    pub(crate) fn from_property_descriptor(&mut self, p: &Prop) -> Result<Value, Abrupt> {
        if p.synthetic {
            return Err(Abrupt::Fatal(
                "descriptor of an engine-specific (synthetic) value".to_string(),
            ));
        }
        let oid = self.alloc(Object::new(ObjKind::Plain, Some(self.intr.object_proto)));
        let put = |it: &mut Interp, k: &str, v: Value| {
            it.obj_mut(oid).props.insert(units_from_str(k), Prop::data(v));
        };
        match &p.val {
            PropVal::Data { value, writable } => {
                put(self, "value", value.clone());
                put(self, "writable", Value::Bool(*writable));
            }
            PropVal::Accessor { get, set } => {
                put(
                    self,
                    "get",
                    get.map_or(Value::Undefined, Value::Obj),
                );
                put(
                    self,
                    "set",
                    set.map_or(Value::Undefined, Value::Obj),
                );
            }
        }
        put(self, "enumerable", Value::Bool(p.enumerable));
        put(self, "configurable", Value::Bool(p.configurable));
        Ok(Value::Obj(oid))
    }
}

/// SameValue (7.2.10): strict equality but NaN==NaN and +0 != -0.
pub(crate) fn same_value(it: &Interp, a: &Value, b: &Value) -> bool {
    match (a, b) {
        (Value::Num(x), Value::Num(y)) => {
            if x.is_nan() && y.is_nan() {
                true
            } else {
                x == y && x.is_sign_negative() == y.is_sign_negative()
            }
        }
        _ => strict_eq(it, a, b),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn to_uint32_vectors() {
        assert_eq!(to_uint32(0.0), 0);
        assert_eq!(to_uint32(-0.0), 0);
        assert_eq!(to_uint32(1.5), 1);
        assert_eq!(to_uint32(-1.0), 4_294_967_295);
        assert_eq!(to_uint32(4_294_967_296.0), 0);
        assert_eq!(to_uint32(4_294_967_297.0), 1);
        assert_eq!(to_uint32(f64::NAN), 0);
        assert_eq!(to_uint32(f64::INFINITY), 0);
        assert_eq!(to_uint32(-2.5), 4_294_967_294);
        assert_eq!(to_uint32(1e80), 0);
    }
}
