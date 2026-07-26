// Symbol values (6.1.5) and the symbol-keyed property surface: the %Symbol%
// function + registry (20.4.1-20.4.2), Symbol.prototype (20.4.3), and the
// symbol analogues of [[Get]]/[[Set]]/[[HasProperty]]/[[Delete]]/
// [[DefineOwnProperty]] over `Object.sym_props`. The string-keyed machinery in
// expr.rs/props.rs is untouched; here the same soundness discipline is applied
// per symbol key — a MISS of a well-known symbol a real engine owns but we do
// not model refuses (never a wrong `undefined`), while an ordinary user
// object's symbol surface is complete.
//
// Author: Andrew Yates
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

use crate::interp::{Abrupt, ERes, Interp};
use crate::value::{
    units_from_str, Builtin, NativeErrorKind, ObjId, ObjKind, Prop, PropDesc, PropVal, PropertyKey,
    SymData, SymId, Units, Value,
};
use std::rc::Rc;

impl Interp {
    // -- symbol value helpers ------------------------------------------------

    /// SymbolDescriptiveString (20.4.3.3.1): `"Symbol(" + desc + ")"`.
    #[must_use]
    pub(crate) fn symbol_descriptive_string(&self, sid: SymId) -> Units {
        let mut out = units_from_str("Symbol(");
        if let Some(d) = &self.sym_data(sid).desc {
            out.extend_from_slice(d);
        }
        out.push(u16::from(b')'));
        out
    }

    /// thisSymbolValue (20.4.3): unwrap a Symbol primitive or a Symbol wrapper.
    pub(crate) fn this_symbol_value(&mut self, this: &Value) -> Result<SymId, Abrupt> {
        match this {
            Value::Sym(s) => Ok(*s),
            Value::Obj(o) => match self.obj(*o).kind {
                ObjKind::SymbolObj(s) => Ok(s),
                _ => Err(self.throw_native(NativeErrorKind::TypeError)),
            },
            _ => Err(self.throw_native(NativeErrorKind::TypeError)),
        }
    }

    // -- symbol-keyed property surface --------------------------------------

    /// Refusal reason when a symbol-key MISS at `oid` is unsound: a real engine
    /// owns a well-known symbol here we do not model, or the object's whole
    /// symbol surface is unmodeled (global/console). None = soundly absent.
    pub(crate) fn sym_miss_danger(&self, oid: ObjId, sid: SymId) -> Option<String> {
        if oid == self.global {
            return Some("global-object symbol surface unmodeled".to_string());
        }
        if oid == self.intr.console {
            return Some("host-object (console) symbol surface unmodeled".to_string());
        }
        if self.intr.sym_real_owns(oid, sid) {
            return Some("unimplemented well-known symbol property".to_string());
        }
        None
    }

    /// OrdinaryGet with a symbol key (10.1.8.1). Getters run with `receiver`.
    pub(crate) fn get_with_receiver_sym(
        &mut self,
        oid: ObjId,
        sid: SymId,
        receiver: Value,
    ) -> ERes {
        let mut cur = Some(oid);
        let mut hops = 0;
        while let Some(o) = cur {
            if hops >= 64 {
                return Err(Abrupt::Fatal("prototype chain too deep".to_string()));
            }
            if matches!(self.obj(o).kind, ObjKind::Proxy { .. }) {
                return self.mop_get(o, &PropertyKey::Sym(sid), receiver);
            }
            if let Some(p) = self.obj(o).sym_props.get(&sid).cloned() {
                return match p.val {
                    PropVal::Data { value, .. } => Ok(value),
                    PropVal::Accessor { get: None, .. } => Ok(Value::Undefined),
                    PropVal::Accessor { get: Some(g), .. } => {
                        self.call_function(g, receiver, Vec::new(), false)
                    }
                };
            }
            if let Some(gap) = self.sym_miss_danger(o, sid) {
                return Err(Abrupt::Fatal(gap));
            }
            cur = self.obj(o).proto;
            hops += 1;
        }
        Ok(Value::Undefined)
    }

    /// GetValue for `base[symbol]` — primitives resolve through their wrapper
    /// prototype, exactly like the string path in `get_prop_value`.
    pub(crate) fn get_prop_value_sym(&mut self, base: &Value, sid: SymId) -> ERes {
        match base {
            Value::Obj(oid) => self.get_with_receiver_sym(*oid, sid, base.clone()),
            Value::Str(_) => {
                self.get_with_receiver_sym(self.intr.string_proto, sid, base.clone())
            }
            Value::Num(_) => {
                self.get_with_receiver_sym(self.intr.number_proto, sid, base.clone())
            }
            Value::BigInt(_) => {
                self.get_with_receiver_sym(self.intr.bigint_proto, sid, base.clone())
            }
            Value::Bool(_) => {
                self.get_with_receiver_sym(self.intr.boolean_proto, sid, base.clone())
            }
            Value::Sym(_) => {
                self.get_with_receiver_sym(self.intr.symbol_proto, sid, base.clone())
            }
            Value::Undefined | Value::Null => {
                Err(self.throw_native(NativeErrorKind::TypeError))
            }
        }
    }

    /// HasProperty (7.3.12) with a symbol key.
    pub(crate) fn has_property_sym(&self, oid: ObjId, sid: SymId) -> Result<bool, Abrupt> {
        let mut cur = Some(oid);
        let mut hops = 0;
        while let Some(o) = cur {
            if hops >= 64 {
                return Err(Abrupt::Fatal("prototype chain too deep".to_string()));
            }
            if matches!(self.obj(o).kind, ObjKind::Proxy { .. }) {
                return Err(Abrupt::Fatal(
                    "HasProperty reaches a proxy in the prototype chain (needs trap routing)"
                        .to_string(),
                ));
            }
            if self.obj(o).sym_props.contains_key(&sid) {
                return Ok(true);
            }
            if let Some(gap) = self.sym_miss_danger(o, sid) {
                return Err(Abrupt::Fatal(gap));
            }
            cur = self.obj(o).proto;
            hops += 1;
        }
        Ok(false)
    }

    /// GetMethod(v, @@symbol) (7.3.11): the callable at a symbol key, or None
    /// for undefined/null. A non-callable non-nullish value is a TypeError.
    pub(crate) fn get_method_symbol(
        &mut self,
        v: &Value,
        sid: SymId,
    ) -> Result<Option<ObjId>, Abrupt> {
        let m = self.get_prop_value_sym(v, sid)?;
        match m {
            Value::Undefined | Value::Null => Ok(None),
            Value::Obj(f) if self.obj(f).is_callable() => Ok(Some(f)),
            _ => Err(self.throw_native(NativeErrorKind::TypeError)),
        }
    }

    /// OrdinarySet with a symbol key (10.1.9). No array/length/arguments
    /// exotics apply to symbol keys.
    pub(crate) fn set_on_object_sym(
        &mut self,
        oid: ObjId,
        sid: SymId,
        v: Value,
        strict: bool,
    ) -> Result<(), Abrupt> {
        if matches!(self.obj(oid).kind, ObjKind::Proxy { .. }) {
            let ok = self.mop_set(oid, &PropertyKey::Sym(sid), v, Value::Obj(oid))?;
            return if ok { Ok(()) } else { self.set_reject(strict) };
        }
        if let Some(p) = self.obj(oid).sym_props.get(&sid) {
            match &p.val {
                PropVal::Data { writable, .. } => {
                    if !*writable {
                        return self.set_reject(strict);
                    }
                    let p = self.obj_mut(oid).sym_props.get_mut(&sid).expect("own hit");
                    if let PropVal::Data { value, .. } = &mut p.val {
                        *value = v;
                    }
                    return Ok(());
                }
                PropVal::Accessor { set, .. } => {
                    return match *set {
                        Some(s) => {
                            self.call_function(s, Value::Obj(oid), vec![v], false)?;
                            Ok(())
                        }
                        None => self.set_reject(strict),
                    };
                }
            }
        }
        if let Some(gap) = self.sym_miss_danger(oid, sid) {
            return Err(Abrupt::Fatal(format!("set: {gap}")));
        }
        let proto = self.obj(oid).proto;
        self.set_walk_chain_sym(proto, sid, v, strict, Value::Obj(oid), Some(oid))
    }

    fn set_walk_chain_sym(
        &mut self,
        start: Option<ObjId>,
        sid: SymId,
        v: Value,
        strict: bool,
        receiver: Value,
        create_on: Option<ObjId>,
    ) -> Result<(), Abrupt> {
        let mut cur = start;
        let mut hops = 0;
        while let Some(o) = cur {
            if hops >= 64 {
                return Err(Abrupt::Fatal("prototype chain too deep".to_string()));
            }
            if matches!(self.obj(o).kind, ObjKind::Proxy { .. }) {
                let ok = self.mop_set(o, &PropertyKey::Sym(sid), v, receiver)?;
                return if ok { Ok(()) } else { self.set_reject(strict) };
            }
            if let Some(p) = self.obj(o).sym_props.get(&sid) {
                match &p.val {
                    PropVal::Data { writable, .. } => {
                        if !*writable {
                            return self.set_reject(strict);
                        }
                        break;
                    }
                    PropVal::Accessor { set, .. } => {
                        return match *set {
                            Some(s) => {
                                self.call_function(s, receiver, vec![v], false)?;
                                Ok(())
                            }
                            None => self.set_reject(strict),
                        };
                    }
                }
            }
            if let Some(gap) = self.sym_miss_danger(o, sid) {
                return Err(Abrupt::Fatal(format!("set: {gap}")));
            }
            cur = self.obj(o).proto;
            hops += 1;
        }
        let Some(target) = create_on else {
            return self.set_reject(strict);
        };
        if !self.obj(target).extensible {
            return self.set_reject(strict);
        }
        self.obj_mut(target).sym_props.insert(sid, Prop::data(v));
        Ok(())
    }

    /// PutValue for `base[symbol] = v`.
    pub(crate) fn set_prop_value_sym(
        &mut self,
        base: &Value,
        sid: SymId,
        v: Value,
        strict: bool,
    ) -> Result<(), Abrupt> {
        match base {
            Value::Obj(oid) => self.set_on_object_sym(*oid, sid, v, strict),
            Value::Str(_) => {
                self.set_walk_chain_sym(Some(self.intr.string_proto), sid, v, strict, base.clone(), None)
            }
            Value::Num(_) => {
                self.set_walk_chain_sym(Some(self.intr.number_proto), sid, v, strict, base.clone(), None)
            }
            Value::BigInt(_) => {
                self.set_walk_chain_sym(Some(self.intr.bigint_proto), sid, v, strict, base.clone(), None)
            }
            Value::Bool(_) => {
                self.set_walk_chain_sym(Some(self.intr.boolean_proto), sid, v, strict, base.clone(), None)
            }
            Value::Sym(_) => {
                self.set_walk_chain_sym(Some(self.intr.symbol_proto), sid, v, strict, base.clone(), None)
            }
            Value::Undefined | Value::Null => {
                Err(self.throw_native(NativeErrorKind::TypeError))
            }
        }
    }

    /// [[Delete]] with a symbol key.
    pub(crate) fn delete_property_sym(&mut self, oid: ObjId, sid: SymId) -> Result<bool, Abrupt> {
        if matches!(self.obj(oid).kind, ObjKind::Proxy { .. }) {
            return self.mop_delete(oid, &PropertyKey::Sym(sid));
        }
        match self.obj(oid).sym_props.get(&sid) {
            None => {
                if let Some(gap) = self.sym_miss_danger(oid, sid) {
                    return Err(Abrupt::Fatal(format!("delete: {gap}")));
                }
                Ok(true)
            }
            Some(p) => {
                if !p.configurable {
                    return Ok(false);
                }
                self.obj_mut(oid).sym_props.shift_remove(&sid);
                Ok(true)
            }
        }
    }

    /// OrdinaryDefineOwnProperty + ValidateAndApply with a symbol key.
    pub(crate) fn define_own_property_sym(
        &mut self,
        oid: ObjId,
        sid: SymId,
        desc: &PropDesc,
    ) -> Result<bool, Abrupt> {
        if matches!(self.obj(oid).kind, ObjKind::Proxy { .. }) {
            return self.mop_define_own(oid, &PropertyKey::Sym(sid), desc);
        }
        if oid == self.global {
            return Err(Abrupt::Fatal(
                "defineProperty (symbol) on the global object".to_string(),
            ));
        }
        if !self.obj(oid).sym_props.contains_key(&sid) {
            if let Some(gap) = self.sym_miss_danger(oid, sid) {
                return Err(Abrupt::Fatal(format!("defineProperty: {gap}")));
            }
        }
        let current = self.obj(oid).sym_props.get(&sid).cloned();
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
            self.obj_mut(oid).sym_props.insert(sid, prop);
            return Ok(true);
        };

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
                            if !crate::props::same_value(self, v, value) {
                                return Ok(false);
                            }
                        }
                    }
                }
            }
        }
        let p = self
            .obj_mut(oid)
            .sym_props
            .get_mut(&sid)
            .expect("current exists");
        if desc.is_accessor() && p.is_data() {
            p.val = PropVal::Accessor {
                get: desc.get.clone().flatten(),
                set: desc.set.clone().flatten(),
            };
        } else if desc.is_data() && !p.is_data() {
            p.val = PropVal::Data {
                value: desc.value.clone().unwrap_or(Value::Undefined),
                writable: desc.writable.unwrap_or(false),
            };
        } else {
            match &mut p.val {
                PropVal::Data { value, writable } => {
                    if let Some(v) = &desc.value {
                        *value = v.clone();
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
        Ok(true)
    }

    // -- key-generic dispatchers --------------------------------------------

    pub(crate) fn get_prop_value_pk(&mut self, base: &Value, key: &PropertyKey) -> ERes {
        match key {
            PropertyKey::Str(u) => self.get_prop_value(base, u),
            PropertyKey::Sym(s) => self.get_prop_value_sym(base, *s),
        }
    }

    pub(crate) fn set_prop_value_pk(
        &mut self,
        base: &Value,
        key: &PropertyKey,
        v: Value,
        strict: bool,
    ) -> Result<(), Abrupt> {
        match key {
            PropertyKey::Str(u) => self.set_prop_value(base, u, v, strict),
            PropertyKey::Sym(s) => self.set_prop_value_sym(base, *s, v, strict),
        }
    }

    pub(crate) fn define_own_property_pk(
        &mut self,
        oid: ObjId,
        key: &PropertyKey,
        desc: &PropDesc,
    ) -> Result<bool, Abrupt> {
        match key {
            PropertyKey::Str(u) => self.define_own_property(oid, u, desc),
            PropertyKey::Sym(s) => self.define_own_property_sym(oid, *s, desc),
        }
    }

    /// The function `name` string for a property key (SetFunctionName, 10.2.9):
    /// a string key as-is; a symbol key as `[desc]`, or `""` if the symbol has
    /// no description.
    #[must_use]
    pub(crate) fn prop_key_name(&self, key: &PropertyKey) -> Units {
        match key {
            PropertyKey::Str(u) => u.clone(),
            PropertyKey::Sym(s) => match &self.sym_data(*s).desc {
                Some(d) => {
                    let mut out = Vec::with_capacity(d.len() + 2);
                    out.push(u16::from(b'['));
                    out.extend_from_slice(d);
                    out.push(u16::from(b']'));
                    out
                }
                None => Vec::new(),
            },
        }
    }

    // -- Symbol builtins -----------------------------------------------------

    pub(crate) fn dispatch_symbol_builtin(
        &mut self,
        b: Builtin,
        this: Value,
        args: &[Value],
        is_new: bool,
    ) -> ERes {
        let arg = |i: usize| args.get(i).cloned().unwrap_or(Value::Undefined);
        match b {
            Builtin::SymbolFn => {
                if is_new {
                    // `new Symbol()` is a TypeError (20.4.1).
                    return Err(self.throw_native(NativeErrorKind::TypeError));
                }
                let desc = match arg(0) {
                    Value::Undefined => None,
                    v => Some(self.to_string_units(&v)?),
                };
                let s = self.alloc_symbol(SymData {
                    desc,
                    well_known: None,
                    registry_key: None,
                });
                Ok(Value::Sym(s))
            }
            Builtin::SymbolFor => {
                let key = self.to_string_units(&arg(0))?;
                if let Some(s) = self.sym_registry.get(&key) {
                    return Ok(Value::Sym(*s));
                }
                let s = self.alloc_symbol(SymData {
                    desc: Some(key.clone()),
                    well_known: None,
                    registry_key: Some(key.clone()),
                });
                self.sym_registry.insert(key, s);
                Ok(Value::Sym(s))
            }
            Builtin::SymbolKeyFor => {
                let Value::Sym(s) = arg(0) else {
                    return Err(self.throw_native(NativeErrorKind::TypeError));
                };
                match &self.sym_data(s).registry_key {
                    Some(k) => Ok(Value::Str(Rc::new(k.clone()))),
                    None => Ok(Value::Undefined),
                }
            }
            Builtin::SymbolProtoValueOf | Builtin::SymbolProtoToPrimitive => {
                let s = self.this_symbol_value(&this)?;
                Ok(Value::Sym(s))
            }
            Builtin::SymbolProtoToString => {
                let s = self.this_symbol_value(&this)?;
                Ok(Value::Str(Rc::new(self.symbol_descriptive_string(s))))
            }
            Builtin::SymbolProtoDescriptionGet => {
                let s = self.this_symbol_value(&this)?;
                match &self.sym_data(s).desc {
                    Some(d) => Ok(Value::Str(Rc::new(d.clone()))),
                    None => Ok(Value::Undefined),
                }
            }
            Builtin::FunctionProtoHasInstance => {
                // OrdinaryHasInstance(this, arg0) (20.2.3.6 → 7.3.22).
                Ok(Value::Bool(self.ordinary_has_instance(&this, &arg(0))?))
            }
            Builtin::ObjectGetOwnPropertySymbols => {
                let oid = match arg(0) {
                    Value::Obj(o) => o,
                    // ToObject(undefined/null) is a TypeError (7.1.18).
                    Value::Undefined | Value::Null => {
                        return Err(self.throw_native(NativeErrorKind::TypeError));
                    }
                    // ToObject on a valid primitive (Boolean/Number/String/
                    // Symbol) yields a fresh wrapper whose [[OwnPropertyKeys]]
                    // holds no symbol keys, so the symbol list is empty.
                    _ => return Ok(Value::Obj(self.new_array(0))),
                };
                // A proxy routes through its ownKeys trap, keeping only symbols.
                let syms: Vec<Value> = if matches!(self.obj(oid).kind, ObjKind::Proxy { .. }) {
                    self.mop_own_keys(oid)?
                        .into_iter()
                        .filter_map(|k| match k {
                            PropertyKey::Sym(s) => Some(Value::Sym(s)),
                            PropertyKey::Str(_) => None,
                        })
                        .collect()
                } else {
                    // The symbol surface must be model-complete (intrinsics with
                    // unmodeled well-known symbols refuse via own_surface).
                    if !self.sym_surface_complete(oid) {
                        return Err(Abrupt::Fatal(
                            "getOwnPropertySymbols over an object with unmodeled symbol surface"
                                .to_string(),
                        ));
                    }
                    self.obj(oid)
                        .sym_props
                        .keys()
                        .map(|s| Value::Sym(*s))
                        .collect()
                };
                let n = syms.len();
                let arr = self.new_array(n);
                for (i, v) in syms.into_iter().enumerate() {
                    self.obj_mut(arr)
                        .props
                        .insert(units_from_str(&i.to_string()), Prop::data(v));
                }
                #[allow(clippy::cast_precision_loss)]
                self.set_array_length_raw(arr, n as f64);
                Ok(Value::Obj(arr))
            }
            _ => Err(Abrupt::Fatal(format!("symbol dispatch: {b:?}"))),
        }
    }

    /// Is `oid`'s OWN symbol surface completely modeled (every well-known
    /// symbol a real engine owns is in `sym_props`)?
    pub(crate) fn sym_surface_complete(&self, oid: ObjId) -> bool {
        if oid == self.global || oid == self.intr.console {
            return false;
        }
        // Intrinsics with unmodeled well-known symbols (array_proto's
        // @@unscopables, etc.) are incomplete; ordinary objects are complete.
        for sid in self.intr.wk_syms.iter() {
            if self.intr.sym_real_owns(oid, *sid) && !self.obj(oid).sym_props.contains_key(sid) {
                return false;
            }
        }
        matches!(
            self.obj(oid).kind,
            ObjKind::Plain
                | ObjKind::Array
                | ObjKind::Arguments(_)
                | ObjKind::StringObj(_)
                | ObjKind::NumberObj(_)
                | ObjKind::BoolObj(_)
                | ObjKind::SymbolObj(_)
                | ObjKind::DateObj(_)
                | ObjKind::RegExpObj(_)
                | ObjKind::RegExpStringIterator { .. }
                | ObjKind::Generator(_)
                | ObjKind::ArrayIterator { .. }
                | ObjKind::ArrayBuffer(_)
                | ObjKind::DataView { .. }
                | ObjKind::TypedArray { .. }
                | ObjKind::Function(_)
        )
    }

    /// OrdinaryHasInstance (7.3.22): the default `instanceof` behavior, shared
    /// by the operator and %Function.prototype%[@@hasInstance].
    pub(crate) fn ordinary_has_instance(&mut self, c: &Value, o: &Value) -> Result<bool, Abrupt> {
        let Value::Obj(cid) = c else {
            return Ok(false);
        };
        if !self.obj(*cid).is_callable() {
            return Ok(false);
        }
        if let ObjKind::Function(crate::value::FnImpl::Bound { target, .. }) = &self.obj(*cid).kind {
            let target = *target;
            return self.ordinary_has_instance(&Value::Obj(target), o);
        }
        let Value::Obj(mut cur) = o.clone() else {
            return Ok(false);
        };
        let proto_v = self.get_prop_value(c, &units_from_str("prototype"))?;
        let Value::Obj(proto) = proto_v else {
            return Err(self.throw_native(NativeErrorKind::TypeError));
        };
        let mut hops = 0;
        loop {
            // [[GetPrototypeOf]] routes through a proxy in the chain.
            match self.mop_get_proto(cur)? {
                None => return Ok(false),
                Some(p) => {
                    if p == proto {
                        return Ok(true);
                    }
                    cur = p;
                }
            }
            hops += 1;
            if hops >= 64 {
                return Err(Abrupt::Fatal("prototype chain too deep".to_string()));
            }
        }
    }
}

/// Project a Symbol value to the trace schema (mirrors the driver's
/// `projectValue` symbol arm): a well-known symbol carries `wk`; an ordinary
/// symbol carries its (escaped) description, or null.
#[must_use]
pub(crate) fn project_symbol(data: &SymData) -> trust_js_trace::ProjectedValue {
    if let Some(wk) = data.well_known {
        trust_js_trace::ProjectedValue::Sym {
            wk: Some(wk.to_string()),
            v: None,
        }
    } else {
        trust_js_trace::ProjectedValue::Sym {
            wk: None,
            v: data
                .desc
                .as_ref()
                .map(|d| crate::project::escape_units(d)),
        }
    }
}
