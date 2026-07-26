// The Proxy exotic object (ECMA-262 §10.5) and the complete %Reflect%
// namespace (§28.1), written from the spec. Every one of a proxy's 13
// essential internal methods routes through its handler traps with the FULL
// invariant checks (10.5.1-10.5.13): a missing trap falls through to the
// target's ordinary internal method; a present trap's result is validated
// against the target's non-configurable / non-extensible reality, and a
// violation is a TypeError. A revoked proxy (both [[ProxyTarget]] and
// [[ProxyHandler]] null) throws TypeError on every internal method.
//
// The metaobject-protocol dispatchers (`mop_*`) are the single routing layer:
// each picks the proxy internal method for a proxy receiver and the ordinary
// one otherwise, so a proxy of a proxy composes without special-casing. The
// ordinary property machinery in expr.rs/props.rs/symbol.rs is untouched
// except for the handful of top-of-dispatch proxy routes that hand control
// here.
//
// SOUNDNESS. A proxy never reaches the trace projection (project.rs refuses
// it): the driver's deep-print would invoke the ownKeys /
// getOwnPropertyDescriptor traps, which a pure structural read cannot
// reproduce. The synchronous-assert Proxy tests — the majority — never log the
// proxy, so they cover. Any operation over a proxy the router does not model
// exactly is a `NoCoverage` refusal, never a wrong trace.
//
// Author: Andrew Yates
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

use crate::interp::{Abrupt, ERes, Interp};
use crate::promise::NativeClosure;
use crate::props::same_value;
use crate::value::{
    units_from_str, units_to_lossy, Builtin, NativeErrorKind, ObjId, ObjKind, Object, Prop,
    PropDesc, PropVal, PropertyKey, Units, Value,
};
use std::rc::Rc;

/// Refusal reason when a construct query targets a builtin whose driver-firewall
/// replacement is constructable but the real intrinsic is not (see
/// `firewall_plain_fn_ctor`).
const FIREWALL_CTOR_REFUSAL: &str =
    "IsConstructor(Date.now): real intrinsic is not a constructor but the driver's clock-firewall replacement is (out of slice)";

/// ToLength (7.1.20) on an already-ToNumber'd value.
fn to_length_local(n: f64) -> u64 {
    if n.is_nan() || n <= 0.0 {
        0
    } else {
        let m = n.floor();
        if m > 9_007_199_254_740_991.0 {
            9_007_199_254_740_991
        } else {
            #[allow(clippy::cast_sign_loss, clippy::cast_possible_truncation)]
            {
                m as u64
            }
        }
    }
}

impl Interp {
    // -- proxy construction --------------------------------------------------

    /// ProxyCreate (10.5.14): a fresh Proxy exotic over `target`/`handler`.
    /// Both must be objects (else TypeError). [[Call]]/[[Construct]] presence
    /// is fixed here from the target and never changes (even after revoke).
    pub(crate) fn proxy_create(&mut self, target: Value, handler: Value) -> Result<ObjId, Abrupt> {
        let Value::Obj(t) = target else {
            return Err(self.throw_native(NativeErrorKind::TypeError));
        };
        let Value::Obj(h) = handler else {
            return Err(self.throw_native(NativeErrorKind::TypeError));
        };
        let callable = self.obj(t).is_callable();
        let constructor = callable && self.is_constructor(t);
        let p = self.alloc(Object::new(
            ObjKind::Proxy {
                target: Some(t),
                handler: Some(h),
                callable,
                constructor,
            },
            None,
        ));
        Ok(p)
    }

    /// The ([[ProxyTarget]], [[ProxyHandler]]) of a live proxy, or a TypeError
    /// if it has been revoked (10.5, "If handler is null, throw a TypeError").
    fn proxy_parts(&mut self, pid: ObjId) -> Result<(ObjId, ObjId), Abrupt> {
        match self.obj(pid).kind {
            ObjKind::Proxy {
                target: Some(t),
                handler: Some(h),
                ..
            } => Ok((t, h)),
            ObjKind::Proxy { .. } => Err(self.throw_native(NativeErrorKind::TypeError)),
            _ => Err(Abrupt::Fatal(
                "proxy internal method on a non-proxy (router invariant)".to_string(),
            )),
        }
    }

    fn is_proxy(&self, oid: ObjId) -> bool {
        matches!(self.obj(oid).kind, ObjKind::Proxy { .. })
    }

    /// GetMethod(handler, name) for a string-named trap (7.3.11): the callable
    /// at that key, None for undefined/null, TypeError for a non-callable.
    fn get_trap(&mut self, handler: ObjId, name: &str) -> Result<Option<ObjId>, Abrupt> {
        let m = self.get_from_object(handler, &units_from_str(name))?;
        match m {
            Value::Undefined | Value::Null => Ok(None),
            Value::Obj(f) if self.obj(f).is_callable() => Ok(Some(f)),
            _ => Err(self.throw_native(NativeErrorKind::TypeError)),
        }
    }

    /// The JS value form of a property key (a string or a symbol), for passing
    /// to a trap.
    fn key_value(&self, key: &PropertyKey) -> Value {
        match key {
            PropertyKey::Str(u) => Value::Str(Rc::new(u.clone())),
            PropertyKey::Sym(s) => Value::Sym(*s),
        }
    }

    // -- metaobject-protocol dispatchers (proxy vs ordinary) -----------------

    /// [[GetOwnProperty]](P) → the own descriptor, or None. Synthetic
    /// (engine-specific) values refuse (their text is not reproducible).
    pub(crate) fn mop_get_own_property(
        &mut self,
        oid: ObjId,
        key: &PropertyKey,
    ) -> Result<Option<Prop>, Abrupt> {
        if self.is_proxy(oid) {
            return self.proxy_get_own_property(oid, key);
        }
        match key {
            PropertyKey::Str(u) => {
                if let Some(p) = self.own_prop_resolved(oid, u) {
                    if p.synthetic {
                        return Err(Abrupt::Fatal(
                            "own descriptor of an engine-specific (synthetic) value".to_string(),
                        ));
                    }
                    return Ok(Some(p));
                }
                if let Some(gap) = self.own_miss_gap(oid, &units_to_lossy(u)) {
                    return Err(Abrupt::Fatal(format!("[[GetOwnProperty]]: {gap}")));
                }
                Ok(None)
            }
            PropertyKey::Sym(s) => {
                if let Some(p) = self.obj(oid).sym_props.get(s).cloned() {
                    return Ok(Some(p));
                }
                if let Some(gap) = self.sym_miss_danger(oid, *s) {
                    return Err(Abrupt::Fatal(format!("[[GetOwnProperty]]: {gap}")));
                }
                Ok(None)
            }
        }
    }

    /// [[Get]](P, Receiver).
    pub(crate) fn mop_get(&mut self, oid: ObjId, key: &PropertyKey, receiver: Value) -> ERes {
        if self.is_proxy(oid) {
            return self.proxy_get(oid, key, receiver);
        }
        match key {
            PropertyKey::Str(u) => self.get_with_receiver(oid, u, receiver),
            PropertyKey::Sym(s) => self.get_with_receiver_sym(oid, *s, receiver),
        }
    }

    /// [[Set]](P, V, Receiver) → the boolean success.
    pub(crate) fn mop_set(
        &mut self,
        oid: ObjId,
        key: &PropertyKey,
        v: Value,
        receiver: Value,
    ) -> Result<bool, Abrupt> {
        if self.is_proxy(oid) {
            return self.proxy_set(oid, key, v, receiver);
        }
        self.ordinary_set(oid, key, v, receiver)
    }

    /// [[HasProperty]](P).
    pub(crate) fn mop_has(&mut self, oid: ObjId, key: &PropertyKey) -> Result<bool, Abrupt> {
        if self.is_proxy(oid) {
            return self.proxy_has(oid, key);
        }
        self.ordinary_has(oid, key)
    }

    /// [[Delete]](P).
    pub(crate) fn mop_delete(&mut self, oid: ObjId, key: &PropertyKey) -> Result<bool, Abrupt> {
        if self.is_proxy(oid) {
            return self.proxy_delete(oid, key);
        }
        match key {
            PropertyKey::Str(u) => self.delete_property(oid, u),
            PropertyKey::Sym(s) => self.delete_property_sym(oid, *s),
        }
    }

    /// [[DefineOwnProperty]](P, Desc).
    pub(crate) fn mop_define_own(
        &mut self,
        oid: ObjId,
        key: &PropertyKey,
        desc: &PropDesc,
    ) -> Result<bool, Abrupt> {
        if self.is_proxy(oid) {
            return self.proxy_define_own(oid, key, desc);
        }
        self.define_own_property_pk(oid, key, desc)
    }

    /// [[OwnPropertyKeys]]() → the own keys in spec order (integer-ascending,
    /// then string insertion order, then symbol insertion order).
    pub(crate) fn mop_own_keys(&mut self, oid: ObjId) -> Result<Vec<PropertyKey>, Abrupt> {
        if self.is_proxy(oid) {
            return self.proxy_own_keys(oid);
        }
        let strs = self
            .own_keys_exact(oid)
            .map_err(|e| Abrupt::Fatal(format!("[[OwnPropertyKeys]]: {e}")))?;
        if !self.sym_surface_complete(oid) {
            return Err(Abrupt::Fatal(
                "[[OwnPropertyKeys]] over an object with unmodeled symbol surface".to_string(),
            ));
        }
        let mut keys: Vec<PropertyKey> = strs.into_iter().map(PropertyKey::Str).collect();
        for s in self.obj(oid).sym_props.keys() {
            keys.push(PropertyKey::Sym(*s));
        }
        Ok(keys)
    }

    /// [[GetPrototypeOf]]() → the prototype object, or None (null).
    pub(crate) fn mop_get_proto(&mut self, oid: ObjId) -> Result<Option<ObjId>, Abrupt> {
        if self.is_proxy(oid) {
            return self.proxy_get_proto(oid);
        }
        Ok(self.obj(oid).proto)
    }

    /// [[SetPrototypeOf]](V) → the boolean success.
    pub(crate) fn mop_set_proto(
        &mut self,
        oid: ObjId,
        proto: Option<ObjId>,
    ) -> Result<bool, Abrupt> {
        if self.is_proxy(oid) {
            return self.proxy_set_proto(oid, proto);
        }
        // %Object.prototype% is an Immutable Prototype Exotic Object (10.4.7):
        // [[SetPrototypeOf]](V) returns true iff SameValue(V, current), else
        // false — never actually mutating the [[Prototype]].
        if oid == self.intr.object_proto {
            return Ok(proto == self.obj(oid).proto);
        }
        // OrdinarySetPrototypeOf (10.1.2.1).
        if oid == self.global {
            return Err(Abrupt::Fatal(
                "setPrototypeOf on the global object (host surface unmodeled)".to_string(),
            ));
        }
        let current = self.obj(oid).proto;
        if proto == current {
            return Ok(true);
        }
        if !self.obj(oid).extensible {
            return Ok(false);
        }
        // Cycle check: walk up from `proto`, stopping at null or a proxy hop
        // (whose [[GetPrototypeOf]] is not the ordinary one).
        let mut p = proto;
        let mut hops = 0;
        while let Some(pp) = p {
            if pp == oid {
                return Ok(false);
            }
            if self.is_proxy(pp) {
                break;
            }
            p = self.obj(pp).proto;
            hops += 1;
            if hops >= 100_000 {
                return Err(Abrupt::Fatal("prototype chain too deep".to_string()));
            }
        }
        self.obj_mut(oid).proto = proto;
        Ok(true)
    }

    /// [[IsExtensible]]().
    pub(crate) fn mop_is_extensible(&mut self, oid: ObjId) -> Result<bool, Abrupt> {
        if self.is_proxy(oid) {
            return self.proxy_is_extensible(oid);
        }
        Ok(self.obj(oid).extensible)
    }

    /// [[PreventExtensions]]().
    pub(crate) fn mop_prevent_extensions(&mut self, oid: ObjId) -> Result<bool, Abrupt> {
        if self.is_proxy(oid) {
            return self.proxy_prevent_extensions(oid);
        }
        if oid == self.global {
            return Err(Abrupt::Fatal(
                "preventExtensions on the global object (host surface unmodeled)".to_string(),
            ));
        }
        self.obj_mut(oid).extensible = false;
        Ok(true)
    }

    /// OrdinarySet + OrdinarySetWithOwnDescriptor (10.1.9.1-2), receiver-aware
    /// and boolean, for a non-proxy `oid`. Only reached via the proxy router
    /// (the common `obj.x = v` path keeps the proven set_on_object machinery).
    fn ordinary_set(
        &mut self,
        oid: ObjId,
        key: &PropertyKey,
        v: Value,
        receiver: Value,
    ) -> Result<bool, Abrupt> {
        // Integer-Indexed exotic [[Set]] (10.4.5.5, as V8/Node implement it) for
        // a canonical numeric index on a typed array O:
        //   * an OUT-OF-RANGE index → TypedArraySetElement (coerces V observably
        //     once, stores nothing) and returns true — regardless of Receiver;
        //   * an in-range index with O === Receiver → TypedArraySetElement
        //     (coerces + stores) and returns true;
        //   * an in-range index with O != Receiver → OrdinarySet: the value
        //     lands on Receiver via CreateDataProperty (no coercion into O).
        if let PropertyKey::Str(u) = key {
            if matches!(self.obj(oid).kind, ObjKind::TypedArray { .. }) {
                if let Some(n) = crate::typedarray::canonical_numeric_index(u) {
                    let valid = {
                        let f = self.ta_fields(oid).expect("typed array");
                        self.ta_valid_index(f, n).is_some()
                    };
                    if !valid || same_value(self, &receiver, &Value::Obj(oid)) {
                        self.ta_element_set(oid, n, v)?;
                        return Ok(true);
                    }
                    // in-range, O != Receiver: fall through to OrdinarySet.
                }
            }
        }
        let own = match self.mop_get_own_property(oid, key)? {
            Some(d) => d,
            None => match self.mop_get_proto(oid)? {
                Some(parent) => return self.mop_set(parent, key, v, receiver),
                // No parent: treat as a default writable/enumerable/
                // configurable data descriptor with value undefined.
                None => Prop::data(Value::Undefined),
            },
        };
        match &own.val {
            PropVal::Data { writable, .. } => {
                if !*writable {
                    return Ok(false);
                }
                let Value::Obj(r) = receiver else {
                    return Ok(false);
                };
                match self.mop_get_own_property(r, key)? {
                    Some(existing) => {
                        if !existing.is_data() || !existing.writable() {
                            return Ok(false);
                        }
                        let d = PropDesc {
                            value: Some(v),
                            ..PropDesc::default()
                        };
                        self.mop_define_own(r, key, &d)
                    }
                    None => {
                        let d = PropDesc {
                            value: Some(v),
                            writable: Some(true),
                            enumerable: Some(true),
                            configurable: Some(true),
                            ..PropDesc::default()
                        };
                        self.mop_define_own(r, key, &d)
                    }
                }
            }
            PropVal::Accessor { set, .. } => match set {
                Some(s) => {
                    let s = *s;
                    self.call_function(s, receiver, vec![v], false)?;
                    Ok(true)
                }
                None => Ok(false),
            },
        }
    }

    /// OrdinaryHasProperty (7.3.12) for a non-proxy `oid`, `&mut` so a proxy
    /// prototype hop routes through its [[HasProperty]] trap.
    fn ordinary_has(&mut self, oid: ObjId, key: &PropertyKey) -> Result<bool, Abrupt> {
        // Typed-array integer-indexed [[HasProperty]] never consults the
        // prototype for a canonical numeric index.
        if let PropertyKey::Str(u) = key {
            if matches!(self.obj(oid).kind, ObjKind::TypedArray { .. }) {
                if let Some(n) = crate::typedarray::canonical_numeric_index(u) {
                    let f = self.ta_fields(oid).expect("typed array");
                    return Ok(self.ta_valid_index(f, n).is_some());
                }
            }
        }
        if self.mop_get_own_property(oid, key)?.is_some() {
            return Ok(true);
        }
        match self.mop_get_proto(oid)? {
            Some(parent) => self.mop_has(parent, key),
            None => Ok(false),
        }
    }

    // -- the 13 proxy internal methods (10.5.1-10.5.13) ----------------------

    /// 10.5.1 [[GetPrototypeOf]].
    fn proxy_get_proto(&mut self, pid: ObjId) -> Result<Option<ObjId>, Abrupt> {
        let (target, handler) = self.proxy_parts(pid)?;
        let Some(trap) = self.get_trap(handler, "getPrototypeOf")? else {
            return self.mop_get_proto(target);
        };
        let r = self.call_function(trap, Value::Obj(handler), vec![Value::Obj(target)], false)?;
        let proto = match r {
            Value::Obj(o) => Some(o),
            Value::Null => None,
            _ => return Err(self.throw_native(NativeErrorKind::TypeError)),
        };
        if self.mop_is_extensible(target)? {
            return Ok(proto);
        }
        let target_proto = self.mop_get_proto(target)?;
        if proto != target_proto {
            return Err(self.throw_native(NativeErrorKind::TypeError));
        }
        Ok(proto)
    }

    /// 10.5.2 [[SetPrototypeOf]].
    fn proxy_set_proto(&mut self, pid: ObjId, proto: Option<ObjId>) -> Result<bool, Abrupt> {
        let (target, handler) = self.proxy_parts(pid)?;
        let Some(trap) = self.get_trap(handler, "setPrototypeOf")? else {
            return self.mop_set_proto(target, proto);
        };
        let arg = proto.map_or(Value::Null, Value::Obj);
        let r = self.call_function(trap, Value::Obj(handler), vec![Value::Obj(target), arg], false)?;
        if !self.to_boolean(&r) {
            return Ok(false);
        }
        if self.mop_is_extensible(target)? {
            return Ok(true);
        }
        let target_proto = self.mop_get_proto(target)?;
        if proto != target_proto {
            return Err(self.throw_native(NativeErrorKind::TypeError));
        }
        Ok(true)
    }

    /// 10.5.3 [[IsExtensible]].
    fn proxy_is_extensible(&mut self, pid: ObjId) -> Result<bool, Abrupt> {
        let (target, handler) = self.proxy_parts(pid)?;
        let Some(trap) = self.get_trap(handler, "isExtensible")? else {
            return self.mop_is_extensible(target);
        };
        let r = self.call_function(trap, Value::Obj(handler), vec![Value::Obj(target)], false)?;
        let boolean = self.to_boolean(&r);
        let target_result = self.mop_is_extensible(target)?;
        if boolean != target_result {
            return Err(self.throw_native(NativeErrorKind::TypeError));
        }
        Ok(boolean)
    }

    /// 10.5.4 [[PreventExtensions]].
    fn proxy_prevent_extensions(&mut self, pid: ObjId) -> Result<bool, Abrupt> {
        let (target, handler) = self.proxy_parts(pid)?;
        let Some(trap) = self.get_trap(handler, "preventExtensions")? else {
            return self.mop_prevent_extensions(target);
        };
        let r = self.call_function(trap, Value::Obj(handler), vec![Value::Obj(target)], false)?;
        let boolean = self.to_boolean(&r);
        if boolean && self.mop_is_extensible(target)? {
            return Err(self.throw_native(NativeErrorKind::TypeError));
        }
        Ok(boolean)
    }

    /// 10.5.5 [[GetOwnProperty]].
    fn proxy_get_own_property(
        &mut self,
        pid: ObjId,
        key: &PropertyKey,
    ) -> Result<Option<Prop>, Abrupt> {
        let (target, handler) = self.proxy_parts(pid)?;
        let Some(trap) = self.get_trap(handler, "getOwnPropertyDescriptor")? else {
            return self.mop_get_own_property(target, key);
        };
        let kv = self.key_value(key);
        let trap_result = self.call_function(trap, Value::Obj(handler), vec![Value::Obj(target), kv], false)?;
        if !matches!(trap_result, Value::Obj(_) | Value::Undefined) {
            return Err(self.throw_native(NativeErrorKind::TypeError));
        }
        let target_desc = self.mop_get_own_property(target, key)?;
        if matches!(trap_result, Value::Undefined) {
            let Some(td) = target_desc else {
                return Ok(None);
            };
            if !td.configurable {
                return Err(self.throw_native(NativeErrorKind::TypeError));
            }
            if !self.mop_is_extensible(target)? {
                return Err(self.throw_native(NativeErrorKind::TypeError));
            }
            return Ok(None);
        }
        let extensible_target = self.mop_is_extensible(target)?;
        let result_desc = self.to_property_descriptor(&trap_result)?;
        let complete = complete_prop_from_desc(&result_desc);
        if !self.is_compatible_descriptor(extensible_target, &result_desc, target_desc.as_ref()) {
            return Err(self.throw_native(NativeErrorKind::TypeError));
        }
        if !complete.configurable {
            match &target_desc {
                None => return Err(self.throw_native(NativeErrorKind::TypeError)),
                Some(td) if td.configurable => {
                    return Err(self.throw_native(NativeErrorKind::TypeError))
                }
                Some(td) => {
                    // A non-configurable non-writable data result must match a
                    // non-writable target data field.
                    if complete.is_data() && !complete.writable() && td.is_data() && td.writable() {
                        return Err(self.throw_native(NativeErrorKind::TypeError));
                    }
                }
            }
        }
        Ok(Some(complete))
    }

    /// 10.5.6 [[DefineOwnProperty]].
    fn proxy_define_own(
        &mut self,
        pid: ObjId,
        key: &PropertyKey,
        desc: &PropDesc,
    ) -> Result<bool, Abrupt> {
        let (target, handler) = self.proxy_parts(pid)?;
        let Some(trap) = self.get_trap(handler, "defineProperty")? else {
            return self.mop_define_own(target, key, desc);
        };
        let kv = self.key_value(key);
        let desc_obj = self.from_partial_descriptor(desc);
        let r = self.call_function(
            trap,
            Value::Obj(handler),
            vec![Value::Obj(target), kv, desc_obj],
            false,
        )?;
        if !self.to_boolean(&r) {
            return Ok(false);
        }
        let target_desc = self.mop_get_own_property(target, key)?;
        let extensible_target = self.mop_is_extensible(target)?;
        let setting_config_false = desc.configurable == Some(false);
        match &target_desc {
            None => {
                if !extensible_target {
                    return Err(self.throw_native(NativeErrorKind::TypeError));
                }
                if setting_config_false {
                    return Err(self.throw_native(NativeErrorKind::TypeError));
                }
            }
            Some(td) => {
                if !self.is_compatible_descriptor(extensible_target, desc, Some(td)) {
                    return Err(self.throw_native(NativeErrorKind::TypeError));
                }
                if setting_config_false && td.configurable {
                    return Err(self.throw_native(NativeErrorKind::TypeError));
                }
                if td.is_data() && !td.configurable && td.writable() && desc.writable == Some(false) {
                    return Err(self.throw_native(NativeErrorKind::TypeError));
                }
            }
        }
        Ok(true)
    }

    /// 10.5.7 [[HasProperty]].
    fn proxy_has(&mut self, pid: ObjId, key: &PropertyKey) -> Result<bool, Abrupt> {
        let (target, handler) = self.proxy_parts(pid)?;
        let Some(trap) = self.get_trap(handler, "has")? else {
            return self.mop_has(target, key);
        };
        let kv = self.key_value(key);
        let r = self.call_function(trap, Value::Obj(handler), vec![Value::Obj(target), kv], false)?;
        let boolean = self.to_boolean(&r);
        if !boolean {
            if let Some(td) = self.mop_get_own_property(target, key)? {
                if !td.configurable {
                    return Err(self.throw_native(NativeErrorKind::TypeError));
                }
                if !self.mop_is_extensible(target)? {
                    return Err(self.throw_native(NativeErrorKind::TypeError));
                }
            }
        }
        Ok(boolean)
    }

    /// 10.5.8 [[Get]].
    fn proxy_get(&mut self, pid: ObjId, key: &PropertyKey, receiver: Value) -> ERes {
        let (target, handler) = self.proxy_parts(pid)?;
        let Some(trap) = self.get_trap(handler, "get")? else {
            return self.mop_get(target, key, receiver);
        };
        let kv = self.key_value(key);
        let trap_result = self.call_function(
            trap,
            Value::Obj(handler),
            vec![Value::Obj(target), kv, receiver],
            false,
        )?;
        if let Some(td) = self.mop_get_own_property(target, key)? {
            if !td.configurable {
                match &td.val {
                    PropVal::Data { value, writable: false } => {
                        if !same_value(self, &trap_result, value) {
                            return Err(self.throw_native(NativeErrorKind::TypeError));
                        }
                    }
                    PropVal::Accessor { get: None, .. } => {
                        if !matches!(trap_result, Value::Undefined) {
                            return Err(self.throw_native(NativeErrorKind::TypeError));
                        }
                    }
                    _ => {}
                }
            }
        }
        Ok(trap_result)
    }

    /// 10.5.9 [[Set]].
    fn proxy_set(
        &mut self,
        pid: ObjId,
        key: &PropertyKey,
        v: Value,
        receiver: Value,
    ) -> Result<bool, Abrupt> {
        let (target, handler) = self.proxy_parts(pid)?;
        let Some(trap) = self.get_trap(handler, "set")? else {
            // target.[[Set]](P, V, Receiver): mop_set routes a proxy target
            // through its own trap (proxy-of-proxy).
            return self.mop_set(target, key, v, receiver);
        };
        let kv = self.key_value(key);
        let r = self.call_function(
            trap,
            Value::Obj(handler),
            vec![Value::Obj(target), kv, v.clone(), receiver],
            false,
        )?;
        if !self.to_boolean(&r) {
            return Ok(false);
        }
        if let Some(td) = self.mop_get_own_property(target, key)? {
            if !td.configurable {
                match &td.val {
                    PropVal::Data { value, writable: false } => {
                        if !same_value(self, &v, value) {
                            return Err(self.throw_native(NativeErrorKind::TypeError));
                        }
                    }
                    PropVal::Accessor { set: None, .. } => {
                        return Err(self.throw_native(NativeErrorKind::TypeError));
                    }
                    _ => {}
                }
            }
        }
        Ok(true)
    }

    /// 10.5.10 [[Delete]].
    fn proxy_delete(&mut self, pid: ObjId, key: &PropertyKey) -> Result<bool, Abrupt> {
        let (target, handler) = self.proxy_parts(pid)?;
        let Some(trap) = self.get_trap(handler, "deleteProperty")? else {
            return self.mop_delete(target, key);
        };
        let kv = self.key_value(key);
        let r = self.call_function(trap, Value::Obj(handler), vec![Value::Obj(target), kv], false)?;
        if !self.to_boolean(&r) {
            return Ok(false);
        }
        let Some(td) = self.mop_get_own_property(target, key)? else {
            return Ok(true);
        };
        if !td.configurable {
            return Err(self.throw_native(NativeErrorKind::TypeError));
        }
        if !self.mop_is_extensible(target)? {
            return Err(self.throw_native(NativeErrorKind::TypeError));
        }
        Ok(true)
    }

    /// 10.5.11 [[OwnPropertyKeys]].
    fn proxy_own_keys(&mut self, pid: ObjId) -> Result<Vec<PropertyKey>, Abrupt> {
        let (target, handler) = self.proxy_parts(pid)?;
        let Some(trap) = self.get_trap(handler, "ownKeys")? else {
            return self.mop_own_keys(target);
        };
        let trap_array = self.call_function(trap, Value::Obj(handler), vec![Value::Obj(target)], false)?;
        let trap_result = self.create_list_of_property_keys(&trap_array)?;
        // No duplicate entries (SameValue).
        for i in 0..trap_result.len() {
            for j in (i + 1)..trap_result.len() {
                if trap_result[i] == trap_result[j] {
                    return Err(self.throw_native(NativeErrorKind::TypeError));
                }
            }
        }
        let extensible_target = self.mop_is_extensible(target)?;
        let target_keys = self.mop_own_keys(target)?;
        let mut target_config: Vec<PropertyKey> = Vec::new();
        let mut target_nonconfig: Vec<PropertyKey> = Vec::new();
        for k in target_keys {
            match self.mop_get_own_property(target, &k)? {
                Some(d) if !d.configurable => target_nonconfig.push(k),
                _ => target_config.push(k),
            }
        }
        if extensible_target && target_nonconfig.is_empty() {
            return Ok(trap_result);
        }
        let mut unchecked = trap_result.clone();
        for k in &target_nonconfig {
            match unchecked.iter().position(|x| x == k) {
                Some(pos) => {
                    unchecked.remove(pos);
                }
                None => return Err(self.throw_native(NativeErrorKind::TypeError)),
            }
        }
        if extensible_target {
            return Ok(trap_result);
        }
        for k in &target_config {
            match unchecked.iter().position(|x| x == k) {
                Some(pos) => {
                    unchecked.remove(pos);
                }
                None => return Err(self.throw_native(NativeErrorKind::TypeError)),
            }
        }
        if !unchecked.is_empty() {
            return Err(self.throw_native(NativeErrorKind::TypeError));
        }
        Ok(trap_result)
    }

    /// 10.5.12 [[Call]].
    pub(crate) fn proxy_call(&mut self, pid: ObjId, this: Value, args: Vec<Value>) -> ERes {
        let (target, handler) = self.proxy_parts(pid)?;
        let Some(trap) = self.get_trap(handler, "apply")? else {
            return self.call_function(target, this, args, false);
        };
        let arg_array = self.create_array_from_list(&args);
        self.call_function(
            trap,
            Value::Obj(handler),
            vec![Value::Obj(target), this, arg_array],
            false,
        )
    }

    /// 10.5.13 [[Construct]].
    pub(crate) fn proxy_construct(
        &mut self,
        pid: ObjId,
        args: Vec<Value>,
        new_target: ObjId,
    ) -> ERes {
        let (target, handler) = self.proxy_parts(pid)?;
        if !self.is_constructor(target) {
            return Err(self.throw_native(NativeErrorKind::TypeError));
        }
        let Some(trap) = self.get_trap(handler, "construct")? else {
            return self.construct_with_target(target, args, new_target);
        };
        let arg_array = self.create_array_from_list(&args);
        let new_obj = self.call_function(
            trap,
            Value::Obj(handler),
            vec![Value::Obj(target), arg_array, Value::Obj(new_target)],
            false,
        )?;
        if !new_obj.is_object() {
            return Err(self.throw_native(NativeErrorKind::TypeError));
        }
        Ok(new_obj)
    }

    // -- shared descriptor / list helpers ------------------------------------

    /// IsCompatiblePropertyDescriptor (10.5.5/10.5.6):
    /// ValidateAndApplyPropertyDescriptor(undefined, Extensible, Desc, Current)
    /// as a pure predicate (no application).
    fn is_compatible_descriptor(
        &self,
        extensible: bool,
        desc: &PropDesc,
        current: Option<&Prop>,
    ) -> bool {
        let Some(cur) = current else {
            return extensible;
        };
        if desc.value.is_none()
            && desc.writable.is_none()
            && desc.get.is_none()
            && desc.set.is_none()
            && desc.enumerable.is_none()
            && desc.configurable.is_none()
        {
            return true;
        }
        if !cur.configurable {
            if desc.configurable == Some(true) {
                return false;
            }
            if let Some(e) = desc.enumerable {
                if e != cur.enumerable {
                    return false;
                }
            }
            if !desc.is_generic() && desc.is_accessor() == cur.is_data() {
                return false;
            }
            match &cur.val {
                PropVal::Accessor { get, set } => {
                    if let Some(g) = &desc.get {
                        if *g != *get {
                            return false;
                        }
                    }
                    if let Some(s) = &desc.set {
                        if *s != *set {
                            return false;
                        }
                    }
                }
                PropVal::Data { value, writable } => {
                    if !writable {
                        if desc.writable == Some(true) {
                            return false;
                        }
                        if let Some(v) = &desc.value {
                            if !same_value(self, v, value) {
                                return false;
                            }
                        }
                    }
                }
            }
        }
        true
    }

    /// FromPropertyDescriptor (6.2.6.4) over a partial descriptor: an object
    /// carrying exactly the fields present in `desc`.
    fn from_partial_descriptor(&mut self, desc: &PropDesc) -> Value {
        let oid = self.alloc(Object::new(ObjKind::Plain, Some(self.intr.object_proto)));
        let put = |it: &mut Interp, k: &str, v: Value| {
            it.obj_mut(oid).props.insert(units_from_str(k), Prop::data(v));
        };
        if let Some(v) = &desc.value {
            put(self, "value", v.clone());
        }
        if let Some(w) = desc.writable {
            put(self, "writable", Value::Bool(w));
        }
        if let Some(g) = desc.get {
            put(self, "get", g.map_or(Value::Undefined, Value::Obj));
        }
        if let Some(s) = desc.set {
            put(self, "set", s.map_or(Value::Undefined, Value::Obj));
        }
        if let Some(e) = desc.enumerable {
            put(self, "enumerable", Value::Bool(e));
        }
        if let Some(c) = desc.configurable {
            put(self, "configurable", Value::Bool(c));
        }
        Value::Obj(oid)
    }

    /// CreateArrayFromList (7.3.18): a fresh array whose indices are `list`.
    pub(crate) fn create_array_from_list(&mut self, list: &[Value]) -> Value {
        let arr = self.new_array(list.len());
        for (i, v) in list.iter().enumerate() {
            self.obj_mut(arr)
                .props
                .insert(units_from_str(&i.to_string()), Prop::data(v.clone()));
        }
        #[allow(clippy::cast_precision_loss)]
        self.set_array_length_raw(arr, list.len() as f64);
        Value::Obj(arr)
    }

    /// CreateListFromArrayLike(obj, «String, Symbol») (7.3.17): every element
    /// must be a property key (string or symbol) or it is a TypeError.
    fn create_list_of_property_keys(&mut self, v: &Value) -> Result<Vec<PropertyKey>, Abrupt> {
        let Value::Obj(o) = v else {
            return Err(self.throw_native(NativeErrorKind::TypeError));
        };
        let o = *o;
        let len_v = self.get_from_object(o, &units_from_str("length"))?;
        let len = to_length_local(self.to_number(&len_v)?);
        if len > 1_000_000 {
            return Err(Abrupt::Fatal(
                "ownKeys trap result length exceeds slice cap".to_string(),
            ));
        }
        let mut out = Vec::with_capacity(usize::try_from(len).unwrap_or(0));
        for i in 0..len {
            let el = self.get_from_object(o, &units_from_str(&i.to_string()))?;
            match el {
                Value::Str(s) => out.push(PropertyKey::Str((*s).clone())),
                Value::Sym(s) => out.push(PropertyKey::Sym(s)),
                _ => return Err(self.throw_native(NativeErrorKind::TypeError)),
            }
        }
        Ok(out)
    }

    /// CreateListFromArrayLike(obj) with the default (any) element types:
    /// used by Reflect.apply / Reflect.construct for the arguments list.
    fn create_list_from_array_like(&mut self, v: &Value) -> Result<Vec<Value>, Abrupt> {
        let Value::Obj(o) = v else {
            return Err(self.throw_native(NativeErrorKind::TypeError));
        };
        let o = *o;
        let len_v = self.get_from_object(o, &units_from_str("length"))?;
        let len = to_length_local(self.to_number(&len_v)?);
        if len > 1_000_000 {
            return Err(Abrupt::Fatal(
                "arguments list length exceeds slice cap".to_string(),
            ));
        }
        let mut out = Vec::with_capacity(usize::try_from(len).unwrap_or(0));
        for i in 0..len {
            out.push(self.get_from_object(o, &units_from_str(&i.to_string()))?);
        }
        Ok(out)
    }

    /// A builtin the sem models as a NON-constructor whose driver-firewall
    /// replacement is a plain (constructable) function — so a construct-time
    /// `IsConstructor` query on it diverges between the real intrinsic and the
    /// firewalled oracle. `Date.now` is replaced by `function now(){...}`
    /// (`trace_driver.mjs`), which HAS a [[Construct]] the real intrinsic lacks;
    /// any construct query on it is therefore refused (sound), never guessed.
    fn firewall_plain_fn_ctor(&self, oid: ObjId) -> bool {
        matches!(
            self.obj(oid).kind,
            ObjKind::Function(crate::value::FnImpl::Builtin(Builtin::DateNow))
        )
    }

    /// GetFunctionRealm (7.3.24), reduced to its only observable in a
    /// single-realm model: recurse through bound functions and (live) proxies,
    /// and throw a TypeError if a **revoked** proxy is reached (10.5.14 forbids
    /// reading a revoked proxy's realm). Consulted by GetPrototypeFromConstructor
    /// when `Get(newTarget, "prototype")` is not an object.
    pub(crate) fn get_function_realm_check(&mut self, oid: ObjId) -> Result<(), Abrupt> {
        let mut cur = oid;
        let mut hops = 0;
        loop {
            match &self.obj(cur).kind {
                ObjKind::Proxy { handler: None, .. } => {
                    return Err(self.throw_native(NativeErrorKind::TypeError));
                }
                ObjKind::Proxy {
                    target: Some(t), ..
                } => cur = *t,
                ObjKind::Function(crate::value::FnImpl::Bound { target, .. }) => cur = *target,
                _ => return Ok(()),
            }
            hops += 1;
            if hops >= 100_000 {
                return Err(Abrupt::Fatal("function-realm chain too deep".to_string()));
            }
        }
    }

    /// IsArray (7.2.2): recurses through a proxy target; a revoked proxy is a
    /// TypeError.
    pub(crate) fn is_array_value(&mut self, v: &Value) -> Result<bool, Abrupt> {
        let Value::Obj(o0) = v else {
            return Ok(false);
        };
        let mut o = *o0;
        let mut hops = 0;
        loop {
            match self.obj(o).kind {
                ObjKind::Array => return Ok(true),
                ObjKind::Proxy {
                    target: Some(t), ..
                } => {
                    o = t;
                }
                ObjKind::Proxy { .. } => {
                    // Revoked proxy: TypeError.
                    return Err(self.throw_native(NativeErrorKind::TypeError));
                }
                _ => return Ok(false),
            }
            hops += 1;
            if hops >= 100_000 {
                return Err(Abrupt::Fatal("proxy chain too deep".to_string()));
            }
        }
    }

    // -- Reflect (28.1) ------------------------------------------------------

    pub(crate) fn dispatch_reflect(&mut self, b: Builtin, args: &[Value]) -> ERes {
        let arg = |i: usize| args.get(i).cloned().unwrap_or(Value::Undefined);
        let obj_arg = |it: &mut Interp, v: &Value| -> Result<ObjId, Abrupt> {
            match v {
                Value::Obj(o) => Ok(*o),
                _ => Err(it.throw_native(NativeErrorKind::TypeError)),
            }
        };
        match b {
            Builtin::ReflectApply => {
                let target = arg(0);
                if !matches!(&target, Value::Obj(o) if self.obj(*o).is_callable()) {
                    return Err(self.throw_native(NativeErrorKind::TypeError));
                }
                let this_arg = arg(1);
                let list = self.create_list_from_array_like(&arg(2))?;
                self.call_value(&target, this_arg, list)
            }
            Builtin::ReflectConstruct => {
                let target = arg(0);
                let Value::Obj(t) = target else {
                    return Err(self.throw_native(NativeErrorKind::TypeError));
                };
                if self.firewall_plain_fn_ctor(t) {
                    return Err(Abrupt::Fatal(FIREWALL_CTOR_REFUSAL.to_string()));
                }
                if !self.is_constructor(t) {
                    return Err(self.throw_native(NativeErrorKind::TypeError));
                }
                let new_target = if args.len() >= 3 {
                    match arg(2) {
                        Value::Obj(nt) if self.firewall_plain_fn_ctor(nt) => {
                            return Err(Abrupt::Fatal(FIREWALL_CTOR_REFUSAL.to_string()));
                        }
                        Value::Obj(nt) if self.is_constructor(nt) => nt,
                        _ => return Err(self.throw_native(NativeErrorKind::TypeError)),
                    }
                } else {
                    t
                };
                let list = self.create_list_from_array_like(&arg(1))?;
                self.construct_with_target(t, list, new_target)
            }
            Builtin::ReflectDefineProperty => {
                let o = obj_arg(self, &arg(0))?;
                let key = self.to_property_key(&arg(1))?;
                let desc = self.to_property_descriptor(&arg(2))?;
                let ok = self.mop_define_own(o, &key, &desc)?;
                Ok(Value::Bool(ok))
            }
            Builtin::ReflectDeleteProperty => {
                let o = obj_arg(self, &arg(0))?;
                let key = self.to_property_key(&arg(1))?;
                let ok = self.mop_delete(o, &key)?;
                Ok(Value::Bool(ok))
            }
            Builtin::ReflectGet => {
                let o = obj_arg(self, &arg(0))?;
                let key = self.to_property_key(&arg(1))?;
                let receiver = if args.len() >= 3 { arg(2) } else { arg(0) };
                self.mop_get(o, &key, receiver)
            }
            Builtin::ReflectGetOwnPropertyDescriptor => {
                let o = obj_arg(self, &arg(0))?;
                let key = self.to_property_key(&arg(1))?;
                match self.mop_get_own_property(o, &key)? {
                    Some(p) => self.from_property_descriptor(&p),
                    None => Ok(Value::Undefined),
                }
            }
            Builtin::ReflectGetPrototypeOf => {
                let o = obj_arg(self, &arg(0))?;
                Ok(self.mop_get_proto(o)?.map_or(Value::Null, Value::Obj))
            }
            Builtin::ReflectHas => {
                let o = obj_arg(self, &arg(0))?;
                let key = self.to_property_key(&arg(1))?;
                Ok(Value::Bool(self.mop_has(o, &key)?))
            }
            Builtin::ReflectIsExtensible => {
                let o = obj_arg(self, &arg(0))?;
                Ok(Value::Bool(self.mop_is_extensible(o)?))
            }
            Builtin::ReflectOwnKeys => {
                let o = obj_arg(self, &arg(0))?;
                let keys = self.mop_own_keys(o)?;
                let vals: Vec<Value> = keys.iter().map(|k| self.key_value(k)).collect();
                Ok(self.create_array_from_list(&vals))
            }
            Builtin::ReflectPreventExtensions => {
                let o = obj_arg(self, &arg(0))?;
                Ok(Value::Bool(self.mop_prevent_extensions(o)?))
            }
            Builtin::ReflectSet => {
                let o = obj_arg(self, &arg(0))?;
                let key = self.to_property_key(&arg(1))?;
                let value = arg(2);
                let receiver = if args.len() >= 4 { arg(3) } else { arg(0) };
                let ok = self.mop_set(o, &key, value, receiver)?;
                Ok(Value::Bool(ok))
            }
            Builtin::ReflectSetPrototypeOf => {
                let o = obj_arg(self, &arg(0))?;
                let proto = match arg(1) {
                    Value::Obj(p) => Some(p),
                    Value::Null => None,
                    _ => return Err(self.throw_native(NativeErrorKind::TypeError)),
                };
                let ok = self.mop_set_proto(o, proto)?;
                Ok(Value::Bool(ok))
            }
            _ => Err(Abrupt::Fatal(format!("reflect dispatch: {b:?}"))),
        }
    }

    // -- Proxy (28.2) --------------------------------------------------------

    pub(crate) fn dispatch_proxy(&mut self, b: Builtin, args: &[Value], is_new: bool) -> ERes {
        let arg = |i: usize| args.get(i).cloned().unwrap_or(Value::Undefined);
        match b {
            Builtin::ProxyCtor => {
                // 28.2.1.1: NewTarget undefined (a plain call) → TypeError.
                if !is_new {
                    return Err(self.throw_native(NativeErrorKind::TypeError));
                }
                let p = self.proxy_create(arg(0), arg(1))?;
                Ok(Value::Obj(p))
            }
            Builtin::ProxyRevocable => {
                let p = self.proxy_create(arg(0), arg(1))?;
                let revoke = self.alloc_native(NativeClosure::ProxyRevoke { proxy: p });
                let result = self.alloc(Object::new(ObjKind::Plain, Some(self.intr.object_proto)));
                self.obj_mut(result)
                    .props
                    .insert(units_from_str("proxy"), Prop::data(Value::Obj(p)));
                self.obj_mut(result)
                    .props
                    .insert(units_from_str("revoke"), Prop::data(revoke));
                Ok(Value::Obj(result))
            }
            _ => Err(Abrupt::Fatal(format!("proxy dispatch: {b:?}"))),
        }
    }

    // -- proxy-aware Object integrity (7.3.15 / 7.3.16) ----------------------

    /// SetIntegrityLevel over a proxy receiver (used by Object.freeze/seal on a
    /// proxy): drives the ownKeys + defineProperty traps in spec order.
    pub(crate) fn proxy_set_integrity(&mut self, pid: ObjId, freeze: bool) -> Result<bool, Abrupt> {
        if !self.mop_prevent_extensions(pid)? {
            return Ok(false);
        }
        let keys = self.mop_own_keys(pid)?;
        if freeze {
            for k in &keys {
                let cur = self.mop_get_own_property(pid, k)?;
                let desc = if cur.is_some_and(|c| !c.is_data()) {
                    // Accessor: only clear configurable.
                    PropDesc {
                        configurable: Some(false),
                        ..PropDesc::default()
                    }
                } else {
                    PropDesc {
                        configurable: Some(false),
                        writable: Some(false),
                        ..PropDesc::default()
                    }
                };
                if !self.mop_define_own(pid, k, &desc)? {
                    return Ok(false);
                }
            }
        } else {
            for k in &keys {
                let desc = PropDesc {
                    configurable: Some(false),
                    ..PropDesc::default()
                };
                if !self.mop_define_own(pid, k, &desc)? {
                    return Ok(false);
                }
            }
        }
        Ok(true)
    }

    /// EnumerableOwnPropertyNames(proxy, key) filtered to STRING keys whose
    /// own descriptor (via the getOwnPropertyDescriptor trap) is enumerable —
    /// the Object.keys surface of a proxy.
    pub(crate) fn proxy_enumerable_string_keys(&mut self, pid: ObjId) -> Result<Vec<Units>, Abrupt> {
        let keys = self.proxy_own_keys(pid)?;
        let mut out = Vec::new();
        for k in keys {
            if let PropertyKey::Str(u) = &k {
                if let Some(d) = self.mop_get_own_property(pid, &k)? {
                    if d.enumerable {
                        out.push(u.clone());
                    }
                }
            }
        }
        Ok(out)
    }

    /// TestIntegrityLevel over a proxy receiver (Object.isFrozen/isSealed).
    pub(crate) fn proxy_test_integrity(&mut self, pid: ObjId, frozen: bool) -> Result<bool, Abrupt> {
        if self.mop_is_extensible(pid)? {
            return Ok(false);
        }
        let keys = self.mop_own_keys(pid)?;
        for k in &keys {
            if let Some(cur) = self.mop_get_own_property(pid, k)? {
                if cur.configurable {
                    return Ok(false);
                }
                if frozen && cur.is_data() && cur.writable() {
                    return Ok(false);
                }
            }
        }
        Ok(true)
    }
}

/// CompletePropertyDescriptor (6.2.6.6) as a fully-populated `Prop`: a generic
/// descriptor completes to a data descriptor with value undefined.
fn complete_prop_from_desc(d: &PropDesc) -> Prop {
    if d.is_accessor() {
        Prop {
            val: PropVal::Accessor {
                get: d.get.flatten(),
                set: d.set.flatten(),
            },
            enumerable: d.enumerable.unwrap_or(false),
            configurable: d.configurable.unwrap_or(false),
            synthetic: false,
        }
    } else {
        Prop {
            val: PropVal::Data {
                value: d.value.clone().unwrap_or(Value::Undefined),
                writable: d.writable.unwrap_or(false),
            },
            enumerable: d.enumerable.unwrap_or(false),
            configurable: d.configurable.unwrap_or(false),
            synthetic: false,
        }
    }
}
