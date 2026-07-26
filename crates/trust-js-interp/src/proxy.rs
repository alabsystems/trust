// Proxy exotic objects (§10.5) and their handler traps, plus the `Proxy`
// constructor and `Proxy.revocable`. Every one of the 13 essential internal
// methods routes through its trap with the FULL spec invariant checks (a
// trap that contradicts a non-configurable/non-extensible target invariant is
// a TypeError), and a missing trap falls through to the target's own internal
// method (so a proxy of a typed array / array / another proxy stays exact).
// A revoked proxy throws TypeError on every internal method.
//
// The `im_*` helpers are the proxy-aware entry points for the internal
// methods that ordinary code reads off the object directly ([[GetOwnProperty]],
// [[GetPrototypeOf]], [[SetPrototypeOf]], [[IsExtensible]],
// [[PreventExtensions]], [[OwnPropertyKeys]]); [[Get]]/[[Set]]/[[HasProperty]]/
// [[Delete]]/[[DefineOwnProperty]] intercept proxies inside props.rs, and
// [[Call]]/[[Construct]] inside funcs.rs.
//
// Author: Andrew Yates
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

use crate::interp::{Abrupt, ERes, Interp};
use crate::props::PartialDesc;
use std::rc::Rc;
use trust_js_value::{
    units_from_str, JsObject, JsValue, ObjId, ObjKind, PropKey, PropValue, Property, ProxyData,
};

impl Interp {
    // -- construction --------------------------------------------------------

    /// ProxyCreate (10.5.14): both operands must be objects.
    pub(crate) fn proxy_create(&mut self, target: &JsValue, handler: &JsValue) -> Result<ObjId, Abrupt> {
        let (JsValue::Obj(t), JsValue::Obj(h)) = (target, handler) else {
            return Err(self.throw_type_error());
        };
        let callable = self.heap.obj(*t).is_callable();
        let constructor = self.is_constructor(target);
        // The [[Prototype]] slot is unused for a proxy (its [[GetPrototypeOf]]
        // is the trap); store None.
        self.alloc_obj(JsObject::new(
            ObjKind::Proxy(ProxyData {
                target: Some(*t),
                handler: Some(*h),
                callable,
                constructor,
            }),
            None,
        ))
    }

    /// `Proxy.revocable(target, handler)` (28.2.2.1): the `{proxy, revoke}`
    /// result record.
    pub(crate) fn proxy_revocable(&mut self, target: &JsValue, handler: &JsValue) -> ERes {
        let proxy = self.proxy_create(target, handler)?;
        let revoker = self.alloc_obj(JsObject::new(
            ObjKind::Function(trust_js_value::FnData::Native(
                trust_js_value::NativeFn::ProxyRevoke,
            )),
            Some(self.intr.function_proto),
        ))?;
        // CreateBuiltinFunction(revoke, 0, "", « [[RevocableProxy]] »): length 0,
        // name "".
        self.heap.obj_mut(revoker).props.insert(
            PropKey::from_str("length"),
            Property::with_attrs(JsValue::Num(0.0), false, false, true),
        );
        self.heap.obj_mut(revoker).props.insert(
            PropKey::from_str("name"),
            Property::with_attrs(JsValue::str_from(""), false, false, true),
        );
        self.revoke_targets.insert(revoker, Some(proxy));
        let result = self.new_plain()?;
        self.create_data_property_or_throw(result, "proxy", JsValue::Obj(proxy))?;
        self.create_data_property_or_throw(result, "revoke", JsValue::Obj(revoker))?;
        Ok(JsValue::Obj(result))
    }

    /// The per-proxy revoke closure (28.2.2.1.1): sets [[ProxyTarget]] /
    /// [[ProxyHandler]] to null.
    pub(crate) fn proxy_revoke(&mut self, revoker: ObjId) -> ERes {
        if let Some(slot) = self.revoke_targets.get_mut(&revoker) {
            if let Some(pid) = slot.take() {
                if let ObjKind::Proxy(p) = &mut self.heap.obj_mut(pid).kind {
                    p.target = None;
                    p.handler = None;
                }
            }
        }
        Ok(JsValue::Undefined)
    }

    // -- shared trap plumbing ------------------------------------------------

    /// The live (target, handler) of a proxy, or a TypeError when revoked.
    fn proxy_parts(&mut self, pid: ObjId) -> Result<(ObjId, ObjId), Abrupt> {
        let parts = match &self.heap.obj(pid).kind {
            ObjKind::Proxy(p) => p.parts(),
            _ => return Err(Abrupt::Fatal("proxy_parts on a non-proxy".to_string())),
        };
        parts.ok_or_else(|| self.throw_type_error())
    }

    /// GetMethod(handler, name) restricted to the trap names (a present-but-
    /// non-callable trap is a TypeError; undefined/null yields `None`).
    fn proxy_trap(&mut self, handler: ObjId, name: &str) -> Result<Option<JsValue>, Abrupt> {
        self.get_method(&JsValue::Obj(handler), &PropKey::from_str(name))
    }

    // -- the 13 internal methods ---------------------------------------------

    /// [[GetPrototypeOf]] (10.5.1). Returns the prototype (None = null).
    pub(crate) fn proxy_get_prototype_of(&mut self, pid: ObjId) -> Result<Option<ObjId>, Abrupt> {
        let (target, handler) = self.proxy_parts(pid)?;
        let Some(trap) = self.proxy_trap(handler, "getPrototypeOf")? else {
            return self.im_get_prototype_of(target);
        };
        let handler_proto = self.call_value(&trap, JsValue::Obj(handler), vec![JsValue::Obj(target)])?;
        let result = match handler_proto {
            JsValue::Obj(o) => Some(o),
            JsValue::Null => None,
            _ => return Err(self.throw_type_error()),
        };
        if self.im_is_extensible(target)? {
            return Ok(result);
        }
        let target_proto = self.im_get_prototype_of(target)?;
        if result != target_proto {
            return Err(self.throw_type_error());
        }
        Ok(result)
    }

    /// [[SetPrototypeOf]] (10.5.2). `proto` None = null.
    pub(crate) fn proxy_set_prototype_of(
        &mut self,
        pid: ObjId,
        proto: Option<ObjId>,
    ) -> Result<bool, Abrupt> {
        let (target, handler) = self.proxy_parts(pid)?;
        let Some(trap) = self.proxy_trap(handler, "setPrototypeOf")? else {
            return self.im_set_prototype_of(target, proto);
        };
        let v = proto.map_or(JsValue::Null, JsValue::Obj);
        let r = self.call_value(&trap, JsValue::Obj(handler), vec![JsValue::Obj(target), v])?;
        if !self.to_boolean(&r) {
            return Ok(false);
        }
        if self.im_is_extensible(target)? {
            return Ok(true);
        }
        let target_proto = self.im_get_prototype_of(target)?;
        if proto != target_proto {
            return Err(self.throw_type_error());
        }
        Ok(true)
    }

    /// [[IsExtensible]] (10.5.3).
    pub(crate) fn proxy_is_extensible(&mut self, pid: ObjId) -> Result<bool, Abrupt> {
        let (target, handler) = self.proxy_parts(pid)?;
        let Some(trap) = self.proxy_trap(handler, "isExtensible")? else {
            return self.im_is_extensible(target);
        };
        let r = self.call_value(&trap, JsValue::Obj(handler), vec![JsValue::Obj(target)])?;
        let boolean_trap_result = self.to_boolean(&r);
        let target_result = self.im_is_extensible(target)?;
        if boolean_trap_result != target_result {
            return Err(self.throw_type_error());
        }
        Ok(boolean_trap_result)
    }

    /// [[PreventExtensions]] (10.5.4).
    pub(crate) fn proxy_prevent_extensions(&mut self, pid: ObjId) -> Result<bool, Abrupt> {
        let (target, handler) = self.proxy_parts(pid)?;
        let Some(trap) = self.proxy_trap(handler, "preventExtensions")? else {
            return self.im_prevent_extensions(target);
        };
        let r = self.call_value(&trap, JsValue::Obj(handler), vec![JsValue::Obj(target)])?;
        let boolean_trap_result = self.to_boolean(&r);
        if boolean_trap_result && self.im_is_extensible(target)? {
            return Err(self.throw_type_error());
        }
        Ok(boolean_trap_result)
    }

    /// [[GetOwnProperty]] (10.5.5). Returns the resolved descriptor.
    pub(crate) fn proxy_get_own_property(
        &mut self,
        pid: ObjId,
        key: &PropKey,
    ) -> Result<Option<Property>, Abrupt> {
        let (target, handler) = self.proxy_parts(pid)?;
        let Some(trap) = self.proxy_trap(handler, "getOwnPropertyDescriptor")? else {
            return self.im_get_own_property(target, key);
        };
        let key_v = self.prop_key_value(key);
        let trap_result =
            self.call_value(&trap, JsValue::Obj(handler), vec![JsValue::Obj(target), key_v])?;
        if !matches!(trap_result, JsValue::Obj(_) | JsValue::Undefined) {
            return Err(self.throw_type_error());
        }
        let target_desc = self.im_get_own_property(target, key)?;
        if matches!(trap_result, JsValue::Undefined) {
            match &target_desc {
                None => return Ok(None),
                Some(td) => {
                    if !td.configurable {
                        return Err(self.throw_type_error());
                    }
                    if !self.im_is_extensible(target)? {
                        return Err(self.throw_type_error());
                    }
                    return Ok(None);
                }
            }
        }
        let extensible_target = self.im_is_extensible(target)?;
        let partial = self.to_property_descriptor(&trap_result)?;
        let result_desc = complete_property_descriptor(&partial);
        if !is_compatible_property_descriptor(extensible_target, &result_desc, target_desc.as_ref())
        {
            return Err(self.throw_type_error());
        }
        if !result_desc.configurable {
            match &target_desc {
                None => return Err(self.throw_type_error()),
                Some(td) if td.configurable => return Err(self.throw_type_error()),
                Some(td) => {
                    // A non-configurable non-writable data report must match a
                    // non-configurable non-writable target.
                    if let PropValue::Data { writable: false, .. } = &result_desc.v {
                        if let PropValue::Data { writable: true, .. } = &td.v {
                            return Err(self.throw_type_error());
                        }
                    }
                }
            }
        }
        Ok(Some(result_desc))
    }

    /// [[DefineOwnProperty]] (10.5.6).
    pub(crate) fn proxy_define_own(
        &mut self,
        pid: ObjId,
        key: &PropKey,
        desc: PartialDesc,
    ) -> Result<bool, Abrupt> {
        let (target, handler) = self.proxy_parts(pid)?;
        let Some(trap) = self.proxy_trap(handler, "defineProperty")? else {
            return self.im_define_own(target, key, desc);
        };
        let desc_obj = self.from_partial_descriptor(&desc)?;
        let key_v = self.prop_key_value(key);
        let r = self.call_value(
            &trap,
            JsValue::Obj(handler),
            vec![JsValue::Obj(target), key_v, desc_obj],
        )?;
        if !self.to_boolean(&r) {
            return Ok(false);
        }
        let target_desc = self.im_get_own_property(target, key)?;
        let extensible_target = self.im_is_extensible(target)?;
        let setting_config_false = desc.configurable == Some(false);
        match &target_desc {
            None => {
                if !extensible_target {
                    return Err(self.throw_type_error());
                }
                if setting_config_false {
                    return Err(self.throw_type_error());
                }
            }
            Some(td) => {
                if !ProbeDesc(desc.clone()).compatible(extensible_target, Some(td)) {
                    return Err(self.throw_type_error());
                }
                if setting_config_false && td.configurable {
                    return Err(self.throw_type_error());
                }
                if let PropValue::Data { writable: true, .. } = &td.v {
                    if !td.configurable && desc.writable == Some(false) {
                        return Err(self.throw_type_error());
                    }
                }
            }
        }
        Ok(true)
    }

    /// [[HasProperty]] (10.5.7).
    pub(crate) fn proxy_has(&mut self, pid: ObjId, key: &PropKey) -> Result<bool, Abrupt> {
        let (target, handler) = self.proxy_parts(pid)?;
        let Some(trap) = self.proxy_trap(handler, "has")? else {
            return self.has_property(target, key);
        };
        let key_v = self.prop_key_value(key);
        let r = self.call_value(&trap, JsValue::Obj(handler), vec![JsValue::Obj(target), key_v])?;
        let boolean_trap_result = self.to_boolean(&r);
        if !boolean_trap_result {
            if let Some(td) = self.im_get_own_property(target, key)? {
                if !td.configurable {
                    return Err(self.throw_type_error());
                }
                if !self.im_is_extensible(target)? {
                    return Err(self.throw_type_error());
                }
            }
        }
        Ok(boolean_trap_result)
    }

    /// [[Get]] (10.5.8).
    pub(crate) fn proxy_get(&mut self, pid: ObjId, key: &PropKey, receiver: JsValue) -> ERes {
        let (target, handler) = self.proxy_parts(pid)?;
        let Some(trap) = self.proxy_trap(handler, "get")? else {
            return self.get_from_object(target, key, receiver);
        };
        let key_v = self.prop_key_value(key);
        let trap_result = self.call_value(
            &trap,
            JsValue::Obj(handler),
            vec![JsValue::Obj(target), key_v, receiver],
        )?;
        if let Some(td) = self.im_get_own_property(target, key)? {
            if !td.configurable {
                match &td.v {
                    PropValue::Data { value, writable: false } => {
                        if td.synthetic {
                            return Err(Abrupt::Fatal(
                                "proxy invariant against engine-specific synthetic text".to_string(),
                            ));
                        }
                        if !crate::ops::same_value(&trap_result, value) {
                            return Err(self.throw_type_error());
                        }
                    }
                    PropValue::Accessor { get: None, .. } => {
                        if !matches!(trap_result, JsValue::Undefined) {
                            return Err(self.throw_type_error());
                        }
                    }
                    _ => {}
                }
            }
        }
        Ok(trap_result)
    }

    /// [[Set]] (10.5.9).
    pub(crate) fn proxy_set(
        &mut self,
        pid: ObjId,
        key: &PropKey,
        v: JsValue,
        receiver: JsValue,
    ) -> Result<bool, Abrupt> {
        let (target, handler) = self.proxy_parts(pid)?;
        let Some(trap) = self.proxy_trap(handler, "set")? else {
            return self.set_obj_with_receiver(target, key, v, &receiver);
        };
        let key_v = self.prop_key_value(key);
        let r = self.call_value(
            &trap,
            JsValue::Obj(handler),
            vec![JsValue::Obj(target), key_v, v.clone(), receiver],
        )?;
        if !self.to_boolean(&r) {
            return Ok(false);
        }
        if let Some(td) = self.im_get_own_property(target, key)? {
            if !td.configurable {
                match &td.v {
                    PropValue::Data { value, writable: false } => {
                        if td.synthetic {
                            return Err(Abrupt::Fatal(
                                "proxy invariant against engine-specific synthetic text".to_string(),
                            ));
                        }
                        if !crate::ops::same_value(&v, value) {
                            return Err(self.throw_type_error());
                        }
                    }
                    PropValue::Accessor { set: None, .. } => {
                        return Err(self.throw_type_error());
                    }
                    _ => {}
                }
            }
        }
        Ok(true)
    }

    /// [[Delete]] (10.5.10).
    pub(crate) fn proxy_delete(&mut self, pid: ObjId, key: &PropKey) -> Result<bool, Abrupt> {
        let (target, handler) = self.proxy_parts(pid)?;
        let Some(trap) = self.proxy_trap(handler, "deleteProperty")? else {
            return self.delete_prop(target, key);
        };
        let key_v = self.prop_key_value(key);
        let r = self.call_value(&trap, JsValue::Obj(handler), vec![JsValue::Obj(target), key_v])?;
        if !self.to_boolean(&r) {
            return Ok(false);
        }
        let Some(td) = self.im_get_own_property(target, key)? else {
            return Ok(true);
        };
        if !td.configurable {
            return Err(self.throw_type_error());
        }
        if !self.im_is_extensible(target)? {
            return Err(self.throw_type_error());
        }
        Ok(true)
    }

    /// [[OwnPropertyKeys]] (10.5.11).
    pub(crate) fn proxy_own_property_keys(&mut self, pid: ObjId) -> Result<Vec<PropKey>, Abrupt> {
        let (target, handler) = self.proxy_parts(pid)?;
        let Some(trap) = self.proxy_trap(handler, "ownKeys")? else {
            return self.im_own_property_keys(target);
        };
        let trap_array = self.call_value(&trap, JsValue::Obj(handler), vec![JsValue::Obj(target)])?;
        let JsValue::Obj(arr) = trap_array else {
            return Err(self.throw_type_error());
        };
        // CreateListFromArrayLike(trapResultArray, « String, Symbol »).
        let trap_result = self.create_key_list_from_array_like(arr)?;
        // No duplicate entries.
        if has_duplicate_keys(&trap_result) {
            return Err(self.throw_type_error());
        }
        let extensible_target = self.im_is_extensible(target)?;
        let target_keys = self.im_own_property_keys(target)?;
        let mut target_configurable: Vec<PropKey> = Vec::new();
        let mut target_nonconfigurable: Vec<PropKey> = Vec::new();
        for k in target_keys {
            match self.im_get_own_property(target, &k)? {
                Some(d) if !d.configurable => target_nonconfigurable.push(k),
                _ => target_configurable.push(k),
            }
        }
        if extensible_target && target_nonconfigurable.is_empty() {
            return Ok(trap_result);
        }
        let mut unchecked: Vec<PropKey> = trap_result.clone();
        for k in &target_nonconfigurable {
            match unchecked.iter().position(|x| x == k) {
                Some(i) => {
                    unchecked.remove(i);
                }
                None => return Err(self.throw_type_error()),
            }
        }
        if extensible_target {
            return Ok(trap_result);
        }
        for k in &target_configurable {
            match unchecked.iter().position(|x| x == k) {
                Some(i) => {
                    unchecked.remove(i);
                }
                None => return Err(self.throw_type_error()),
            }
        }
        if !unchecked.is_empty() {
            return Err(self.throw_type_error());
        }
        Ok(trap_result)
    }

    /// [[Call]] (10.5.12).
    pub(crate) fn proxy_call(&mut self, pid: ObjId, this: JsValue, args: Vec<JsValue>) -> ERes {
        let (target, handler) = self.proxy_parts(pid)?;
        let Some(trap) = self.proxy_trap(handler, "apply")? else {
            return self.call_obj(target, this, args, None);
        };
        let arg_array = self.create_array_from_list(args)?;
        self.call_value(
            &trap,
            JsValue::Obj(handler),
            vec![JsValue::Obj(target), this, arg_array],
        )
    }

    /// [[Construct]] (10.5.13).
    pub(crate) fn proxy_construct(
        &mut self,
        pid: ObjId,
        args: Vec<JsValue>,
        new_target: JsValue,
    ) -> ERes {
        let (target, handler) = self.proxy_parts(pid)?;
        let Some(trap) = self.proxy_trap(handler, "construct")? else {
            return self.construct(&JsValue::Obj(target), args, Some(&new_target));
        };
        let arg_array = self.create_array_from_list(args)?;
        let new_obj = self.call_value(
            &trap,
            JsValue::Obj(handler),
            vec![JsValue::Obj(target), arg_array, new_target],
        )?;
        if !new_obj.is_object() {
            return Err(self.throw_type_error());
        }
        Ok(new_obj)
    }

    // -- proxy-aware internal-method entry points ----------------------------

    /// [[GetOwnProperty]] with proxy routing.
    pub(crate) fn im_get_own_property(
        &mut self,
        oid: ObjId,
        key: &PropKey,
    ) -> Result<Option<Property>, Abrupt> {
        if matches!(self.heap.obj(oid).kind, ObjKind::Proxy(_)) {
            return self.proxy_get_own_property(oid, key);
        }
        self.own_prop_checked(oid, key)
    }

    /// [[GetPrototypeOf]] with proxy routing (None = null).
    pub(crate) fn im_get_prototype_of(&mut self, oid: ObjId) -> Result<Option<ObjId>, Abrupt> {
        if matches!(self.heap.obj(oid).kind, ObjKind::Proxy(_)) {
            return self.proxy_get_prototype_of(oid);
        }
        Ok(self.heap.obj(oid).proto)
    }

    /// [[SetPrototypeOf]] with proxy routing.
    pub(crate) fn im_set_prototype_of(
        &mut self,
        oid: ObjId,
        proto: Option<ObjId>,
    ) -> Result<bool, Abrupt> {
        if matches!(self.heap.obj(oid).kind, ObjKind::Proxy(_)) {
            return self.proxy_set_prototype_of(oid, proto);
        }
        self.set_prototype_of(oid, proto)
    }

    /// [[IsExtensible]] with proxy routing.
    pub(crate) fn im_is_extensible(&mut self, oid: ObjId) -> Result<bool, Abrupt> {
        if matches!(self.heap.obj(oid).kind, ObjKind::Proxy(_)) {
            return self.proxy_is_extensible(oid);
        }
        Ok(self.heap.obj(oid).extensible)
    }

    /// [[PreventExtensions]] with proxy routing.
    pub(crate) fn im_prevent_extensions(&mut self, oid: ObjId) -> Result<bool, Abrupt> {
        if matches!(self.heap.obj(oid).kind, ObjKind::Proxy(_)) {
            return self.proxy_prevent_extensions(oid);
        }
        if oid == self.global {
            return Err(Abrupt::Fatal(
                "preventExtensions on the global object (unmodeled)".to_string(),
            ));
        }
        self.heap.obj_mut(oid).extensible = false;
        Ok(true)
    }

    /// [[DefineOwnProperty]] with proxy routing (the ordinary path is in
    /// props.rs `define_own`, which already intercepts proxies; this is the
    /// name proxy trap code uses when forwarding to a target).
    pub(crate) fn im_define_own(
        &mut self,
        oid: ObjId,
        key: &PropKey,
        desc: PartialDesc,
    ) -> Result<bool, Abrupt> {
        self.define_own(oid, key, desc)
    }

    /// [[OwnPropertyKeys]] with proxy routing.
    pub(crate) fn im_own_property_keys(&mut self, oid: ObjId) -> Result<Vec<PropKey>, Abrupt> {
        if matches!(self.heap.obj(oid).kind, ObjKind::Proxy(_)) {
            return self.proxy_own_property_keys(oid);
        }
        self.own_keys_reflectable(oid)
    }

    // -- descriptor / list helpers ------------------------------------------

    /// The property key as a value (String or Symbol).
    fn prop_key_value(&self, key: &PropKey) -> JsValue {
        match key {
            PropKey::Str(u) => JsValue::Str(Rc::new(u.clone())),
            PropKey::Sym(s) => JsValue::Sym(*s),
        }
    }

    /// FromPropertyDescriptor over a PARTIAL descriptor (only present fields
    /// are emitted) — the trap argument for [[DefineOwnProperty]].
    fn from_partial_descriptor(&mut self, d: &PartialDesc) -> ERes {
        let oid = self.new_plain()?;
        let set = |it: &mut Interp, k: &str, v: JsValue| {
            it.heap
                .obj_mut(oid)
                .props
                .insert(PropKey::from_str(k), Property::data(v));
        };
        if let Some(v) = &d.value {
            set(self, "value", v.clone());
        }
        if let Some(w) = d.writable {
            set(self, "writable", JsValue::Bool(w));
        }
        if let Some(g) = &d.get {
            set(self, "get", g.map_or(JsValue::Undefined, JsValue::Obj));
        }
        if let Some(s) = &d.set {
            set(self, "set", s.map_or(JsValue::Undefined, JsValue::Obj));
        }
        if let Some(e) = d.enumerable {
            set(self, "enumerable", JsValue::Bool(e));
        }
        if let Some(c) = d.configurable {
            set(self, "configurable", JsValue::Bool(c));
        }
        Ok(JsValue::Obj(oid))
    }

    /// CreateArrayFromList (7.3.18).
    fn create_array_from_list(&mut self, list: Vec<JsValue>) -> ERes {
        let arr = self.new_array(0)?;
        let mut n: u32 = 0;
        for v in list {
            self.heap.obj_mut(arr).props.insert(
                PropKey::Str(units_from_str(&n.to_string())),
                Property::data(v),
            );
            n += 1;
        }
        self.set_array_length_raw(arr, f64::from(n));
        Ok(JsValue::Obj(arr))
    }

    /// CreateListFromArrayLike(obj, « String, Symbol ») — the [[OwnPropertyKeys]]
    /// trap result validation: every element must be a String or Symbol.
    fn create_key_list_from_array_like(&mut self, oid: ObjId) -> Result<Vec<PropKey>, Abrupt> {
        let len = self.length_of_array_like(oid)?;
        if len > 1_000_000 {
            return Err(Abrupt::Fatal("proxy ownKeys list cap exceeded".to_string()));
        }
        let mut out = Vec::with_capacity(usize::try_from(len).expect("capped"));
        for i in 0..len {
            self.charge_loop()?;
            let key = PropKey::Str(units_from_str(&i.to_string()));
            let el = self.get_from_object(oid, &key, JsValue::Obj(oid))?;
            match el {
                JsValue::Str(u) => out.push(PropKey::Str(u.as_ref().clone())),
                JsValue::Sym(s) => out.push(PropKey::Sym(s)),
                _ => return Err(self.throw_type_error()),
            }
        }
        Ok(out)
    }

    /// IsArray (7.2.2) with proxy recursion (revoked proxy → TypeError).
    pub(crate) fn is_array_exotic(&mut self, oid: ObjId) -> Result<bool, Abrupt> {
        let mut cur = oid;
        let mut hops = 0;
        loop {
            match &self.heap.obj(cur).kind {
                ObjKind::Array => return Ok(true),
                ObjKind::Proxy(p) => match p.target {
                    Some(t) => cur = t,
                    None => return Err(self.throw_type_error()),
                },
                _ => return Ok(false),
            }
            hops += 1;
            if hops >= 128 {
                return Err(Abrupt::Fatal("proxy chain too deep".to_string()));
            }
        }
    }
}

/// CompletePropertyDescriptor (6.2.5.6): a partial descriptor filled with the
/// spec defaults, as a concrete `Property`.
fn complete_property_descriptor(d: &PartialDesc) -> Property {
    if d.is_accessor() {
        Property {
            v: PropValue::Accessor {
                get: d.get.unwrap_or(None),
                set: d.set.unwrap_or(None),
            },
            enumerable: d.enumerable.unwrap_or(false),
            configurable: d.configurable.unwrap_or(false),
            synthetic: false,
        }
    } else if d.is_data() {
        Property {
            v: PropValue::Data {
                value: d.value.clone().unwrap_or(JsValue::Undefined),
                writable: d.writable.unwrap_or(false),
            },
            enumerable: d.enumerable.unwrap_or(false),
            configurable: d.configurable.unwrap_or(false),
            synthetic: false,
        }
    } else {
        // Generic descriptor completes to a data descriptor.
        Property {
            v: PropValue::Data {
                value: JsValue::Undefined,
                writable: false,
            },
            enumerable: d.enumerable.unwrap_or(false),
            configurable: d.configurable.unwrap_or(false),
            synthetic: false,
        }
    }
}

/// A wrapper carrying a partial descriptor for the compatibility predicate,
/// so the predicate can distinguish "field absent" (no constraint) from
/// "field present with a value" — used by the [[DefineOwnProperty]] path,
/// where the incoming `Desc` is partial.
struct ProbeDesc(PartialDesc);

/// Are there duplicate keys in the list? (Set-based, so a hostile large trap
/// result stays linear.)
fn has_duplicate_keys(keys: &[PropKey]) -> bool {
    let mut seen = std::collections::HashSet::with_capacity(keys.len());
    for k in keys {
        if !seen.insert(k) {
            return true;
        }
    }
    false
}

/// IsCompatiblePropertyDescriptor(Extensible, Desc, Current) =
/// ValidateAndApplyPropertyDescriptor with O = undefined (validation only).
/// `Desc` is a completed `Property` here (proxy [[GetOwnProperty]]); the
/// [[DefineOwnProperty]] path uses the `ProbeDesc` overload below.
fn is_compatible_property_descriptor(
    extensible: bool,
    desc: &Property,
    current: Option<&Property>,
) -> bool {
    let Some(cur) = current else {
        return extensible;
    };
    // For a completed descriptor every field is present.
    if !cur.configurable {
        if desc.configurable {
            return false;
        }
        if desc.enumerable != cur.enumerable {
            return false;
        }
        let desc_accessor = matches!(desc.v, PropValue::Accessor { .. });
        let cur_accessor = matches!(cur.v, PropValue::Accessor { .. });
        if desc_accessor != cur_accessor {
            return false;
        }
        match (&cur.v, &desc.v) {
            (
                PropValue::Accessor { get: cg, set: cs },
                PropValue::Accessor { get: dg, set: ds },
            ) => {
                if dg != cg || ds != cs {
                    return false;
                }
            }
            (
                PropValue::Data { value: cv, writable: cw },
                PropValue::Data { value: dv, writable: dw },
            ) => {
                if !cw {
                    if *dw {
                        return false;
                    }
                    if !crate::ops::same_value(dv, cv) {
                        return false;
                    }
                }
            }
            _ => {}
        }
    }
    true
}

/// IsCompatiblePropertyDescriptor for a PARTIAL `Desc` (the define trap path):
/// only present fields impose a constraint.
impl ProbeDesc {
    fn compatible(&self, extensible: bool, current: Option<&Property>) -> bool {
        let d = &self.0;
        let Some(cur) = current else {
            return extensible;
        };
        if cur.configurable {
            return true;
        }
        if d.configurable == Some(true) {
            return false;
        }
        if let Some(e) = d.enumerable {
            if e != cur.enumerable {
                return false;
            }
        }
        let cur_accessor = matches!(cur.v, PropValue::Accessor { .. });
        if !d.is_generic() && d.is_accessor() != cur_accessor {
            return false;
        }
        match &cur.v {
            PropValue::Accessor { get, set } => {
                if let Some(dg) = &d.get {
                    if dg != get {
                        return false;
                    }
                }
                if let Some(ds) = &d.set {
                    if ds != set {
                        return false;
                    }
                }
            }
            PropValue::Data { value, writable } => {
                if !writable {
                    if d.writable == Some(true) {
                        return false;
                    }
                    if let Some(dv) = &d.value {
                        if !crate::ops::same_value(dv, value) {
                            return false;
                        }
                    }
                }
            }
        }
        true
    }
}
