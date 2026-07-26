// Object statics (assign/entries/values/fromEntries/descriptors/
// defineProperties/freeze/seal/integrity/setPrototypeOf/hasOwn) and the
// Reflect namespace — written from the spec algorithms over the modeled
// internal methods. Reflection that would expose an unmodeled or
// order-opaque own surface refuses via `own_surface_complete`.
//
// Author: Andrew Yates
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

use crate::interp::{Abrupt, ERes, Interp};
use crate::props::PartialDesc;
use std::rc::Rc;
use trust_js_value::{JsValue, ObjId, PropKey, PropValue, Property};

impl Interp {
    /// Own keys for full-list reflection; refuses on unmodeled/order-opaque
    /// surfaces.
    pub(crate) fn own_keys_reflectable(&mut self, oid: ObjId) -> Result<Vec<PropKey>, Abrupt> {
        // A proxy's [[OwnPropertyKeys]] is the handler trap.
        if matches!(self.heap.obj(oid).kind, trust_js_value::ObjKind::Proxy(_)) {
            return self.proxy_own_property_keys(oid);
        }
        if !self.own_surface_complete(oid) {
            return Err(Abrupt::Fatal(
                "own-key reflection over an object with unmodeled own surface".to_string(),
            ));
        }
        Ok(self.ordered_own_keys_of(oid))
    }

    /// Object.assign (20.1.2.1).
    pub(crate) fn object_assign(&mut self, args: &[JsValue]) -> ERes {
        let target = args.first().cloned().unwrap_or(JsValue::Undefined);
        let to = self.to_object(&target)?;
        for src in args.iter().skip(1) {
            if src.is_nullish() {
                continue;
            }
            let from = self.to_object(src)?;
            let keys = self.own_keys_reflectable(from)?;
            for key in keys {
                self.charge_loop()?;
                let Some(d) = self.im_get_own_property(from, &key)? else {
                    continue;
                };
                if !d.enumerable {
                    continue;
                }
                let v = self.get_from_object(from, &key, JsValue::Obj(from))?;
                self.set_on_object(to, &key, v, true)?;
            }
        }
        Ok(JsValue::Obj(to))
    }

    /// Object.entries / Object.values (EnumerableOwnProperties).
    pub(crate) fn object_entries_values(&mut self, target: &JsValue, values: bool) -> ERes {
        let oid = self.to_object(target)?;
        let keys = self.own_keys_reflectable(oid)?;
        let out = self.new_array(0)?;
        let mut n: u64 = 0;
        for key in keys {
            self.charge_loop()?;
            let PropKey::Str(u) = &key else { continue };
            let u = u.clone();
            let Some(d) = self.im_get_own_property(oid, &key)? else {
                continue;
            };
            if !d.enumerable {
                continue;
            }
            let v = self.get_from_object(oid, &key, JsValue::Obj(oid))?;
            let entry = if values {
                v
            } else {
                let pair = self.new_array(2)?;
                self.heap.obj_mut(pair).props.insert(
                    PropKey::from_str("0"),
                    Property::data(JsValue::Str(Rc::new(u))),
                );
                self.heap
                    .obj_mut(pair)
                    .props
                    .insert(PropKey::from_str("1"), Property::data(v));
                JsValue::Obj(pair)
            };
            self.create_data_property_or_throw(out, &n.to_string(), entry)?;
            n += 1;
        }
        #[allow(clippy::cast_precision_loss)]
        self.set_array_length_raw(out, n as f64);
        Ok(JsValue::Obj(out))
    }

    /// Object.fromEntries (20.1.2.7); iteration via the fast-iterator
    /// discipline only.
    pub(crate) fn object_from_entries(&mut self, iterable: &JsValue) -> ERes {
        self.require_object_coercible(iterable)?;
        let obj = self.new_plain()?;
        let mut it = self.get_iterator_or_type_error(iterable)?;
        loop {
            let entry = match self.fast_iter_next(&mut it) {
                Ok(Some(e)) => e,
                Ok(None) => break,
                Err(a) => return Err(a),
            };
            self.charge_loop()?;
            let body = (|s: &mut Self| -> Result<(), Abrupt> {
                let JsValue::Obj(eo) = entry else {
                    return Err(s.throw_type_error());
                };
                let k = s.get_from_object(eo, &PropKey::from_str("0"), JsValue::Obj(eo))?;
                let v = s.get_from_object(eo, &PropKey::from_str("1"), JsValue::Obj(eo))?;
                let key = s.to_property_key(&k)?;
                let ok = s.define_own(obj, &key, PartialDesc::full_data(v, true, true, true))?;
                if !ok {
                    return Err(s.throw_type_error());
                }
                Ok(())
            })(self);
            if let Err(a) = body {
                return Err(self.close_after_body_abrupt(&it, a));
            }
        }
        Ok(JsValue::Obj(obj))
    }

    /// Object.getOwnPropertyDescriptors (20.1.2.9).
    pub(crate) fn object_get_own_property_descriptors(&mut self, target: &JsValue) -> ERes {
        let oid = self.to_object(target)?;
        let keys = self.own_keys_reflectable(oid)?;
        let out = self.new_plain()?;
        for key in keys {
            self.charge_loop()?;
            let Some(d) = self.im_get_own_property(oid, &key)? else {
                continue;
            };
            let desc_obj = self.from_property_descriptor(&d)?;
            let ok = self.define_own(out, &key, PartialDesc::full_data(desc_obj, true, true, true))?;
            if !ok {
                return Err(self.throw_type_error());
            }
        }
        Ok(JsValue::Obj(out))
    }

    /// Object.getOwnPropertySymbols (GetOwnPropertyKeys, symbol filter).
    pub(crate) fn object_get_own_property_symbols(&mut self, target: &JsValue) -> ERes {
        let oid = self.to_object(target)?;
        let keys = self.own_keys_reflectable(oid)?;
        let out = self.new_array(0)?;
        let mut n: u32 = 0;
        for key in keys {
            let PropKey::Sym(s) = key else { continue };
            self.heap.obj_mut(out).props.insert(
                PropKey::Str(trust_js_value::units_from_str(&n.to_string())),
                Property::data(JsValue::Sym(s)),
            );
            n += 1;
        }
        self.set_array_length_raw(out, f64::from(n));
        Ok(JsValue::Obj(out))
    }

    /// ObjectDefineProperties (20.1.2.3.1): two-phase (collect all
    /// descriptors, then apply).
    pub(crate) fn object_define_properties(&mut self, oid: ObjId, props_v: &JsValue) -> Result<(), Abrupt> {
        if props_v.is_nullish() {
            return Err(self.throw_type_error());
        }
        let props_obj = self.to_object(props_v)?;
        let keys = self.own_keys_reflectable(props_obj)?;
        let mut descs: Vec<(PropKey, PartialDesc)> = Vec::new();
        for key in keys {
            self.charge_loop()?;
            let Some(p) = self.im_get_own_property(props_obj, &key)? else {
                continue;
            };
            if !p.enumerable {
                continue;
            }
            let desc_obj = self.get_from_object(props_obj, &key, JsValue::Obj(props_obj))?;
            let desc = self.to_property_descriptor(&desc_obj)?;
            descs.push((key, desc));
        }
        if oid == self.global {
            return Err(Abrupt::Fatal(
                "defineProperties on the global object (attribute surface unmodeled)".to_string(),
            ));
        }
        for (key, desc) in descs {
            let ok = self.define_own(oid, &key, desc)?;
            if !ok {
                return Err(self.throw_type_error());
            }
        }
        Ok(())
    }

    /// SetIntegrityLevel (7.3.15); returns the argument like freeze/seal.
    pub(crate) fn object_set_integrity(&mut self, v: &JsValue, frozen: bool) -> ERes {
        let JsValue::Obj(oid) = v else {
            return Ok(v.clone());
        };
        let oid = *oid;
        // SetIntegrityLevel: [[PreventExtensions]] first (a false result is a
        // TypeError), then [[OwnPropertyKeys]], then per-key define.
        if !self.im_prevent_extensions(oid)? {
            return Err(self.throw_type_error());
        }
        let keys = self.own_keys_reflectable(oid)?;
        for key in keys {
            self.charge_loop()?;
            let Some(cur) = self.im_get_own_property(oid, &key)? else {
                continue;
            };
            let desc = if frozen && cur.is_data() {
                PartialDesc {
                    writable: Some(false),
                    configurable: Some(false),
                    ..Default::default()
                }
            } else {
                PartialDesc {
                    configurable: Some(false),
                    ..Default::default()
                }
            };
            let ok = self.define_own(oid, &key, desc)?;
            if !ok {
                return Err(self.throw_type_error());
            }
        }
        Ok(v.clone())
    }

    /// TestIntegrityLevel (7.3.16).
    pub(crate) fn object_test_integrity(&mut self, v: &JsValue, frozen: bool) -> ERes {
        let JsValue::Obj(oid) = v else {
            return Ok(JsValue::Bool(true));
        };
        let oid = *oid;
        // TestIntegrityLevel: ! [[IsExtensible]] first, then per-key
        // [[GetOwnProperty]].
        if self.im_is_extensible(oid)? {
            return Ok(JsValue::Bool(false));
        }
        let keys = self.own_keys_reflectable(oid)?;
        for key in keys {
            self.charge_loop()?;
            let Some(cur) = self.im_get_own_property(oid, &key)? else {
                continue;
            };
            if cur.configurable {
                return Ok(JsValue::Bool(false));
            }
            if frozen {
                if let PropValue::Data { writable: true, .. } = cur.v {
                    return Ok(JsValue::Bool(false));
                }
            }
        }
        Ok(JsValue::Bool(true))
    }

    /// [[SetPrototypeOf]] (ordinary 10.1.2.1 + %Object.prototype% immutable
    /// exotic). Returns spec true/false.
    pub(crate) fn set_prototype_of(&mut self, oid: ObjId, proto: Option<ObjId>) -> Result<bool, Abrupt> {
        if oid == self.global {
            return Err(Abrupt::Fatal(
                "setPrototypeOf on the global object (unmodeled)".to_string(),
            ));
        }
        let current = self.heap.obj(oid).proto;
        if current == proto {
            return Ok(true);
        }
        if oid == self.intr.object_proto {
            // SetImmutablePrototype: change refused.
            return Ok(false);
        }
        if !self.heap.obj(oid).extensible {
            return Ok(false);
        }
        // Cycle check over ordinary prototype chains.
        let mut p = proto;
        let mut hops = 0;
        while let Some(pp) = p {
            if pp == oid {
                return Ok(false);
            }
            if hops >= 128 {
                return Err(Abrupt::Fatal("prototype chain too deep".to_string()));
            }
            p = self.heap.obj(pp).proto;
            hops += 1;
        }
        self.heap.obj_mut(oid).proto = proto;
        Ok(true)
    }

    // -- Reflect -------------------------------------------------------------

    pub(crate) fn reflect_target(&mut self, v: &JsValue) -> Result<ObjId, Abrupt> {
        match v {
            JsValue::Obj(o) => Ok(*o),
            _ => Err(self.throw_type_error()),
        }
    }

    #[allow(clippy::too_many_lines)]
    pub(crate) fn dispatch_reflect(
        &mut self,
        nf: trust_js_value::NativeFn,
        args: &[JsValue],
    ) -> ERes {
        use trust_js_value::NativeFn as N;
        let arg = |i: usize| args.get(i).cloned().unwrap_or(JsValue::Undefined);
        match nf {
            N::ReflectApply => {
                let target = arg(0);
                let t = self.reflect_target(&target)?;
                if !self.heap.obj(t).is_callable() {
                    return Err(self.throw_type_error());
                }
                let al = arg(2);
                let alo = self.reflect_target(&al)?;
                let list = self.create_list_from_array_like(alo)?;
                self.call_value(&target, arg(1), list)
            }
            N::ReflectConstruct => {
                let target = arg(0);
                if !self.is_constructor(&target) {
                    return Err(self.throw_type_error());
                }
                let nt = if args.len() > 2 {
                    let ntv = arg(2);
                    if !self.is_constructor(&ntv) {
                        return Err(self.throw_type_error());
                    }
                    ntv
                } else {
                    target.clone()
                };
                let al = arg(1);
                let alo = self.reflect_target(&al)?;
                let list = self.create_list_from_array_like(alo)?;
                self.construct(&target, list, Some(&nt))
            }
            N::ReflectDefineProperty => {
                let t = {
                    let target = arg(0);
                    self.reflect_target(&target)?
                };
                let key = {
                    let k = arg(1);
                    self.to_property_key(&k)?
                };
                let desc = self.to_property_descriptor(&arg(2))?;
                if t == self.global {
                    return Err(Abrupt::Fatal(
                        "defineProperty on the global object (attribute surface unmodeled)"
                            .to_string(),
                    ));
                }
                Ok(JsValue::Bool(self.define_own(t, &key, desc)?))
            }
            N::ReflectDeleteProperty => {
                let t = {
                    let target = arg(0);
                    self.reflect_target(&target)?
                };
                let key = {
                    let k = arg(1);
                    self.to_property_key(&k)?
                };
                Ok(JsValue::Bool(self.delete_prop(t, &key)?))
            }
            N::ReflectGet => {
                let target = arg(0);
                let t = self.reflect_target(&target)?;
                let key = {
                    let k = arg(1);
                    self.to_property_key(&k)?
                };
                let receiver = if args.len() > 2 { arg(2) } else { target };
                self.get_from_object(t, &key, receiver)
            }
            N::ReflectGetOwnPropertyDescriptor => {
                let t = {
                    let target = arg(0);
                    self.reflect_target(&target)?
                };
                let key = {
                    let k = arg(1);
                    self.to_property_key(&k)?
                };
                match self.im_get_own_property(t, &key)? {
                    None => Ok(JsValue::Undefined),
                    Some(p) => self.from_property_descriptor(&p),
                }
            }
            N::ReflectGetPrototypeOf => {
                let t = {
                    let target = arg(0);
                    self.reflect_target(&target)?
                };
                Ok(match self.im_get_prototype_of(t)? {
                    Some(p) => JsValue::Obj(p),
                    None => JsValue::Null,
                })
            }
            N::ReflectHas => {
                let t = {
                    let target = arg(0);
                    self.reflect_target(&target)?
                };
                let key = {
                    let k = arg(1);
                    self.to_property_key(&k)?
                };
                Ok(JsValue::Bool(self.has_property(t, &key)?))
            }
            N::ReflectIsExtensible => {
                let t = {
                    let target = arg(0);
                    self.reflect_target(&target)?
                };
                Ok(JsValue::Bool(self.im_is_extensible(t)?))
            }
            N::ReflectOwnKeys => {
                let t = {
                    let target = arg(0);
                    self.reflect_target(&target)?
                };
                let keys = self.own_keys_reflectable(t)?;
                let out = self.new_array(0)?;
                let mut n: u32 = 0;
                for key in keys {
                    let v = match key {
                        PropKey::Str(u) => JsValue::Str(Rc::new(u)),
                        PropKey::Sym(s) => JsValue::Sym(s),
                    };
                    self.heap.obj_mut(out).props.insert(
                        PropKey::Str(trust_js_value::units_from_str(&n.to_string())),
                        Property::data(v),
                    );
                    n += 1;
                }
                self.set_array_length_raw(out, f64::from(n));
                Ok(JsValue::Obj(out))
            }
            N::ReflectPreventExtensions => {
                let t = {
                    let target = arg(0);
                    self.reflect_target(&target)?
                };
                Ok(JsValue::Bool(self.im_prevent_extensions(t)?))
            }
            N::ReflectSet => {
                let target = arg(0);
                let t = self.reflect_target(&target)?;
                let key = {
                    let k = arg(1);
                    self.to_property_key(&k)?
                };
                let receiver = if args.len() > 3 { arg(3) } else { target };
                Ok(JsValue::Bool(self.set_obj_with_receiver(
                    t,
                    &key,
                    arg(2),
                    &receiver,
                )?))
            }
            N::ReflectSetPrototypeOf => {
                let t = {
                    let target = arg(0);
                    self.reflect_target(&target)?
                };
                let proto = match arg(1) {
                    JsValue::Obj(p) => Some(p),
                    JsValue::Null => None,
                    _ => return Err(self.throw_type_error()),
                };
                Ok(JsValue::Bool(self.im_set_prototype_of(t, proto)?))
            }
            _ => Err(Abrupt::Fatal("unrouted Reflect native (interpreter bug)".to_string())),
        }
    }
}
