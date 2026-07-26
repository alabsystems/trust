// Map / Set / WeakMap / WeakSet (S1c), written from the spec algorithms:
// SameValueZero keying with -0 canonicalization, insertion-ordered entry
// lists with in-place tombstones (spec [[MapData]] record emptying — live
// iteration indices stay exact), AddEntriesFromIterable through the
// observable `set`/`add` adder Get, forEach over the live list, and the
// ratified-at-this-pin upsert pair getOrInsert/getOrInsertComputed
// (features.txt lists `upsert` as standard; Node 24 lacks the methods while
// Bun carries them — an audited engine divergence; this model follows the
// spec/Bun side). WeakMap/WeakSet hold strong references: without
// WeakRef/FinalizationRegistry (unmodeled, refusing), collection is
// unobservable.
//
// Author: Andrew Yates
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

use crate::interp::{Abrupt, ERes, Interp};
use trust_js_value::{
    JsObject, JsValue, MapData, NativeFn, ObjId, ObjKind, PropKey, SetData, SymId,
};

/// CanonicalizeKeyedCollectionKey: -0 becomes +0.
fn canon_key(k: JsValue) -> JsValue {
    match k {
        JsValue::Num(n) if n == 0.0 => JsValue::Num(0.0),
        other => other,
    }
}

/// CanBeHeldWeakly: objects, and symbols not in the global registry.
fn can_be_held_weakly(it: &Interp, v: &JsValue) -> bool {
    match v {
        JsValue::Obj(_) => true,
        JsValue::Sym(s) => match s {
            SymId::WellKnown(_) => true,
            SymId::User(_) => !it.sym_registry.iter().any(|(_, rs)| rs == s),
        },
        _ => false,
    }
}

impl Interp {
    // -- internal-slot access ------------------------------------------------

    fn this_map(&mut self, this: &JsValue, weak: bool) -> Result<ObjId, Abrupt> {
        if let JsValue::Obj(oid) = this {
            let ok = match &self.heap.obj(*oid).kind {
                ObjKind::MapObj(_) => !weak,
                ObjKind::WeakMapObj(_) => weak,
                _ => false,
            };
            if ok {
                return Ok(*oid);
            }
        }
        Err(self.throw_type_error())
    }

    fn this_set(&mut self, this: &JsValue, weak: bool) -> Result<ObjId, Abrupt> {
        if let JsValue::Obj(oid) = this {
            let ok = match &self.heap.obj(*oid).kind {
                ObjKind::SetObj(_) => !weak,
                ObjKind::WeakSetObj(_) => weak,
                _ => false,
            };
            if ok {
                return Ok(*oid);
            }
        }
        Err(self.throw_type_error())
    }

    fn map_data(&self, oid: ObjId) -> &MapData {
        match &self.heap.obj(oid).kind {
            ObjKind::MapObj(d) | ObjKind::WeakMapObj(d) => d,
            _ => unreachable!("checked by this_map"),
        }
    }

    fn map_data_mut(&mut self, oid: ObjId) -> &mut MapData {
        match &mut self.heap.obj_mut(oid).kind {
            ObjKind::MapObj(d) | ObjKind::WeakMapObj(d) => d,
            _ => unreachable!("checked by this_map"),
        }
    }

    fn set_data(&self, oid: ObjId) -> &SetData {
        match &self.heap.obj(oid).kind {
            ObjKind::SetObj(d) | ObjKind::WeakSetObj(d) => d,
            _ => unreachable!("checked by this_set"),
        }
    }

    fn set_data_mut(&mut self, oid: ObjId) -> &mut SetData {
        match &mut self.heap.obj_mut(oid).kind {
            ObjKind::SetObj(d) | ObjKind::WeakSetObj(d) => d,
            _ => unreachable!("checked by this_set"),
        }
    }

    /// Linear SameValueZero scan (bounded: one loop charge per 256 slots).
    fn map_find(&mut self, oid: ObjId, key: &JsValue) -> Result<Option<usize>, Abrupt> {
        for start in (0..self.map_data(oid).entries.len()).step_by(256) {
            self.charge_loop()?;
            let end = (start + 256).min(self.map_data(oid).entries.len());
            for i in start..end {
                if let Some((k, _)) = &self.map_data(oid).entries[i] {
                    if crate::ops::same_value_zero(k, key) {
                        return Ok(Some(i));
                    }
                }
            }
        }
        Ok(None)
    }

    fn set_find(&mut self, oid: ObjId, key: &JsValue) -> Result<Option<usize>, Abrupt> {
        for start in (0..self.set_data(oid).entries.len()).step_by(256) {
            self.charge_loop()?;
            let end = (start + 256).min(self.set_data(oid).entries.len());
            for i in start..end {
                if let Some(k) = &self.set_data(oid).entries[i] {
                    if crate::ops::same_value_zero(k, key) {
                        return Ok(Some(i));
                    }
                }
            }
        }
        Ok(None)
    }

    // -- constructors --------------------------------------------------------

    /// Map/WeakMap constructor: ordinary create + AddEntriesFromIterable via
    /// the observable `set` adder.
    pub(crate) fn map_like_ctor(
        &mut self,
        weak: bool,
        args: &[JsValue],
        new_target: Option<&JsValue>,
    ) -> ERes {
        let Some(ntv) = new_target else {
            return Err(self.throw_type_error());
        };
        let default_proto = if weak {
            self.intr.weakmap_proto
        } else {
            self.intr.map_proto
        };
        let proto = self.get_prototype_from_constructor(ntv, default_proto)?;
        let kind = if weak {
            ObjKind::WeakMapObj(MapData::default())
        } else {
            ObjKind::MapObj(MapData::default())
        };
        let oid = self.alloc_obj(JsObject::new(kind, Some(proto)))?;
        let iterable = args.first().cloned().unwrap_or(JsValue::Undefined);
        if iterable.is_nullish() {
            return Ok(JsValue::Obj(oid));
        }
        // AddEntriesFromIterable: adder = Get(target, "set"), then iterate.
        let adder = self.get_from_object(oid, &PropKey::from_str("set"), JsValue::Obj(oid))?;
        if !matches!(&adder, JsValue::Obj(f) if self.heap.obj(*f).is_callable()) {
            return Err(self.throw_type_error());
        }
        let mut it = self.get_iterator_or_type_error(&iterable)?;
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
                s.call_value(&adder, JsValue::Obj(oid), vec![k, v])?;
                Ok(())
            })(self);
            if let Err(a) = body {
                return Err(self.close_after_body_abrupt(&it, a));
            }
        }
        Ok(JsValue::Obj(oid))
    }

    /// Set/WeakSet constructor via the observable `add` adder.
    pub(crate) fn set_like_ctor(
        &mut self,
        weak: bool,
        args: &[JsValue],
        new_target: Option<&JsValue>,
    ) -> ERes {
        let Some(ntv) = new_target else {
            return Err(self.throw_type_error());
        };
        let default_proto = if weak {
            self.intr.weakset_proto
        } else {
            self.intr.set_proto
        };
        let proto = self.get_prototype_from_constructor(ntv, default_proto)?;
        let kind = if weak {
            ObjKind::WeakSetObj(SetData::default())
        } else {
            ObjKind::SetObj(SetData::default())
        };
        let oid = self.alloc_obj(JsObject::new(kind, Some(proto)))?;
        let iterable = args.first().cloned().unwrap_or(JsValue::Undefined);
        if iterable.is_nullish() {
            return Ok(JsValue::Obj(oid));
        }
        let adder = self.get_from_object(oid, &PropKey::from_str("add"), JsValue::Obj(oid))?;
        if !matches!(&adder, JsValue::Obj(f) if self.heap.obj(*f).is_callable()) {
            return Err(self.throw_type_error());
        }
        let mut it = self.get_iterator_or_type_error(&iterable)?;
        loop {
            let v = match self.fast_iter_next(&mut it) {
                Ok(Some(v)) => v,
                Ok(None) => break,
                Err(a) => return Err(a),
            };
            self.charge_loop()?;
            if let Err(a) = self.call_value(&adder, JsValue::Obj(oid), vec![v]) {
                return Err(self.close_after_body_abrupt(&it, a));
            }
        }
        Ok(JsValue::Obj(oid))
    }

    // -- dispatch ------------------------------------------------------------

    #[allow(clippy::too_many_lines)]
    pub(crate) fn dispatch_collections(
        &mut self,
        nf: NativeFn,
        this: JsValue,
        args: Vec<JsValue>,
    ) -> ERes {
        let arg = |i: usize| args.get(i).cloned().unwrap_or(JsValue::Undefined);
        use NativeFn as N;
        match nf {
            // -- Map ----------------------------------------------------------
            N::MapGet => {
                let oid = self.this_map(&this, false)?;
                let key = canon_key(arg(0));
                Ok(match self.map_find(oid, &key)? {
                    Some(i) => self.map_data(oid).entries[i]
                        .as_ref()
                        .map_or(JsValue::Undefined, |(_, v)| v.clone()),
                    None => JsValue::Undefined,
                })
            }
            N::MapSet => {
                let oid = self.this_map(&this, false)?;
                let key = canon_key(arg(0));
                let v = arg(1);
                match self.map_find(oid, &key)? {
                    Some(i) => {
                        if let Some(slot) = self.map_data_mut(oid).entries.get_mut(i) {
                            if let Some((_, ev)) = slot {
                                *ev = v;
                            }
                        }
                    }
                    None => self.map_data_mut(oid).entries.push(Some((key, v))),
                }
                Ok(JsValue::Obj(oid))
            }
            N::MapHas => {
                let oid = self.this_map(&this, false)?;
                let key = canon_key(arg(0));
                Ok(JsValue::Bool(self.map_find(oid, &key)?.is_some()))
            }
            N::MapDelete => {
                let oid = self.this_map(&this, false)?;
                let key = canon_key(arg(0));
                match self.map_find(oid, &key)? {
                    Some(i) => {
                        self.map_data_mut(oid).entries[i] = None;
                        Ok(JsValue::Bool(true))
                    }
                    None => Ok(JsValue::Bool(false)),
                }
            }
            N::MapClear => {
                let oid = self.this_map(&this, false)?;
                for slot in &mut self.map_data_mut(oid).entries {
                    *slot = None;
                }
                Ok(JsValue::Undefined)
            }
            N::MapSizeGetter => {
                let oid = self.this_map(&this, false)?;
                let n = self.map_data(oid).entries.iter().flatten().count();
                #[allow(clippy::cast_precision_loss)]
                Ok(JsValue::Num(n as f64))
            }
            N::MapForEach => {
                let oid = self.this_map(&this, false)?;
                let cb = arg(0);
                if !matches!(&cb, JsValue::Obj(f) if self.heap.obj(*f).is_callable()) {
                    return Err(self.throw_type_error());
                }
                let this_arg = arg(1);
                // Live-list walk: entries appended during iteration are
                // visited; tombstones are skipped (spec 24.1.3.5).
                let mut i = 0;
                while i < self.map_data(oid).entries.len() {
                    self.charge_loop()?;
                    if let Some((k, v)) = self.map_data(oid).entries[i].clone() {
                        self.call_value(
                            &cb,
                            this_arg.clone(),
                            vec![v, k, JsValue::Obj(oid)],
                        )?;
                    }
                    i += 1;
                }
                Ok(JsValue::Undefined)
            }
            N::MapGetOrInsert => {
                let oid = self.this_map(&this, false)?;
                let key = canon_key(arg(0));
                let v = arg(1);
                if let Some(i) = self.map_find(oid, &key)? {
                    if let Some((_, ev)) = &self.map_data(oid).entries[i] {
                        return Ok(ev.clone());
                    }
                }
                self.map_data_mut(oid).entries.push(Some((key, v.clone())));
                Ok(v)
            }
            N::MapGetOrInsertComputed => {
                let oid = self.this_map(&this, false)?;
                let cb = arg(1);
                if !matches!(&cb, JsValue::Obj(f) if self.heap.obj(*f).is_callable()) {
                    return Err(self.throw_type_error());
                }
                let key = canon_key(arg(0));
                if let Some(i) = self.map_find(oid, &key)? {
                    if let Some((_, ev)) = &self.map_data(oid).entries[i] {
                        return Ok(ev.clone());
                    }
                }
                let v = self.call_value(&cb, JsValue::Undefined, vec![key.clone()])?;
                // The callback may have inserted the key: overwrite in place.
                if let Some(i) = self.map_find(oid, &key)? {
                    if let Some(slot) = self.map_data_mut(oid).entries.get_mut(i) {
                        if let Some((_, ev)) = slot {
                            *ev = v.clone();
                        }
                    }
                    return Ok(v);
                }
                self.map_data_mut(oid).entries.push(Some((key, v.clone())));
                Ok(v)
            }
            N::MapEntries | N::MapKeys | N::MapValues => {
                // 24.1.3.{4,7,12}: CreateMapIterator over the live [[MapData]].
                let oid = self.this_map(&this, false)?;
                let kind = match nf {
                    N::MapKeys => crate::iterobj::IterKind::Key,
                    N::MapValues => crate::iterobj::IterKind::Value,
                    _ => crate::iterobj::IterKind::KeyValue,
                };
                self.make_map_iterator(oid, kind)
            }
            N::SetValues | N::SetEntries => {
                // 24.2.3.{10,5}: CreateSetIterator (values kind; entries →
                // [v, v]). Set.prototype.keys IS values (same native).
                let oid = self.this_set(&this, false)?;
                let kind = if matches!(nf, N::SetEntries) {
                    crate::iterobj::IterKind::KeyValue
                } else {
                    crate::iterobj::IterKind::Value
                };
                self.make_set_iterator(oid, kind)
            }
            // -- Set ----------------------------------------------------------
            N::SetAdd => {
                let oid = self.this_set(&this, false)?;
                let v = canon_key(arg(0));
                if self.set_find(oid, &v)?.is_none() {
                    self.set_data_mut(oid).entries.push(Some(v));
                }
                Ok(JsValue::Obj(oid))
            }
            N::SetHas => {
                let oid = self.this_set(&this, false)?;
                let v = canon_key(arg(0));
                Ok(JsValue::Bool(self.set_find(oid, &v)?.is_some()))
            }
            N::SetDelete => {
                let oid = self.this_set(&this, false)?;
                let v = canon_key(arg(0));
                match self.set_find(oid, &v)? {
                    Some(i) => {
                        self.set_data_mut(oid).entries[i] = None;
                        Ok(JsValue::Bool(true))
                    }
                    None => Ok(JsValue::Bool(false)),
                }
            }
            N::SetClear => {
                let oid = self.this_set(&this, false)?;
                for slot in &mut self.set_data_mut(oid).entries {
                    *slot = None;
                }
                Ok(JsValue::Undefined)
            }
            N::SetSizeGetter => {
                let oid = self.this_set(&this, false)?;
                let n = self.set_data(oid).entries.iter().flatten().count();
                #[allow(clippy::cast_precision_loss)]
                Ok(JsValue::Num(n as f64))
            }
            N::SetForEach => {
                let oid = self.this_set(&this, false)?;
                let cb = arg(0);
                if !matches!(&cb, JsValue::Obj(f) if self.heap.obj(*f).is_callable()) {
                    return Err(self.throw_type_error());
                }
                let this_arg = arg(1);
                let mut i = 0;
                while i < self.set_data(oid).entries.len() {
                    self.charge_loop()?;
                    if let Some(v) = self.set_data(oid).entries[i].clone() {
                        self.call_value(
                            &cb,
                            this_arg.clone(),
                            vec![v.clone(), v, JsValue::Obj(oid)],
                        )?;
                    }
                    i += 1;
                }
                Ok(JsValue::Undefined)
            }
            // -- WeakMap ------------------------------------------------------
            N::WeakMapGet => {
                let oid = self.this_map(&this, true)?;
                let key = arg(0);
                if !can_be_held_weakly(self, &key) {
                    return Ok(JsValue::Undefined);
                }
                Ok(match self.map_find(oid, &key)? {
                    Some(i) => self.map_data(oid).entries[i]
                        .as_ref()
                        .map_or(JsValue::Undefined, |(_, v)| v.clone()),
                    None => JsValue::Undefined,
                })
            }
            N::WeakMapSet => {
                let oid = self.this_map(&this, true)?;
                let key = arg(0);
                if !can_be_held_weakly(self, &key) {
                    return Err(self.throw_type_error());
                }
                let v = arg(1);
                match self.map_find(oid, &key)? {
                    Some(i) => {
                        if let Some((_, ev)) = &mut self.map_data_mut(oid).entries[i] {
                            *ev = v;
                        }
                    }
                    None => self.map_data_mut(oid).entries.push(Some((key, v))),
                }
                Ok(JsValue::Obj(oid))
            }
            N::WeakMapHas => {
                let oid = self.this_map(&this, true)?;
                let key = arg(0);
                if !can_be_held_weakly(self, &key) {
                    return Ok(JsValue::Bool(false));
                }
                Ok(JsValue::Bool(self.map_find(oid, &key)?.is_some()))
            }
            N::WeakMapDelete => {
                let oid = self.this_map(&this, true)?;
                let key = arg(0);
                if !can_be_held_weakly(self, &key) {
                    return Ok(JsValue::Bool(false));
                }
                match self.map_find(oid, &key)? {
                    Some(i) => {
                        self.map_data_mut(oid).entries[i] = None;
                        Ok(JsValue::Bool(true))
                    }
                    None => Ok(JsValue::Bool(false)),
                }
            }
            N::WeakMapGetOrInsert => {
                let oid = self.this_map(&this, true)?;
                let key = arg(0);
                if !can_be_held_weakly(self, &key) {
                    return Err(self.throw_type_error());
                }
                let v = arg(1);
                if let Some(i) = self.map_find(oid, &key)? {
                    if let Some((_, ev)) = &self.map_data(oid).entries[i] {
                        return Ok(ev.clone());
                    }
                }
                self.map_data_mut(oid).entries.push(Some((key, v.clone())));
                Ok(v)
            }
            N::WeakMapGetOrInsertComputed => {
                let oid = self.this_map(&this, true)?;
                let cb = arg(1);
                if !matches!(&cb, JsValue::Obj(f) if self.heap.obj(*f).is_callable()) {
                    return Err(self.throw_type_error());
                }
                let key = arg(0);
                if !can_be_held_weakly(self, &key) {
                    return Err(self.throw_type_error());
                }
                if let Some(i) = self.map_find(oid, &key)? {
                    if let Some((_, ev)) = &self.map_data(oid).entries[i] {
                        return Ok(ev.clone());
                    }
                }
                let v = self.call_value(&cb, JsValue::Undefined, vec![key.clone()])?;
                if let Some(i) = self.map_find(oid, &key)? {
                    if let Some((_, ev)) = &mut self.map_data_mut(oid).entries[i] {
                        *ev = v.clone();
                    }
                    return Ok(v);
                }
                self.map_data_mut(oid).entries.push(Some((key, v.clone())));
                Ok(v)
            }
            // -- WeakSet ------------------------------------------------------
            N::WeakSetAdd => {
                let oid = self.this_set(&this, true)?;
                let v = arg(0);
                if !can_be_held_weakly(self, &v) {
                    return Err(self.throw_type_error());
                }
                if self.set_find(oid, &v)?.is_none() {
                    self.set_data_mut(oid).entries.push(Some(v));
                }
                Ok(JsValue::Obj(oid))
            }
            N::WeakSetHas => {
                let oid = self.this_set(&this, true)?;
                let v = arg(0);
                if !can_be_held_weakly(self, &v) {
                    return Ok(JsValue::Bool(false));
                }
                Ok(JsValue::Bool(self.set_find(oid, &v)?.is_some()))
            }
            N::WeakSetDelete => {
                let oid = self.this_set(&this, true)?;
                let v = arg(0);
                if !can_be_held_weakly(self, &v) {
                    return Ok(JsValue::Bool(false));
                }
                match self.set_find(oid, &v)? {
                    Some(i) => {
                        self.set_data_mut(oid).entries[i] = None;
                        Ok(JsValue::Bool(true))
                    }
                    None => Ok(JsValue::Bool(false)),
                }
            }
            _ => Err(Abrupt::Fatal(
                "unrouted collection native (interpreter bug)".to_string(),
            )),
        }
    }
}
