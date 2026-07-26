// Map (24.1) / Set (24.2) / WeakMap (24.3) / WeakSet (24.4): the keyed
// collections, written from the spec. The shared entry store keeps insertion
// order with in-place tombstones so a live iterator observes later additions
// and skips deletions/clears (24.1.5.1); keys compare under SameValueZero with
// CanonicalizeKeyedCollectionKey (-0𝔽 folds to +0𝔽). AddEntriesFromIterable
// (24.1.1.2) calls the receiver's OWN `set`/`add` (adder-observable) through
// the general iterator protocol and IteratorClose-es on an adder fault. The
// Map/Set iterator objects (%MapIteratorPrototype% / %SetIteratorPrototype%)
// step the live store. WeakMap/WeakSet accept only object / non-registered-
// symbol keys (CanBeHeldWeakly); with no observable GC the store never
// collects, which is sound for a deterministic trace.
//
// Author: Andrew Yates
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

use crate::interp::{Abrupt, ERes, Interp};
use crate::value::{
    units_from_str, Builtin, CollIterKind, CollKey, CollectionData, NativeErrorKind, ObjId,
    ObjKind, Object, Prop, Value,
};
use std::cell::RefCell;
use std::rc::Rc;

/// CanonicalizeKeyedCollectionKey (24.5.1): -0𝔽 → +0𝔽; every other value
/// unchanged. Applied to the STORED key so iteration reads back +0.
fn canon_key(v: Value) -> Value {
    match v {
        Value::Num(n) if n == 0.0 => Value::Num(0.0),
        other => other,
    }
}

/// The hashable index key for a value under SameValueZero. Folds -0 to +0 and
/// collapses every NaN to one canonical bit pattern, so the index map's key
/// identity is exactly SameValueZero.
fn coll_key(v: &Value) -> CollKey {
    match v {
        Value::Undefined => CollKey::Undef,
        Value::Null => CollKey::Null,
        Value::Bool(b) => CollKey::Bool(*b),
        Value::Num(n) => {
            let bits = if n.is_nan() {
                0x7ff8_0000_0000_0000
            } else if *n == 0.0 {
                0
            } else {
                n.to_bits()
            };
            CollKey::Num(bits)
        }
        Value::BigInt(b) => CollKey::Big((**b).clone()),
        Value::Str(s) => CollKey::Str((**s).clone()),
        Value::Sym(s) => CollKey::Sym(s.0),
        Value::Obj(o) => CollKey::Obj(o.0),
    }
}

impl CollectionData {
    /// [[MapData]] get: the value paired with `key` under SameValueZero, or
    /// None.
    fn get(&self, key: &Value) -> Option<Value> {
        let i = *self.index.get(&coll_key(key))?;
        self.entries[i].as_ref().map(|(_, v)| v.clone())
    }

    fn has(&self, key: &Value) -> bool {
        self.index.contains_key(&coll_key(key))
    }

    /// Insert or update. `value` is stored as-is; the stored key is canonical.
    fn set(&mut self, key: Value, value: Value) {
        let ck = coll_key(&key);
        if let Some(&i) = self.index.get(&ck) {
            if let Some(slot) = self.entries.get_mut(i) {
                if let Some((_, v)) = slot.as_mut() {
                    *v = value;
                    return;
                }
            }
        }
        let i = self.entries.len();
        self.entries.push(Some((canon_key(key), value)));
        self.index.insert(ck, i);
        self.size += 1;
    }

    /// [[Delete]]: tombstone the entry in place (24.1.3.3). Returns whether a
    /// live entry existed.
    fn delete(&mut self, key: &Value) -> bool {
        let ck = coll_key(key);
        if let Some(i) = self.index.remove(&ck) {
            if let Some(slot) = self.entries.get_mut(i) {
                *slot = None;
            }
            self.size = self.size.saturating_sub(1);
            true
        } else {
            false
        }
    }

    /// clear (24.1.3.1): tombstone every entry in place so live iterators skip
    /// them; later additions append.
    fn clear(&mut self) {
        for slot in &mut self.entries {
            *slot = None;
        }
        self.index.clear();
        self.size = 0;
    }
}

impl Interp {
    // -- internal-slot accessors -------------------------------------------

    /// RequireInternalSlot for a Map/Set/WeakMap/WeakSet: the shared store, or
    /// a TypeError if `this` lacks the exact slot.
    fn map_store(&mut self, this: &Value) -> Result<Rc<RefCell<CollectionData>>, Abrupt> {
        match this {
            Value::Obj(o) => match &self.obj(*o).kind {
                ObjKind::Map(d) => Ok(Rc::clone(d)),
                _ => Err(self.throw_native(NativeErrorKind::TypeError)),
            },
            _ => Err(self.throw_native(NativeErrorKind::TypeError)),
        }
    }

    fn set_store(&mut self, this: &Value) -> Result<Rc<RefCell<CollectionData>>, Abrupt> {
        match this {
            Value::Obj(o) => match &self.obj(*o).kind {
                ObjKind::Set(d) => Ok(Rc::clone(d)),
                _ => Err(self.throw_native(NativeErrorKind::TypeError)),
            },
            _ => Err(self.throw_native(NativeErrorKind::TypeError)),
        }
    }

    fn weakmap_store(&mut self, this: &Value) -> Result<Rc<RefCell<CollectionData>>, Abrupt> {
        match this {
            Value::Obj(o) => match &self.obj(*o).kind {
                ObjKind::WeakMap(d) => Ok(Rc::clone(d)),
                _ => Err(self.throw_native(NativeErrorKind::TypeError)),
            },
            _ => Err(self.throw_native(NativeErrorKind::TypeError)),
        }
    }

    fn weakset_store(&mut self, this: &Value) -> Result<Rc<RefCell<CollectionData>>, Abrupt> {
        match this {
            Value::Obj(o) => match &self.obj(*o).kind {
                ObjKind::WeakSet(d) => Ok(Rc::clone(d)),
                _ => Err(self.throw_native(NativeErrorKind::TypeError)),
            },
            _ => Err(self.throw_native(NativeErrorKind::TypeError)),
        }
    }

    /// CanBeHeldWeakly (7.4.4): an object, or a symbol not in the global
    /// registry (a `Symbol.for` result cannot be held weakly; well-known and
    /// ordinary symbols can).
    fn can_be_held_weakly(&self, v: &Value) -> bool {
        match v {
            Value::Obj(_) => true,
            Value::Sym(s) => self.sym_data(*s).registry_key.is_none(),
            _ => false,
        }
    }

    // -- constructors -------------------------------------------------------

    /// The shared constructor body for Map/Set/WeakMap/WeakSet: create the
    /// instance parented per new.target, then (if the iterable is present)
    /// read the OWN adder and AddEntriesFromIterable.
    fn collection_construct(
        &mut self,
        default_proto: ObjId,
        make_kind: fn(Rc<RefCell<CollectionData>>) -> ObjKind,
        iterable: Value,
        adder_name: &str,
        is_map: bool,
    ) -> ERes {
        let proto = match self.pending_new_target.take() {
            Some(nt) => self.proto_from_new_target(nt, default_proto)?,
            None => default_proto,
        };
        let store = Rc::new(RefCell::new(CollectionData::default()));
        let oid = self.alloc(Object::new(make_kind(Rc::clone(&store)), Some(proto)));
        if matches!(iterable, Value::Undefined | Value::Null) {
            return Ok(Value::Obj(oid));
        }
        // adder = Get(obj, "set"/"add"); must be callable.
        let adder = self.get_from_object(oid, &units_from_str(adder_name))?;
        let Value::Obj(adder_fn) = adder else {
            return Err(self.throw_native(NativeErrorKind::TypeError));
        };
        if !self.obj(adder_fn).is_callable() {
            return Err(self.throw_native(NativeErrorKind::TypeError));
        }
        self.add_entries_from_iterable(oid, &iterable, adder_fn, is_map)?;
        Ok(Value::Obj(oid))
    }

    /// AddEntriesFromIterable (24.1.1.2) for a Map/WeakMap (`is_map`), or the
    /// Set/WeakSet loop (24.2.1.1) otherwise. The adder is called with the
    /// target as `this`; an adder/entry fault IteratorCloses the iterator
    /// (IfAbruptCloseIterator).
    fn add_entries_from_iterable(
        &mut self,
        target: ObjId,
        iterable: &Value,
        adder: ObjId,
        is_map: bool,
    ) -> Result<(), Abrupt> {
        let mut it = self.slice_iterator(iterable)?;
        loop {
            self.charge_loop()?;
            // IteratorStep/IteratorValue faults propagate WITHOUT close.
            let Some(item) = self.slice_iter_next(&mut it)? else {
                return Ok(());
            };
            if is_map {
                // nextItem must be an Object (else TypeError + IteratorClose).
                if !matches!(item, Value::Obj(_)) {
                    let err = self.throw_native(NativeErrorKind::TypeError);
                    let _ = self.slice_iterator_close(&mut it);
                    return Err(err);
                }
                let step = (|| -> Result<(), Abrupt> {
                    let k = self.get_prop_value(&item, &units_from_str("0"))?;
                    let v = self.get_prop_value(&item, &units_from_str("1"))?;
                    self.call_function(adder, Value::Obj(target), vec![k, v], false)?;
                    Ok(())
                })();
                if step.is_err() {
                    let _ = self.slice_iterator_close(&mut it);
                    return step;
                }
            } else {
                let r = self.call_function(adder, Value::Obj(target), vec![item], false);
                if r.is_err() {
                    let _ = self.slice_iterator_close(&mut it);
                    return r.map(|_| ());
                }
            }
        }
    }

    // -- iterator objects ---------------------------------------------------

    /// CreateMapIterator (24.1.5.1) / CreateSetIterator (24.2.5.1): a fresh
    /// iterator sharing `this`'s store. RequireInternalSlot on the receiver.
    fn make_coll_iterator(
        &mut self,
        this: &Value,
        kind: CollIterKind,
        is_set: bool,
    ) -> ERes {
        let store = if is_set {
            self.set_store(this)?
        } else {
            self.map_store(this)?
        };
        let proto = if is_set {
            self.intr.set_iterator_proto
        } else {
            self.intr.map_iterator_proto
        };
        let okind = if is_set {
            ObjKind::SetIterator {
                target: Some(store),
                index: 0,
                kind,
            }
        } else {
            ObjKind::MapIterator {
                target: Some(store),
                index: 0,
                kind,
            }
        };
        let oid = self.alloc(Object::new(okind, Some(proto)));
        Ok(Value::Obj(oid))
    }

    /// %MapIteratorPrototype%.next (24.1.5.2.1) / %SetIteratorPrototype%.next
    /// (24.2.5.2.1): step the shared store, skipping tombstones, seeing
    /// additions. Totality: defensive indexing, never panics.
    fn coll_iterator_next(&mut self, this: &Value, is_set: bool) -> ERes {
        let Value::Obj(oid) = this else {
            return Err(self.throw_native(NativeErrorKind::TypeError));
        };
        let oid = *oid;
        // Read the iterator's slots; the variant must match the prototype.
        let (store, mut index, kind) = match &self.obj(oid).kind {
            ObjKind::MapIterator {
                target,
                index,
                kind,
            } if !is_set => (target.clone(), *index, *kind),
            ObjKind::SetIterator {
                target,
                index,
                kind,
            } if is_set => (target.clone(), *index, *kind),
            _ => return Err(self.throw_native(NativeErrorKind::TypeError)),
        };
        let Some(store) = store else {
            return Ok(self.iter_result(Value::Undefined, true));
        };
        loop {
            let slot = {
                let d = store.borrow();
                if index >= d.entries.len() {
                    None
                } else {
                    Some(d.entries[index].clone())
                }
            };
            match slot {
                // Past the end: mark exhausted ([[Map]]/[[Set]] ← empty).
                None => {
                    self.set_coll_iter_target_none(oid, is_set);
                    return Ok(self.iter_result(Value::Undefined, true));
                }
                Some(None) => {
                    index += 1;
                    continue;
                }
                Some(Some((k, v))) => {
                    self.set_coll_iter_index(oid, index + 1, is_set);
                    let value = match kind {
                        CollIterKind::Key => k,
                        CollIterKind::Value => v,
                        CollIterKind::Entry => {
                            let arr = self.new_array(2);
                            self.obj_mut(arr)
                                .props
                                .insert(units_from_str("0"), Prop::data(k));
                            self.obj_mut(arr)
                                .props
                                .insert(units_from_str("1"), Prop::data(v));
                            self.set_array_length_raw(arr, 2.0);
                            Value::Obj(arr)
                        }
                    };
                    return Ok(self.iter_result(value, false));
                }
            }
        }
    }

    fn set_coll_iter_index(&mut self, oid: ObjId, new_index: usize, is_set: bool) {
        match &mut self.obj_mut(oid).kind {
            ObjKind::MapIterator { index, .. } if !is_set => *index = new_index,
            ObjKind::SetIterator { index, .. } if is_set => *index = new_index,
            _ => {}
        }
    }

    fn set_coll_iter_target_none(&mut self, oid: ObjId, is_set: bool) {
        match &mut self.obj_mut(oid).kind {
            ObjKind::MapIterator { target, .. } if !is_set => *target = None,
            ObjKind::SetIterator { target, .. } if is_set => *target = None,
            _ => {}
        }
    }

    // -- forEach ------------------------------------------------------------

    /// Map.prototype.forEach (24.1.3.5) / Set.prototype.forEach (24.2.3.6):
    /// live iteration over the store; the callback is `(value, key, coll)` for
    /// a Map and `(value, value, coll)` for a Set.
    fn coll_for_each(&mut self, this: &Value, args: &[Value], is_set: bool) -> ERes {
        let store = if is_set {
            self.set_store(this)?
        } else {
            self.map_store(this)?
        };
        let cb = args.first().cloned().unwrap_or(Value::Undefined);
        let cb_fn = match &cb {
            Value::Obj(o) if self.obj(*o).is_callable() => *o,
            _ => return Err(self.throw_native(NativeErrorKind::TypeError)),
        };
        let this_arg = args.get(1).cloned().unwrap_or(Value::Undefined);
        let mut index = 0usize;
        loop {
            self.charge_loop()?;
            let (past_end, slot) = {
                let d = store.borrow();
                if index >= d.entries.len() {
                    (true, None)
                } else {
                    (false, d.entries[index].clone())
                }
            };
            if past_end {
                break;
            }
            index += 1;
            if let Some((k, v)) = slot {
                let call_args = if is_set {
                    vec![v.clone(), v, this.clone()]
                } else {
                    vec![v, k, this.clone()]
                };
                self.call_function(cb_fn, this_arg.clone(), call_args, false)?;
            }
        }
        Ok(Value::Undefined)
    }

    // -- dispatch -----------------------------------------------------------

    /// Is `b` a Map/Set/WeakMap/WeakSet builtin (routed here from
    /// `dispatch_builtin`)?
    pub(crate) fn is_collection_builtin(b: Builtin) -> bool {
        matches!(
            b,
            Builtin::MapCtor
                | Builtin::SetCtor
                | Builtin::WeakMapCtor
                | Builtin::WeakSetCtor
                | Builtin::MapGroupBy
                | Builtin::MapProtoGet
                | Builtin::MapProtoSet
                | Builtin::MapProtoHas
                | Builtin::MapProtoDelete
                | Builtin::MapProtoClear
                | Builtin::MapProtoForEach
                | Builtin::MapSizeGet
                | Builtin::MapProtoEntries
                | Builtin::MapProtoKeys
                | Builtin::MapProtoValues
                | Builtin::SetProtoAdd
                | Builtin::SetProtoHas
                | Builtin::SetProtoDelete
                | Builtin::SetProtoClear
                | Builtin::SetProtoForEach
                | Builtin::SetSizeGet
                | Builtin::SetProtoEntries
                | Builtin::SetProtoValues
                | Builtin::SetProtoCombinator
                | Builtin::WeakMapProtoGet
                | Builtin::WeakMapProtoSet
                | Builtin::WeakMapProtoHas
                | Builtin::WeakMapProtoDelete
                | Builtin::WeakSetProtoAdd
                | Builtin::WeakSetProtoHas
                | Builtin::WeakSetProtoDelete
                | Builtin::MapIteratorNext
                | Builtin::SetIteratorNext
        )
    }

    #[allow(clippy::too_many_lines)]
    pub(crate) fn dispatch_collection_builtin(
        &mut self,
        b: Builtin,
        this: Value,
        args: Vec<Value>,
        is_new: bool,
    ) -> ERes {
        let arg = |i: usize| args.get(i).cloned().unwrap_or(Value::Undefined);
        match b {
            // ---- constructors (new-only) ---------------------------------
            Builtin::MapCtor => {
                if !is_new {
                    return Err(self.throw_native(NativeErrorKind::TypeError));
                }
                self.collection_construct(
                    self.intr.map_proto,
                    ObjKind::Map,
                    arg(0),
                    "set",
                    true,
                )
            }
            Builtin::SetCtor => {
                if !is_new {
                    return Err(self.throw_native(NativeErrorKind::TypeError));
                }
                self.collection_construct(
                    self.intr.set_proto,
                    ObjKind::Set,
                    arg(0),
                    "add",
                    false,
                )
            }
            Builtin::WeakMapCtor => {
                if !is_new {
                    return Err(self.throw_native(NativeErrorKind::TypeError));
                }
                self.collection_construct(
                    self.intr.weakmap_proto,
                    ObjKind::WeakMap,
                    arg(0),
                    "set",
                    true,
                )
            }
            Builtin::WeakSetCtor => {
                if !is_new {
                    return Err(self.throw_native(NativeErrorKind::TypeError));
                }
                self.collection_construct(
                    self.intr.weakset_proto,
                    ObjKind::WeakSet,
                    arg(0),
                    "add",
                    false,
                )
            }
            Builtin::MapGroupBy => Err(Abrupt::Fatal(
                "Map.groupBy (grouping proposal, out of slice)".to_string(),
            )),
            Builtin::SetProtoCombinator => Err(Abrupt::Fatal(
                "Set-methods combinator (union/intersection/... out of slice)".to_string(),
            )),

            // ---- Map.prototype -------------------------------------------
            Builtin::MapProtoGet => {
                let store = self.map_store(&this)?;
                let v = store.borrow().get(&arg(0)).unwrap_or(Value::Undefined);
                Ok(v)
            }
            Builtin::MapProtoSet => {
                let store = self.map_store(&this)?;
                store.borrow_mut().set(arg(0), arg(1));
                Ok(this)
            }
            Builtin::MapProtoHas => {
                let store = self.map_store(&this)?;
                let h = store.borrow().has(&arg(0));
                Ok(Value::Bool(h))
            }
            Builtin::MapProtoDelete => {
                let store = self.map_store(&this)?;
                let d = store.borrow_mut().delete(&arg(0));
                Ok(Value::Bool(d))
            }
            Builtin::MapProtoClear => {
                let store = self.map_store(&this)?;
                store.borrow_mut().clear();
                Ok(Value::Undefined)
            }
            Builtin::MapSizeGet => {
                let store = self.map_store(&this)?;
                #[allow(clippy::cast_precision_loss)]
                let n = store.borrow().size as f64;
                Ok(Value::Num(n))
            }
            Builtin::MapProtoForEach => self.coll_for_each(&this, &args, false),
            Builtin::MapProtoEntries => self.make_coll_iterator(&this, CollIterKind::Entry, false),
            Builtin::MapProtoKeys => self.make_coll_iterator(&this, CollIterKind::Key, false),
            Builtin::MapProtoValues => self.make_coll_iterator(&this, CollIterKind::Value, false),

            // ---- Set.prototype -------------------------------------------
            Builtin::SetProtoAdd => {
                let store = self.set_store(&this)?;
                let k = canon_key(arg(0));
                store.borrow_mut().set(k.clone(), k);
                Ok(this)
            }
            Builtin::SetProtoHas => {
                let store = self.set_store(&this)?;
                let h = store.borrow().has(&arg(0));
                Ok(Value::Bool(h))
            }
            Builtin::SetProtoDelete => {
                let store = self.set_store(&this)?;
                let d = store.borrow_mut().delete(&arg(0));
                Ok(Value::Bool(d))
            }
            Builtin::SetProtoClear => {
                let store = self.set_store(&this)?;
                store.borrow_mut().clear();
                Ok(Value::Undefined)
            }
            Builtin::SetSizeGet => {
                let store = self.set_store(&this)?;
                #[allow(clippy::cast_precision_loss)]
                let n = store.borrow().size as f64;
                Ok(Value::Num(n))
            }
            Builtin::SetProtoForEach => self.coll_for_each(&this, &args, true),
            Builtin::SetProtoEntries => self.make_coll_iterator(&this, CollIterKind::Entry, true),
            Builtin::SetProtoValues => self.make_coll_iterator(&this, CollIterKind::Value, true),

            // ---- WeakMap.prototype ---------------------------------------
            Builtin::WeakMapProtoGet => {
                let store = self.weakmap_store(&this)?;
                if !self.can_be_held_weakly(&arg(0)) {
                    return Ok(Value::Undefined);
                }
                Ok(store.borrow().get(&arg(0)).unwrap_or(Value::Undefined))
            }
            Builtin::WeakMapProtoSet => {
                let store = self.weakmap_store(&this)?;
                if !self.can_be_held_weakly(&arg(0)) {
                    return Err(self.throw_native(NativeErrorKind::TypeError));
                }
                store.borrow_mut().set(arg(0), arg(1));
                Ok(this)
            }
            Builtin::WeakMapProtoHas => {
                let store = self.weakmap_store(&this)?;
                if !self.can_be_held_weakly(&arg(0)) {
                    return Ok(Value::Bool(false));
                }
                Ok(Value::Bool(store.borrow().has(&arg(0))))
            }
            Builtin::WeakMapProtoDelete => {
                let store = self.weakmap_store(&this)?;
                if !self.can_be_held_weakly(&arg(0)) {
                    return Ok(Value::Bool(false));
                }
                Ok(Value::Bool(store.borrow_mut().delete(&arg(0))))
            }

            // ---- WeakSet.prototype ---------------------------------------
            Builtin::WeakSetProtoAdd => {
                let store = self.weakset_store(&this)?;
                if !self.can_be_held_weakly(&arg(0)) {
                    return Err(self.throw_native(NativeErrorKind::TypeError));
                }
                let k = arg(0);
                store.borrow_mut().set(k.clone(), k);
                Ok(this)
            }
            Builtin::WeakSetProtoHas => {
                let store = self.weakset_store(&this)?;
                if !self.can_be_held_weakly(&arg(0)) {
                    return Ok(Value::Bool(false));
                }
                Ok(Value::Bool(store.borrow().has(&arg(0))))
            }
            Builtin::WeakSetProtoDelete => {
                let store = self.weakset_store(&this)?;
                if !self.can_be_held_weakly(&arg(0)) {
                    return Ok(Value::Bool(false));
                }
                Ok(Value::Bool(store.borrow_mut().delete(&arg(0))))
            }

            // ---- iterator next -------------------------------------------
            Builtin::MapIteratorNext => self.coll_iterator_next(&this, false),
            Builtin::SetIteratorNext => self.coll_iterator_next(&this, true),

            _ => Err(Abrupt::Fatal(format!("collection dispatch: {b:?}"))),
        }
    }
}
