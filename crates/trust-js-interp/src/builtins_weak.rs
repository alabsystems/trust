// §26.1 WeakRef, §26.2 FinalizationRegistry, and the §27.1 %Iterator% abstract
// global constructor.
//
// GC and finalization are UNOBSERVABLE in the synchronous S0 slice: no cleanup
// callback ever fires, and a WeakRef target is never collected. So the object
// model + methods are exact and complete for every observation these programs
// can make — construction, prototype identity, @@toStringTag, deref (always the
// live target), and register/unregister (which observe only the presence of a
// matching unregister token). A program that tried to observe actual
// finalization timing (an async cleanup callback) would refuse elsewhere, since
// no such callback is ever queued.
//
// %Iterator% is the abstract constructor: [[Call]] and direct [[Construct]]
// (NewTarget === %Iterator%) throw TypeError; a subclass proceeds via
// OrdinaryCreateFromConstructor. `Iterator.prototype` IS %IteratorPrototype%;
// its `constructor` and @@toStringTag are accessor properties (the
// iterator-helpers web-compat design). The iterator-helper methods
// (map/filter/take/drop/...) are proposal surface both engines ship but this
// slice does not model — they stay danger-listed and refuse (NoCoverage).
//
// Author: Andrew Yates
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

use crate::interp::{Abrupt, ERes, Interp};
use crate::ops::same_value;
use crate::props::PartialDesc;
use trust_js_value::{JsObject, JsValue, ObjId, ObjKind, PropKey, SymId, WkSym};

/// CanBeHeldWeakly (7.3.4-adjacent): objects, and symbols not registered in the
/// GlobalSymbolRegistry (well-known symbols and unregistered user symbols
/// qualify; a `Symbol.for(...)` result does not).
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
    // -- §26.1 WeakRef -------------------------------------------------------

    /// `WeakRef ( target )` [[Construct]]: NewTarget required; target must be
    /// weakly-holdable; OrdinaryCreateFromConstructor(NewTarget,
    /// "%WeakRef.prototype%") with [[WeakRefTarget]] = target.
    pub(crate) fn weakref_construct(
        &mut self,
        args: &[JsValue],
        new_target: Option<&JsValue>,
    ) -> ERes {
        let Some(ntv) = new_target else {
            return Err(self.throw_type_error());
        };
        let target = args.first().cloned().unwrap_or(JsValue::Undefined);
        if !can_be_held_weakly(self, &target) {
            return Err(self.throw_type_error());
        }
        let proto = self.get_prototype_from_constructor(ntv, self.intr.weakref_proto)?;
        let oid = self.alloc_obj(JsObject::new(ObjKind::Plain, Some(proto)))?;
        self.weakref_targets.insert(oid, target);
        Ok(JsValue::Obj(oid))
    }

    /// `WeakRef.prototype.deref ( )`: requires [[WeakRefTarget]]. GC never runs,
    /// so the target is always live and returned.
    fn weakref_deref(&mut self, this: &JsValue) -> ERes {
        let JsValue::Obj(oid) = this else {
            return Err(self.throw_type_error());
        };
        match self.weakref_targets.get(oid) {
            Some(t) => Ok(t.clone()),
            None => Err(self.throw_type_error()),
        }
    }

    // -- §26.2 FinalizationRegistry -----------------------------------------

    /// `FinalizationRegistry ( cleanupCallback )` [[Construct]]: NewTarget
    /// required; callback must be callable; the [[Cells]] list starts empty.
    pub(crate) fn finreg_construct(
        &mut self,
        args: &[JsValue],
        new_target: Option<&JsValue>,
    ) -> ERes {
        let Some(ntv) = new_target else {
            return Err(self.throw_type_error());
        };
        let callback = args.first().cloned().unwrap_or(JsValue::Undefined);
        if !matches!(&callback, JsValue::Obj(o) if self.heap.obj(*o).is_callable()) {
            return Err(self.throw_type_error());
        }
        let proto = self.get_prototype_from_constructor(ntv, self.intr.finreg_proto)?;
        let oid = self.alloc_obj(JsObject::new(ObjKind::Plain, Some(proto)))?;
        self.finreg_cells.insert(oid, Vec::new());
        Ok(JsValue::Obj(oid))
    }

    /// `FinalizationRegistry.prototype.register ( target, heldValue [ ,
    /// unregisterToken ] )`.
    fn finreg_register(&mut self, this: &JsValue, args: &[JsValue]) -> ERes {
        let JsValue::Obj(oid) = this else {
            return Err(self.throw_type_error());
        };
        if !self.finreg_cells.contains_key(oid) {
            return Err(self.throw_type_error());
        }
        let target = args.first().cloned().unwrap_or(JsValue::Undefined);
        let held = args.get(1).cloned().unwrap_or(JsValue::Undefined);
        let token = args.get(2).cloned().unwrap_or(JsValue::Undefined);
        if !can_be_held_weakly(self, &target) {
            return Err(self.throw_type_error());
        }
        if same_value(&target, &held) {
            return Err(self.throw_type_error());
        }
        let token_slot = if matches!(token, JsValue::Undefined) {
            None
        } else if can_be_held_weakly(self, &token) {
            Some(token)
        } else {
            return Err(self.throw_type_error());
        };
        // The cell's target/held are unobservable (no cleanup runs); only the
        // token is retained (what `unregister` observes).
        self.finreg_cells
            .get_mut(oid)
            .expect("brand-checked above")
            .push(token_slot);
        Ok(JsValue::Undefined)
    }

    /// `FinalizationRegistry.prototype.unregister ( unregisterToken )`: removes
    /// every cell whose token SameValue-matches; returns whether any were.
    fn finreg_unregister(&mut self, this: &JsValue, args: &[JsValue]) -> ERes {
        let JsValue::Obj(oid) = this else {
            return Err(self.throw_type_error());
        };
        if !self.finreg_cells.contains_key(oid) {
            return Err(self.throw_type_error());
        }
        let token = args.first().cloned().unwrap_or(JsValue::Undefined);
        if !can_be_held_weakly(self, &token) {
            return Err(self.throw_type_error());
        }
        let cells = self.finreg_cells.get_mut(oid).expect("brand-checked above");
        let before = cells.len();
        cells.retain(|slot| !matches!(slot, Some(t) if same_value(t, &token)));
        Ok(JsValue::Bool(cells.len() != before))
    }

    // -- §27.1 %Iterator% ----------------------------------------------------

    /// `Iterator ( )` [[Construct]]: throw if NewTarget is absent ([[Call]]) or
    /// is %Iterator% itself (the abstract base); otherwise
    /// OrdinaryCreateFromConstructor(NewTarget, "%Iterator.prototype%").
    pub(crate) fn iterator_construct(&mut self, new_target: Option<&JsValue>) -> ERes {
        let Some(ntv) = new_target else {
            return Err(self.throw_type_error());
        };
        if matches!(ntv, JsValue::Obj(o) if *o == self.intr.iterator_ctor) {
            return Err(self.throw_type_error());
        }
        let proto = self.get_prototype_from_constructor(ntv, self.intr.iterator_proto)?;
        let oid = self.alloc_obj(JsObject::new(ObjKind::Plain, Some(proto)))?;
        Ok(JsValue::Obj(oid))
    }

    /// SetterThatIgnoresPrototypeProperties(this, home, key, value): the shared
    /// setter behind %Iterator.prototype%'s `constructor` / @@toStringTag. A set
    /// on the home prototype itself throws (emulating a non-writable data
    /// property); on any other object it creates/updates an own property.
    fn setter_ignoring_proto(
        &mut self,
        this: &JsValue,
        home: ObjId,
        key: &PropKey,
        value: JsValue,
    ) -> Result<(), Abrupt> {
        let JsValue::Obj(oid) = this else {
            return Err(self.throw_type_error());
        };
        if *oid == home {
            return Err(self.throw_type_error());
        }
        if self.own_prop(*oid, key).is_none() {
            // CreateDataPropertyOrThrow.
            let ok = self.define_own(*oid, key, PartialDesc::full_data(value, true, true, true))?;
            if !ok {
                return Err(self.throw_type_error());
            }
        } else {
            // Set(this, key, value, true).
            self.set_prop(this, key, value, true)?;
        }
        Ok(())
    }

    /// Dispatch for the WeakRef/FinalizationRegistry/Iterator native functions.
    pub(crate) fn dispatch_weak(
        &mut self,
        nf: trust_js_value::NativeFn,
        this: JsValue,
        args: Vec<JsValue>,
    ) -> ERes {
        use trust_js_value::NativeFn as N;
        match nf {
            // Constructors reach here only via a bare [[Call]] (no `new`), which
            // is always a TypeError for these classes; the `new` path routes
            // through `construct` in funcs.rs.
            N::WeakRefCtor | N::FinalizationRegistryCtor => Err(self.throw_type_error()),
            N::WeakRefDeref => self.weakref_deref(&this),
            N::FinRegRegister => self.finreg_register(&this, &args),
            N::FinRegUnregister => self.finreg_unregister(&this, &args),
            N::IteratorCtor => Err(self.throw_type_error()),
            N::IteratorProtoCtorGet => Ok(JsValue::Obj(self.intr.iterator_ctor)),
            N::IteratorProtoTagGet => Ok(JsValue::str_from("Iterator")),
            N::IteratorProtoCtorSet => {
                let home = self.intr.iterator_proto;
                let v = args.first().cloned().unwrap_or(JsValue::Undefined);
                self.setter_ignoring_proto(&this, home, &PropKey::from_str("constructor"), v)?;
                Ok(JsValue::Undefined)
            }
            N::IteratorProtoTagSet => {
                let home = self.intr.iterator_proto;
                let v = args.first().cloned().unwrap_or(JsValue::Undefined);
                let key = PropKey::Sym(SymId::WellKnown(WkSym::ToStringTag));
                self.setter_ignoring_proto(&this, home, &key, v)?;
                Ok(JsValue::Undefined)
            }
            _ => Err(Abrupt::Fatal(format!("dispatch_weak: unexpected {nf:?}"))),
        }
    }
}
