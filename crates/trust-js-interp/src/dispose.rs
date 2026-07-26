// Explicit resource management — SYNC half (ES2026 §14.3.3 / §27.3).
//
// `using x = e` declarations register a DisposableResource on the enclosing
// block/function DisposeCapability; at scope exit (normal OR abrupt),
// DisposeResources calls each `[[DisposeMethod]]` in REVERSE registration
// order, aggregating a body-throw + dispose-throw into a `SuppressedError`.
// The `DisposableStack` class exposes the same machinery imperatively
// (use/adopt/defer/move/dispose). Every disposal runs entirely synchronously:
// the sync slice never awaits.
//
// The ASYNC surface (`await using`, `AsyncDisposableStack`, @@asyncDispose) is
// deliberately NOT modeled here: those constructs refuse (NoCoverage) rather
// than run, so no async-disposal trace is ever fabricated. @@asyncDispose
// exists only as a realm symbol identity; no code path consults it.
//
// Soundness: a `using` in a scope this interpreter does not dispose (switch
// case block, for-head, async/generator function body, module top level)
// refuses at the declaration — `eval_decl` only accepts a `using` whose
// environment has an active DisposeCapability (registered by the scope that
// will dispose it). A dispose method that evaluates to an out-of-slice
// `Fatal`, or a completion carrying multiple simultaneous throws whose
// SuppressedError allocation fails, refuses — never a wrong trace.
//
// Author: Andrew Yates
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

use crate::interp::{Abrupt, Compl, ERes, Interp};
use std::rc::Rc;
use trust_js_value::{ErrKind, JsObject, JsValue, ObjId, ObjKind, PropKey, Property};

/// One entry of a `[[DisposableResourceStack]]`, sync-dispose hint only.
#[derive(Clone)]
pub(crate) enum DisposableResource {
    /// `using x = v`, `stack.use(v)`, `stack.defer(onDispose)`: Dispose calls
    /// `Call(method, value)` (for `defer`, value is undefined so the callback
    /// runs with `this` = undefined).
    Method { value: JsValue, method: JsValue },
    /// `stack.adopt(value, onDispose)`: Dispose calls
    /// `Call(onDispose, undefined, «value»)`.
    Adopt { value: JsValue, on_dispose: JsValue },
}

/// The per-`DisposableStack`-instance state (its internal slots), keyed by the
/// instance `ObjId` in `Interp::disposable_stack_state`. Presence is the brand
/// (RequireInternalSlot).
pub(crate) struct DisposableStackData {
    pub disposed: bool,
    pub resources: Vec<DisposableResource>,
}

impl Interp {
    // -- DisposableResource machinery ---------------------------------------

    /// AddDisposableResource(dc, V, sync-dispose) with no explicit method:
    /// CreateDisposableResource looks up @@dispose. Returns `Ok(None)` when V
    /// is null/undefined (spec: no resource is added), `Ok(Some(_))` for a
    /// registerable resource, and a TypeError when V is a non-object primitive
    /// or lacks a callable @@dispose.
    pub(crate) fn create_sync_disposable_resource(
        &mut self,
        value: &JsValue,
    ) -> Result<Option<DisposableResource>, Abrupt> {
        match value {
            JsValue::Undefined | JsValue::Null => Ok(None),
            JsValue::Obj(_) => {
                let key = PropKey::Sym(self.intr.dispose_sym);
                // GetMethod: TypeError if @@dispose is present but not callable.
                match self.get_method(value, &key)? {
                    Some(method) => Ok(Some(DisposableResource::Method {
                        value: value.clone(),
                        method,
                    })),
                    // @@dispose absent/undefined → CreateDisposableResource TypeError.
                    None => Err(self.throw_type_error()),
                }
            }
            // A non-nullish primitive is not an Object → TypeError.
            _ => Err(self.throw_type_error()),
        }
    }

    /// Dispose a single resource (Dispose(V, sync-dispose, method)): `Ok(())`
    /// on a normal return, `Err` carrying the dispose method's abrupt (a Throw
    /// to aggregate, or a Fatal refusal to propagate).
    fn dispose_one(&mut self, resource: &DisposableResource) -> Result<(), Abrupt> {
        match resource {
            DisposableResource::Method { value, method } => {
                self.call_value(method, value.clone(), vec![])?;
            }
            DisposableResource::Adopt { value, on_dispose } => {
                self.call_value(on_dispose, JsValue::Undefined, vec![value.clone()])?;
            }
        }
        Ok(())
    }

    /// DisposeResources(dc, completion): call each registered method in REVERSE
    /// order, folding a dispose throw into `completion` (a SuppressedError when
    /// `completion` is already a throw; otherwise the dispose throw replaces
    /// it). A Fatal (out-of-slice refusal) in either the incoming completion or
    /// a dispose method short-circuits to a refusal.
    pub(crate) fn dispose_resources(
        &mut self,
        resources: Vec<DisposableResource>,
        completion: Compl,
    ) -> Compl {
        let mut completion = completion;
        for resource in resources.into_iter().rev() {
            // Once the completion is an out-of-slice refusal we cannot produce
            // a trace for the rest of disposal — refuse the whole case.
            if matches!(&completion, Err(Abrupt::Fatal(_))) {
                return completion;
            }
            match self.dispose_one(&resource) {
                Ok(()) => {}
                Err(Abrupt::Throw(dispose_err)) => {
                    completion = match completion {
                        Err(Abrupt::Throw(suppressed)) => {
                            // Both the body and this disposal threw: aggregate.
                            let se = self.make_suppressed_error(dispose_err, suppressed)?;
                            Err(Abrupt::Throw(se))
                        }
                        // Any non-throw completion (normal / return / break /
                        // continue) is simply replaced by the dispose throw.
                        _ => Err(Abrupt::Throw(dispose_err)),
                    };
                }
                // A dispose method call cannot surface Break/Continue (the call
                // boundary contains them) and Return is converted at the
                // boundary; a Fatal is an out-of-slice refusal. Either way,
                // refuse rather than risk a wrong trace.
                Err(other) => return Err(other),
            }
        }
        completion
    }

    /// A newly created SuppressedError with non-enumerable `error` / `suppressed`
    /// data properties (CreateNonEnumerableDataPropertyOrThrow), no own message.
    fn make_suppressed_error(&mut self, error: JsValue, suppressed: JsValue) -> ERes {
        let proto = self.intr.suppressed_error_proto;
        let oid = self.make_native_error_with_proto(ErrKind::Error, false, proto)?;
        self.heap.obj_mut(oid).props.insert(
            PropKey::from_str("error"),
            Property::with_attrs(error, true, false, true),
        );
        self.heap.obj_mut(oid).props.insert(
            PropKey::from_str("suppressed"),
            Property::with_attrs(suppressed, true, false, true),
        );
        Ok(JsValue::Obj(oid))
    }

    // -- SuppressedError constructor ----------------------------------------

    /// SuppressedError ( error, suppressed, message ) — [[Call]] and
    /// [[Construct]]. Own keys, in spec order: `message` (only when the
    /// argument is not undefined), then `error`, then `suppressed`.
    pub(crate) fn suppressed_error_construct(
        &mut self,
        args: &[JsValue],
        new_target: Option<&JsValue>,
    ) -> ERes {
        let arg = |i: usize| args.get(i).cloned().unwrap_or(JsValue::Undefined);
        let default_proto = self.intr.suppressed_error_proto;
        let proto = match new_target {
            Some(ntv) => self.get_prototype_from_constructor(ntv, default_proto)?,
            None => default_proto,
        };
        let oid = self.make_native_error_with_proto(ErrKind::Error, false, proto)?;
        if !matches!(arg(2), JsValue::Undefined) {
            let msg = self.to_string_units(&arg(2))?;
            self.heap.obj_mut(oid).props.insert(
                PropKey::from_str("message"),
                Property::with_attrs(JsValue::Str(Rc::new(msg)), true, false, true),
            );
        }
        self.heap.obj_mut(oid).props.insert(
            PropKey::from_str("error"),
            Property::with_attrs(arg(0), true, false, true),
        );
        self.heap.obj_mut(oid).props.insert(
            PropKey::from_str("suppressed"),
            Property::with_attrs(arg(1), true, false, true),
        );
        Ok(JsValue::Obj(oid))
    }

    // -- DisposableStack ----------------------------------------------------

    /// `new DisposableStack()` [[Construct]]: NewTarget required;
    /// OrdinaryCreateFromConstructor with an empty pending DisposeCapability.
    pub(crate) fn disposable_stack_construct(&mut self, new_target: Option<&JsValue>) -> ERes {
        let Some(ntv) = new_target else {
            return Err(self.throw_type_error());
        };
        let proto = self.get_prototype_from_constructor(ntv, self.intr.disposable_stack_proto)?;
        let oid = self.alloc_obj(JsObject::new(ObjKind::Plain, Some(proto)))?;
        self.disposable_stack_state.insert(
            oid,
            DisposableStackData {
                disposed: false,
                resources: Vec::new(),
            },
        );
        Ok(JsValue::Obj(oid))
    }

    /// RequireInternalSlot([[DisposableState]]): a DisposableStack this-brand.
    fn ds_require(&mut self, this: &JsValue) -> Result<ObjId, Abrupt> {
        let JsValue::Obj(oid) = this else {
            return Err(self.throw_type_error());
        };
        if !self.disposable_stack_state.contains_key(oid) {
            return Err(self.throw_type_error());
        }
        Ok(*oid)
    }

    /// `get DisposableStack.prototype.disposed`.
    pub(crate) fn ds_disposed_getter(&mut self, this: &JsValue) -> ERes {
        let oid = self.ds_require(this)?;
        Ok(JsValue::Bool(self.disposable_stack_state[&oid].disposed))
    }

    /// `DisposableStack.prototype.use ( value )`.
    pub(crate) fn ds_use(&mut self, this: &JsValue, value: JsValue) -> ERes {
        let oid = self.ds_require(this)?;
        if self.disposable_stack_state[&oid].disposed {
            return Err(self.throw_native(ErrKind::Reference));
        }
        if let Some(res) = self.create_sync_disposable_resource(&value)? {
            self.disposable_stack_state
                .get_mut(&oid)
                .expect("brand checked")
                .resources
                .push(res);
        }
        Ok(value)
    }

    /// `DisposableStack.prototype.adopt ( value, onDispose )`.
    pub(crate) fn ds_adopt(&mut self, this: &JsValue, value: JsValue, on_dispose: JsValue) -> ERes {
        let oid = self.ds_require(this)?;
        if self.disposable_stack_state[&oid].disposed {
            return Err(self.throw_native(ErrKind::Reference));
        }
        if !matches!(&on_dispose, JsValue::Obj(o) if self.heap.obj(*o).is_callable()) {
            return Err(self.throw_type_error());
        }
        self.disposable_stack_state
            .get_mut(&oid)
            .expect("brand checked")
            .resources
            .push(DisposableResource::Adopt {
                value: value.clone(),
                on_dispose,
            });
        Ok(value)
    }

    /// `DisposableStack.prototype.defer ( onDispose )`.
    pub(crate) fn ds_defer(&mut self, this: &JsValue, on_dispose: JsValue) -> ERes {
        let oid = self.ds_require(this)?;
        if self.disposable_stack_state[&oid].disposed {
            return Err(self.throw_native(ErrKind::Reference));
        }
        if !matches!(&on_dispose, JsValue::Obj(o) if self.heap.obj(*o).is_callable()) {
            return Err(self.throw_type_error());
        }
        self.disposable_stack_state
            .get_mut(&oid)
            .expect("brand checked")
            .resources
            .push(DisposableResource::Method {
                value: JsValue::Undefined,
                method: on_dispose,
            });
        Ok(JsValue::Undefined)
    }

    /// `DisposableStack.prototype.move ( )`: transfer the resource stack to a
    /// fresh DisposableStack and mark the receiver disposed.
    pub(crate) fn ds_move(&mut self, this: &JsValue) -> ERes {
        let oid = self.ds_require(this)?;
        if self.disposable_stack_state[&oid].disposed {
            return Err(self.throw_native(ErrKind::Reference));
        }
        let proto = self.intr.disposable_stack_proto;
        let new_oid = self.alloc_obj(JsObject::new(ObjKind::Plain, Some(proto)))?;
        let resources = std::mem::take(
            &mut self
                .disposable_stack_state
                .get_mut(&oid)
                .expect("brand checked")
                .resources,
        );
        self.disposable_stack_state.insert(
            new_oid,
            DisposableStackData {
                disposed: false,
                resources,
            },
        );
        self.disposable_stack_state
            .get_mut(&oid)
            .expect("brand checked")
            .disposed = true;
        Ok(JsValue::Obj(new_oid))
    }

    /// `DisposableStack.prototype.dispose ( )` (also @@dispose): idempotent;
    /// runs DisposeResources over the captured stack.
    pub(crate) fn ds_dispose(&mut self, this: &JsValue) -> ERes {
        let oid = self.ds_require(this)?;
        if self.disposable_stack_state[&oid].disposed {
            return Ok(JsValue::Undefined);
        }
        let entry = self
            .disposable_stack_state
            .get_mut(&oid)
            .expect("brand checked");
        entry.disposed = true;
        let resources = std::mem::take(&mut entry.resources);
        self.dispose_resources(resources, Ok(Some(JsValue::Undefined)))?;
        Ok(JsValue::Undefined)
    }
}
