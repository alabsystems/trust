// Class semantics, written from the spec: ClassDefinitionEvaluation (15.7.14)
// with method/accessor [[HomeObject]] wiring, exact member attributes, public
// instance/static fields (init order, per-instance evaluation, anonymous-
// value naming), class-constructor [[Construct]] (base and derived,
// OrdinaryCreateFromConstructor from the live new.target), super() with the
// spec's argument-evaluation-before-IsConstructor order and the this-TDZ
// cell, and super.x property references (receiver-aware [[Set]]).
//
// Heritage support is deliberately bounded: `null`, user functions, class
// constructors, and the Object/Error-family intrinsics (whose [[Construct]]
// honors new.target here); subclassing other intrinsics (Array's exotic
// instances, Function's eval surface, wrapper ctors) refuses.
//
// Author: Andrew Yates
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

use crate::ast::{ClassKey, ClassLit, ClassMember, Expr, MethodKind};
use crate::interp::{Abrupt, Ctx, CtorFrame, ERes, Interp, MAX_CALL_DEPTH};
use crate::value::{
    units_from_str, Builtin, ClassCtorRec, FieldKey, FieldRec, FnImpl, NativeErrorKind, ObjId,
    ObjKind, Object, PrivElemKind, PrivName, PrivateElement, Prop, PropDesc, PropVal, Units, Value,
};
use std::rc::Rc;

/// Add a private method/accessor element to a list, merging a getter/setter
/// pair (same PrivateName) into one accessor element.
fn merge_private_method(list: &mut Vec<PrivateElement>, key: PrivName, mk: MethodKind, fnobj: ObjId) {
    match mk {
        MethodKind::Normal => list.push(PrivateElement {
            key,
            kind: PrivElemKind::Method(fnobj),
        }),
        MethodKind::Get | MethodKind::Set => {
            if let Some(e) = list.iter_mut().find(|e| e.key == key) {
                if let PrivElemKind::Accessor { get, set } = &mut e.kind {
                    if mk == MethodKind::Get {
                        *get = Some(fnobj);
                    } else {
                        *set = Some(fnobj);
                    }
                }
            } else {
                let (get, set) = if mk == MethodKind::Get {
                    (Some(fnobj), None)
                } else {
                    (None, Some(fnobj))
                };
                list.push(PrivateElement {
                    key,
                    kind: PrivElemKind::Accessor { get, set },
                });
            }
        }
    }
}

impl Interp {
    /// IsConstructor (7.2.4) over the modeled callables.
    pub(crate) fn is_constructor(&self, fid: ObjId) -> bool {
        match &self.obj(fid).kind {
            // MethodDefinition functions, generator functions and async
            // functions have no [[Construct]] (MakeConstructor is not called on
            // them).
            ObjKind::Function(FnImpl::User { lit, .. }) => {
                !lit.is_method && !lit.is_generator && !lit.is_async
            }
            ObjKind::Function(FnImpl::ClassCtor(_)) => true,
            ObjKind::Function(FnImpl::Bound { target, .. }) => self.is_constructor(*target),
            // A proxy has [[Construct]] iff its target had one at creation.
            ObjKind::Proxy { constructor, .. } => *constructor,
            ObjKind::Function(FnImpl::Builtin(b)) => matches!(
                b,
                Builtin::ObjectCtor
                    | Builtin::ArrayCtor
                    | Builtin::FunctionCtor
                    | Builtin::StringFn
                    | Builtin::NumberFn
                    | Builtin::BooleanFn
                    | Builtin::ErrorCtor(_)
                    // %Date% (subclassable: super() creates a [[DateValue]]
                    // instance from new.target) and %Symbol% (subclassable as
                    // an `extends` value, but super() throws TypeError since
                    // the Symbol constructor rejects a non-undefined
                    // NewTarget).
                    | Builtin::DateCtor
                    | Builtin::SymbolFn
                    // %BigInt% implements [[Construct]] (IsConstructor(BigInt)
                    // is true — it may head an `extends` clause), even though a
                    // `new BigInt()` / super() call always throws TypeError.
                    | Builtin::BigIntFn
                    // %RegExp% (subclassable: super() creates a RegExp instance
                    // parented on new.target's `.prototype`).
                    | Builtin::RegExpCtor
                    // %GeneratorFunction% IS a constructor (it may head an
                    // `extends` clause); its exotic dynamic-source instance
                    // creation is out of slice, so the heritage lowering below
                    // routes it to a sound NoCoverage rather than constructing.
                    | Builtin::GeneratorFunctionCtor
                    // %AsyncFunction% is a constructor; its exotic dynamic
                    // construction is out of slice, so the heritage lowering
                    // routes it to a sound NoCoverage rather than constructing.
                    | Builtin::AsyncFunctionCtor
                    // %Promise% is a constructor and subclassable; the exotic
                    // subclass construction (custom @@species / NewTarget) is
                    // out of slice, so the heritage lowering routes it to a
                    // sound NoCoverage rather than a wrong TypeError.
                    | Builtin::PromiseCtor
                    // %ArrayBuffer% / %DataView% / %TypedArray% + the concrete
                    // typed-array constructors are all subclassable.
                    | Builtin::ArrayBufferCtor
                    | Builtin::DataViewCtor
                    | Builtin::TypedArrayAbstractCtor
                    | Builtin::TypedArrayCtor(_)
                    // %Map% / %Set% / %WeakMap% / %WeakSet% are subclassable:
                    // super() creates the collection instance parented on
                    // new.target's `.prototype` (24.1.1/24.2.1/24.3.1/24.4.1).
                    | Builtin::MapCtor
                    | Builtin::SetCtor
                    | Builtin::WeakMapCtor
                    | Builtin::WeakSetCtor
            ),
            _ => false,
        }
    }

    /// OrdinaryCreateFromConstructor's prototype lookup: Get(newTarget,
    /// "prototype"), falling back to the intrinsic default when non-object.
    pub(crate) fn proto_from_new_target(
        &mut self,
        nt: ObjId,
        default: ObjId,
    ) -> Result<ObjId, Abrupt> {
        let v = self.get_from_object(nt, &units_from_str("prototype"))?;
        match v {
            Value::Obj(p) => Ok(p),
            // GetPrototypeFromConstructor step 4: a non-object `prototype`
            // falls back to the intrinsic default — but only after
            // GetFunctionRealm(constructor), which throws if `nt` is a revoked
            // proxy (e.g. a `get` trap that revokes itself during the lookup).
            _ => {
                self.get_function_realm_check(nt)?;
                Ok(default)
            }
        }
    }

    // -- ClassDefinitionEvaluation ------------------------------------------

    #[allow(clippy::too_many_lines)]
    pub(crate) fn eval_class(&mut self, cl: &Rc<ClassLit>, ctx: &Ctx) -> ERes {
        // The class scope, carrying the inner immutable self-binding (TDZ
        // during heritage/keys evaluation). Class code is strict.
        let class_env = self.alloc_env(Some(ctx.env));
        if let Some(n) = &cl.name {
            self.envs[class_env.0 as usize].bindings.insert(
                n.clone(),
                crate::value::Binding {
                    value: Value::Undefined,
                    mutable: false,
                    initialized: false,
                    fn_name_immutable: false,
                },
            );
        }
        // The class PrivateEnvironment (9.2): one fresh PrivateName per
        // declared `#name`, parented on the enclosing class's private env
        // (nested-class resolution). Active for heritage, computed keys,
        // methods, field initializers, and the constructor body.
        let class_priv_env = {
            let mut names = std::collections::HashMap::new();
            for n in &cl.private_names {
                names.insert(n.clone(), self.alloc_priv_name());
            }
            std::rc::Rc::new(crate::interp::PrivEnvFrame {
                parent: ctx.priv_env.clone(),
                names,
            })
        };
        let class_ctx = Ctx {
            env: class_env,
            strict: true,
            priv_env: Some(Rc::clone(&class_priv_env)),
            ..ctx.clone()
        };

        // Heritage: (prototype parent, constructor parent).
        let (proto_parent, ctor_parent): (Option<ObjId>, ObjId) = match &cl.heritage {
            None => (Some(self.intr.object_proto), self.intr.function_proto),
            Some(h) => {
                let v = self.eval_expr(h, &class_ctx)?;
                match v {
                    Value::Null => (None, self.intr.function_proto),
                    Value::Obj(hid) => {
                        if !self.is_constructor(hid) {
                            // Callable-but-not-constructor and plain objects
                            // are the same pinned TypeError.
                            return Err(self.throw_native(NativeErrorKind::TypeError));
                        }
                        match &self.obj(hid).kind {
                            ObjKind::Function(FnImpl::User { .. })
                            | ObjKind::Function(FnImpl::ClassCtor(_)) => {}
                            // %Object% / %Error% subclass via
                            // OrdinaryCreateFromConstructor; %Date% super()
                            // creates a [[DateValue]] instance from new.target;
                            // %Symbol% is a valid `extends` value whose super()
                            // throws TypeError (Symbol rejects a NewTarget).
                            ObjKind::Function(FnImpl::Builtin(
                                Builtin::ErrorCtor(_)
                                | Builtin::ObjectCtor
                                | Builtin::DateCtor
                                | Builtin::SymbolFn
                                // %RegExp% super() creates a RegExp instance
                                // ([[RegExpMatcher]]) from new.target.
                                | Builtin::RegExpCtor
                                // %Map%/%Set%/%WeakMap%/%WeakSet% super() creates
                                // the collection instance from new.target.
                                | Builtin::MapCtor
                                | Builtin::SetCtor
                                | Builtin::WeakMapCtor
                                | Builtin::WeakSetCtor,
                            )) => {}
                            _ => {
                                return Err(Abrupt::Fatal(
                                    "class heritage: subclassing this intrinsic constructor (exotic instance creation out of slice)"
                                        .to_string(),
                                ))
                            }
                        }
                        let p = self.get_from_object(hid, &units_from_str("prototype"))?;
                        match p {
                            Value::Obj(pp) => (Some(pp), hid),
                            Value::Null => (None, hid),
                            _ => return Err(self.throw_native(NativeErrorKind::TypeError)),
                        }
                    }
                    _ => return Err(self.throw_native(NativeErrorKind::TypeError)),
                }
            }
        };
        let derived = cl.heritage.is_some();

        // The prototype object and the constructor function object.
        let proto = self.alloc(Object::new(ObjKind::Plain, proto_parent));
        let mut fields: Vec<FieldRec> = Vec::new();
        let rec = Rc::new(ClassCtorRec {
            lit: cl.ctor.clone(),
            env: class_env,
            home: proto,
            derived,
            fields: Rc::new(Vec::new()), // replaced below (two-phase: keys first)
            priv_methods: Rc::new(Vec::new()),
            priv_env: Some(Rc::clone(&class_priv_env)),
        });
        // NOTE: fields' keys are evaluated interleaved with method
        // definitions below; the rec is rebuilt afterwards with the final
        // list, then the F object's payload updated.
        let f = self.alloc(Object::new(
            ObjKind::Function(FnImpl::ClassCtor(Rc::clone(&rec))),
            Some(ctor_parent),
        ));
        #[allow(clippy::cast_precision_loss)]
        let ctor_len = cl.ctor.as_ref().map_or(0.0, |c| c.params.len() as f64);
        let class_name = cl
            .name
            .clone()
            .or_else(|| cl.inferred_name.borrow().clone())
            .unwrap_or_default();
        self.obj_mut(f).props.insert(
            units_from_str("length"),
            Prop::with_attrs(Value::Num(ctor_len), false, false, true),
        );
        self.obj_mut(f).props.insert(
            units_from_str("name"),
            Prop::with_attrs(Value::str_from(&class_name), false, false, true),
        );
        self.obj_mut(f).props.insert(
            units_from_str("prototype"),
            Prop::with_attrs(Value::Obj(proto), false, false, false),
        );
        self.obj_mut(proto).props.insert(
            units_from_str("constructor"),
            Prop::with_attrs(Value::Obj(f), true, false, true),
        );
        // The constructor body resolves `#name` through the class private env.
        self.fn_priv_env.insert(f, Rc::clone(&class_priv_env));

        // Phase 1 (source order): evaluate keys, define methods, collect
        // field records. Static field INITIALIZERS run in phase 2, after the
        // inner class binding initializes (spec 15.7.14 step order). Instance
        // private methods/accessors are collected to install per instance.
        let mut static_fields: Vec<FieldRec> = Vec::new();
        let mut priv_methods: Vec<PrivateElement> = Vec::new();
        for m in &cl.members {
            match m {
                ClassMember::Method {
                    stat,
                    key: ClassKey::Private(name),
                    mk,
                    lit,
                } => {
                    let pn = *class_priv_env
                        .names
                        .get(name)
                        .expect("declared private name");
                    let target_home = if *stat { f } else { proto };
                    let fnobj = self.create_method(
                        lit,
                        class_env,
                        target_home,
                        Some(Rc::clone(&class_priv_env)),
                    );
                    let prefix = match mk {
                        MethodKind::Normal => "",
                        MethodKind::Get => "get ",
                        MethodKind::Set => "set ",
                    };
                    let mut name_units = units_from_str(prefix);
                    name_units.push(u16::from(b'#'));
                    name_units.extend_from_slice(&units_from_str(name));
                    self.set_fn_name(fnobj, &name_units);
                    if *stat {
                        // Static private method/accessor: brand F now.
                        let elems = &mut self.obj_mut(f).priv_elems;
                        merge_private_method(elems, pn, *mk, fnobj);
                    } else {
                        merge_private_method(&mut priv_methods, pn, *mk, fnobj);
                    }
                }
                ClassMember::Method { stat, key, mk, lit } => {
                    let key_u = self.eval_class_key(key, &class_ctx)?;
                    let target = if *stat { f } else { proto };
                    let fnobj =
                        self.create_method(lit, class_env, target, Some(Rc::clone(&class_priv_env)));
                    let prefix = match mk {
                        MethodKind::Normal => "",
                        MethodKind::Get => "get ",
                        MethodKind::Set => "set ",
                    };
                    let mut name_units = units_from_str(prefix);
                    name_units.extend_from_slice(&key_u);
                    self.set_fn_name(fnobj, &name_units);
                    let desc = match mk {
                        MethodKind::Normal => PropDesc {
                            value: Some(Value::Obj(fnobj)),
                            writable: Some(true),
                            enumerable: Some(false),
                            configurable: Some(true),
                            ..PropDesc::default()
                        },
                        MethodKind::Get => PropDesc {
                            get: Some(Some(fnobj)),
                            enumerable: Some(false),
                            configurable: Some(true),
                            ..PropDesc::default()
                        },
                        MethodKind::Set => PropDesc {
                            set: Some(Some(fnobj)),
                            enumerable: Some(false),
                            configurable: Some(true),
                            ..PropDesc::default()
                        },
                    };
                    // DefinePropertyOrThrow (a static computed "prototype"
                    // hits the non-configurable slot: TypeError).
                    let ok = self.define_own_property(target, &key_u, &desc)?;
                    if !ok {
                        return Err(self.throw_native(NativeErrorKind::TypeError));
                    }
                }
                ClassMember::Field {
                    stat,
                    key: ClassKey::Private(name),
                    init,
                } => {
                    let pn = *class_priv_env
                        .names
                        .get(name)
                        .expect("declared private name");
                    let mut ident = units_from_str("#");
                    ident.extend_from_slice(&units_from_str(name));
                    let rec = FieldRec {
                        key: FieldKey::Private { name: pn, ident },
                        init: init.clone(),
                    };
                    if *stat {
                        static_fields.push(rec);
                    } else {
                        fields.push(rec);
                    }
                }
                ClassMember::Field { stat, key, init } => {
                    let key_u = self.eval_class_key(key, &class_ctx)?;
                    let rec = FieldRec {
                        key: FieldKey::Public(key_u),
                        init: init.clone(),
                    };
                    if *stat {
                        static_fields.push(rec);
                    } else {
                        fields.push(rec);
                    }
                }
            }
        }

        // Attach the final field + private-method lists to the constructor
        // payload (static initializers below may construct instances).
        let final_rec = Rc::new(ClassCtorRec {
            lit: cl.ctor.clone(),
            env: class_env,
            home: proto,
            derived,
            fields: Rc::new(fields),
            priv_methods: Rc::new(priv_methods),
            priv_env: Some(Rc::clone(&class_priv_env)),
        });
        self.obj_mut(f).kind = ObjKind::Function(FnImpl::ClassCtor(final_rec));

        // The inner class binding initializes BEFORE static initializers run.
        if let Some(n) = &cl.name {
            let mut cur = Some(class_env);
            while let Some(e) = cur {
                if let Some(b) = self.envs[e.0 as usize].bindings.get_mut(n) {
                    b.value = Value::Obj(f);
                    b.initialized = true;
                    break;
                }
                cur = self.envs[e.0 as usize].parent;
            }
        }

        // Phase 2: static field initializers (this = F, [[HomeObject]] = F).
        for fr in &static_fields {
            let ident = match &fr.key {
                FieldKey::Public(u) => u.clone(),
                FieldKey::Private { ident, .. } => ident.clone(),
            };
            let v = self.eval_field_init(
                fr.init.as_ref(),
                &ident,
                class_env,
                f,
                f,
                Some(Rc::clone(&class_priv_env)),
            )?;
            match &fr.key {
                FieldKey::Public(key_u) => {
                    let desc = PropDesc {
                        value: Some(v),
                        writable: Some(true),
                        enumerable: Some(true),
                        configurable: Some(true),
                        ..PropDesc::default()
                    };
                    let ok = self.define_own_property(f, key_u, &desc)?;
                    if !ok {
                        return Err(self.throw_native(NativeErrorKind::TypeError));
                    }
                }
                FieldKey::Private { name, .. } => {
                    self.private_field_add(f, *name, v)?;
                }
            }
        }
        Ok(Value::Obj(f))
    }

    fn eval_class_key(&mut self, key: &ClassKey, ctx: &Ctx) -> Result<Units, Abrupt> {
        match key {
            ClassKey::Fixed(u) => Ok(u.clone()),
            ClassKey::Computed(e) => {
                let v = self.eval_expr(e, ctx)?;
                // Symbol-keyed class members (`class { [Symbol.iterator]() {} }`)
                // are out of the current slice — refuse rather than lose the
                // symbol key through a string coercion.
                match self.to_property_key(&v)? {
                    crate::value::PropertyKey::Str(u) => Ok(u),
                    crate::value::PropertyKey::Sym(_) => Err(Abrupt::Fatal(
                        "symbol-keyed class member (out of slice)".to_string(),
                    )),
                }
            }
            ClassKey::Private(_) => Err(Abrupt::Fatal(
                "private class key routed through eval_class_key (bug)".to_string(),
            )),
        }
    }

    /// Overwrite a function object's `name` own property value in place
    /// (SetFunctionName at definition time; attributes unchanged).
    pub(crate) fn set_fn_name(&mut self, fid: ObjId, name: &[u16]) {
        if let Some(p) = self.obj_mut(fid).props.get_mut(&units_from_str("name")) {
            if let PropVal::Data { value, .. } = &mut p.val {
                *value = Value::Str(Rc::new(name.to_vec()));
            }
        }
    }

    /// Evaluate one field initializer (this = `instance`, [[HomeObject]] =
    /// `home`, PrivateEnvironment = the class's), with NamedEvaluation for
    /// anonymous function/class values. `name` is the NamedEvaluation key (a
    /// public property key, or the `#ident` for a private field).
    #[allow(clippy::too_many_arguments)]
    fn eval_field_init(
        &mut self,
        init: Option<&Rc<Expr>>,
        name: &Units,
        class_env: crate::value::EnvId,
        instance: ObjId,
        home: ObjId,
        priv_env: Option<std::rc::Rc<crate::interp::PrivEnvFrame>>,
    ) -> ERes {
        let Some(init) = init else {
            return Ok(Value::Undefined);
        };
        let ictx = Ctx {
            env: class_env,
            this_val: Value::Obj(instance),
            strict: true,
            home_object: Some(home),
            ctor_frame: None,
            priv_env,
            in_formal_params: false,
        };
        let v = self.eval_expr(init, &ictx)?;
        // NamedEvaluation: an anonymous function/arrow/class initializer value
        // gets the field key as its name.
        let anonymous = match init.as_ref() {
            Expr::Function(lit) | Expr::Arrow(lit) => lit.name.is_none(),
            Expr::Class(cl) => cl.name.is_none() && cl.inferred_name.borrow().is_none(),
            _ => false,
        };
        if anonymous {
            if let Value::Obj(fo) = &v {
                self.set_fn_name(*fo, name);
            }
        }
        Ok(v)
    }

    /// InitializeInstanceElements (15.7.15): first brand the instance with the
    /// class's private methods/accessors, THEN run the field initializers
    /// (public and private) in declaration order.
    pub(crate) fn init_instance_fields(
        &mut self,
        instance: &Value,
        rec: &ClassCtorRec,
    ) -> Result<(), Abrupt> {
        let Value::Obj(oid) = instance else {
            return Ok(()); // construct always yields objects in this model
        };
        let oid = *oid;
        for m in rec.priv_methods.iter() {
            self.private_method_add(oid, m.clone())?;
        }
        let fields = Rc::clone(&rec.fields);
        for fr in fields.iter() {
            let ident = match &fr.key {
                FieldKey::Public(u) => u.clone(),
                FieldKey::Private { ident, .. } => ident.clone(),
            };
            let v = self.eval_field_init(
                fr.init.as_ref(),
                &ident,
                rec.env,
                oid,
                rec.home,
                rec.priv_env.clone(),
            )?;
            match &fr.key {
                FieldKey::Public(key_u) => {
                    let desc = PropDesc {
                        value: Some(v),
                        writable: Some(true),
                        enumerable: Some(true),
                        configurable: Some(true),
                        ..PropDesc::default()
                    };
                    let ok = self.define_own_property(oid, key_u, &desc)?;
                    if !ok {
                        return Err(self.throw_native(NativeErrorKind::TypeError));
                    }
                }
                FieldKey::Private { name, .. } => {
                    self.private_field_add(oid, *name, v)?;
                }
            }
        }
        Ok(())
    }

    // -- [[Construct]] for class constructors --------------------------------

    #[allow(clippy::too_many_lines)]
    pub(crate) fn construct_class(
        &mut self,
        fid: ObjId,
        rec: &Rc<ClassCtorRec>,
        args: Vec<Value>,
        new_target: ObjId,
    ) -> ERes {
        self.call_depth += 1;
        if self.call_depth > MAX_CALL_DEPTH {
            self.call_depth -= 1;
            return Err(Abrupt::Fatal("call depth cap exceeded".to_string()));
        }
        let r = self.construct_class_inner(fid, rec, args, new_target);
        self.call_depth -= 1;
        r
    }

    fn construct_class_inner(
        &mut self,
        fid: ObjId,
        rec: &Rc<ClassCtorRec>,
        args: Vec<Value>,
        new_target: ObjId,
    ) -> ERes {
        if !rec.derived {
            // Base: OrdinaryCreateFromConstructor(newTarget, %Object.prototype%).
            let proto = self.proto_from_new_target(new_target, self.intr.object_proto)?;
            let obj = self.alloc(Object::new(ObjKind::Plain, Some(proto)));
            let this = Value::Obj(obj);
            self.init_instance_fields(&this, rec)?;
            let Some(lit) = &rec.lit else {
                return Ok(this); // default base constructor: empty body
            };
            let lit = Rc::clone(lit);
            let body_ctx = self.prepare_fn_ctx_full(
                &lit,
                rec.env,
                fid,
                this.clone(),
                &args,
                Some(rec.home),
                None,
            )?;
            let mut v: Option<Value> = None;
            match self.eval_stmt_list(&lit.body, &body_ctx, &mut v) {
                Ok(()) => Ok(this),
                Err(Abrupt::Return(rv)) => Ok(match rv {
                    Value::Obj(_) => rv,
                    _ => this, // base ctors ignore primitive returns
                }),
                Err(other) => Err(other),
            }
        } else {
            let frame = Rc::new(CtorFrame {
                cell: std::cell::RefCell::new(None),
                new_target,
                active: fid,
            });
            let Some(lit) = &rec.lit else {
                // Default derived constructor: constructor(...args) {
                // super(...args); } — performed directly.
                return self.perform_super_call(&frame, args);
            };
            let lit = Rc::clone(lit);
            let body_ctx = self.prepare_fn_ctx_full(
                &lit,
                rec.env,
                fid,
                Value::Undefined,
                &args,
                Some(rec.home),
                Some(Rc::clone(&frame)),
            )?;
            let mut v: Option<Value> = None;
            let completion = self.eval_stmt_list(&lit.body, &body_ctx, &mut v);
            let this_of = |frame: &CtorFrame| frame.cell.borrow().clone();
            match completion {
                Ok(()) => match this_of(&frame) {
                    Some(t) => Ok(t),
                    None => Err(self.throw_native(NativeErrorKind::ReferenceError)),
                },
                Err(Abrupt::Return(rv)) => match rv {
                    Value::Obj(_) => Ok(rv),
                    Value::Undefined => match this_of(&frame) {
                        Some(t) => Ok(t),
                        None => Err(self.throw_native(NativeErrorKind::ReferenceError)),
                    },
                    // Derived constructors reject primitive returns.
                    _ => Err(self.throw_native(NativeErrorKind::TypeError)),
                },
                Err(other) => Err(other),
            }
        }
    }

    /// The super(...) steps shared by explicit calls and the default derived
    /// constructor: parent from the active constructor's [[GetPrototypeOf]],
    /// arguments BEFORE the IsConstructor check, construct with the original
    /// new.target, bind the this cell (ReferenceError when already bound),
    /// then the active class's instance fields.
    pub(crate) fn perform_super_call(
        &mut self,
        frame: &Rc<CtorFrame>,
        args: Vec<Value>,
    ) -> ERes {
        let parent = self.obj(frame.active).proto;
        let parent_ok = parent.is_some_and(|p| self.is_constructor(p));
        if !parent_ok {
            return Err(self.throw_native(NativeErrorKind::TypeError));
        }
        let parent = parent.expect("checked");
        let result = self.construct_with_target(parent, args, frame.new_target)?;
        {
            let mut cell = frame.cell.borrow_mut();
            if cell.is_some() {
                drop(cell);
                return Err(self.throw_native(NativeErrorKind::ReferenceError));
            }
            *cell = Some(result.clone());
        }
        let rec = match &self.obj(frame.active).kind {
            ObjKind::Function(FnImpl::ClassCtor(rec)) => Rc::clone(rec),
            _ => {
                return Err(Abrupt::Fatal(
                    "super() with a non-class active function".to_string(),
                ))
            }
        };
        self.init_instance_fields(&result, &rec)?;
        Ok(result)
    }
}
