// ClassDefinitionEvaluation (15.7.14) and class-constructor [[Construct]]:
// base + derived classes, methods/accessors (with [[HomeObject]]), static
// members, public + PRIVATE fields/methods/accessors (instance + static), the
// per-class PrivateEnvironment, default constructors, and the super
// machinery's class half. Private names live in a per-object side table
// (crate::private), invisible to enumeration/reflection/projection. OUT OF
// SLICE (refuses): static initialization blocks, generator/async methods,
// decorators.
//
// Author: Andrew Yates
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

use crate::interp::{hoist, Abrupt, Ctx, ERes, Interp};
use crate::private::{PrivElem, PrivEnvId, PrivName};
use crate::props::PartialDesc;
use std::rc::Rc;
use trust_js_parse::ast::{Class, ClassElement, Expr, Func, MethodKind, PropKey as AstKey, Stmt};
use trust_js_value::{
    Binding, EnvId, FnFlavor, JsObject, JsValue, ObjId, ObjKind, PropKey, Property,
};

/// Per-class-constructor metadata, keyed by the constructor's ObjId.
#[derive(Debug)]
pub(crate) struct ClassInfo {
    pub default_ctor: bool,
    /// Instance fields (public + private) in source order.
    pub instance_elems: Vec<InstanceElem>,
    /// Instance private methods/accessors, added to each instance's
    /// [[PrivateElements]] before its fields (InitializeInstanceElements).
    pub instance_priv_methods: Vec<(PrivName, PrivElem)>,
}

/// One instance field definition: a public data field or a private field.
#[derive(Debug)]
pub(crate) enum InstanceElem {
    Public(FieldDef),
    Private(PrivFieldDef),
}

/// One STATIC class element that runs during ClassDefinitionEvaluation, in
/// source order: a static field (public or private) or a static initialization
/// block. Static methods are defined earlier (during the element loop), so they
/// are not represented here.
enum StaticItem {
    Field(InstanceElem),
    /// A `static { ... }` block body (ClassStaticBlockDefinitionEvaluation).
    Block(Rc<Vec<Stmt>>),
}

/// One public field definition (key precomputed at class-definition time).
#[derive(Debug, Clone)]
pub(crate) struct FieldDef {
    pub key: PropKey,
    /// NamedEvaluation name for anonymous initializers.
    pub name: String,
    /// The inferred name is lossy (lone surrogates): NamedEvaluation refuses.
    pub lossy: bool,
    pub init: Option<Rc<Expr>>,
    /// The class scope the initializer closes over.
    pub env: EnvId,
    /// [[HomeObject]] of the initializer (proto for instance, F for static).
    pub home: ObjId,
}

/// One private field definition.
#[derive(Debug, Clone)]
pub(crate) struct PrivFieldDef {
    pub name: PrivName,
    /// The NamedEvaluation name ("#x") for anonymous initializers.
    pub display: String,
    pub init: Option<Rc<Expr>>,
    pub env: EnvId,
    pub home: ObjId,
}

impl Interp {
    /// ClassDefinitionEvaluation. `name_override` implements NamedEvaluation
    /// for anonymous class expressions.
    #[allow(clippy::too_many_lines)]
    pub(crate) fn eval_class(
        &mut self,
        c: &Class,
        ctx: &Ctx,
        name_override: Option<&str>,
    ) -> ERes {
        // Refusal scan: out-of-slice class surface refuses before any
        // observable side effect. Private (non-generator, non-async) methods,
        // accessors, fields, AND static initialization blocks ARE in slice.
        for el in &c.elements {
            match el {
                ClassElement::StaticBlock(_) => {}
                ClassElement::Method { .. } => {
                    // Plain async methods (`async m(){}`), generator methods
                    // (`*m(){}`), and async generator methods (`async *m(){}`)
                    // all route through create_function's object-graph wiring.
                }
                ClassElement::Field { .. } => {}
            }
        }

        // Class scope with the (immutable) inner class binding in TDZ.
        let class_env = self.alloc_env(Some(ctx.env));
        if let Some(n) = &c.name {
            self.heap
                .env_mut(class_env)
                .bindings
                .insert(n.clone(), Binding::tdz(false));
        }
        let cctx = Ctx {
            env: class_env,
            strict: true,
        };

        // Heritage: protoParent + constructorParent. Evaluated with the
        // OUTER PrivateEnvironment (class_env's own is not yet attached), so a
        // heritage private reference resolves against the enclosing class.
        let (proto_parent, ctor_parent, derived) = match &c.heritage {
            None => (Some(self.intr.object_proto), self.intr.function_proto, false),
            Some(h) => {
                let sv = self.eval_expr(h, &cctx)?;
                match &sv {
                    JsValue::Null => (None, self.intr.function_proto, true),
                    _ if self.is_constructor(&sv) => {
                        let JsValue::Obj(sc) = sv else {
                            unreachable!("constructors are objects")
                        };
                        let pp = self.get_prop(&JsValue::Obj(sc), &PropKey::from_str("prototype"))?;
                        match pp {
                            JsValue::Obj(p) => (Some(p), sc, true),
                            JsValue::Null => (None, sc, true),
                            _ => return Err(self.throw_type_error()),
                        }
                    }
                    _ => return Err(self.throw_type_error()),
                }
            }
        };

        // NewPrivateEnvironment(outer): populate all private names first
        // (forward references within a class body are legal), then make it the
        // class scope's active PrivateEnvironment.
        let outer_penv = self.nearest_priv_env(ctx.env);
        let penv: PrivEnvId = self.new_priv_env(outer_penv);
        for el in &c.elements {
            let key = match el {
                ClassElement::Method { key, .. } | ClassElement::Field { key, .. } => key,
                ClassElement::StaticBlock(_) => continue,
            };
            if let AstKey::Private(name) = key {
                self.priv_env_bind(penv, name);
            }
        }
        self.priv_env_of.insert(class_env, penv);

        let proto = self.alloc_obj(JsObject::new(ObjKind::Plain, proto_parent))?;

        // The constructor function object.
        let class_name: String = c
            .name
            .clone()
            .or_else(|| name_override.map(str::to_string))
            .unwrap_or_default();
        let ctor_el = c.elements.iter().find_map(|el| match el {
            ClassElement::Method {
                kind: MethodKind::Constructor,
                func,
                ..
            } => Some(func),
            _ => None,
        });
        let default_ctor = ctor_el.is_none();
        let default_func: Func;
        let ctor_func: &Func = match ctor_el {
            Some(f) => f,
            None => {
                default_func = Func {
                    name: None,
                    params: Vec::new(),
                    body: Vec::new(),
                    expr_body: None,
                    is_async: false,
                    is_gen: false,
                    is_arrow: false,
                    strict: true,
                };
                &default_func
            }
        };
        let fobj = self.create_function(
            ctor_func,
            class_env,
            true,
            Some(&class_name),
            FnFlavor::ClassCtor { derived },
            Some(proto),
        )?;
        // F.[[Prototype]] = constructorParent; MakeClassConstructor +
        // MakeConstructor(F, false, proto).
        self.heap.obj_mut(fobj).proto = Some(ctor_parent);
        self.heap.obj_mut(fobj).props.insert(
            PropKey::from_str("prototype"),
            Property::frozen(JsValue::Obj(proto)),
        );
        self.heap.obj_mut(proto).props.insert(
            PropKey::from_str("constructor"),
            Property::with_attrs(JsValue::Obj(fobj), true, false, true),
        );

        // Elements, in order.
        let mut instance_elems: Vec<InstanceElem> = Vec::new();
        let mut static_elems: Vec<StaticItem> = Vec::new();
        let mut instance_priv_methods: Vec<(PrivName, PrivElem)> = Vec::new();
        let mut static_priv_methods: Vec<(PrivName, PrivElem)> = Vec::new();
        for el in &c.elements {
            match el {
                ClassElement::Method { kind: MethodKind::Constructor, .. } => {}
                ClassElement::StaticBlock(body) => {
                    static_elems.push(StaticItem::Block(Rc::new(body.clone())));
                }
                ClassElement::Method {
                    is_static,
                    kind,
                    key: AstKey::Private(pname),
                    func,
                } => {
                    let target = if *is_static { fobj } else { proto };
                    let id = self.priv_env_bind(penv, pname);
                    let (fname, flavor) = match kind {
                        MethodKind::Method => (format!("#{pname}"), FnFlavor::Method),
                        MethodKind::Get => (format!("get #{pname}"), FnFlavor::Getter),
                        MethodKind::Set => (format!("set #{pname}"), FnFlavor::Setter),
                        MethodKind::Constructor => unreachable!("filtered above"),
                    };
                    let fo = self.create_function(
                        func,
                        class_env,
                        true,
                        Some(&fname),
                        flavor,
                        Some(target),
                    )?;
                    let list = if *is_static {
                        &mut static_priv_methods
                    } else {
                        &mut instance_priv_methods
                    };
                    add_priv_method(list, id, kind, fo);
                }
                ClassElement::Method {
                    is_static,
                    kind,
                    key,
                    func,
                } => {
                    let (k, name, lossy) = self.eval_prop_key(key, &cctx)?;
                    if lossy {
                        return Err(Abrupt::Fatal(
                            "method-name inference over a lone-surrogate key (out of slice)"
                                .to_string(),
                        ));
                    }
                    let target = if *is_static { fobj } else { proto };
                    match kind {
                        MethodKind::Method => {
                            let fo = self.create_function(
                                func,
                                class_env,
                                true,
                                Some(&name),
                                FnFlavor::Method,
                                Some(target),
                            )?;
                            // DefineMethodProperty: {w:true, e:false, c:true}.
                            let ok = self.define_own(
                                target,
                                &k,
                                PartialDesc::full_data(JsValue::Obj(fo), true, false, true),
                            )?;
                            if !ok {
                                return Err(self.throw_type_error());
                            }
                        }
                        MethodKind::Get => {
                            let fo = self.create_function(
                                func,
                                class_env,
                                true,
                                Some(&format!("get {name}")),
                                FnFlavor::Getter,
                                Some(target),
                            )?;
                            let desc = PartialDesc {
                                get: Some(Some(fo)),
                                enumerable: Some(false),
                                configurable: Some(true),
                                ..Default::default()
                            };
                            let ok = self.define_own(target, &k, desc)?;
                            if !ok {
                                return Err(self.throw_type_error());
                            }
                        }
                        MethodKind::Set => {
                            let fo = self.create_function(
                                func,
                                class_env,
                                true,
                                Some(&format!("set {name}")),
                                FnFlavor::Setter,
                                Some(target),
                            )?;
                            let desc = PartialDesc {
                                set: Some(Some(fo)),
                                enumerable: Some(false),
                                configurable: Some(true),
                                ..Default::default()
                            };
                            let ok = self.define_own(target, &k, desc)?;
                            if !ok {
                                return Err(self.throw_type_error());
                            }
                        }
                        MethodKind::Constructor => unreachable!("filtered above"),
                    }
                }
                ClassElement::Field {
                    is_static,
                    key: AstKey::Private(pname),
                    init,
                } => {
                    let id = self.priv_env_bind(penv, pname);
                    let pfd = PrivFieldDef {
                        name: id,
                        display: format!("#{pname}"),
                        init: init.as_ref().map(|e| Rc::new(e.clone())),
                        env: class_env,
                        home: if *is_static { fobj } else { proto },
                    };
                    if *is_static {
                        static_elems.push(StaticItem::Field(InstanceElem::Private(pfd)));
                    } else {
                        instance_elems.push(InstanceElem::Private(pfd));
                    }
                }
                ClassElement::Field {
                    is_static,
                    key,
                    init,
                } => {
                    let (k, name, lossy) = self.eval_prop_key(key, &cctx)?;
                    let fd = FieldDef {
                        key: k,
                        name,
                        lossy,
                        init: init.as_ref().map(|e| Rc::new(e.clone())),
                        env: class_env,
                        home: if *is_static { fobj } else { proto },
                    };
                    if *is_static {
                        static_elems.push(StaticItem::Field(InstanceElem::Public(fd)));
                    } else {
                        instance_elems.push(InstanceElem::Public(fd));
                    }
                }
            }
        }

        self.class_info.insert(
            fobj,
            Rc::new(ClassInfo {
                default_ctor,
                instance_elems,
                instance_priv_methods,
            }),
        );

        // Static private methods land on F before the class binding
        // initializes (so static field initializers can call them).
        for (name, elem) in static_priv_methods {
            self.priv_add(fobj, name, elem)?;
        }

        // Initialize the inner class binding, then run static fields and static
        // initialization blocks in source order.
        if let Some(n) = &c.name {
            self.initialize_binding(class_env, n, JsValue::Obj(fobj))?;
        }
        let receiver = JsValue::Obj(fobj);
        for el in &static_elems {
            match el {
                StaticItem::Field(InstanceElem::Public(fd)) => self.define_field(&receiver, fd)?,
                StaticItem::Field(InstanceElem::Private(pfd)) => {
                    self.define_private_field(&receiver, pfd)?;
                }
                StaticItem::Block(body) => self.exec_static_block(fobj, body, class_env)?,
            }
        }
        Ok(JsValue::Obj(fobj))
    }

    /// ClassStaticBlockDefinitionEvaluation + its Call: run a `static { ... }`
    /// block body as a parameterless strict function with `this` = the class
    /// constructor `fobj`, [[HomeObject]] = `fobj`, new.target = undefined, and
    /// no `arguments` object (the parser makes `arguments` an early error in a
    /// static block). The block closes over the class scope (`class_env`), so it
    /// sees the class binding and the private environment.
    fn exec_static_block(
        &mut self,
        fobj: ObjId,
        body: &[Stmt],
        class_env: EnvId,
    ) -> Result<(), Abrupt> {
        let senv = self.alloc_env(Some(class_env));
        {
            let fr = self.heap.env_mut(senv);
            fr.this_val = Some(JsValue::Obj(fobj));
            fr.new_target = Some(JsValue::Undefined);
            fr.home_object = Some(fobj);
            fr.var_scope = true;
        }
        // FunctionDeclarationInstantiation for a strict, parameterless body:
        // var names, then top-level lexical declarations (TDZ), then top-level
        // function declarations (bound var-scoped). All share `senv` (strict).
        let analysis = hoist::analyze(body, true).map_err(Abrupt::Fatal)?;
        let lexical = hoist::lexical_decls(body).map_err(Abrupt::Fatal)?;
        for v in &analysis.vars {
            if !self.heap.env(senv).bindings.contains_key(v) {
                self.heap
                    .env_mut(senv)
                    .bindings
                    .insert(v.clone(), Binding::var(JsValue::Undefined));
            }
        }
        for (n, mutable) in lexical {
            self.heap
                .env_mut(senv)
                .bindings
                .insert(n, Binding::tdz(mutable));
        }
        for g in &analysis.funcs {
            let fo = self.instantiate_hoisted_function(g, senv)?;
            self.heap.env_mut(senv).bindings.insert(
                g.name.clone().expect("declaration has a name"),
                Binding::var(JsValue::Obj(fo)),
            );
        }
        let ctx = Ctx {
            env: senv,
            strict: true,
        };
        let mut v: Option<JsValue> = None;
        // A static block cannot `return` (an early error), so any abrupt
        // completion is a throw/fatal that propagates out of the class
        // definition unchanged.
        self.eval_stmt_list(body, &ctx, &mut v)
    }

    /// InitializeInstanceElements(O, F): add the instance private methods and
    /// accessors, then DefineField each instance field (public and private) in
    /// source order.
    pub(crate) fn init_instance_elements(
        &mut self,
        receiver: &JsValue,
        info: &Rc<ClassInfo>,
    ) -> Result<(), Abrupt> {
        let JsValue::Obj(oid) = *receiver else {
            return Err(Abrupt::Fatal("instance receiver is not an object".to_string()));
        };
        for (name, elem) in &info.instance_priv_methods {
            self.priv_add(oid, *name, elem.clone())?;
        }
        for el in &info.instance_elems {
            match el {
                InstanceElem::Public(fd) => self.define_field(receiver, fd)?,
                InstanceElem::Private(pfd) => self.define_private_field(receiver, pfd)?,
            }
        }
        Ok(())
    }

    /// Evaluate a field initializer with `this` = receiver, [[HomeObject]] =
    /// home, and the NamedEvaluation name for an anonymous initializer.
    fn eval_field_initializer(
        &mut self,
        receiver: &JsValue,
        init: &Option<Rc<Expr>>,
        env: EnvId,
        home: ObjId,
        name: &str,
        lossy: bool,
    ) -> ERes {
        match init {
            None => Ok(JsValue::Undefined),
            Some(e) => {
                if lossy {
                    // Refuse only when the name would actually be taken.
                    self.check_infer_name(true, e)?;
                }
                let fenv = self.alloc_env(Some(env));
                {
                    let fr = self.heap.env_mut(fenv);
                    fr.this_val = Some(receiver.clone());
                    fr.new_target = Some(JsValue::Undefined);
                    fr.home_object = Some(home);
                }
                let fctx = Ctx {
                    env: fenv,
                    strict: true,
                };
                self.eval_expr_named(e, name, &fctx)
            }
        }
    }

    /// DefineField (7.3.32): evaluate the initializer, then
    /// CreateDataPropertyOrThrow.
    pub(crate) fn define_field(&mut self, receiver: &JsValue, fd: &FieldDef) -> Result<(), Abrupt> {
        let value =
            self.eval_field_initializer(receiver, &fd.init, fd.env, fd.home, &fd.name, fd.lossy)?;
        let JsValue::Obj(oid) = receiver else {
            return Err(Abrupt::Fatal("field receiver is not an object".to_string()));
        };
        let ok = self.define_own(*oid, &fd.key, PartialDesc::full_data(value, true, true, true))?;
        if !ok {
            return Err(self.throw_type_error());
        }
        Ok(())
    }

    /// DefineField for a private field: evaluate the initializer, then
    /// PrivateFieldAdd.
    pub(crate) fn define_private_field(
        &mut self,
        receiver: &JsValue,
        pfd: &PrivFieldDef,
    ) -> Result<(), Abrupt> {
        let value = self.eval_field_initializer(
            receiver,
            &pfd.init,
            pfd.env,
            pfd.home,
            &pfd.display,
            false,
        )?;
        let JsValue::Obj(oid) = receiver else {
            return Err(Abrupt::Fatal("field receiver is not an object".to_string()));
        };
        self.priv_add(*oid, pfd.name, PrivElem::Field(value))
    }

    /// [[Construct]] for class constructors (10.2.2 with constructorKind).
    pub(crate) fn construct_class(
        &mut self,
        fid: ObjId,
        derived: bool,
        args: Vec<JsValue>,
        nt: JsValue,
    ) -> ERes {
        let info = self
            .class_info
            .get(&fid)
            .cloned()
            .ok_or_else(|| Abrupt::Fatal("class metadata missing (interpreter bug)".to_string()))?;
        if derived {
            if info.default_ctor {
                // constructor(...args) { super(...args) }
                let superc = match self.heap.obj(fid).proto {
                    Some(p) => JsValue::Obj(p),
                    None => JsValue::Null,
                };
                if !self.is_constructor(&superc) {
                    return Err(self.throw_type_error());
                }
                let result = self.construct(&superc, args, Some(&nt))?;
                self.init_instance_elements(&result, &info)?;
                return Ok(result);
            }
            // this-TDZ body run; call_user applies the derived return
            // protocol (super() inside binds this + runs the fields).
            return self.call_obj(fid, JsValue::Undefined, args, Some(nt));
        }
        // Base: create this from newTarget, run fields, then the body.
        let proto = self.get_prototype_from_constructor(&nt, self.intr.object_proto)?;
        let obj = self.alloc_obj(JsObject::new(ObjKind::Plain, Some(proto)))?;
        let receiver = JsValue::Obj(obj);
        self.init_instance_elements(&receiver, &info)?;
        if info.default_ctor {
            return Ok(receiver);
        }
        let r = self.call_obj(fid, receiver.clone(), args, Some(nt))?;
        Ok(match r {
            JsValue::Obj(_) => r,
            _ => receiver,
        })
    }
}

/// Add a private method/accessor to a per-class list, merging a `get`/`set`
/// pair (same identity) into one Accessor entry.
fn add_priv_method(
    list: &mut Vec<(PrivName, PrivElem)>,
    name: PrivName,
    kind: &MethodKind,
    fo: ObjId,
) {
    match kind {
        MethodKind::Method => list.push((name, PrivElem::Method(fo))),
        MethodKind::Get => {
            if let Some((_, PrivElem::Accessor { get, .. })) = list
                .iter_mut()
                .find(|(n, e)| *n == name && matches!(e, PrivElem::Accessor { .. }))
            {
                *get = Some(fo);
            } else {
                list.push((name, PrivElem::Accessor { get: Some(fo), set: None }));
            }
        }
        MethodKind::Set => {
            if let Some((_, PrivElem::Accessor { set, .. })) = list
                .iter_mut()
                .find(|(n, e)| *n == name && matches!(e, PrivElem::Accessor { .. }))
            {
                *set = Some(fo);
            } else {
                list.push((name, PrivElem::Accessor { get: None, set: Some(fo) }));
            }
        }
        MethodKind::Constructor => {}
    }
}
