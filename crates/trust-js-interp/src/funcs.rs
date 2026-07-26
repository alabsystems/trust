// Function objects and invocation: OrdinaryFunctionCreate (with flavor —
// declaration/expression/arrow/method/accessor), FunctionDeclaration-
// Instantiation (10.2.11) including the exact arguments object
// (mapped/unmapped, parameter-map aliasing), [[Call]]/[[Construct]], and
// bound functions.
//
// Author: Andrew Yates
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

use crate::interp::{hoist, Abrupt, Ctx, ERes, Interp, MAX_CALL_DEPTH};
use std::collections::HashSet;
use std::rc::Rc;
use trust_js_parse::ast::{Func, Pat};
use trust_js_value::{
    units_from_str, ArgsData, Binding, BoundFn, FnData, FnFlavor, JsObject, JsValue, ObjId,
    ObjKind, PropKey, Property, SymId, UserFn, WkSym,
};

impl Interp {
    /// Address-cached Rc of an AST function (so closure creation in loops
    /// does not re-clone the body).
    fn rc_func(&mut self, f: &Func) -> Rc<Func> {
        let key = std::ptr::from_ref(f) as usize;
        if let Some(rc) = self.fn_cache.get(&key) {
            return Rc::clone(rc);
        }
        let rc = Rc::new(f.clone());
        self.fn_cache.insert(key, Rc::clone(&rc));
        rc
    }

    /// OrdinaryFunctionCreate + SetFunctionName/Length (+ MakeConstructor
    /// for Normal flavor). `is_decl` suppresses the named-function-expression
    /// self-binding scope. `home` is the [[HomeObject]] (class/object
    /// methods).
    pub(crate) fn create_function(
        &mut self,
        f: &Func,
        env: trust_js_value::EnvId,
        is_decl: bool,
        name_override: Option<&str>,
        flavor: FnFlavor,
        home: Option<ObjId>,
    ) -> Result<ObjId, Abrupt> {
        let needs_self_binding =
            !is_decl && flavor == FnFlavor::Normal && f.name.is_some() && name_override.is_none();
        let closure_env = if needs_self_binding {
            self.alloc_env(Some(env))
        } else {
            env
        };
        let rc = self.rc_func(f);
        // [[Prototype]]: %AsyncGeneratorFunction.prototype% for async generators,
        // %GeneratorFunction.prototype% for generators, %AsyncFunction.prototype%
        // for async functions, else %Function.prototype%.
        let fn_proto = if f.is_async && f.is_gen {
            self.intr.async_generator_function_proto
        } else if f.is_gen {
            self.intr.generator_function_proto
        } else if f.is_async {
            self.intr.async_function_proto
        } else {
            self.intr.function_proto
        };
        let fobj = self.alloc_obj(JsObject::new(
            ObjKind::Function(FnData::User(Rc::new(UserFn {
                func: rc,
                env: closure_env,
                flavor,
                home,
            }))),
            Some(fn_proto),
        ))?;
        if needs_self_binding {
            self.heap.env_mut(closure_env).bindings.insert(
                f.name.clone().expect("checked"),
                Binding {
                    value: JsValue::Obj(fobj),
                    mutable: false,
                    initialized: true,
                    // CreateImmutableBinding(name, false): sloppy writes are
                    // silent no-ops; strict writing code gets TypeError.
                    strict_immutable: false,
                    deletable: false,
                },
            );
        }
        // SetFunctionLength FIRST, then SetFunctionName (own-key order is an
        // observable via Object.getOwnPropertyNames).
        let len = expected_argument_count(&f.params);
        self.heap.obj_mut(fobj).props.insert(
            PropKey::from_str("length"),
            Property::with_attrs(JsValue::Num(len), false, false, true),
        );
        let name: String = name_override
            .map(str::to_string)
            .or_else(|| f.name.clone())
            .unwrap_or_default();
        self.heap.obj_mut(fobj).props.insert(
            PropKey::from_str("name"),
            Property::with_attrs(JsValue::str_from(&name), false, false, true),
        );
        if f.is_gen {
            // A (async) generator function's `.prototype` is OrdinaryObjectCreate(
            // %GeneratorPrototype% / %AsyncGeneratorPrototype%) with
            // {w:true, e:false, c:false} and NO `constructor` back-link; the
            // function itself is not a constructor.
            let proto_parent = if f.is_async {
                self.intr.async_generator_proto
            } else {
                self.intr.generator_proto
            };
            let proto_obj = self.alloc_obj(JsObject::new(
                ObjKind::Plain,
                Some(proto_parent),
            ))?;
            self.heap.obj_mut(fobj).props.insert(
                PropKey::from_str("prototype"),
                Property::with_attrs(JsValue::Obj(proto_obj), true, false, false),
            );
        } else if flavor == FnFlavor::Normal && !f.is_async {
            // Async functions are not constructors and carry no own `prototype`.
            let proto_obj = self.new_plain()?;
            self.heap.obj_mut(proto_obj).props.insert(
                PropKey::from_str("constructor"),
                Property::with_attrs(JsValue::Obj(fobj), true, false, true),
            );
            self.heap.obj_mut(fobj).props.insert(
                PropKey::from_str("prototype"),
                Property::with_attrs(JsValue::Obj(proto_obj), true, false, false),
            );
        }
        Ok(fobj)
    }

    /// A hoisted function declaration (script top level / function top level
    /// / strict block).
    pub(crate) fn instantiate_hoisted_function(
        &mut self,
        f: &Func,
        env: trust_js_value::EnvId,
    ) -> Result<ObjId, Abrupt> {
        let flavor = if f.is_arrow { FnFlavor::Arrow } else { FnFlavor::Normal };
        self.create_function(f, env, true, None, flavor, None)
    }

    // -- calls ---------------------------------------------------------------

    pub(crate) fn call_value(&mut self, f: &JsValue, this: JsValue, args: Vec<JsValue>) -> ERes {
        let JsValue::Obj(fid) = f else {
            return Err(self.throw_type_error());
        };
        if !self.heap.obj(*fid).is_callable() {
            return Err(self.throw_type_error());
        }
        self.call_obj(*fid, this, args, None)
    }

    pub(crate) fn call_obj(
        &mut self,
        fid: ObjId,
        this: JsValue,
        args: Vec<JsValue>,
        new_target: Option<JsValue>,
    ) -> ERes {
        self.call_depth += 1;
        if self.call_depth > MAX_CALL_DEPTH {
            self.call_depth -= 1;
            return Err(Abrupt::Fatal("call depth cap exceeded".to_string()));
        }
        let r = self.call_obj_inner(fid, this, args, new_target);
        self.call_depth -= 1;
        r
    }

    fn call_obj_inner(
        &mut self,
        fid: ObjId,
        this: JsValue,
        args: Vec<JsValue>,
        new_target: Option<JsValue>,
    ) -> ERes {
        let data = match &self.heap.obj(fid).kind {
            ObjKind::Function(d) => d.clone(),
            // A callable proxy: [[Call]] routes through the `apply` trap.
            ObjKind::Proxy(_) => return self.proxy_call(fid, this, args),
            _ => return Err(self.throw_type_error()),
        };
        match data {
            FnData::User(uf) => self.call_user(fid, &uf, this, args, new_target),
            FnData::Native(nf) => self.dispatch_native(nf, fid, this, args, new_target),
            FnData::Bound(b) => {
                let mut merged = b.args.clone();
                merged.extend(args);
                match new_target {
                    None => self.call_obj(b.target, b.this.clone(), merged, None),
                    Some(nt) => {
                        // [[Construct]]: newTarget == F → replace with target.
                        let nt = if matches!(&nt, JsValue::Obj(o) if *o == fid) {
                            JsValue::Obj(b.target)
                        } else {
                            nt
                        };
                        self.call_obj(b.target, this, merged, Some(nt))
                    }
                }
            }
        }
    }

    fn call_user(
        &mut self,
        fid: ObjId,
        uf: &UserFn,
        this: JsValue,
        args: Vec<JsValue>,
        new_target: Option<JsValue>,
    ) -> ERes {
        let f = Rc::clone(&uf.func);
        let is_class_ctor = matches!(uf.flavor, FnFlavor::ClassCtor { .. });
        if is_class_ctor && new_target.is_none() {
            // [[Call]] of a class constructor throws.
            return Err(self.throw_type_error());
        }
        let derived = matches!(uf.flavor, FnFlavor::ClassCtor { derived: true });
        let fenv = self.alloc_env(Some(uf.env));
        if uf.flavor != FnFlavor::Arrow {
            if derived {
                // this-TDZ until super() binds it.
                self.heap.env_mut(fenv).this_uninit = true;
            } else {
                let this_val = if f.strict || is_class_ctor {
                    this
                } else {
                    match this {
                        JsValue::Undefined | JsValue::Null => JsValue::Obj(self.global),
                        JsValue::Obj(_) => this,
                        prim => JsValue::Obj(self.to_object(&prim)?),
                    }
                };
                self.heap.env_mut(fenv).this_val = Some(this_val);
            }
            self.heap.env_mut(fenv).new_target =
                Some(new_target.unwrap_or(JsValue::Undefined));
            self.heap.env_mut(fenv).home_object = uf.home;
            self.heap.env_mut(fenv).active_fn = Some(fid);
        }
        // EvaluateAsyncFunctionBody (15.8.4): FunctionDeclarationInstantiation
        // runs INSIDE the async function's promise machinery — a THROW during
        // parameter binding (a default-initializer that throws, a self/later
        // TDZ reference, an eval SyntaxError) rejects the result promise rather
        // than propagating synchronously to the caller. A Fatal refusal (an
        // out-of-slice construct) still propagates: it is a no-coverage signal,
        // never a JS value the promise could carry.
        let body_ctx = match self.function_declaration_instantiation(fid, &f, uf.flavor, fenv, args)
        {
            Ok(ctx) => ctx,
            Err(Abrupt::Throw(reason)) if f.is_async && !f.is_gen => {
                return self.async_reject(reason);
            }
            Err(other) => return Err(other),
        };
        // An async-generator-function [[Call]] runs FunctionDeclarationInstantiation
        // now, then returns a fresh AsyncGenerator suspended at start — the body
        // runs on `.next()` (§27.6). Checked before the pure-generator / pure-
        // async branches since it is both `is_gen` and `is_async`.
        if f.is_async && f.is_gen {
            return self.make_async_generator(fid, &f.body, body_ctx);
        }
        // A generator-function [[Call]] runs FunctionDeclarationInstantiation
        // (parameter defaults, the arguments object) now, then returns a fresh
        // generator object suspended at start — the body runs on `.next()`.
        if f.is_gen {
            return self.make_generator(fid, &f.body, body_ctx);
        }
        // An async function desugars onto the reactor: it returns a promise and
        // runs its body (reusing the generator resumption machine in Await mode)
        // synchronously up to the first `await`.
        if f.is_async {
            return self.make_async(&f.body, f.expr_body.as_deref(), body_ctx);
        }
        if let Some(e) = &f.expr_body {
            return self.eval_expr(e, &body_ctx);
        }
        // §15: a function body with a top-level `using` establishes a
        // DisposeCapability on its lexical environment and runs DisposeResources
        // over the body completion on exit (this synchronous path only — an
        // async/generator body's top-level `using` refuses in `eval_decl`).
        let has_using = hoist::has_top_level_sync_using(&f.body);
        if has_using {
            self.dispose_stacks.insert(body_ctx.env, Vec::new());
        }
        let mut v: Option<JsValue> = None;
        let raw = match self.eval_stmt_list(&f.body, &body_ctx, &mut v) {
            Ok(()) => Ok(JsValue::Undefined),
            Err(Abrupt::Return(rv)) => Ok(rv),
            Err(other) => Err(other),
        };
        let completion = if has_using {
            let resources = self.dispose_stacks.remove(&body_ctx.env).unwrap_or_default();
            self.dispose_resources(resources, raw.map(Some))
                .map(|opt| opt.unwrap_or(JsValue::Undefined))
        } else {
            raw
        };
        if derived {
            // 10.2.2 [[Construct]] derived-kind return protocol.
            let rv = completion?;
            return match rv {
                JsValue::Obj(_) => Ok(rv),
                JsValue::Undefined => {
                    let fr = self.heap.env(fenv);
                    if fr.this_uninit {
                        // super() never called.
                        Err(self.throw_native(trust_js_value::ErrKind::Reference))
                    } else {
                        Ok(fr.this_val.clone().unwrap_or(JsValue::Undefined))
                    }
                }
                _ => Err(self.throw_type_error()),
            };
        }
        completion
    }

    /// Construct(F, args, newTarget): user Normal-flavor functions, class
    /// constructors, modeled native constructors, driver-created ordinary
    /// functions, and bound functions. `new_target` None means F itself.
    pub(crate) fn construct(
        &mut self,
        f: &JsValue,
        args: Vec<JsValue>,
        new_target: Option<&JsValue>,
    ) -> ERes {
        let nt = new_target.cloned().unwrap_or_else(|| f.clone());
        let JsValue::Obj(fid) = f else {
            return Err(self.throw_type_error());
        };
        let data = match &self.heap.obj(*fid).kind {
            ObjKind::Function(d) => d.clone(),
            // A constructor proxy: [[Construct]] routes through the `construct`
            // trap (a non-constructor proxy was rejected by IsConstructor).
            ObjKind::Proxy(_) => return self.proxy_construct(*fid, args, nt),
            _ => return Err(self.throw_type_error()),
        };
        match data {
            FnData::User(uf) => match uf.flavor {
                // Generator/async functions are not constructors.
                FnFlavor::Normal if uf.func.is_gen || uf.func.is_async => {
                    Err(self.throw_type_error())
                }
                FnFlavor::Normal => {
                    let proto = self.get_prototype_from_constructor(&nt, self.intr.object_proto)?;
                    let obj = self.alloc_obj(JsObject::new(ObjKind::Plain, Some(proto)))?;
                    let r = self.call_obj(*fid, JsValue::Obj(obj), args, Some(nt))?;
                    Ok(match r {
                        JsValue::Obj(_) => r,
                        _ => JsValue::Obj(obj),
                    })
                }
                FnFlavor::ClassCtor { derived } => {
                    self.construct_class(*fid, derived, args, nt)
                }
                _ => Err(self.throw_type_error()), // not a constructor
            },
            FnData::Native(nf) => {
                use trust_js_value::NativeFn as N;
                match nf {
                    N::ObjectCtor
                    | N::ArrayCtor
                    | N::StringCtor
                    | N::NumberCtor
                    | N::BooleanCtor
                    | N::SymbolCtor
                    | N::ErrorCtor(_)
                    | N::AggregateErrorCtor
                    | N::MapCtor
                    | N::SetCtor
                    | N::WeakMapCtor
                    | N::WeakSetCtor
                    | N::DateWrapperCtor
                    | N::DateRealCtor
                    | N::RegExpCtor
                    | N::ProxyCtor
                    | N::ArrayBufferCtor
                    | N::DataViewCtor
                    | N::TypedArrayBaseCtor
                    | N::TypedArrayCtor(_)
                    | N::SuppressedErrorCtor
                    | N::DisposableStackCtor
                    | N::PromiseCtor => {
                        self.call_obj(*fid, JsValue::Undefined, args, Some(nt))
                    }
                    N::WeakRefCtor => self.weakref_construct(&args, Some(&nt)),
                    N::FinalizationRegistryCtor => self.finreg_construct(&args, Some(&nt)),
                    N::IteratorCtor => self.iterator_construct(Some(&nt)),
                    N::FunctionCtor => self.create_dynamic_function(&args, Some(&nt)),
                    N::AsyncFunctionCtor => {
                        self.create_dynamic_function_kind(&args, Some(&nt), true)
                    }
                    N::GeneratorFunctionCtor => Err(Abrupt::Fatal(
                        "GeneratorFunction constructor (dynamic generators, out of slice)"
                            .to_string(),
                    )),
                    N::AsyncGeneratorFunctionCtor => Err(Abrupt::Fatal(
                        "AsyncGeneratorFunction constructor (dynamic async generators, out of slice)"
                            .to_string(),
                    )),
                    // The driver's ordinary function expressions (console
                    // recorders, print, the deterministic Date.now) ARE
                    // constructible: the body's side effect runs (a clock
                    // tick for Date.now), the fresh object is returned.
                    N::ConsoleWrite { .. } | N::Print | N::DateNow => {
                        let proto =
                            self.get_prototype_from_constructor(&nt, self.intr.object_proto)?;
                        let obj = self.alloc_obj(JsObject::new(ObjKind::Plain, Some(proto)))?;
                        self.call_obj(*fid, JsValue::Obj(obj), args, Some(nt))?;
                        Ok(JsValue::Obj(obj))
                    }
                    _ => Err(self.throw_type_error()), // not a constructor
                }
            }
            FnData::Bound(b) => {
                let mut merged = b.args.clone();
                merged.extend(args);
                let nt2 = if matches!(&nt, JsValue::Obj(o) if *o == *fid) {
                    JsValue::Obj(b.target)
                } else {
                    nt
                };
                self.construct(&JsValue::Obj(b.target), merged, Some(&nt2))
            }
        }
    }

    /// GetPrototypeFromConstructor (10.1.13): Get(constructor, "prototype"),
    /// falling back to the realm default when not an Object. When `prototype`
    /// is not an Object the spec takes `? GetFunctionRealm(constructor)` — with
    /// a single modeled realm that is observable only as a THROW when the
    /// bound/proxy chain reaches a revoked proxy (null handler).
    pub(crate) fn get_prototype_from_constructor(
        &mut self,
        nt: &JsValue,
        default: ObjId,
    ) -> Result<ObjId, Abrupt> {
        if let JsValue::Obj(o) = nt {
            let p = self.get_prop(nt, &PropKey::from_str("prototype"))?;
            if let JsValue::Obj(po) = p {
                return Ok(po);
            }
            // proto is not an Object → GetFunctionRealm(constructor).
            self.get_function_realm_check(*o)?;
        }
        Ok(default)
    }

    /// GetFunctionRealm (7.3.22) reduced to its only observable behavior under
    /// a single realm: walk the bound-target / proxy-target chain and throw a
    /// TypeError if it reaches a revoked proxy (a null [[ProxyHandler]]);
    /// otherwise the (sole) realm, so no effect.
    fn get_function_realm_check(&mut self, oid: ObjId) -> Result<(), Abrupt> {
        let mut cur = oid;
        let mut hops = 0;
        loop {
            match &self.heap.obj(cur).kind {
                ObjKind::Function(FnData::Bound(b)) => cur = b.target,
                ObjKind::Proxy(p) => match p.parts() {
                    Some((target, _)) => cur = target,
                    None => return Err(self.throw_type_error()),
                },
                _ => return Ok(()),
            }
            hops += 1;
            if hops >= 128 {
                return Err(Abrupt::Fatal("function-realm chain too deep".to_string()));
            }
        }
    }

    // -- FunctionDeclarationInstantiation (10.2.11) --------------------------

    #[allow(clippy::too_many_lines)]
    fn function_declaration_instantiation(
        &mut self,
        fid: ObjId,
        f: &Func,
        flavor: FnFlavor,
        fenv: trust_js_value::EnvId,
        args: Vec<JsValue>,
    ) -> Result<Ctx, Abrupt> {
        let strict = f.strict;
        let simple = f.params.iter().all(|p| matches!(p, Pat::Ident(_)));
        let mut param_names: Vec<String> = Vec::new();
        for p in &f.params {
            hoist::pat_bound_names(p, &mut param_names);
        }
        let has_dups = {
            let mut seen = HashSet::new();
            param_names.iter().any(|n| !seen.insert(n))
        };
        let has_param_exprs = f.params.iter().any(contains_expression);
        let analysis = hoist::analyze(&f.body, strict).map_err(Abrupt::Fatal)?;
        let lexical = hoist::lexical_decls(&f.body).map_err(Abrupt::Fatal)?;
        let func_names: HashSet<&str> = analysis
            .funcs
            .iter()
            .filter_map(|g| g.name.as_deref())
            .collect();

        let arguments_needed = flavor != FnFlavor::Arrow
            && !param_names.iter().any(|n| n == "arguments")
            && !(!has_param_exprs
                && (func_names.contains("arguments")
                    || lexical.iter().any(|(n, _)| n == "arguments")));

        // Parameter bindings (unique names). Without duplicates the bindings
        // start uninitialized (a default expression reading a later parameter
        // hits the TDZ → ReferenceError).
        let mut seen = HashSet::new();
        for n in &param_names {
            if seen.insert(n.clone()) {
                self.heap.env_mut(fenv).bindings.insert(
                    n.clone(),
                    Binding {
                        value: JsValue::Undefined,
                        mutable: true,
                        initialized: has_dups,
                        strict_immutable: false,
                        deletable: false,
                    },
                );
            }
        }

        if arguments_needed {
            let mapped = !strict && simple;
            let ao = self.create_arguments_object(fid, &args, mapped, &param_names, fenv)?;
            let binding = if strict {
                Binding {
                    value: JsValue::Obj(ao),
                    mutable: false,
                    initialized: true,
                    strict_immutable: false,
                    deletable: false,
                }
            } else {
                Binding::var(JsValue::Obj(ao))
            };
            self.heap
                .env_mut(fenv)
                .bindings
                .insert("arguments".to_string(), binding);
        }

        // IteratorBindingInitialization over the actual argument list.
        let pctx = Ctx { env: fenv, strict };
        let mut i = 0usize;
        for p in &f.params {
            if let Pat::Rest(inner) = p {
                let arr = self.new_array(0)?;
                let mut n: u32 = 0;
                while i < args.len() {
                    self.heap.obj_mut(arr).props.insert(
                        PropKey::Str(units_from_str(&n.to_string())),
                        Property::data(args[i].clone()),
                    );
                    n += 1;
                    i += 1;
                }
                self.set_array_length_raw(arr, f64::from(n));
                self.bind_pattern(inner, JsValue::Obj(arr), Some(fenv), &pctx)?;
            } else {
                let v = args.get(i).cloned().unwrap_or(JsValue::Undefined);
                i += 1;
                self.bind_pattern(p, v, Some(fenv), &pctx)?;
            }
        }

        // Var-scoped names.
        let var_env = if has_param_exprs {
            let ve = self.alloc_env(Some(fenv));
            for v in &analysis.vars {
                if self.heap.env(ve).bindings.contains_key(v) {
                    continue;
                }
                let initial = if param_names.contains(v) && !func_names.contains(v.as_str()) {
                    self.heap
                        .env(fenv)
                        .bindings
                        .get(v)
                        .map_or(JsValue::Undefined, |b| b.value.clone())
                } else {
                    JsValue::Undefined
                };
                self.heap
                    .env_mut(ve)
                    .bindings
                    .insert(v.clone(), Binding::var(initial));
            }
            ve
        } else {
            for v in &analysis.vars {
                if !self.heap.env(fenv).bindings.contains_key(v) {
                    self.heap
                        .env_mut(fenv)
                        .bindings
                        .insert(v.clone(), Binding::var(JsValue::Undefined));
                }
            }
            fenv
        };

        // Mark the frame `var`-scoped names live in as this function's
        // variable environment, so a sloppy direct `eval` in the body can
        // find it (10.2.11 creates this VariableEnvironment).
        self.heap.env_mut(var_env).var_scope = true;

        // lexEnv (10.2.11 step 29): a NON-strict function body's top-level
        // lexical declarations live in a declarative Environment Record
        // DISTINCT from the variable environment. That distinctness is
        // observable: a direct `eval` adding a `var` hoists into varEnv, and
        // EvalDeclarationInstantiation walks lexEnv→varEnv checking the var
        // name against the intervening lexical bindings — so `let x` in the
        // body and a later `eval('var x')` are a conflict (SyntaxError). A
        // strict body reuses varEnv (a strict eval gets its own scope, so the
        // distinction is unneeded); so does a body with no lexical
        // declarations, where the separate frame would be empty and
        // unobservable.
        let lex_env = if !strict && !lexical.is_empty() {
            self.alloc_env(Some(var_env))
        } else {
            var_env
        };

        // Lexical declarations (TDZ) into lexEnv; top-level function
        // declarations close over lexEnv but are bound (var-scoped) into
        // varEnv.
        for (n, mutable) in lexical {
            self.heap
                .env_mut(lex_env)
                .bindings
                .insert(n, Binding::tdz(mutable));
        }
        for g in &analysis.funcs {
            let fo = self.instantiate_hoisted_function(g, lex_env)?;
            self.heap.env_mut(var_env).bindings.insert(
                g.name.clone().expect("declaration has a name"),
                Binding::var(JsValue::Obj(fo)),
            );
        }

        Ok(Ctx {
            env: lex_env,
            strict,
        })
    }

    /// CreateMappedArgumentsObject / CreateUnmappedArgumentsObject.
    fn create_arguments_object(
        &mut self,
        fid: ObjId,
        args: &[JsValue],
        mapped: bool,
        param_names: &[String],
        fenv: trust_js_value::EnvId,
    ) -> Result<ObjId, Abrupt> {
        let map: Vec<Option<String>> = if mapped {
            let mut map = vec![None; args.len()];
            let mut seen: HashSet<&str> = HashSet::new();
            let upto = param_names.len().min(args.len());
            for i in (0..upto).rev() {
                let name = param_names[i].as_str();
                if seen.insert(name) {
                    map[i] = Some(name.to_string());
                }
            }
            map
        } else {
            Vec::new()
        };
        let ao = self.alloc_obj(JsObject::new(
            ObjKind::Arguments(ArgsData { map, env: fenv }),
            Some(self.intr.object_proto),
        ))?;
        for (i, v) in args.iter().enumerate() {
            self.heap.obj_mut(ao).props.insert(
                PropKey::Str(units_from_str(&i.to_string())),
                Property::data(v.clone()),
            );
        }
        #[allow(clippy::cast_precision_loss)]
        self.heap.obj_mut(ao).props.insert(
            PropKey::from_str("length"),
            Property::with_attrs(JsValue::Num(args.len() as f64), true, false, true),
        );
        if mapped {
            self.heap.obj_mut(ao).props.insert(
                PropKey::from_str("callee"),
                Property::with_attrs(JsValue::Obj(fid), true, false, true),
            );
        } else {
            let tte = self.intr.throw_type_error;
            self.heap.obj_mut(ao).props.insert(
                PropKey::from_str("callee"),
                Property::accessor(Some(tte), Some(tte), false, false),
            );
        }
        let values = self.intr.array_values_fn;
        self.heap.obj_mut(ao).props.insert(
            PropKey::Sym(SymId::WellKnown(WkSym::Iterator)),
            Property::with_attrs(JsValue::Obj(values), true, false, true),
        );
        Ok(ao)
    }

    /// Function.prototype.bind's exotic object.
    pub(crate) fn make_bound_function(
        &mut self,
        target: ObjId,
        this: JsValue,
        bound_args: Vec<JsValue>,
    ) -> Result<ObjId, Abrupt> {
        let proto = self.heap.obj(target).proto;
        let bf = self.alloc_obj(JsObject::new(
            ObjKind::Function(FnData::Bound(Rc::new(BoundFn {
                target,
                this,
                args: bound_args.clone(),
            }))),
            proto,
        ))?;
        // length: max(0, targetLen - boundArgCount) when target has an own
        // numeric length (danger-checked own read).
        let mut len = 0.0f64;
        if let Some(p) = self.own_prop_checked(target, &PropKey::from_str("length"))? {
            if let Some(JsValue::Num(n)) = p.data_value() {
                let adj = trust_js_value::to_integer_or_infinity(*n)
                    - args_len_f64(bound_args.len());
                len = adj.max(0.0);
            }
        }
        self.heap.obj_mut(bf).props.insert(
            PropKey::from_str("length"),
            Property::with_attrs(JsValue::Num(len), false, false, true),
        );
        // name: "bound " + target-name-if-string (kept as code units so
        // surrogate-bearing names survive).
        let name_v = self.get_prop(&JsValue::Obj(target), &PropKey::from_str("name"))?;
        let mut name_units = units_from_str("bound ");
        if let JsValue::Str(s) = name_v {
            name_units.extend_from_slice(&s);
        }
        self.heap.obj_mut(bf).props.insert(
            PropKey::from_str("name"),
            Property::with_attrs(
                JsValue::Str(Rc::new(name_units)),
                false,
                false,
                true,
            ),
        );
        Ok(bf)
    }
}

/// ExpectedArgumentCount: formals before the first initializer or rest.
fn expected_argument_count(params: &[Pat]) -> f64 {
    let mut n = 0.0;
    for p in params {
        match p {
            Pat::Default(..) | Pat::Rest(_) => break,
            _ => n += 1.0,
        }
    }
    n
}

/// ContainsExpression of a binding pattern (10.2.11 hasParameterExpressions).
fn contains_expression(p: &Pat) -> bool {
    match p {
        Pat::Ident(_) => false,
        Pat::Expr(_) | Pat::Default(..) => true,
        Pat::Rest(inner) => contains_expression(inner),
        Pat::Array { elems, rest } => {
            elems.iter().flatten().any(contains_expression)
                || rest.as_deref().is_some_and(contains_expression)
        }
        Pat::Object { props, rest } => {
            props.iter().any(|pp| {
                matches!(pp.key, trust_js_parse::ast::PropKey::Computed(_))
                    || contains_expression(&pp.value)
            }) || rest.as_deref().is_some_and(contains_expression)
        }
    }
}

#[allow(clippy::cast_precision_loss)]
fn args_len_f64(n: usize) -> f64 {
    n as f64
}
