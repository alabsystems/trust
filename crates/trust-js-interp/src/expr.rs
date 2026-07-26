// Expression evaluation: identifier resolution (with TDZ), Reference Records
// (GetValue/PutValue each coerce a raw computed key — a compound assignment
// or update observably runs the key's toString twice, verified against
// Node 24), optional chains, literals, operators, assignment (including the
// short-circuit logical forms), function-name inference (NamedEvaluation),
// calls, and `new`.
//
// Author: Andrew Yates
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

use crate::interp::{Abrupt, Ctx, ERes, Interp, MAX_EVAL_DEPTH, MAX_STRING_UNITS};
use crate::literals::{cook_template_piece, decode_string_literal};
use std::rc::Rc;
use trust_js_parse::ast::{Arg, Expr, ObjProp, Pat, PropKey as AstKey};
use crate::ops::Numeric;
use trust_js_value::{
    bigint_binary, bigint_from_i64, bigint_neg, bigint_not, numeric_literal_mv,
    parse_bigint_literal, units_from_str, BigOp, ErrKind, FnFlavor, JsValue, PropKey, Property,
};

/// A resolved Reference Record (data + accessor properties).
pub(crate) enum JsRef {
    Env(String),
    Member { base: JsValue, key: RefKey },
    /// A super reference: base = [[HomeObject]].[[GetPrototypeOf]] at
    /// GetValue/PutValue time; `this` is the actualThis receiver.
    SuperMember { home: trust_js_value::ObjId, this: JsValue, key: RefKey },
    /// A private reference (`obj.#x`): the resolved private-name identity.
    Private { base: JsValue, name: crate::private::PrivName },
}

/// The [[ReferencedName]]: already a property key (dot access / literal), or
/// the raw computed-key value coerced by ToPropertyKey at each
/// GetValue/PutValue.
pub(crate) enum RefKey {
    Key(PropKey),
    Raw(JsValue),
}

/// Is an UNBOUND `name` — absent from every environment record AND from the
/// modeled global object — a genuinely-undeclared identifier, i.e. an
/// UNRESOLVABLE reference (a real ReferenceError on read / strict-assign, a
/// `typeof` of `"undefined"`, a sloppy `delete` of `true`)?
///
/// True only when the name is neither a realm global (see
/// `trust_js_value::is_realm_global_name` — a real global we may simply not
/// model, so we must refuse, never mis-throw) NOR a context-restricted special
/// binding. `arguments` is excluded: at true global scope an unbound
/// `arguments` IS a ReferenceError, but inside a class field initializer — and
/// a direct eval within one — a reference to `arguments` is an EARLY
/// SyntaxError (a static rule this interpreter does not enforce). Since the two
/// contexts are indistinguishable here, treating `arguments` as plain-undeclared
/// could mis-throw a runtime ReferenceError where the engine raises an early
/// SyntaxError before the body runs; we refuse on `arguments` instead (sound).
fn is_genuinely_undeclared(name: &str) -> bool {
    name != "arguments" && !trust_js_value::is_realm_global_name(name)
}

enum ChainVal {
    Val(JsValue),
    ShortCircuit,
}

impl Interp {
    pub(crate) fn eval_expr(&mut self, e: &Expr, ctx: &Ctx) -> ERes {
        self.eval_depth += 1;
        let r = if self.eval_depth > MAX_EVAL_DEPTH {
            Err(Abrupt::Fatal("evaluation depth cap exceeded".to_string()))
        } else {
            self.eval_expr_inner(e, ctx)
        };
        self.eval_depth -= 1;
        r
    }

    /// NamedEvaluation: an anonymous function/arrow on the right-hand side of
    /// a binding/assignment gets the binding's name.
    pub(crate) fn eval_expr_named(&mut self, e: &Expr, name: &str, ctx: &Ctx) -> ERes {
        let mut inner = e;
        while let Expr::Paren(p) = inner {
            inner = p;
        }
        match inner {
            Expr::Function(f) if f.name.is_none() => self
                .create_function(f, ctx.env, false, Some(name), FnFlavor::Normal, None)
                .map(JsValue::Obj),
            Expr::Arrow(f) => self
                .create_function(f, ctx.env, false, Some(name), FnFlavor::Arrow, None)
                .map(JsValue::Obj),
            Expr::Class(c) if c.name.is_none() => self.eval_class(c, ctx, Some(name)),
            _ => self.eval_expr(e, ctx),
        }
    }

    #[allow(clippy::too_many_lines)]
    fn eval_expr_inner(&mut self, e: &Expr, ctx: &Ctx) -> ERes {
        match e {
            Expr::Ident(name) => self.env_get(ctx, name),
            Expr::This => self.resolve_this(ctx),
            Expr::Null => Ok(JsValue::Null),
            Expr::Bool(b) => Ok(JsValue::Bool(*b)),
            Expr::Num(raw) => Ok(JsValue::Num(numeric_literal_mv(raw).map_err(Abrupt::Fatal)?)),
            Expr::Str { raw, octal, .. } => {
                if *octal {
                    return Err(Abrupt::Fatal(
                        "legacy octal / \\8 \\9 string escape (out of slice)".to_string(),
                    ));
                }
                Ok(JsValue::Str(Rc::new(
                    decode_string_literal(raw).map_err(Abrupt::Fatal)?,
                )))
            }
            Expr::BigInt(raw) => match parse_bigint_literal(raw) {
                Some(b) => Ok(JsValue::bigint(b)),
                None => Err(Abrupt::Fatal(format!(
                    "malformed BigInt literal `{raw}` (parser invariant)"
                ))),
            },
            Expr::Regex { pattern, flags } => self.eval_regex_literal(pattern, flags),
            Expr::Template { quasis, exprs } => self.eval_template(quasis, exprs, ctx),
            Expr::TaggedTemplate { tag, quasis, exprs } => {
                self.eval_tagged_template(tag, quasis, exprs, ctx)
            }
            Expr::Array {
                elems,
                trailing_comma: _,
            } => self.eval_array_literal(elems, ctx),
            Expr::Object(props) => self.eval_object_literal(props, ctx),
            Expr::Function(f) => {
                let flavor = FnFlavor::Normal;
                self.create_function(f, ctx.env, false, None, flavor, None)
                    .map(JsValue::Obj)
            }
            Expr::Arrow(f) => self
                .create_function(f, ctx.env, false, None, FnFlavor::Arrow, None)
                .map(JsValue::Obj),
            Expr::Class(c) => self.eval_class(c, ctx, None),
            Expr::Paren(inner) => self.eval_expr(inner, ctx),
            Expr::Seq(exprs) => {
                let mut last = JsValue::Undefined;
                for e in exprs {
                    last = self.eval_expr(e, ctx)?;
                }
                Ok(last)
            }
            Expr::Unary { op, arg } => self.eval_unary(op, arg, ctx),
            Expr::Update { op, prefix, arg } => self.eval_update(op, *prefix, arg, ctx),
            Expr::Binary { op, left, right } => {
                // `#x in obj` (13.10.1): the left operand is a PrivateIdentifier.
                if *op == "in" {
                    if let Expr::PrivateRef(pname) = left.as_ref() {
                        let name = self.resolve_priv_or_fatal(ctx.env, pname)?;
                        let r = self.eval_expr(right, ctx)?;
                        return self.private_brand_check(name, &r);
                    }
                }
                let l = self.eval_expr(left, ctx)?;
                let r = self.eval_expr(right, ctx)?;
                self.binary_op(op, &l, &r)
            }
            Expr::Logical { op, left, right } => {
                let l = self.eval_expr(left, ctx)?;
                match *op {
                    "&&" => {
                        if self.to_boolean(&l) {
                            self.eval_expr(right, ctx)
                        } else {
                            Ok(l)
                        }
                    }
                    "||" => {
                        if self.to_boolean(&l) {
                            Ok(l)
                        } else {
                            self.eval_expr(right, ctx)
                        }
                    }
                    "??" => {
                        if l.is_nullish() {
                            self.eval_expr(right, ctx)
                        } else {
                            Ok(l)
                        }
                    }
                    other => Err(Abrupt::Fatal(format!("logical operator `{other}`"))),
                }
            }
            Expr::Cond { test, cons, alt } => {
                let t = self.eval_expr(test, ctx)?;
                if self.to_boolean(&t) {
                    self.eval_expr(cons, ctx)
                } else {
                    self.eval_expr(alt, ctx)
                }
            }
            Expr::Assign { op, target, value } => self.eval_assign(op, target, value, ctx),
            Expr::Member { .. } | Expr::Call { .. } => {
                let (v, _) = self.eval_chain(e, ctx)?;
                Ok(match v {
                    ChainVal::Val(v) => v,
                    ChainVal::ShortCircuit => JsValue::Undefined,
                })
            }
            Expr::New { callee, args } => {
                let f = self.eval_expr(callee, ctx)?;
                let argv = self.eval_args(args, ctx)?;
                if !self.is_constructor(&f) {
                    return Err(self.throw_type_error());
                }
                self.construct(&f, argv, None)
            }
            Expr::NewTarget => self.resolve_new_target(ctx),
            Expr::ImportMeta => Err(Abrupt::Fatal(
                "import.meta (module goal, out of slice)".to_string(),
            )),
            Expr::ImportCall(_) => Err(Abrupt::Fatal("import() (M2, out of slice)".to_string())),
            Expr::SuperProp(key) => self.eval_super_prop(key, ctx).map(|(v, _)| v),
            Expr::SuperCall(args) => self.eval_super_call(args, ctx),
            Expr::Yield { .. } => Err(Abrupt::Fatal("yield (S1e, out of slice)".to_string())),
            // An `await` reached here is being evaluated WHOLESALE — outside the
            // async suspension machine (top-level await, or an await in a
            // position the resumption machine cannot suspend at). Sound refusal.
            Expr::Await(_) => Err(Abrupt::Fatal(
                "await outside a suspendable position (top-level await or unsupported position, out of slice)"
                    .to_string(),
            )),
            Expr::PrivateRef(_) => {
                Err(Abrupt::Fatal("private name reference (S1b, out of slice)".to_string()))
            }
        }
    }

    // -- identifier resolution ----------------------------------------------

    pub(crate) fn env_get(&mut self, ctx: &Ctx, name: &str) -> ERes {
        let mut cur = Some(ctx.env);
        while let Some(e) = cur {
            if let Some(b) = self.heap.env(e).bindings.get(name) {
                if !b.initialized {
                    return Err(self.throw_native(ErrKind::Reference));
                }
                return Ok(b.value.clone());
            }
            cur = self.heap.env(e).parent;
        }
        let key = PropKey::from_str(name);
        if let Some(p) = self.heap.obj(self.global).props.get(&key) {
            if let Some(v) = p.data_value() {
                return Ok(v.clone());
            }
        }
        // Unbound in every environment record AND not an own property of the
        // (modeled) global object. If the name is not a global of the driver
        // realm either, the reference is UNRESOLVABLE — a genuine ReferenceError
        // ("<name> is not defined"), exactly as every engine. A name that IS a
        // realm global we simply do not model refuses (NoCoverage): we cannot
        // synthesize its value, but we must not mis-throw. See
        // trust_js_value::is_realm_global_name (empirically-derived registry).
        if is_genuinely_undeclared(name) {
            return Err(self.throw_native(ErrKind::Reference));
        }
        Err(Abrupt::Fatal(format!(
            "unresolved identifier `{name}` (unmodeled realm global or context-restricted binding)"
        )))
    }

    pub(crate) fn env_set(&mut self, ctx: &Ctx, name: &str, v: JsValue) -> Result<(), Abrupt> {
        let mut cur = Some(ctx.env);
        while let Some(e) = cur {
            if let Some(b) = self.heap.env_mut(e).bindings.get_mut(name) {
                if !b.initialized {
                    return Err(self.throw_native(ErrKind::Reference));
                }
                if !b.mutable {
                    // const always throws; the named-function-expression
                    // self-binding (and strict `arguments`) throws only when
                    // the ASSIGNING code is strict.
                    if !b.strict_immutable && !ctx.strict {
                        return Ok(());
                    }
                    return Err(self.throw_type_error());
                }
                b.value = v;
                return Ok(());
            }
            cur = self.heap.env(e).parent;
        }
        let key = PropKey::from_str(name);
        if let Some(p) = self.heap.obj_mut(self.global).props.get_mut(&key) {
            if let trust_js_value::PropValue::Data { value, writable } = &mut p.v {
                if *writable {
                    *value = v;
                    p.synthetic = false;
                } else if ctx.strict {
                    return Err(self.throw_type_error());
                }
                return Ok(());
            }
            return Err(Abrupt::Fatal(format!(
                "assignment through accessor global `{name}` (out of slice)"
            )));
        }
        if ctx.strict {
            // PutValue on an unresolvable reference in strict code throws a
            // ReferenceError. A name absent from every environment record, from
            // the modeled global object, AND from the realm-global registry is
            // genuinely undeclared → unresolvable → the exact ReferenceError.
            // A registry global we do not model refuses: its writability /
            // accessor surface (which decides assign-vs-TypeError) is unknown.
            if is_genuinely_undeclared(name) {
                return Err(self.throw_native(ErrKind::Reference));
            }
            return Err(Abrupt::Fatal(format!(
                "strict assignment to unresolved `{name}` (unmodeled realm global or context-restricted binding)"
            )));
        }
        self.heap
            .obj_mut(self.global)
            .props
            .insert(key, Property::data(v));
        Ok(())
    }

    pub(crate) fn resolve_this(&mut self, ctx: &Ctx) -> ERes {
        let mut cur = Some(ctx.env);
        while let Some(e) = cur {
            if self.heap.env(e).this_uninit {
                // Derived-constructor this-TDZ (super() not yet called).
                return Err(self.throw_native(trust_js_value::ErrKind::Reference));
            }
            if let Some(t) = &self.heap.env(e).this_val {
                return Ok(t.clone());
            }
            cur = self.heap.env(e).parent;
        }
        Err(Abrupt::Fatal("`this` outside any this-environment".to_string()))
    }

    /// GetThisEnvironment (9.4.3): the nearest frame with this-capability.
    pub(crate) fn find_this_env(&self, env: trust_js_value::EnvId) -> Option<trust_js_value::EnvId> {
        let mut cur = Some(env);
        while let Some(e) = cur {
            let fr = self.heap.env(e);
            if fr.this_uninit || fr.this_val.is_some() {
                return Some(e);
            }
            cur = fr.parent;
        }
        None
    }

    /// The lexically-resolved [[HomeObject]] for super references.
    pub(crate) fn resolve_home_object(&self, ctx: &Ctx) -> Option<trust_js_value::ObjId> {
        let mut cur = Some(ctx.env);
        while let Some(e) = cur {
            let fr = self.heap.env(e);
            // Stop at the nearest function environment (home may be None on
            // a plain function: super is then a parser-rejected form).
            if fr.this_uninit || fr.this_val.is_some() || fr.active_fn.is_some() {
                return fr.home_object;
            }
            cur = fr.parent;
        }
        None
    }

    fn resolve_new_target(&mut self, ctx: &Ctx) -> ERes {
        let mut cur = Some(ctx.env);
        while let Some(e) = cur {
            if let Some(t) = &self.heap.env(e).new_target {
                return Ok(t.clone());
            }
            cur = self.heap.env(e).parent;
        }
        Err(Abrupt::Fatal("new.target outside a function (parser gap?)".to_string()))
    }

    // -- super ---------------------------------------------------------------

    /// SuperProperty evaluation in GetValue/call contexts (13.3.7). ENGINE
    /// consensus (Node and Bun agree, matching the spec here): the this-TDZ
    /// check runs BEFORE the computed key expression evaluates. Object-valued
    /// computed keys refuse (the base-capture vs ToPropertyKey order
    /// diverges between engines). Returns (value, actualThis) so
    /// `super.m(...)` calls carry the right receiver.
    pub(crate) fn eval_super_prop(
        &mut self,
        key: &AstKey,
        ctx: &Ctx,
    ) -> Result<(JsValue, JsValue), Abrupt> {
        let home = self
            .resolve_home_object(ctx)
            .ok_or_else(|| Abrupt::Fatal("super property outside a method (parser gap?)".to_string()))?;
        let this = self.resolve_this(ctx)?;
        let k = match key {
            AstKey::Ident(n) => PropKey::from_str(n),
            AstKey::Str(cooked) => PropKey::Str(units_from_str(cooked)),
            AstKey::Num(raw) => {
                let n = numeric_literal_mv(raw).map_err(Abrupt::Fatal)?;
                PropKey::from_str(&trust_js_value::js_number_to_string(n))
            }
            AstKey::Computed(ke) => {
                let kv = self.eval_expr(ke, ctx)?;
                if matches!(kv, JsValue::Obj(_)) {
                    // ToPropertyKey user code can mutate the home prototype;
                    // Node resolves the super base AFTER the coercion, Bun
                    // BEFORE (spec) — no consensus to match.
                    return Err(Abrupt::Fatal(
                        "object-valued computed super key (base/coercion order diverges between engines)"
                            .to_string(),
                    ));
                }
                self.to_property_key(&kv)?
            }
            AstKey::Private(_) => {
                return Err(Abrupt::Fatal("private super member (out of slice)".to_string()))
            }
        };
        let Some(base) = self.heap.obj(home).proto else {
            // Get on an undefined/null base.
            return Err(self.throw_type_error());
        };
        let v = self.get_from_object(base, &k, this.clone())?;
        Ok((v, this))
    }

    /// SuperCall evaluation (13.3.7.1).
    pub(crate) fn eval_super_call(&mut self, args: &[Arg], ctx: &Ctx) -> ERes {
        let this_env = self
            .find_this_env(ctx.env)
            .ok_or_else(|| Abrupt::Fatal("super() outside a constructor (parser gap?)".to_string()))?;
        let active = self
            .heap
            .env(this_env)
            .active_fn
            .ok_or_else(|| Abrupt::Fatal("super() without an active function (parser gap?)".to_string()))?;
        // 1. newTarget; 2. GetSuperConstructor; 3. args; 4. IsConstructor;
        // 5. Construct.
        let nt = self.resolve_new_target(ctx)?;
        let superc = match self.heap.obj(active).proto {
            Some(p) => JsValue::Obj(p),
            None => JsValue::Null,
        };
        let argv = self.eval_args(args, ctx)?;
        if !self.is_constructor(&superc) {
            return Err(self.throw_type_error());
        }
        let result = self.construct(&superc, argv, Some(&nt))?;
        // BindThisValue: ReferenceError when already initialized.
        {
            let fr = self.heap.env_mut(this_env);
            if !fr.this_uninit {
                return Err(self.throw_native(trust_js_value::ErrKind::Reference));
            }
            fr.this_uninit = false;
            fr.this_val = Some(result.clone());
        }
        // InitializeInstanceElements(result, activeFn).
        if let Some(info) = self.class_info.get(&active).cloned() {
            self.init_instance_elements(&result, &info)?;
        }
        Ok(result)
    }

    // -- references ----------------------------------------------------------

    /// Evaluate a MemberExpression (or identifier) to a Reference Record;
    /// the base is NOT validated and a computed key NOT coerced here.
    pub(crate) fn expr_ref(&mut self, e: &Expr, ctx: &Ctx) -> Result<JsRef, Abrupt> {
        let mut inner = e;
        while let Expr::Paren(p) = inner {
            inner = p;
        }
        match inner {
            Expr::Ident(name) => Ok(JsRef::Env(name.clone())),
            Expr::Member {
                obj,
                prop,
                optional,
                in_chain,
            } => {
                if *optional || *in_chain {
                    return Err(Abrupt::Fatal(
                        "optional chain as a reference target (out of slice)".to_string(),
                    ));
                }
                let base = self.eval_expr(obj, ctx)?;
                if let AstKey::Private(pname) = prop.as_ref() {
                    let name = self.resolve_priv_or_fatal(ctx.env, pname)?;
                    return Ok(JsRef::Private { base, name });
                }
                let key = match prop.as_ref() {
                    AstKey::Ident(n) => RefKey::Key(PropKey::from_str(n)),
                    AstKey::Str(cooked) => RefKey::Key(PropKey::Str(units_from_str(cooked))),
                    AstKey::Num(raw) => {
                        let n = numeric_literal_mv(raw).map_err(Abrupt::Fatal)?;
                        RefKey::Key(PropKey::from_str(&trust_js_value::js_number_to_string(n)))
                    }
                    AstKey::Computed(ke) => RefKey::Raw(self.eval_expr(ke, ctx)?),
                    AstKey::Private(_) => unreachable!("private handled above"),
                };
                Ok(JsRef::Member { base, key })
            }
            Expr::SuperProp(key) => {
                let home = self.resolve_home_object(ctx).ok_or_else(|| {
                    Abrupt::Fatal("super property outside a method (parser gap?)".to_string())
                })?;
                // Assignment-flavored super references (PutValue, compound,
                // update): with `this` still in TDZ Node checks this FIRST
                // (ReferenceError) while Bun evaluates the key expression
                // first — no consensus, so a computed key under this-TDZ
                // refuses. With `this` initialized the order is
                // unobservable (this resolution is pure).
                let this_uninit = self
                    .find_this_env(ctx.env)
                    .is_some_and(|e| self.heap.env(e).this_uninit);
                if this_uninit && matches!(key.as_ref(), AstKey::Computed(_)) {
                    return Err(Abrupt::Fatal(
                        "computed super key under uninitialized this (evaluation order diverges between engines)"
                            .to_string(),
                    ));
                }
                let key = match key.as_ref() {
                    AstKey::Ident(n) => RefKey::Key(PropKey::from_str(n)),
                    AstKey::Str(cooked) => RefKey::Key(PropKey::Str(units_from_str(cooked))),
                    AstKey::Num(raw) => {
                        let n = numeric_literal_mv(raw).map_err(Abrupt::Fatal)?;
                        RefKey::Key(PropKey::from_str(&trust_js_value::js_number_to_string(n)))
                    }
                    AstKey::Computed(ke) => RefKey::Raw(self.eval_expr(ke, ctx)?),
                    AstKey::Private(_) => {
                        return Err(Abrupt::Fatal("private super member (out of slice)".to_string()))
                    }
                };
                let this = self.resolve_this(ctx)?;
                Ok(JsRef::SuperMember { home, this, key })
            }
            _ => Err(Abrupt::Fatal("non-reference assignment target".to_string())),
        }
    }

    fn resolve_ref_key(&mut self, key: &RefKey) -> Result<PropKey, Abrupt> {
        match key {
            RefKey::Key(k) => Ok(k.clone()),
            RefKey::Raw(v) => {
                let raw = v.clone();
                self.to_property_key(&raw)
            }
        }
    }

    /// GetValue (6.2.5.5): base validation (TypeError for nullish) happens
    /// BEFORE ToPropertyKey of a not-yet-coerced key.
    pub(crate) fn ref_get(&mut self, r: &JsRef, ctx: &Ctx) -> ERes {
        match r {
            JsRef::Env(name) => {
                let name = name.clone();
                self.env_get(ctx, &name)
            }
            JsRef::Member { base, key } => {
                let base = base.clone();
                if base.is_nullish() {
                    return Err(self.throw_type_error());
                }
                let k = self.resolve_ref_key(key)?;
                self.get_prop(&base, &k)
            }
            JsRef::SuperMember { home, this, key } => {
                let home = *home;
                let this = this.clone();
                if matches!(key, RefKey::Raw(JsValue::Obj(_))) {
                    return Err(Abrupt::Fatal(
                        "object-valued computed super key (base/coercion order diverges between engines)"
                            .to_string(),
                    ));
                }
                let Some(base) = self.heap.obj(home).proto else {
                    return Err(self.throw_type_error());
                };
                let k = self.resolve_ref_key(key)?;
                self.get_from_object(base, &k, this)
            }
            JsRef::Private { base, name } => {
                let base = base.clone();
                let name = *name;
                self.private_get(&base, name)
            }
        }
    }

    /// PutValue (6.2.5.6): same order.
    pub(crate) fn ref_set(&mut self, r: &JsRef, v: JsValue, ctx: &Ctx) -> Result<(), Abrupt> {
        match r {
            JsRef::Env(name) => {
                let name = name.clone();
                self.env_set(ctx, &name, v)
            }
            JsRef::Member { base, key } => {
                let base = base.clone();
                if base.is_nullish() {
                    return Err(self.throw_type_error());
                }
                let k = self.resolve_ref_key(key)?;
                self.set_prop(&base, &k, v, ctx.strict)
            }
            JsRef::SuperMember { home, this, key } => {
                let home = *home;
                let this = this.clone();
                if matches!(key, RefKey::Raw(JsValue::Obj(_))) {
                    return Err(Abrupt::Fatal(
                        "object-valued computed super key (base/coercion order diverges between engines)"
                            .to_string(),
                    ));
                }
                let Some(base) = self.heap.obj(home).proto else {
                    return Err(self.throw_type_error());
                };
                let k = self.resolve_ref_key(key)?;
                let ok = self.set_obj_with_receiver(base, &k, v, &this)?;
                if !ok && ctx.strict {
                    return Err(self.throw_type_error());
                }
                Ok(())
            }
            JsRef::Private { base, name } => {
                let base = base.clone();
                let name = *name;
                self.private_set(&base, name, v)
            }
        }
    }

    // -- optional chains / member / call -------------------------------------

    fn eval_chain(&mut self, e: &Expr, ctx: &Ctx) -> Result<(ChainVal, Option<JsValue>), Abrupt> {
        match e {
            Expr::Member {
                obj,
                prop,
                optional,
                ..
            } => {
                let (bv, _) = self.eval_chain_operand(obj, ctx)?;
                let ChainVal::Val(base) = bv else {
                    return Ok((ChainVal::ShortCircuit, None));
                };
                if *optional && base.is_nullish() {
                    return Ok((ChainVal::ShortCircuit, None));
                }
                if base.is_nullish() {
                    return Err(self.throw_type_error());
                }
                if let AstKey::Private(pname) = prop.as_ref() {
                    let name = self.resolve_priv_or_fatal(ctx.env, pname)?;
                    let v = self.private_get(&base, name)?;
                    return Ok((ChainVal::Val(v), Some(base)));
                }
                let key = match prop.as_ref() {
                    AstKey::Ident(n) => PropKey::from_str(n),
                    AstKey::Str(cooked) => PropKey::Str(units_from_str(cooked)),
                    AstKey::Num(raw) => {
                        let n = numeric_literal_mv(raw).map_err(Abrupt::Fatal)?;
                        PropKey::from_str(&trust_js_value::js_number_to_string(n))
                    }
                    AstKey::Computed(ke) => {
                        let kv = self.eval_expr(ke, ctx)?;
                        self.to_property_key(&kv)?
                    }
                    AstKey::Private(_) => unreachable!("private handled above"),
                };
                let v = self.get_prop(&base, &key)?;
                Ok((ChainVal::Val(v), Some(base)))
            }
            Expr::Call {
                callee,
                args,
                optional,
                ..
            } => {
                let (fv, this) = self.eval_chain_operand(callee, ctx)?;
                let ChainVal::Val(f) = fv else {
                    return Ok((ChainVal::ShortCircuit, None));
                };
                if *optional && f.is_nullish() {
                    return Ok((ChainVal::ShortCircuit, None));
                }
                let argv = self.eval_args(args, ctx)?;
                // Direct eval (19.2.1): a syntactic unqualified `eval(...)`
                // whose callee resolves to %eval% runs in THIS context. The
                // argument list is already evaluated (spec EvaluateCall order),
                // which is what makes an empty leading/trailing spread
                // (`eval(...[], "x")`) still a direct eval whose iterator side
                // effect has already fired — the direct/indirect determination
                // is purely syntactic and a spread does NOT demote it. Only an
                // optional call (`eval?.(x)`) is a distinct (OptionalExpression)
                // production and is INDIRECT — fall through to %eval% dispatch.
                if !*optional
                    && crate::eval::is_syntactic_eval_callee(callee)
                    && self.is_eval_intrinsic(&f)
                {
                    // ArgumentListEvaluation done; the first element is evalText
                    // (spec step: no elements → return undefined, which
                    // PerformEval yields for a non-string / absent argument).
                    let arg0 = argv.into_iter().next().unwrap_or(JsValue::Undefined);
                    let v = self.eval_direct(arg0, ctx)?;
                    return Ok((ChainVal::Val(v), None));
                }
                let v = self.call_value(&f, this.unwrap_or(JsValue::Undefined), argv)?;
                Ok((ChainVal::Val(v), None))
            }
            Expr::SuperProp(key) => {
                let (v, this) = self.eval_super_prop(key, ctx)?;
                Ok((ChainVal::Val(v), Some(this)))
            }
            _ => {
                let v = self.eval_expr(e, ctx)?;
                Ok((ChainVal::Val(v), None))
            }
        }
    }

    /// A chain operand: member/call links propagate short-circuit;
    /// parentheses stop propagation but keep the this-binding of an inner
    /// member reference.
    fn eval_chain_operand(
        &mut self,
        e: &Expr,
        ctx: &Ctx,
    ) -> Result<(ChainVal, Option<JsValue>), Abrupt> {
        match e {
            Expr::Member { .. } | Expr::Call { .. } | Expr::SuperProp(_) => self.eval_chain(e, ctx),
            Expr::Paren(inner) => {
                let (v, this) = self.eval_chain_operand(inner, ctx)?;
                Ok((
                    ChainVal::Val(match v {
                        ChainVal::Val(v) => v,
                        ChainVal::ShortCircuit => JsValue::Undefined,
                    }),
                    this,
                ))
            }
            _ => {
                let v = self.eval_expr(e, ctx)?;
                Ok((ChainVal::Val(v), None))
            }
        }
    }

    pub(crate) fn eval_args(&mut self, args: &[Arg], ctx: &Ctx) -> Result<Vec<JsValue>, Abrupt> {
        let mut out = Vec::with_capacity(args.len());
        for a in args {
            match a {
                Arg::Expr(e) => out.push(self.eval_expr(e, ctx)?),
                Arg::Spread(e) => {
                    let v = self.eval_expr(e, ctx)?;
                    let mut it = self.get_iterator_or_type_error(&v)?;
                    while let Some(x) = self.fast_iter_next(&mut it)? {
                        self.charge_loop()?;
                        out.push(x);
                    }
                }
            }
        }
        Ok(out)
    }

    // -- literals ------------------------------------------------------------

    fn eval_template(&mut self, quasis: &[String], exprs: &[Expr], ctx: &Ctx) -> ERes {
        let mut out: trust_js_value::Units = Vec::new();
        for (i, q) in quasis.iter().enumerate() {
            let cooked = cook_template_piece(q).map_err(Abrupt::Fatal)?;
            out.extend_from_slice(&cooked);
            if let Some(e) = exprs.get(i) {
                let v = self.eval_expr(e, ctx)?;
                let s = self.to_string_units(&v)?;
                out.extend_from_slice(&s);
            }
            if out.len() > MAX_STRING_UNITS {
                return Err(Abrupt::Fatal("template result cap exceeded".to_string()));
            }
        }
        Ok(JsValue::Str(Rc::new(out)))
    }

    /// Tagged template (13.3.11): GetTemplateObject (per-site identity via
    /// the AST-address cache; frozen cooked+raw arrays, invalid escapes →
    /// undefined cooked) then an ordinary call with the member this-binding.
    fn eval_tagged_template(
        &mut self,
        tag: &Expr,
        quasis: &[String],
        exprs: &[Expr],
        ctx: &Ctx,
    ) -> ERes {
        let (fv, this) = self.eval_chain_operand(tag, ctx)?;
        let f = match fv {
            ChainVal::Val(v) => v,
            ChainVal::ShortCircuit => JsValue::Undefined,
        };
        let site_key = quasis.as_ptr() as usize;
        let tpl = if let Some(cached) = self.tpl_cache.get(&site_key) {
            *cached
        } else {
            let n = u32::try_from(quasis.len())
                .map_err(|_| Abrupt::Fatal("template piece count overflow".to_string()))?;
            let cooked_arr = self.new_array(n)?;
            let raw_arr = self.new_array(n)?;
            for (i, q) in quasis.iter().enumerate() {
                let key = PropKey::Str(units_from_str(&i.to_string()));
                let cooked_v = match cook_template_piece(q) {
                    Ok(u) => JsValue::Str(Rc::new(u)),
                    // NotEscapeSequence in a tagged template: TV undefined.
                    Err(_) => JsValue::Undefined,
                };
                self.heap.obj_mut(cooked_arr).props.insert(
                    key.clone(),
                    Property::with_attrs(cooked_v, false, true, false),
                );
                let raw_norm = q.replace("\r\n", "\n").replace('\r', "\n");
                self.heap.obj_mut(raw_arr).props.insert(
                    key,
                    Property::with_attrs(
                        JsValue::Str(Rc::new(units_from_str(&raw_norm))),
                        false,
                        true,
                        false,
                    ),
                );
            }
            for arr in [cooked_arr, raw_arr] {
                // Freeze: length non-writable, object non-extensible.
                if let Some(p) = self
                    .heap
                    .obj_mut(arr)
                    .props
                    .get_mut(&PropKey::from_str("length"))
                {
                    if let trust_js_value::PropValue::Data { writable, .. } = &mut p.v {
                        *writable = false;
                    }
                }
                self.heap.obj_mut(arr).extensible = false;
            }
            self.heap.obj_mut(cooked_arr).props.insert(
                PropKey::from_str("raw"),
                Property::frozen(JsValue::Obj(raw_arr)),
            );
            self.tpl_cache.insert(site_key, cooked_arr);
            cooked_arr
        };
        let mut argv: Vec<JsValue> = vec![JsValue::Obj(tpl)];
        for e in exprs {
            argv.push(self.eval_expr(e, ctx)?);
        }
        self.call_value(&f, this.unwrap_or(JsValue::Undefined), argv)
    }

    fn eval_array_literal(&mut self, elems: &[Option<Arg>], ctx: &Ctx) -> ERes {
        let arr = self.new_array(0)?;
        let mut idx: u32 = 0;
        for el in elems {
            match el {
                None => {
                    idx += 1; // elision hole
                }
                Some(Arg::Expr(e)) => {
                    let v = self.eval_expr(e, ctx)?;
                    self.heap.obj_mut(arr).props.insert(
                        PropKey::Str(units_from_str(&idx.to_string())),
                        Property::data(v),
                    );
                    idx += 1;
                }
                Some(Arg::Spread(e)) => {
                    let v = self.eval_expr(e, ctx)?;
                    let mut it = self.get_iterator_or_type_error(&v)?;
                    while let Some(x) = self.fast_iter_next(&mut it)? {
                        self.charge_loop()?;
                        self.heap.obj_mut(arr).props.insert(
                            PropKey::Str(units_from_str(&idx.to_string())),
                            Property::data(x),
                        );
                        idx = idx.checked_add(1).ok_or_else(|| {
                            Abrupt::Fatal("array literal spread overflow".to_string())
                        })?;
                    }
                }
            }
        }
        self.set_array_length_raw(arr, f64::from(idx));
        Ok(JsValue::Obj(arr))
    }

    /// Evaluate a property key to (PropKey, function-name-for-inference,
    /// name-is-lossy). `lossy` marks a name whose exact code units cannot be
    /// carried through the &str inference channel (lone surrogates): using it
    /// for NamedEvaluation must refuse rather than store corrupted text.
    /// Symbol keys infer "[description]" / "" per SetFunctionName.
    pub(crate) fn eval_prop_key(
        &mut self,
        key: &AstKey,
        ctx: &Ctx,
    ) -> Result<(PropKey, String, bool), Abrupt> {
        match key {
            AstKey::Ident(n) => Ok((PropKey::from_str(n), n.clone(), false)),
            AstKey::Str(cooked) => {
                Ok((PropKey::Str(units_from_str(cooked)), cooked.clone(), false))
            }
            AstKey::Num(raw) => {
                let n = numeric_literal_mv(raw).map_err(Abrupt::Fatal)?;
                let s = trust_js_value::js_number_to_string(n);
                Ok((PropKey::from_str(&s), s, false))
            }
            AstKey::Computed(e) => {
                let v = self.eval_expr(e, ctx)?;
                let k = self.to_property_key(&v)?;
                let (name, lossy) = match &k {
                    PropKey::Str(u) => match String::from_utf16(u) {
                        Ok(s) => (s, false),
                        Err(_) => (trust_js_value::units_to_lossy(u), true),
                    },
                    PropKey::Sym(s) => match self.heap.sym_description(*s) {
                        Some(d) => match String::from_utf16(&d) {
                            Ok(ds) => (format!("[{ds}]"), false),
                            Err(_) => (format!("[{}]", trust_js_value::units_to_lossy(&d)), true),
                        },
                        None => (String::new(), false),
                    },
                };
                Ok((k, name, lossy))
            }
            AstKey::Private(_) => Err(Abrupt::Fatal("private property key (out of slice)".to_string())),
        }
    }

    /// Refuse NamedEvaluation over a lossy inferred name when the value shape
    /// would actually take the name (anonymous function/arrow/class).
    pub(crate) fn check_infer_name(&self, lossy: bool, value: &Expr) -> Result<(), Abrupt> {
        if !lossy {
            return Ok(());
        }
        let mut inner = value;
        while let Expr::Paren(p) = inner {
            inner = p;
        }
        let anonymous = matches!(inner, Expr::Arrow(_))
            || matches!(inner, Expr::Function(f) if f.name.is_none())
            || matches!(inner, Expr::Class(c) if c.name.is_none());
        if anonymous {
            return Err(Abrupt::Fatal(
                "function-name inference over a lone-surrogate key (out of slice)".to_string(),
            ));
        }
        Ok(())
    }

    #[allow(clippy::too_many_lines)]
    fn eval_object_literal(&mut self, props: &[ObjProp], ctx: &Ctx) -> ERes {
        let oid = self.new_plain()?;
        for p in props {
            match p {
                ObjProp::KeyValue { key, value } => {
                    let is_proto_key = matches!(
                        key,
                        AstKey::Ident(n) if n == "__proto__"
                    ) || matches!(key, AstKey::Str(s) if s == "__proto__");
                    if is_proto_key {
                        // B.3.1 __proto__ in an object initializer sets
                        // [[Prototype]] (object/null; other values ignored).
                        let v = self.eval_expr(value, ctx)?;
                        match v {
                            JsValue::Obj(p) => self.heap.obj_mut(oid).proto = Some(p),
                            JsValue::Null => self.heap.obj_mut(oid).proto = None,
                            _ => {}
                        }
                        continue;
                    }
                    let (k, name, lossy) = self.eval_prop_key(key, ctx)?;
                    self.check_infer_name(lossy, value)?;
                    let v = self.eval_expr_named(value, &name, ctx)?;
                    self.heap
                        .obj_mut(oid)
                        .props
                        .insert(k, Property::data(v));
                }
                ObjProp::Shorthand(name) => {
                    let v = self.env_get(ctx, name)?;
                    self.heap
                        .obj_mut(oid)
                        .props
                        .insert(PropKey::from_str(name), Property::data(v));
                }
                ObjProp::CoverInit(..) => {
                    return Err(Abrupt::Fatal(
                        "cover-initializer in an object literal (parser bug?)".to_string(),
                    ))
                }
                ObjProp::Method { kind, key, func } => {
                    use trust_js_parse::ast::MethodKind;
                    let (k, name, lossy) = self.eval_prop_key(key, ctx)?;
                    if lossy {
                        return Err(Abrupt::Fatal(
                            "method-name inference over a lone-surrogate key (out of slice)"
                                .to_string(),
                        ));
                    }
                    match kind {
                        MethodKind::Method => {
                            let fo = self.create_function(
                                func,
                                ctx.env,
                                false,
                                Some(&name),
                                FnFlavor::Method,
                                Some(oid),
                            )?;
                            self.heap
                                .obj_mut(oid)
                                .props
                                .insert(k, Property::data(JsValue::Obj(fo)));
                        }
                        MethodKind::Get => {
                            let fo = self.create_function(
                                func,
                                ctx.env,
                                false,
                                Some(&format!("get {name}")),
                                FnFlavor::Getter,
                                Some(oid),
                            )?;
                            let desc = crate::props::PartialDesc {
                                get: Some(Some(fo)),
                                enumerable: Some(true),
                                configurable: Some(true),
                                ..Default::default()
                            };
                            self.define_own(oid, &k, desc)?;
                        }
                        MethodKind::Set => {
                            let fo = self.create_function(
                                func,
                                ctx.env,
                                false,
                                Some(&format!("set {name}")),
                                FnFlavor::Setter,
                                Some(oid),
                            )?;
                            let desc = crate::props::PartialDesc {
                                set: Some(Some(fo)),
                                enumerable: Some(true),
                                configurable: Some(true),
                                ..Default::default()
                            };
                            self.define_own(oid, &k, desc)?;
                        }
                        MethodKind::Constructor => {
                            return Err(Abrupt::Fatal(
                                "constructor method outside class (parser bug?)".to_string(),
                            ))
                        }
                    }
                }
                ObjProp::Spread(e) => {
                    let v = self.eval_expr(e, ctx)?;
                    self.copy_data_properties(oid, &v, &[])?;
                }
            }
        }
        Ok(JsValue::Obj(oid))
    }

    // -- unary / update / assignment ------------------------------------------

    fn eval_unary(&mut self, op: &str, arg: &Expr, ctx: &Ctx) -> ERes {
        match op {
            "typeof" => self.eval_typeof(arg, ctx),
            "delete" => self.eval_delete(arg, ctx),
            "void" => {
                self.eval_expr(arg, ctx)?;
                Ok(JsValue::Undefined)
            }
            "!" => {
                let v = self.eval_expr(arg, ctx)?;
                Ok(JsValue::Bool(!self.to_boolean(&v)))
            }
            "-" => {
                let v = self.eval_expr(arg, ctx)?;
                match self.to_numeric(&v)? {
                    Numeric::N(n) => Ok(JsValue::Num(-n)),
                    Numeric::B(b) => Ok(JsValue::bigint(bigint_neg(&b))),
                }
            }
            "+" => {
                // Unary + is ToNumber, which throws TypeError on a BigInt.
                let v = self.eval_expr(arg, ctx)?;
                Ok(JsValue::Num(self.to_number(&v)?))
            }
            "~" => {
                let v = self.eval_expr(arg, ctx)?;
                match self.to_numeric(&v)? {
                    Numeric::N(n) => Ok(JsValue::Num(f64::from(!trust_js_value::to_int32(n)))),
                    Numeric::B(b) => Ok(JsValue::bigint(bigint_not(&b))),
                }
            }
            other => Err(Abrupt::Fatal(format!("unary operator `{other}` (out of slice)"))),
        }
    }

    fn eval_typeof(&mut self, arg: &Expr, ctx: &Ctx) -> ERes {
        let mut inner = arg;
        while let Expr::Paren(p) = inner {
            inner = p;
        }
        if let Expr::Ident(name) = inner {
            let mut cur = Some(ctx.env);
            while let Some(e) = cur {
                if let Some(b) = self.heap.env(e).bindings.get(name) {
                    if !b.initialized {
                        return Err(self.throw_native(ErrKind::Reference));
                    }
                    let t = self.type_of_value(&b.value.clone());
                    return Ok(JsValue::str_from(t));
                }
                cur = self.heap.env(e).parent;
            }
            let key = PropKey::from_str(name);
            if let Some(p) = self.heap.obj(self.global).props.get(&key) {
                if let Some(v) = p.data_value() {
                    let t = self.type_of_value(&v.clone());
                    return Ok(JsValue::str_from(t));
                }
            }
            // `typeof` of an UNRESOLVABLE reference is the string "undefined"
            // (never a ReferenceError). A genuinely-undeclared name (absent
            // from the realm-global registry) is unresolvable → "undefined". A
            // registry global we do not model refuses: its type is unknown.
            if is_genuinely_undeclared(name) {
                return Ok(JsValue::str_from("undefined"));
            }
            return Err(Abrupt::Fatal(format!(
                "typeof unresolved `{name}` (unmodeled realm global or context-restricted binding)"
            )));
        }
        let v = self.eval_expr(arg, ctx)?;
        Ok(JsValue::str_from(self.type_of_value(&v)))
    }

    fn eval_delete(&mut self, arg: &Expr, ctx: &Ctx) -> ERes {
        let mut inner = arg;
        while let Expr::Paren(p) = inner {
            inner = p;
        }
        match inner {
            Expr::Member {
                obj,
                prop,
                optional,
                in_chain,
            } => {
                if *optional || *in_chain {
                    return Err(Abrupt::Fatal(
                        "delete of an optional chain (out of slice)".to_string(),
                    ));
                }
                let base = self.eval_expr(obj, ctx)?;
                let raw_key = match prop.as_ref() {
                    AstKey::Ident(n) => RefKey::Key(PropKey::from_str(n)),
                    AstKey::Str(cooked) => RefKey::Key(PropKey::Str(units_from_str(cooked))),
                    AstKey::Num(raw) => {
                        let n = numeric_literal_mv(raw).map_err(Abrupt::Fatal)?;
                        RefKey::Key(PropKey::from_str(&trust_js_value::js_number_to_string(n)))
                    }
                    AstKey::Computed(ke) => RefKey::Raw(self.eval_expr(ke, ctx)?),
                    AstKey::Private(_) => {
                        return Err(Abrupt::Fatal("private member delete (S1b)".to_string()))
                    }
                };
                // 13.5.1.2: ToObject(base) THEN ToPropertyKey.
                let oid = self.to_object(&base)?;
                let key = self.resolve_ref_key(&raw_key)?;
                let ok = self.delete_prop(oid, &key)?;
                if !ok && ctx.strict {
                    return Err(self.throw_type_error());
                }
                Ok(JsValue::Bool(ok))
            }
            Expr::SuperProp(key) => {
                // 13.5.1.2: deleting a super reference throws ReferenceError
                // after the reference evaluates — with the engines' order
                // (computed key expression before the this-TDZ check).
                self.resolve_home_object(ctx).ok_or_else(|| {
                    Abrupt::Fatal("super property outside a method (parser gap?)".to_string())
                })?;
                if let AstKey::Computed(ke) = key.as_ref() {
                    self.eval_expr(ke, ctx)?;
                }
                self.resolve_this(ctx)?;
                Err(self.throw_native(trust_js_value::ErrKind::Reference))
            }
            Expr::Ident(name) => {
                // Sloppy only (strict `delete x` is an early error).
                let mut cur = Some(ctx.env);
                while let Some(e) = cur {
                    if let Some(b) = self.heap.env(e).bindings.get(name) {
                        // Only a sloppy-eval-created var/function binding is
                        // deletable; every other declarative binding returns
                        // false (DeleteBinding on a non-deletable binding).
                        if b.deletable {
                            self.heap.env_mut(e).bindings.remove(name);
                            return Ok(JsValue::Bool(true));
                        }
                        return Ok(JsValue::Bool(false));
                    }
                    cur = self.heap.env(e).parent;
                }
                // Reached only in sloppy code (`delete x` is a strict early
                // error). Deleting an UNRESOLVABLE reference evaluates to
                // `true` (13.5.1.2). A genuinely-undeclared name that is ALSO
                // not an own property of the (modeled) global object is
                // unresolvable everywhere → `true`. A name that IS a global
                // object property (a global `var`/function binding, or a
                // modeled global) still refuses: `delete` must actually remove
                // a configurable property (or return false for a
                // non-configurable one) — the global attribute surface this
                // path deliberately does not model. Unlike the read paths, the
                // env-chain walk above does not consult the global object, so
                // this own-property guard is required here.
                let key = PropKey::from_str(name);
                if is_genuinely_undeclared(name)
                    && !self.heap.obj(self.global).props.contains_key(&key)
                {
                    return Ok(JsValue::Bool(true));
                }
                Err(Abrupt::Fatal(format!(
                    "delete of global binding `{name}` (global attribute surface unmodeled)"
                )))
            }
            _ => {
                self.eval_expr(arg, ctx)?;
                Ok(JsValue::Bool(true))
            }
        }
    }

    fn eval_update(&mut self, op: &str, prefix: bool, arg: &Expr, ctx: &Ctx) -> ERes {
        let r = self.expr_ref(arg, ctx)?;
        let old = self.ref_get(&r, ctx)?;
        // ToNumeric first: `++`/`--` step a Number by 1 or a BigInt by 1n.
        let (old_num, newv) = match self.to_numeric(&old)? {
            Numeric::N(n) => {
                let nv = if op == "++" { n + 1.0 } else { n - 1.0 };
                (JsValue::Num(n), JsValue::Num(nv))
            }
            Numeric::B(b) => {
                let delta = bigint_from_i64(if op == "++" { 1 } else { -1 });
                let nv = bigint_binary(BigOp::Add, &b, &delta)
                    .map_err(|_| Abrupt::Fatal("BigInt increment overflow (out of slice)".to_string()))?;
                (JsValue::BigInt(b), JsValue::bigint(nv))
            }
        };
        self.ref_set(&r, newv.clone(), ctx)?;
        Ok(if prefix { newv } else { old_num })
    }

    /// The FROZEN parser strips parentheses from assignment targets, so
    /// `(fn) = function () {}` (no NamedEvaluation: IsIdentifierRef is
    /// false) is indistinguishable from `fn = function () {}` (named). The
    /// inferred name is stored but marked SYNTHETIC: any observation of it
    /// (reads, descriptors, projection) refuses instead of risking the
    /// parenthesized corner's wrong name.
    fn mark_assign_inferred_name(&mut self, v: &JsValue, value_expr: &Expr) {
        let mut inner = value_expr;
        while let Expr::Paren(p) = inner {
            inner = p;
        }
        let anonymous = matches!(inner, Expr::Arrow(_))
            || matches!(inner, Expr::Function(f) if f.name.is_none())
            || matches!(inner, Expr::Class(c) if c.name.is_none());
        if !anonymous {
            return;
        }
        if let JsValue::Obj(o) = v {
            if let Some(p) = self
                .heap
                .obj_mut(*o)
                .props
                .get_mut(&PropKey::from_str("name"))
            {
                p.synthetic = true;
            }
        }
    }

    fn eval_assign(&mut self, op: &str, target: &Pat, value: &Expr, ctx: &Ctx) -> ERes {
        // Destructuring assignment (op is "=" by grammar).
        if matches!(target, Pat::Array { .. } | Pat::Object { .. }) {
            let rhs = self.eval_expr(value, ctx)?;
            self.bind_pattern(target, rhs.clone(), None, ctx)?;
            return Ok(rhs);
        }
        match target {
            Pat::Ident(name) => match op {
                "=" => {
                    let v = self.eval_expr_named(value, name, ctx)?;
                    self.mark_assign_inferred_name(&v, value);
                    self.env_set(ctx, name, v.clone())?;
                    Ok(v)
                }
                "&&=" | "||=" | "??=" => {
                    let cur = self.env_get(ctx, name)?;
                    let should = match op {
                        "&&=" => self.to_boolean(&cur),
                        "||=" => !self.to_boolean(&cur),
                        _ => cur.is_nullish(),
                    };
                    if !should {
                        return Ok(cur);
                    }
                    let v = self.eval_expr_named(value, name, ctx)?;
                    self.mark_assign_inferred_name(&v, value);
                    self.env_set(ctx, name, v.clone())?;
                    Ok(v)
                }
                compound => {
                    let base = compound
                        .strip_suffix('=')
                        .ok_or_else(|| Abrupt::Fatal(format!("assignment op `{compound}`")))?;
                    let cur = self.env_get(ctx, name)?;
                    let rhs = self.eval_expr(value, ctx)?;
                    let v = self.binary_op(base, &cur, &rhs)?;
                    self.env_set(ctx, name, v.clone())?;
                    Ok(v)
                }
            },
            Pat::Expr(m) => match op {
                "=" => {
                    let r = self.expr_ref(m, ctx)?;
                    let v = self.eval_expr(value, ctx)?;
                    self.ref_set(&r, v.clone(), ctx)?;
                    Ok(v)
                }
                "&&=" | "||=" | "??=" => {
                    let r = self.expr_ref(m, ctx)?;
                    let cur = self.ref_get(&r, ctx)?;
                    let should = match op {
                        "&&=" => self.to_boolean(&cur),
                        "||=" => !self.to_boolean(&cur),
                        _ => cur.is_nullish(),
                    };
                    if !should {
                        return Ok(cur);
                    }
                    let v = self.eval_expr(value, ctx)?;
                    self.ref_set(&r, v.clone(), ctx)?;
                    Ok(v)
                }
                compound => {
                    let base = compound
                        .strip_suffix('=')
                        .ok_or_else(|| Abrupt::Fatal(format!("assignment op `{compound}`")))?;
                    let r = self.expr_ref(m, ctx)?;
                    let cur = self.ref_get(&r, ctx)?;
                    let rhs = self.eval_expr(value, ctx)?;
                    let v = self.binary_op(base, &cur, &rhs)?;
                    self.ref_set(&r, v.clone(), ctx)?;
                    Ok(v)
                }
            },
            _ => Err(Abrupt::Fatal("invalid assignment target shape".to_string())),
        }
    }
}
