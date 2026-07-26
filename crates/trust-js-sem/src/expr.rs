// Expression semantics: references, identifier resolution, property
// [[Get]]/[[Set]] with accessor invocation and the miss-danger discipline (an
// unimplemented-but-real intrinsic property can never be mis-read as
// `undefined` — it refuses), operators (incl. `in`, `delete`, `void`),
// coercions, template literals, function creation/invocation (user, bound,
// builtin), the arguments object, and `new`.
//
// Author: Andrew Yates
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

use crate::ast::{BinOp, Expr, FuncLit, LogOp, MemberProp, ObjKey, PropDef, TplPart, UnOp};
use crate::interp::{
    strict_eq, Abrupt, Ctx, ERes, Interp, JsRef, RefKey, MAX_CALL_DEPTH, MAX_STRING_UNITS,
};
use crate::number::{js_number_to_string, to_number_str};
use crate::value::{
    array_index_of, units_eq_ascii, units_from_str, units_to_lossy, ArgsMap, Binding, EnvId,
    FnImpl, NativeErrorKind, ObjId, ObjKind, Object, Prop, PropDesc, PropVal, PropertyKey, Units,
    Value,
};
use std::rc::Rc;

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Hint {
    Default,
    Number,
    String,
}

impl Interp {
    #[allow(clippy::too_many_lines)]
    pub fn eval_expr(&mut self, e: &Expr, ctx: &Ctx) -> ERes {
        match e {
            Expr::Num(n) => Ok(Value::Num(*n)),
            Expr::BigInt(b) => Ok(Value::BigInt(Rc::clone(b))),
            Expr::Str(s) => Ok(Value::Str(Rc::new(s.as_ref().clone()))),
            Expr::Bool(b) => Ok(Value::Bool(*b)),
            Expr::Null => Ok(Value::Null),
            Expr::Regex { body, flags } => self.eval_regex_literal(body, flags),
            Expr::This => self.resolve_this(ctx),
            Expr::Ident(name) => self.env_get(ctx, name),
            Expr::Array(elems) => {
                let arr = self.new_array(elems.len());
                // ArrayAccumulation (13.2.5.2): a running index that a spread
                // element advances by each iterated value; an elision advances
                // it by one (a hole); a trailing-comma marker contributes
                // nothing.
                let mut idx: u64 = 0;
                for el in elems {
                    match el {
                        None => idx += 1, // elision: a hole
                        Some(Expr::SpreadTrailingComma) => {} // `[...e,]`: no element
                        Some(Expr::Spread(inner)) => {
                            // SpreadElement: iterate the value via the general
                            // iterator protocol, CreateDataProperty per value.
                            let v = self.eval_expr(inner, ctx)?;
                            let mut it = self.slice_iterator(&v)?;
                            loop {
                                self.charge_loop()?;
                                let Some(item) = self.slice_iter_next(&mut it)? else {
                                    break;
                                };
                                self.obj_mut(arr)
                                    .props
                                    .insert(units_from_str(&idx.to_string()), Prop::data(item));
                                idx += 1;
                            }
                        }
                        Some(e) => {
                            let v = self.eval_expr(e, ctx)?;
                            self.obj_mut(arr)
                                .props
                                .insert(units_from_str(&idx.to_string()), Prop::data(v));
                            idx += 1;
                        }
                    }
                }
                #[allow(clippy::cast_precision_loss)]
                self.set_array_length_raw(arr, idx as f64);
                Ok(Value::Obj(arr))
            }
            Expr::Seq(exprs) => {
                let mut last = Value::Undefined;
                for e in exprs {
                    last = self.eval_expr(e, ctx)?;
                }
                Ok(last)
            }
            Expr::Object(entries) => {
                let oid = self.alloc(Object::new(ObjKind::Plain, Some(self.intr.object_proto)));
                for def in entries {
                    let (key_ast, lit_or_none) = match def {
                        PropDef::Data(k, _) => (k, None),
                        PropDef::ProtoData(_) => {
                            return Err(Abrupt::Fatal(
                                "object literal `__proto__` survived to evaluation (parser invariant)"
                                    .to_string(),
                            ))
                        }
                        PropDef::Method(k, lit)
                        | PropDef::Getter(k, lit)
                        | PropDef::Setter(k, lit) => (k, Some(lit)),
                    };
                    // Key evaluation (computed keys in definition order).
                    let key: PropertyKey = match key_ast {
                        ObjKey::Fixed(u) => PropertyKey::Str(u.clone()),
                        ObjKey::Computed(e) => {
                            let v = self.eval_expr(e, ctx)?;
                            self.to_property_key(&v)?
                        }
                    };
                    let name_units = self.prop_key_name(&key);
                    match def {
                        PropDef::ProtoData(_) => unreachable!("checked above"),
                        PropDef::Data(_, ve) => {
                            // NamedEvaluation for computed keys happens at
                            // runtime (fixed keys were inferred at parse).
                            let v = if matches!(key_ast, ObjKey::Computed(_)) {
                                self.eval_named(ve, ctx, &name_units)?
                            } else {
                                self.eval_expr(ve, ctx)?
                            };
                            match &key {
                                PropertyKey::Str(u) => {
                                    self.obj_mut(oid).props.insert(u.clone(), Prop::data(v));
                                }
                                PropertyKey::Sym(s) => {
                                    self.obj_mut(oid).sym_props.insert(*s, Prop::data(v));
                                }
                            }
                        }
                        PropDef::Method(..) => {
                            let lit = lit_or_none.expect("method literal");
                            let f = self.create_method(lit, ctx.env, oid, ctx.priv_env.clone());
                            self.set_fn_name(f, &name_units);
                            let desc = PropDesc {
                                value: Some(Value::Obj(f)),
                                writable: Some(true),
                                enumerable: Some(true),
                                configurable: Some(true),
                                ..PropDesc::default()
                            };
                            self.define_own_property_pk(oid, &key, &desc)?;
                        }
                        PropDef::Getter(..) | PropDef::Setter(..) => {
                            let lit = lit_or_none.expect("accessor literal");
                            let f = self.create_method(lit, ctx.env, oid, ctx.priv_env.clone());
                            let is_get = matches!(def, PropDef::Getter(..));
                            let mut nm = units_from_str(if is_get { "get " } else { "set " });
                            nm.extend_from_slice(&name_units);
                            self.set_fn_name(f, &nm);
                            let desc = if is_get {
                                PropDesc {
                                    get: Some(Some(f)),
                                    enumerable: Some(true),
                                    configurable: Some(true),
                                    ..PropDesc::default()
                                }
                            } else {
                                PropDesc {
                                    set: Some(Some(f)),
                                    enumerable: Some(true),
                                    configurable: Some(true),
                                    ..PropDesc::default()
                                }
                            };
                            self.define_own_property_pk(oid, &key, &desc)?;
                        }
                    }
                }
                Ok(Value::Obj(oid))
            }
            Expr::Function(lit) => {
                let fobj = self.create_function(lit, ctx.env, false, ctx.priv_env.clone());
                Ok(Value::Obj(fobj))
            }
            Expr::Arrow(lit) => {
                // Lexical this/home/ctor-frame captured at creation. An async
                // arrow's [[Prototype]] is %AsyncFunction.prototype%.
                let arrow_proto = if lit.is_async {
                    self.intr.async_function_proto
                } else {
                    self.intr.function_proto
                };
                let fobj = self.alloc(Object::new(
                    ObjKind::Function(FnImpl::Arrow {
                        lit: Rc::clone(lit),
                        env: ctx.env,
                        this_v: Box::new(ctx.this_val.clone()),
                        home: ctx.home_object,
                        frame: ctx.ctor_frame.clone(),
                    }),
                    Some(arrow_proto),
                ));
                let plen = expected_arg_count(lit);
                self.obj_mut(fobj).props.insert(
                    units_from_str("length"),
                    Prop::with_attrs(Value::Num(plen), false, false, true),
                );
                let name = lit.name.clone().unwrap_or_default();
                self.obj_mut(fobj).props.insert(
                    units_from_str("name"),
                    Prop::with_attrs(Value::str_from(&name), false, false, true),
                );
                // An arrow lexically inside a class body captures its
                // PrivateEnvironment (a `#x` reference in an arrow body resolves
                // through the enclosing class).
                if let Some(pe) = &ctx.priv_env {
                    self.fn_priv_env.insert(fobj, Rc::clone(pe));
                }
                Ok(Value::Obj(fobj))
            }
            Expr::PatternAssign { pat, value } => {
                let v = self.eval_expr(value, ctx)?;
                self.destructure(pat, &v, ctx, crate::pattern::BindMode::Assign)?;
                Ok(v)
            }
            Expr::Spread(_) => Err(Abrupt::Fatal(
                "spread element outside an array literal / argument list (parser invariant)"
                    .to_string(),
            )),
            Expr::SpreadTrailingComma => Err(Abrupt::Fatal(
                "spread trailing-comma marker outside an array literal (parser invariant)"
                    .to_string(),
            )),
            Expr::Paren(inner) => self.eval_expr(inner, ctx),
            Expr::Template(parts) => {
                let mut out: Units = Vec::new();
                for part in parts {
                    match part {
                        TplPart::Str(u) => out.extend_from_slice(u),
                        TplPart::Expr(e) => {
                            let v = self.eval_expr(e, ctx)?;
                            let u = self.to_string_units(&v)?;
                            out.extend_from_slice(&u);
                        }
                    }
                    if out.len() > MAX_STRING_UNITS {
                        return Err(Abrupt::Fatal("template result cap exceeded".to_string()));
                    }
                }
                Ok(Value::Str(Rc::new(out)))
            }
            Expr::Class(cl) => self.eval_class(cl, ctx),
            Expr::Member { .. } | Expr::SuperMember { .. } => {
                let r = self.eval_ref(e, ctx)?;
                self.ref_get(&r, ctx)
            }
            Expr::SuperCall { args } => {
                let Some(frame) = ctx.ctor_frame.clone() else {
                    return Err(Abrupt::Fatal(
                        "super() outside a derived constructor (parser invariant)".to_string(),
                    ));
                };
                // 13.3.7.1: arguments evaluate BEFORE the IsConstructor check
                // (perform_super_call re-checks the parent after this).
                let argv = self.eval_argument_list(args, ctx)?;
                self.perform_super_call(&frame, argv)
            }
            Expr::Call { callee, args } => {
                let (fval, this) = match callee.as_ref() {
                    Expr::Member { .. } | Expr::SuperMember { .. } => {
                        let r = self.eval_ref(callee, ctx)?;
                        let f = self.ref_get(&r, ctx)?;
                        let this = match &r {
                            JsRef::Member { base, .. } => base.clone(),
                            JsRef::SuperMember { this_v, .. } => this_v.clone(),
                            JsRef::PrivateMember { base, .. } => base.clone(),
                            JsRef::Env(_) => Value::Undefined,
                        };
                        (f, this)
                    }
                    other => (self.eval_expr(other, ctx)?, Value::Undefined),
                };
                // Direct eval (19.2.1): the callee resolves to an environment
                // reference named `eval` (parentheses are transparent to
                // references) whose value is the %eval% intrinsic. Everything
                // else — `(0,eval)(x)`, `window.eval(x)`, a stored `eval` —
                // is an ordinary (indirect) call.
                let direct_eval = is_direct_eval_callee(callee)
                    && matches!(&fval, Value::Obj(id) if *id == self.intr.eval_fn);
                // A direct eval whose ArgumentList contains a SpreadElement is
                // an engine-divergent corner (V8's `eval(...iter)` differs from
                // the current spec's first-element semantics) — sound-refuse
                // rather than emit a trace that mismatches the oracle.
                if direct_eval && args.iter().any(|a| matches!(a, Expr::Spread(_))) {
                    return Err(Abrupt::Fatal(
                        "direct eval with a spread argument (engine-divergent, out of slice)"
                            .to_string(),
                    ));
                }
                let argv = self.eval_argument_list(args, ctx)?;
                if direct_eval {
                    let x = argv.into_iter().next().unwrap_or(Value::Undefined);
                    return self.perform_eval(x, Some(ctx.clone()), true);
                }
                self.call_value(&fval, this, argv)
            }
            Expr::New { callee, args } => {
                let f = self.eval_expr(callee, ctx)?;
                let argv = self.eval_argument_list(args, ctx)?;
                self.construct(&f, argv)
            }
            Expr::Unary { op, expr } => {
                let v = self.eval_expr(expr, ctx)?;
                match op {
                    UnOp::Not => Ok(Value::Bool(!self.to_boolean(&v))),
                    UnOp::Neg => {
                        // 13.5.4: ToNumeric, then negate in the operand's type.
                        match self.to_numeric(&v)? {
                            Value::BigInt(n) => Ok(Value::bigint(crate::bigint::neg(&n))),
                            Value::Num(n) => Ok(Value::Num(-n)),
                            _ => unreachable!("to_numeric yields Num or BigInt"),
                        }
                    }
                    UnOp::BitNot => {
                        // 13.5.6: ToNumeric, then bitwise NOT in the type.
                        match self.to_numeric(&v)? {
                            Value::BigInt(n) => Ok(Value::bigint(crate::bigint::bitnot(&n))),
                            Value::Num(n) => Ok(Value::Num(f64::from(!to_int32(n)))),
                            _ => unreachable!("to_numeric yields Num or BigInt"),
                        }
                    }
                    UnOp::Pos => {
                        // 13.5.5 unary `+` is ToNumber — a TypeError on a BigInt.
                        let n = self.to_number(&v)?;
                        Ok(Value::Num(n))
                    }
                    UnOp::TypeOf => Ok(Value::str_from(type_of(self, &v))),
                    UnOp::Void => Ok(Value::Undefined),
                }
            }
            Expr::Delete(target) => self.eval_delete(target, ctx),
            Expr::Update {
                inc,
                prefix,
                target,
            } => {
                let r = self.eval_ref_assign(target, ctx)?;
                let old = self.ref_get(&r, ctx)?;
                // 13.4: ToNumeric(old), then ±1 in the operand's type.
                let (newv, oldv) = match self.to_numeric(&old)? {
                    Value::BigInt(n) => {
                        let one = num_bigint::BigInt::from(1);
                        let delta = if *inc {
                            crate::bigint::add(&n, &one)
                        } else {
                            crate::bigint::sub(&n, &one)
                        };
                        (self.big_res(delta)?, Value::BigInt(n))
                    }
                    Value::Num(n) => {
                        let nv = if *inc { n + 1.0 } else { n - 1.0 };
                        (Value::Num(nv), Value::Num(n))
                    }
                    _ => unreachable!("to_numeric yields Num or BigInt"),
                };
                self.ref_set(&r, newv.clone(), ctx)?;
                Ok(if *prefix { newv } else { oldv })
            }
            Expr::Binary { op, left, right } => {
                let l = self.eval_expr(left, ctx)?;
                let r = self.eval_expr(right, ctx)?;
                self.binary_op(*op, &l, &r)
            }
            Expr::Logical { op, left, right } => {
                let l = self.eval_expr(left, ctx)?;
                let lb = self.to_boolean(&l);
                match op {
                    LogOp::And => {
                        if lb {
                            self.eval_expr(right, ctx)
                        } else {
                            Ok(l)
                        }
                    }
                    LogOp::Or => {
                        if lb {
                            Ok(l)
                        } else {
                            self.eval_expr(right, ctx)
                        }
                    }
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
            Expr::PrivateIn { name, obj } => {
                // `#name in obj` (13.10.1): evaluate the object operand, then
                // the brand check (a non-object RHS is a TypeError).
                let base = self.eval_expr(obj, ctx)?;
                let p = self.resolve_private(ctx, name)?;
                Ok(Value::Bool(self.private_has(&base, p)?))
            }
            Expr::Yield { .. } => Err(Abrupt::Fatal(
                // A YieldExpression is only reachable through the generator
                // machine; encountering one in the ordinary tree-walker means
                // a yield in a position the machine could not lower — refuse.
                "yield expression outside the generator machine (unsupported position)".to_string(),
            )),
            Expr::Await(_) => Err(Abrupt::Fatal(
                // An AwaitExpression is only reachable through the async
                // machine; in the ordinary tree-walker it means an await in a
                // position the machine could not lower — refuse soundly.
                "await expression outside the async machine (unsupported position)".to_string(),
            )),
            Expr::Assign { op, target, value } => {
                let r = self.eval_ref_assign(target, ctx)?;
                let result = match op {
                    None => self.eval_expr(value, ctx)?,
                    Some(bop) => {
                        let old = self.ref_get(&r, ctx)?;
                        let rhs = self.eval_expr(value, ctx)?;
                        self.binary_op(*bop, &old, &rhs)?
                    }
                };
                self.ref_set(&r, result.clone(), ctx)?;
                Ok(result)
            }
        }
    }

    /// NamedEvaluation (8.4.5): evaluate an initializer that may be an
    /// anonymous function/class definition, binding `name`. Classes take the
    /// name BEFORE their static members define (a static `name(){}` method
    /// overrides it), via the literal's inferred-name slot.
    pub(crate) fn eval_named(&mut self, e: &Expr, ctx: &Ctx, name: &[u16]) -> ERes {
        match e {
            Expr::Class(cl) if cl.name.is_none() && cl.inferred_name.borrow().is_none() => {
                *cl.inferred_name.borrow_mut() = Some(units_to_lossy(name));
                let r = self.eval_expr(e, ctx);
                *cl.inferred_name.borrow_mut() = None;
                r
            }
            Expr::Function(l) | Expr::Arrow(l) if l.name.is_none() => {
                let v = self.eval_expr(e, ctx)?;
                if let Value::Obj(fo) = &v {
                    self.set_fn_name(*fo, name);
                }
                Ok(v)
            }
            _ => self.eval_expr(e, ctx),
        }
    }

    /// The this binding: a derived-constructor frame reads its cell (TDZ →
    /// ReferenceError); everything else uses the lexical this value.
    pub(crate) fn resolve_this(&mut self, ctx: &Ctx) -> ERes {
        match &ctx.ctor_frame {
            Some(f) => {
                let v = f.cell.borrow().clone();
                match v {
                    Some(v) => Ok(v),
                    None => Err(self.throw_native(NativeErrorKind::ReferenceError)),
                }
            }
            None => Ok(ctx.this_val.clone()),
        }
    }

    /// Build a super-property Reference Record. this-TDZ resolves FIRST (the
    /// spec order, engine-consistent for GetValue/call contexts); an
    /// ASSIGNMENT-flavored computed super key under uninitialized this is
    /// engine-divergent and refuses.
    fn eval_super_ref(
        &mut self,
        prop: &MemberProp,
        ctx: &Ctx,
        assign_flavor: bool,
    ) -> Result<JsRef, Abrupt> {
        let Some(home) = ctx.home_object else {
            return Err(Abrupt::Fatal(
                "super property outside a method (parser invariant)".to_string(),
            ));
        };
        let this_tdz = ctx
            .ctor_frame
            .as_ref()
            .is_some_and(|f| f.cell.borrow().is_none());
        if this_tdz && assign_flavor && matches!(prop, MemberProp::Computed(_)) {
            return Err(Abrupt::Fatal(
                "assignment to a computed super key under uninitialized `this` (engine-divergent order)"
                    .to_string(),
            ));
        }
        let this_v = self.resolve_this(ctx)?; // ReferenceError on TDZ
        let key = match prop {
            MemberProp::Dot(name) => RefKey::Key(units_from_str(name)),
            MemberProp::Computed(ke) => RefKey::Raw(self.eval_expr(ke, ctx)?),
            // `super.#x` is not a valid SuperProperty (parser-rejected).
            MemberProp::Private(_) => {
                return Err(Abrupt::Fatal(
                    "private name on a super reference (parser invariant)".to_string(),
                ))
            }
        };
        Ok(JsRef::SuperMember {
            start: self.obj(home).proto,
            this_v,
            key,
        })
    }

    /// `delete` (13.5.1): member deletes go through [[Delete]] with the
    /// miss-danger discipline; sloppy identifier deletes resolve bindings and
    /// global properties. (Strict identifier deletes were early errors.)
    fn eval_delete(&mut self, target: &Expr, ctx: &Ctx) -> ERes {
        match target {
            Expr::Ident(name) => {
                let mut cur = Some(ctx.env);
                while let Some(e) = cur {
                    if self.envs[e.0 as usize].bindings.contains_key(name) {
                        // Ordinary declarative bindings are not deletable; a
                        // sloppy direct eval's own `var`/function binding is.
                        if self.envs[e.0 as usize].deletable.remove(name) {
                            self.envs[e.0 as usize].bindings.remove(name);
                            return Ok(Value::Bool(true));
                        }
                        return Ok(Value::Bool(false));
                    }
                    cur = self.envs[e.0 as usize].parent;
                }
                let key = units_from_str(name);
                if let Some(p) = self.obj(self.global).props.get(&key) {
                    if p.configurable {
                        self.obj_mut(self.global).props.shift_remove(&key);
                        return Ok(Value::Bool(true));
                    }
                    return Ok(Value::Bool(false));
                }
                Err(Abrupt::Fatal(format!(
                    "delete of unresolved global `{name}` (engine global surface unmodeled)"
                )))
            }
            Expr::Member { obj, prop } => {
                let base = self.eval_expr(obj, ctx)?;
                let raw_key = match prop {
                    MemberProp::Dot(name) => Value::str_from(name),
                    MemberProp::Computed(ke) => self.eval_expr(ke, ctx)?,
                    // `delete obj.#x` is an early SyntaxError (parser-rejected).
                    MemberProp::Private(_) => {
                        return Err(Abrupt::Fatal(
                            "delete of a private reference (parser invariant)".to_string(),
                        ))
                    }
                };
                if matches!(base, Value::Undefined | Value::Null) {
                    return Err(self.throw_native(NativeErrorKind::TypeError));
                }
                let key = self.to_property_key(&raw_key)?;
                let deleted = match (&base, &key) {
                    (Value::Obj(oid), PropertyKey::Str(k)) => self.delete_property(*oid, k)?,
                    (Value::Obj(oid), PropertyKey::Sym(s)) => self.delete_property_sym(*oid, *s)?,
                    (Value::Str(s), PropertyKey::Str(k)) => {
                        // String exotic own: indices and length are
                        // non-configurable; anything else is not own.
                        if units_eq_ascii(k, "length") {
                            false
                        } else if let Some(i) = array_index_of(k) {
                            (i as usize) >= s.len()
                        } else {
                            true
                        }
                    }
                    // Wrappers/primitives have no own properties to delete.
                    _ => true,
                };
                if !deleted && ctx.strict {
                    return Err(self.throw_native(NativeErrorKind::TypeError));
                }
                Ok(Value::Bool(deleted))
            }
            Expr::SuperMember { prop } => {
                // 13.5.1: deleting a super reference throws ReferenceError
                // (after the reference itself evaluates: this-TDZ, then the
                // computed key).
                self.eval_super_ref(prop, ctx, true)?;
                Err(self.throw_native(NativeErrorKind::ReferenceError))
            }
            Expr::Paren(inner) => self.eval_delete(inner, ctx),
            // Not a reference: evaluate for side effects, return true.
            other => {
                self.eval_expr(other, ctx)?;
                Ok(Value::Bool(true))
            }
        }
    }

    // -- references ---------------------------------------------------------

    /// Evaluate a MemberExpression (or identifier) to a Reference Record.
    /// Spec 13.3.2/13.3.3: base and computed-key expressions are evaluated
    /// (left to right), but the base is NOT validated and the key is NOT
    /// coerced here — a null base with a throwing key expression must throw
    /// the key's error, not TypeError.
    pub fn eval_ref(&mut self, e: &Expr, ctx: &Ctx) -> Result<JsRef, Abrupt> {
        self.eval_ref_flavored(e, ctx, false)
    }

    pub fn eval_ref_assign(&mut self, e: &Expr, ctx: &Ctx) -> Result<JsRef, Abrupt> {
        self.eval_ref_flavored(e, ctx, true)
    }

    fn eval_ref_flavored(
        &mut self,
        e: &Expr,
        ctx: &Ctx,
        assign_flavor: bool,
    ) -> Result<JsRef, Abrupt> {
        match e {
            Expr::Ident(name) => Ok(JsRef::Env(name.clone())),
            Expr::Member { obj, prop } => {
                let base = self.eval_expr(obj, ctx)?;
                if let MemberProp::Private(name) = prop {
                    let key = self.resolve_private(ctx, name)?;
                    return Ok(JsRef::PrivateMember { base, key });
                }
                let key = match prop {
                    MemberProp::Dot(name) => RefKey::Key(units_from_str(name)),
                    MemberProp::Computed(ke) => RefKey::Raw(self.eval_expr(ke, ctx)?),
                    MemberProp::Private(_) => unreachable!("handled above"),
                };
                Ok(JsRef::Member { base, key })
            }
            Expr::SuperMember { prop } => self.eval_super_ref(prop, ctx, assign_flavor),
            Expr::Paren(inner) => self.eval_ref_flavored(inner, ctx, assign_flavor),
            _ => Err(Abrupt::Fatal("non-reference assignment target".to_string())),
        }
    }

    /// ToPropertyKey on the [[ReferencedName]]. Reference Records are spec
    /// VALUES: GetValue and PutValue each coerce a raw computed key, so a
    /// compound assignment / update runs the key's toString TWICE (verified
    /// against Node: `o[p] += 1` → 2 coercions; `o[p] = v` → 1).
    fn resolve_ref_key(&mut self, key: &RefKey) -> Result<PropertyKey, Abrupt> {
        match key {
            RefKey::Key(u) => Ok(PropertyKey::Str(u.clone())),
            RefKey::Raw(v) => {
                let raw = v.clone();
                self.to_property_key(&raw)
            }
        }
    }

    /// GetValue (6.2.5.5): ToObject(base) — a TypeError for null/undefined —
    /// happens BEFORE ToPropertyKey of a not-yet-coerced key.
    pub fn ref_get(&mut self, r: &JsRef, ctx: &Ctx) -> ERes {
        match r {
            JsRef::Env(name) => {
                let name = name.clone();
                self.env_get(ctx, &name)
            }
            JsRef::Member { base, key } => {
                let base = base.clone();
                if matches!(base, Value::Undefined | Value::Null) {
                    return Err(self.throw_native(NativeErrorKind::TypeError));
                }
                let k = self.resolve_ref_key(key)?;
                self.get_prop_value_pk(&base, &k)
            }
            JsRef::SuperMember { start, this_v, key } => {
                let (start, this_v) = (*start, this_v.clone());
                // An absent super base (extends-null prototype chains) is a
                // TypeError before the key coerces, like a null member base.
                let Some(start) = start else {
                    return Err(self.throw_native(NativeErrorKind::TypeError));
                };
                match self.resolve_ref_key(key)? {
                    PropertyKey::Str(k) => self.get_with_receiver(start, &k, this_v),
                    PropertyKey::Sym(s) => self.get_with_receiver_sym(start, s, this_v),
                }
            }
            JsRef::PrivateMember { base, key } => {
                let (base, key) = (base.clone(), *key);
                self.private_get(&base, key)
            }
        }
    }

    /// PutValue (6.2.5.6): same ToObject-before-ToPropertyKey order.
    pub fn ref_set(&mut self, r: &JsRef, v: Value, ctx: &Ctx) -> Result<(), Abrupt> {
        match r {
            JsRef::Env(name) => {
                let name = name.clone();
                self.env_set(ctx, &name, v)
            }
            JsRef::Member { base, key } => {
                let base = base.clone();
                if matches!(base, Value::Undefined | Value::Null) {
                    return Err(self.throw_native(NativeErrorKind::TypeError));
                }
                let k = self.resolve_ref_key(key)?;
                self.set_prop_value_pk(&base, &k, v, ctx.strict)
            }
            JsRef::SuperMember { start, this_v, key } => {
                let (start, this_v) = (*start, this_v.clone());
                let Some(start) = start else {
                    return Err(self.throw_native(NativeErrorKind::TypeError));
                };
                match self.resolve_ref_key(key)? {
                    PropertyKey::Str(k) => self.super_set(start, &k, v, &this_v, ctx.strict),
                    PropertyKey::Sym(_) => Err(Abrupt::Fatal(
                        "assignment to a symbol-keyed super property (out of slice)".to_string(),
                    )),
                }
            }
            JsRef::PrivateMember { base, key } => {
                let (base, key) = (base.clone(), *key);
                self.private_set(&base, key, v)
            }
        }
    }

    // -- identifier resolution ---------------------------------------------

    pub fn env_get(&mut self, ctx: &Ctx, name: &str) -> ERes {
        let mut cur = Some(ctx.env);
        while let Some(e) = cur {
            if let Some(b) = self.envs[e.0 as usize].bindings.get(name) {
                if !b.initialized {
                    return Err(self.throw_native(NativeErrorKind::ReferenceError));
                }
                return Ok(b.value.clone());
            }
            cur = self.envs[e.0 as usize].parent;
        }
        let key = units_from_str(name);
        if let Some(p) = self.obj(self.global).props.get(&key) {
            if let Some(v) = p.data_value() {
                return Ok(v.clone());
            }
        }
        Err(Abrupt::Fatal(format!(
            "unresolved identifier `{name}` (unmodeled global or real ReferenceError)"
        )))
    }

    pub fn env_set(&mut self, ctx: &Ctx, name: &str, v: Value) -> Result<(), Abrupt> {
        let mut cur = Some(ctx.env);
        while let Some(e) = cur {
            if let Some(b) = self.envs[e.0 as usize].bindings.get_mut(name) {
                if !b.initialized {
                    return Err(self.throw_native(NativeErrorKind::ReferenceError));
                }
                if !b.mutable {
                    // SetMutableBinding on an immutable binding: `const`
                    // always throws; the sloppy named-function-expression
                    // self-binding throws only when the ASSIGNING code is
                    // strict — otherwise the write is silently ignored.
                    if b.fn_name_immutable && !ctx.strict {
                        return Ok(());
                    }
                    return Err(self.throw_native(NativeErrorKind::TypeError));
                }
                b.value = v;
                return Ok(());
            }
            cur = self.envs[e.0 as usize].parent;
        }
        let key = units_from_str(name);
        if let Some(p) = self.obj_mut(self.global).props.get_mut(&key) {
            match &mut p.val {
                PropVal::Data { value, writable } => {
                    if *writable {
                        *value = v;
                        p.synthetic = false;
                    } else if ctx.strict {
                        return Err(self.throw_native(NativeErrorKind::TypeError));
                    }
                    return Ok(());
                }
                PropVal::Accessor { .. } => {
                    return Err(Abrupt::Fatal(
                        "accessor property on the global object (out of slice)".to_string(),
                    ));
                }
            }
        }
        if ctx.strict {
            return Err(Abrupt::Fatal(format!(
                "strict assignment to unresolved `{name}` (unmodeled global or real ReferenceError)"
            )));
        }
        self.obj_mut(self.global).props.insert(key, Prop::data(v));
        Ok(())
    }

    // -- property access ----------------------------------------------------

    pub fn get_prop_value(&mut self, base: &Value, key: &Units) -> ERes {
        match base {
            Value::Obj(oid) => self.get_with_receiver(*oid, key, base.clone()),
            Value::Str(s) => {
                if units_eq_ascii(key, "length") {
                    #[allow(clippy::cast_precision_loss)] // capped well below 2^53
                    return Ok(Value::Num(s.len() as f64));
                }
                if let Some(i) = array_index_of(key) {
                    let i = i as usize;
                    if i < s.len() {
                        return Ok(Value::Str(Rc::new(vec![s[i]])));
                    }
                    return Ok(Value::Undefined);
                }
                // Everything else resolves through String.prototype.
                self.get_with_receiver(self.intr.string_proto, key, base.clone())
            }
            // Number/Boolean primitives: the virtual wrapper has no own
            // properties; everything resolves through the prototype.
            Value::Num(_) => {
                self.get_with_receiver(self.intr.number_proto, key, base.clone())
            }
            Value::BigInt(_) => {
                self.get_with_receiver(self.intr.bigint_proto, key, base.clone())
            }
            Value::Bool(_) => {
                self.get_with_receiver(self.intr.boolean_proto, key, base.clone())
            }
            Value::Sym(_) => {
                self.get_with_receiver(self.intr.symbol_proto, key, base.clone())
            }
            Value::Undefined | Value::Null => {
                Err(self.throw_native(NativeErrorKind::TypeError))
            }
        }
    }

    /// Refusal reason when a real engine could have `name` as an OWN property
    /// of `o` that our model does not carry. A miss at `o` (during a get, a
    /// has, or a set walk) is then unsound to answer: the real engine may
    /// find a value HERE, before our chain would provide one further up
    /// (e.g. an unmodeled `Array.prototype.toLocaleString` masking into
    /// `Object.prototype.toLocaleString`). Checked PER OBJECT on every chain
    /// walk, never only on a whole-chain miss.
    pub(crate) fn own_miss_gap(&self, o: ObjId, name: &str) -> Option<String> {
        if o == self.global {
            return Some(format!(
                "global-object property miss `{name}` (engine global surface unmodeled)"
            ));
        }
        if matches!(self.obj(o).kind, ObjKind::Error) && name == "stack" {
            return Some("error instance `stack` (engine-specific)".to_string());
        }
        // Sloppy-mode user functions carry legacy own `caller`/`arguments`
        // properties in real engines (non-spec surface, observed on V8) —
        // but method-class functions (accessors) do not.
        if (name == "caller" || name == "arguments")
            && matches!(
                &self.obj(o).kind,
                ObjKind::Function(FnImpl::User { lit, .. }) if !lit.strict && !lit.is_method
            )
        {
            return Some(format!(
                "sloppy function legacy own `{name}` (engine surface, non-spec)"
            ));
        }
        self.intr
            .danger_reason(o, name)
            .map(|danger| format!("unimplemented intrinsic property `{name}` ({danger})"))
    }

    pub(crate) fn get_from_object(&mut self, oid: ObjId, key: &Units) -> ERes {
        self.get_with_receiver(oid, key, Value::Obj(oid))
    }

    /// OrdinaryGet (10.1.8.1) with an explicit receiver: accessor getters run
    /// with the original receiver `this`.
    pub(crate) fn get_with_receiver(&mut self, oid: ObjId, key: &Units, receiver: Value) -> ERes {
        let name = units_to_lossy(key);
        let mut cur = Some(oid);
        let mut hops = 0;
        while let Some(o) = cur {
            if hops >= 64 {
                return Err(Abrupt::Fatal("prototype chain too deep".to_string()));
            }
            // A proxy in the chain (the receiver itself, or a proxy used as a
            // prototype) routes the whole [[Get]] through its trap.
            if matches!(self.obj(o).kind, ObjKind::Proxy { .. }) {
                return self.mop_get(o, &crate::value::PropertyKey::Str(key.clone()), receiver);
            }
            // Integer-indexed exotic [[Get]] (23.2.3.x): a canonical numeric
            // index yields the element (or undefined out of range) WITHOUT
            // consulting the prototype.
            if matches!(self.obj(o).kind, ObjKind::TypedArray { .. }) {
                if let Some(n) = crate::typedarray::canonical_numeric_index(key) {
                    return Ok(self.ta_element_get(o, n));
                }
            }
            if let Some(p) = self.own_prop_resolved(o, key) {
                if p.synthetic {
                    return Err(Abrupt::Fatal(
                        "read of engine-specific error message text".to_string(),
                    ));
                }
                return match p.val {
                    PropVal::Data { value, .. } => Ok(value),
                    PropVal::Accessor { get: None, .. } => Ok(Value::Undefined),
                    PropVal::Accessor { get: Some(g), .. } => {
                        self.call_function(g, receiver, Vec::new(), false)
                    }
                };
            }
            if let Some(gap) = self.own_miss_gap(o, &name) {
                return Err(Abrupt::Fatal(gap));
            }
            cur = self.obj(o).proto;
            hops += 1;
        }
        Ok(Value::Undefined)
    }

    /// Spec HasProperty (7.3.12): chain walk with the same per-object miss
    /// discipline as [[Get]] — a hole can only be reported where the model is
    /// complete for that object.
    pub(crate) fn has_property_checked(&self, oid: ObjId, key: &Units) -> Result<bool, Abrupt> {
        let name = units_to_lossy(key);
        let mut cur = Some(oid);
        let mut hops = 0;
        while let Some(o) = cur {
            if hops >= 64 {
                return Err(Abrupt::Fatal("prototype chain too deep".to_string()));
            }
            // A proxy reached through this read-only walk needs its trap (the
            // mutable path); refuse soundly rather than bypass it.
            if matches!(self.obj(o).kind, ObjKind::Proxy { .. }) {
                return Err(Abrupt::Fatal(
                    "HasProperty reaches a proxy in the prototype chain (needs trap routing)"
                        .to_string(),
                ));
            }
            // Integer-indexed exotic [[HasProperty]]: a canonical numeric index
            // is present iff it is a valid in-bounds index (never consults the
            // prototype).
            if matches!(self.obj(o).kind, ObjKind::TypedArray { .. }) {
                if let Some(n) = crate::typedarray::canonical_numeric_index(key) {
                    let f = self.ta_fields(o).expect("typed array");
                    return Ok(self.ta_valid_index(f, n).is_some());
                }
            }
            if self.obj(o).props.contains_key(key) {
                return Ok(true);
            }
            if let Some(gap) = self.own_miss_gap(o, &name) {
                return Err(Abrupt::Fatal(gap));
            }
            cur = self.obj(o).proto;
            hops += 1;
        }
        Ok(false)
    }

    pub fn set_prop_value(
        &mut self,
        base: &Value,
        key: &Units,
        v: Value,
        strict: bool,
    ) -> Result<(), Abrupt> {
        match base {
            Value::Obj(oid) => self.set_on_object(*oid, key, v, strict),
            Value::Str(s) => {
                // String exotic own index/length: non-writable → the set
                // fails without consulting the prototype.
                if units_eq_ascii(key, "length")
                    || array_index_of(key).is_some_and(|i| (i as usize) < s.len())
                {
                    return self.set_reject(strict);
                }
                // Otherwise the prototype chain governs (a setter there runs
                // with the primitive receiver); a data hit or chain end
                // fails: CreateDataProperty on a primitive receiver is false.
                self.set_walk_chain(Some(self.intr.string_proto), key, v, strict, base.clone(), None)
            }
            Value::Num(_) | Value::Bool(_) => {
                // The virtual wrapper has no own properties; a setter on the
                // (danger-listed) prototype chain runs with the primitive
                // receiver, and creation on the wrapper always fails.
                let start = if matches!(base, Value::Num(_)) {
                    self.intr.number_proto
                } else {
                    self.intr.boolean_proto
                };
                self.set_walk_chain(Some(start), key, v, strict, base.clone(), None)
            }
            Value::Sym(_) => {
                self.set_walk_chain(Some(self.intr.symbol_proto), key, v, strict, base.clone(), None)
            }
            Value::BigInt(_) => {
                self.set_walk_chain(Some(self.intr.bigint_proto), key, v, strict, base.clone(), None)
            }
            Value::Undefined | Value::Null => {
                Err(self.throw_native(NativeErrorKind::TypeError))
            }
        }
    }

    pub(crate) fn set_reject(&mut self, strict: bool) -> Result<(), Abrupt> {
        if strict {
            Err(self.throw_native(NativeErrorKind::TypeError))
        } else {
            Ok(())
        }
    }

    /// OrdinarySet (10.1.9) on an object receiver.
    pub(crate) fn set_on_object(
        &mut self,
        oid: ObjId,
        key: &Units,
        v: Value,
        strict: bool,
    ) -> Result<(), Abrupt> {
        // A proxy receiver routes the whole [[Set]] through its trap; a false
        // result is the ordinary set-reject.
        if matches!(self.obj(oid).kind, ObjKind::Proxy { .. }) {
            let ok = self.mop_set(
                oid,
                &crate::value::PropertyKey::Str(key.clone()),
                v,
                Value::Obj(oid),
            )?;
            return if ok { Ok(()) } else { self.set_reject(strict) };
        }
        // Integer-indexed exotic [[Set]] (23.2.3.x): a canonical numeric index
        // coerces the value (ToNumber — side effects observable) then stores it
        // only for a valid in-bounds index; the set always "succeeds".
        if matches!(self.obj(oid).kind, ObjKind::TypedArray { .. }) {
            if let Some(n) = crate::typedarray::canonical_numeric_index(key) {
                self.ta_element_set(oid, n, v)?;
                return Ok(());
            }
        }
        // Array length writes: OrdinarySet's own-descriptor writability check
        // comes FIRST (a non-writable length rejects before ANY coercion of
        // the value — its valueOf never runs), then [[DefineOwnProperty]]
        // routes through ArraySetLength.
        if matches!(self.obj(oid).kind, ObjKind::Array) && units_eq_ascii(key, "length") {
            let (_, len_writable) = self.array_length_state(oid);
            if !len_writable {
                return self.set_reject(strict);
            }
            let ok = self.array_set_length(oid, &PropDesc::data(v))?;
            if !ok {
                return self.set_reject(strict);
            }
            return Ok(());
        }
        // Own descriptor on the receiver decides directly.
        if let Some(p) = self.obj(oid).props.get(key) {
            match &p.val {
                PropVal::Data { writable, .. } => {
                    if !*writable {
                        return self.set_reject(strict);
                    }
                    if let Some((env, name)) = self.args_mapped_name(oid, key) {
                        self.set_binding_value(env, &name, v.clone());
                    }
                    let p = self.obj_mut(oid).props.get_mut(key).expect("own hit");
                    if let PropVal::Data { value, .. } = &mut p.val {
                        *value = v;
                    }
                    p.synthetic = false;
                    return Ok(());
                }
                PropVal::Accessor { set, .. } => {
                    return match *set {
                        Some(s) => {
                            self.call_function(s, Value::Obj(oid), vec![v], false)?;
                            Ok(())
                        }
                        None => self.set_reject(strict),
                    };
                }
            }
        }
        // Own miss on the receiver: refuse if the real engine may hold an
        // unmodeled own property here (its attributes or accessor behavior
        // would govern the set). The global object is exempt: it takes fresh
        // data properties like the sloppy `x = 1` fallback in env_set, and
        // its unmodeled real surface stays refused at every read.
        let name = units_to_lossy(key);
        if oid != self.global
            && let Some(gap) = self.own_miss_gap(oid, &name)
        {
            return Err(Abrupt::Fatal(format!("set: {gap}")));
        }
        let proto = self.obj(oid).proto;
        self.set_walk_chain(proto, key, v, strict, Value::Obj(oid), Some(oid))
    }

    /// The prototype-chain half of OrdinarySet: find the controlling
    /// descriptor; a setter runs with `receiver`; a writable data property or
    /// chain end creates a fresh data property on `create_on` (None = the
    /// receiver is a primitive: creation fails).
    fn set_walk_chain(
        &mut self,
        start: Option<ObjId>,
        key: &Units,
        v: Value,
        strict: bool,
        receiver: Value,
        create_on: Option<ObjId>,
    ) -> Result<(), Abrupt> {
        let name = units_to_lossy(key);
        let mut cur = start;
        let mut hops = 0;
        while let Some(o) = cur {
            if hops >= 64 {
                return Err(Abrupt::Fatal("prototype chain too deep".to_string()));
            }
            // A proxy in the prototype chain routes the [[Set]] through its
            // trap with the ORIGINAL receiver.
            if matches!(self.obj(o).kind, ObjKind::Proxy { .. }) {
                let ok = self.mop_set(
                    o,
                    &crate::value::PropertyKey::Str(key.clone()),
                    v,
                    receiver,
                )?;
                return if ok { Ok(()) } else { self.set_reject(strict) };
            }
            // Integer-indexed exotic [[Set]] (23.2.3.x) reached through the
            // prototype chain (Receiver != O): a canonical numeric index never
            // consults the ordinary prototype. A VALID index is a writable own
            // data property that shadows below (the write lands on the
            // receiver, uncoerced); any other canonical numeric index is a
            // no-op that returns true — it must NOT fall through to a
            // %TypedArray%.prototype accessor.
            if matches!(self.obj(o).kind, ObjKind::TypedArray { .. }) {
                if let Some(n) = crate::typedarray::canonical_numeric_index(key) {
                    let f = self.ta_fields(o).expect("ta");
                    if self.ta_valid_index(f, n).is_some() {
                        break; // valid own data index: shadow below → create on receiver
                    }
                    return Ok(()); // canonical numeric but invalid: [[Set]] no-op
                }
            }
            if let Some(p) = self.obj(o).props.get(key) {
                match &p.val {
                    PropVal::Data { writable, .. } => {
                        if !*writable {
                            return self.set_reject(strict);
                        }
                        break; // writable inherited data prop: shadow below
                    }
                    PropVal::Accessor { set, .. } => {
                        return match *set {
                            Some(s) => {
                                self.call_function(s, receiver, vec![v], false)?;
                                Ok(())
                            }
                            None => self.set_reject(strict),
                        };
                    }
                }
            }
            if let Some(gap) = self.own_miss_gap(o, &name) {
                return Err(Abrupt::Fatal(format!("set: {gap}")));
            }
            cur = self.obj(o).proto;
            hops += 1;
        }
        let Some(target) = create_on else {
            return self.set_reject(strict);
        };
        // CreateDataProperty on the receiver, honoring extensibility and the
        // array index/length exotic semantics.
        if !self.obj(target).extensible {
            return self.set_reject(strict);
        }
        if matches!(self.obj(target).kind, ObjKind::Array) {
            if let Some(i) = array_index_of(key) {
                let (len, len_writable) = self.array_length_state(target);
                if i >= len && !len_writable {
                    return self.set_reject(strict);
                }
                self.obj_mut(target).props.insert(key.clone(), Prop::data(v));
                if i >= len {
                    self.set_array_length_raw(target, f64::from(i) + 1.0);
                }
                return Ok(());
            }
        }
        self.obj_mut(target).props.insert(key.clone(), Prop::data(v));
        Ok(())
    }

    /// OrdinarySet where the walk starts at the super base and the receiver
    /// is the method's `this` (10.1.9.2 with Receiver != O): the controlling
    /// descriptor comes from the chain; the write lands on the receiver via
    /// its [[DefineOwnProperty]] (attribute-validated, exotic-aware).
    pub(crate) fn super_set(
        &mut self,
        start: ObjId,
        key: &Units,
        v: Value,
        receiver: &Value,
        strict: bool,
    ) -> Result<(), Abrupt> {
        let name = units_to_lossy(key);
        let mut cur = Some(start);
        let mut hops = 0;
        while let Some(o) = cur {
            if hops >= 64 {
                return Err(Abrupt::Fatal("prototype chain too deep".to_string()));
            }
            if let Some(p) = self.obj(o).props.get(key) {
                match &p.val {
                    PropVal::Data { writable, .. } => {
                        if !*writable {
                            return self.set_reject(strict);
                        }
                        break; // write through to the receiver
                    }
                    PropVal::Accessor { set, .. } => {
                        return match *set {
                            Some(s) => {
                                self.call_function(s, receiver.clone(), vec![v], false)?;
                                Ok(())
                            }
                            None => self.set_reject(strict),
                        };
                    }
                }
            }
            if let Some(gap) = self.own_miss_gap(o, &name) {
                return Err(Abrupt::Fatal(format!("super set: {gap}")));
            }
            cur = self.obj(o).proto;
            hops += 1;
        }
        let Value::Obj(target) = receiver else {
            return self.set_reject(strict); // primitive receiver: no create
        };
        let target = *target;
        // Receiver write-back per OrdinarySetWithOwnDescriptor steps 2-3.
        if let Some(existing) = self.obj(target).props.get(key) {
            match &existing.val {
                PropVal::Accessor { .. } => return self.set_reject(strict),
                PropVal::Data { writable, .. } => {
                    if !*writable {
                        return self.set_reject(strict);
                    }
                }
            }
            let ok = self.define_own_property(target, key, &PropDesc::data(v))?;
            if !ok {
                return self.set_reject(strict);
            }
            return Ok(());
        }
        if let Some(gap) = self.own_miss_gap(target, &name) {
            return Err(Abrupt::Fatal(format!("super set: {gap}")));
        }
        let desc = PropDesc {
            value: Some(v),
            writable: Some(true),
            enumerable: Some(true),
            configurable: Some(true),
            ..PropDesc::default()
        };
        let ok = self.define_own_property(target, key, &desc)?;
        if !ok {
            return self.set_reject(strict);
        }
        Ok(())
    }

    // -- private elements ---------------------------------------------------

    /// Allocate a fresh PrivateName (a distinct brand per ClassDefinition-
    /// Evaluation).
    pub(crate) fn alloc_priv_name(&mut self) -> crate::value::PrivName {
        let n = crate::value::PrivName(self.next_priv_name);
        self.next_priv_name += 1;
        n
    }

    /// Resolve a `#name` reference through the running PrivateEnvironment
    /// (9.4). The parser's AllPrivateIdentifiersValid guarantees a binding
    /// exists; a miss is a parser invariant break (refuse).
    pub(crate) fn resolve_private(
        &self,
        ctx: &Ctx,
        name: &str,
    ) -> Result<crate::value::PrivName, Abrupt> {
        let mut cur = ctx.priv_env.clone();
        while let Some(frame) = cur {
            if let Some(p) = frame.names.get(name) {
                return Ok(*p);
            }
            cur = frame.parent.clone();
        }
        Err(Abrupt::Fatal(format!(
            "private name `#{name}` unresolved at runtime (no PrivateEnvironment binding)"
        )))
    }

    /// PrivateElementFind (6.2.14.1): the index of the element keyed by `p`.
    fn private_find(&self, oid: ObjId, p: crate::value::PrivName) -> Option<usize> {
        self.obj(oid).priv_elems.iter().position(|e| e.key == p)
    }

    /// PrivateGet (6.2.14.4): read a private field/method/accessor. A base
    /// that is not an object, or lacks the brand, is a TypeError.
    pub(crate) fn private_get(&mut self, base: &Value, p: crate::value::PrivName) -> ERes {
        let Value::Obj(oid) = base else {
            return Err(self.throw_native(NativeErrorKind::TypeError));
        };
        let oid = *oid;
        let Some(i) = self.private_find(oid, p) else {
            return Err(self.throw_native(NativeErrorKind::TypeError));
        };
        match self.obj(oid).priv_elems[i].kind.clone() {
            crate::value::PrivElemKind::Field(v) => Ok(v),
            crate::value::PrivElemKind::Method(f) => Ok(Value::Obj(f)),
            crate::value::PrivElemKind::Accessor { get, .. } => match get {
                Some(g) => self.call_function(g, base.clone(), Vec::new(), false),
                None => Err(self.throw_native(NativeErrorKind::TypeError)),
            },
        }
    }

    /// PrivateSet (6.2.14.5): write a private field or invoke a private setter.
    /// A private method target, a missing setter, or a non-branded/non-object
    /// base is a TypeError.
    pub(crate) fn private_set(
        &mut self,
        base: &Value,
        p: crate::value::PrivName,
        v: Value,
    ) -> Result<(), Abrupt> {
        let Value::Obj(oid) = base else {
            return Err(self.throw_native(NativeErrorKind::TypeError));
        };
        let oid = *oid;
        let Some(i) = self.private_find(oid, p) else {
            return Err(self.throw_native(NativeErrorKind::TypeError));
        };
        match self.obj(oid).priv_elems[i].kind.clone() {
            crate::value::PrivElemKind::Field(_) => {
                self.obj_mut(oid).priv_elems[i].kind = crate::value::PrivElemKind::Field(v);
                Ok(())
            }
            crate::value::PrivElemKind::Method(_) => {
                Err(self.throw_native(NativeErrorKind::TypeError))
            }
            crate::value::PrivElemKind::Accessor { set, .. } => match set {
                Some(s) => {
                    self.call_function(s, base.clone(), vec![v], false)?;
                    Ok(())
                }
                None => Err(self.throw_native(NativeErrorKind::TypeError)),
            },
        }
    }

    /// PrivateFieldAdd (6.2.14.2): append a private field; the "add a private
    /// field twice" TypeError fires if the object already carries the brand.
    pub(crate) fn private_field_add(
        &mut self,
        oid: ObjId,
        p: crate::value::PrivName,
        v: Value,
    ) -> Result<(), Abrupt> {
        if self.private_find(oid, p).is_some() {
            return Err(self.throw_native(NativeErrorKind::TypeError));
        }
        self.obj_mut(oid).priv_elems.push(crate::value::PrivateElement {
            key: p,
            kind: crate::value::PrivElemKind::Field(v),
        });
        Ok(())
    }

    /// PrivateMethodOrAccessorAdd (6.2.14.3): brand the object with a shared
    /// private method/accessor element (double-branding is a TypeError).
    pub(crate) fn private_method_add(
        &mut self,
        oid: ObjId,
        elem: crate::value::PrivateElement,
    ) -> Result<(), Abrupt> {
        if self.private_find(oid, elem.key).is_some() {
            return Err(self.throw_native(NativeErrorKind::TypeError));
        }
        self.obj_mut(oid).priv_elems.push(elem);
        Ok(())
    }

    /// The `#name in obj` brand check (13.10.1): a non-object RHS is a
    /// TypeError; otherwise PrivateElementFind is-not-empty.
    pub(crate) fn private_has(
        &mut self,
        base: &Value,
        p: crate::value::PrivName,
    ) -> Result<bool, Abrupt> {
        let Value::Obj(oid) = base else {
            return Err(self.throw_native(NativeErrorKind::TypeError));
        };
        Ok(self.private_find(*oid, p).is_some())
    }

    // -- arrays -------------------------------------------------------------

    pub fn new_array(&mut self, _cap: usize) -> ObjId {
        let oid = self.alloc(Object::new(ObjKind::Array, Some(self.intr.array_proto)));
        self.obj_mut(oid).props.insert(
            units_from_str("length"),
            Prop::with_attrs(Value::Num(0.0), true, false, false),
        );
        oid
    }

    pub fn set_array_length_raw(&mut self, oid: ObjId, len: f64) {
        let key = units_from_str("length");
        if let Some(p) = self.obj_mut(oid).props.get_mut(&key) {
            if let PropVal::Data { value, .. } = &mut p.val {
                *value = Value::Num(len);
            }
        } else {
            self.obj_mut(oid)
                .props
                .insert(key, Prop::with_attrs(Value::Num(len), true, false, false));
        }
    }

    // -- functions ----------------------------------------------------------

    /// Instantiate a function literal. `is_decl` suppresses the named
    /// function-expression self-binding scope. `priv_env` is the lexical
    /// PrivateEnvironment captured (functions defined inside a class body see
    /// its private names).
    pub fn create_function(
        &mut self,
        lit: &Rc<FuncLit>,
        env: EnvId,
        is_decl: bool,
        priv_env: Option<Rc<crate::interp::PrivEnvFrame>>,
    ) -> ObjId {
        let needs_self_binding = !is_decl && lit.name.is_some() && !lit.inferred_name;
        let closure_env = if needs_self_binding {
            self.alloc_env(Some(env))
        } else {
            env
        };
        // A generator function's [[Prototype]] is %GeneratorFunction.prototype%;
        // an async function's is %AsyncFunction.prototype%.
        let fn_proto = if lit.is_generator {
            self.intr.generator_function_proto
        } else if lit.is_async {
            self.intr.async_function_proto
        } else {
            self.intr.function_proto
        };
        let fobj = self.alloc(Object::new(
            ObjKind::Function(FnImpl::User {
                lit: Rc::clone(lit),
                env: closure_env,
                home: None,
            }),
            Some(fn_proto),
        ));
        if needs_self_binding {
            self.envs[closure_env.0 as usize].bindings.insert(
                lit.name.clone().expect("checked"),
                Binding {
                    value: Value::Obj(fobj),
                    mutable: false,
                    initialized: true,
                    // CreateImmutableBinding(name, false): sloppy assignment
                    // to the function-expression name is a silent no-op.
                    fn_name_immutable: true,
                },
            );
        }
        // Spec creation order (OrdinaryFunctionCreate → SetFunctionLength,
        // then SetFunctionName, then MakeConstructor): length, name,
        // prototype.
        let plen = expected_arg_count(lit);
        self.obj_mut(fobj).props.insert(
            units_from_str("length"),
            Prop::with_attrs(Value::Num(plen), false, false, true),
        );
        let name = lit.name.clone().unwrap_or_default();
        self.obj_mut(fobj).props.insert(
            units_from_str("name"),
            Prop::with_attrs(Value::str_from(&name), false, false, true),
        );
        if lit.is_generator {
            // A generator function's `.prototype` inherits %GeneratorPrototype%
            // and carries NO `constructor` back-reference; it is
            // {writable, ~enumerable, ~configurable}.
            let proto_obj =
                self.alloc(Object::new(ObjKind::Plain, Some(self.intr.generator_proto)));
            self.obj_mut(fobj).props.insert(
                units_from_str("prototype"),
                Prop::with_attrs(Value::Obj(proto_obj), true, false, false),
            );
        } else if !lit.is_method && !lit.is_async {
            // .prototype object with .constructor back-reference — but NOT for
            // MethodDefinition functions (accessors) or async functions: no
            // MakeConstructor.
            let proto_obj = self.alloc(Object::new(ObjKind::Plain, Some(self.intr.object_proto)));
            self.obj_mut(proto_obj).props.insert(
                units_from_str("constructor"),
                Prop::with_attrs(Value::Obj(fobj), true, false, true),
            );
            self.obj_mut(fobj).props.insert(
                units_from_str("prototype"),
                Prop::with_attrs(Value::Obj(proto_obj), true, false, false),
            );
        }
        if let Some(pe) = priv_env {
            self.fn_priv_env.insert(fobj, pe);
        }
        fobj
    }

    /// A class method/accessor function: like create_function for an
    /// is_method literal, with the [[HomeObject]] recorded.
    pub(crate) fn create_method(
        &mut self,
        lit: &Rc<FuncLit>,
        env: EnvId,
        home: ObjId,
        priv_env: Option<Rc<crate::interp::PrivEnvFrame>>,
    ) -> ObjId {
        // An async method's [[Prototype]] is %AsyncFunction.prototype%; a
        // generator method's is %GeneratorFunction.prototype%; a plain
        // method's is %Function.prototype%.
        let fn_proto = if lit.is_generator {
            self.intr.generator_function_proto
        } else if lit.is_async {
            self.intr.async_function_proto
        } else {
            self.intr.function_proto
        };
        let fobj = self.alloc(Object::new(
            ObjKind::Function(FnImpl::User {
                lit: Rc::clone(lit),
                env,
                home: Some(home),
            }),
            Some(fn_proto),
        ));
        let plen = expected_arg_count(lit);
        self.obj_mut(fobj).props.insert(
            units_from_str("length"),
            Prop::with_attrs(Value::Num(plen), false, false, true),
        );
        self.obj_mut(fobj).props.insert(
            units_from_str("name"),
            Prop::with_attrs(Value::str_from(""), false, false, true),
        );
        // A generator METHOD still has a `.prototype` (unlike ordinary
        // methods), inheriting %GeneratorPrototype%, with no `constructor`.
        if lit.is_generator {
            let proto_obj =
                self.alloc(Object::new(ObjKind::Plain, Some(self.intr.generator_proto)));
            self.obj_mut(fobj).props.insert(
                units_from_str("prototype"),
                Prop::with_attrs(Value::Obj(proto_obj), true, false, false),
            );
        }
        if let Some(pe) = priv_env {
            self.fn_priv_env.insert(fobj, pe);
        }
        fobj
    }

    /// CreateMappedArgumentsObject / CreateUnmappedArgumentsObject (10.4.4).
    fn create_arguments_object(
        &mut self,
        lit: &FuncLit,
        fenv: EnvId,
        fid: ObjId,
        args: &[Value],
    ) -> ObjId {
        let mut map: Vec<Option<String>> = vec![None; args.len()];
        if !lit.strict && lit.simple_params {
            for i in 0..lit.params.len().min(args.len()) {
                if let crate::ast::BindTarget::Name(n) = &lit.params[i].target {
                    map[i] = Some(n.clone());
                }
            }
        }
        let ao = self.alloc(Object::new(
            ObjKind::Arguments(ArgsMap { env: fenv, map }),
            Some(self.intr.object_proto),
        ));
        for (i, v) in args.iter().enumerate() {
            self.obj_mut(ao)
                .props
                .insert(units_from_str(&i.to_string()), Prop::data(v.clone()));
        }
        #[allow(clippy::cast_precision_loss)]
        let len = args.len() as f64;
        self.obj_mut(ao).props.insert(
            units_from_str("length"),
            Prop::with_attrs(Value::Num(len), true, false, true),
        );
        // @@iterator = %Array.prototype.values% (writable, non-enumerable,
        // configurable) per CreateMapped/UnmappedArgumentsObject (10.4.4.6-7).
        let iter_sid = self.intr.wk(crate::builtins::WK_ITERATOR);
        if let Some(vf) = self
            .obj(self.intr.array_proto)
            .sym_props
            .get(&iter_sid)
            .and_then(|p| p.data_value().cloned())
        {
            self.obj_mut(ao)
                .sym_props
                .insert(iter_sid, Prop::with_attrs(vf, true, false, true));
        }
        if lit.strict {
            let tte = self.intr.throw_type_error;
            self.obj_mut(ao).props.insert(
                units_from_str("callee"),
                Prop::accessor(Some(tte), Some(tte), false, false),
            );
        } else {
            self.obj_mut(ao).props.insert(
                units_from_str("callee"),
                Prop::with_attrs(Value::Obj(fid), true, false, true),
            );
        }
        ao
    }

    /// ToObject on a primitive (9.13): the wrapper exotics. Callers handle
    /// undefined/null.
    pub(crate) fn to_object_wrapper(&mut self, v: &Value) -> Result<ObjId, Abrupt> {
        match v {
            Value::Str(s) => {
                let s = Rc::clone(s);
                self.make_string_obj(&s)
            }
            Value::Num(n) => {
                let n = *n;
                Ok(self.alloc(Object::new(
                    ObjKind::NumberObj(n),
                    Some(self.intr.number_proto),
                )))
            }
            Value::Bool(b) => {
                let b = *b;
                Ok(self.alloc(Object::new(
                    ObjKind::BoolObj(b),
                    Some(self.intr.boolean_proto),
                )))
            }
            Value::BigInt(n) => {
                let n = Rc::clone(n);
                Ok(self.alloc(Object::new(
                    ObjKind::BigIntObj(n),
                    Some(self.intr.bigint_proto),
                )))
            }
            _ => Err(Abrupt::Fatal("ToObject on non-primitive".to_string())),
        }
    }

    /// ArgumentListEvaluation (13.3.8): evaluate an argument list that may
    /// contain SpreadElements (`f(...args)`) left-to-right, iterating each
    /// spread via the general iterator protocol into the flat argument vector.
    /// A spread iterator is driven to completion (no IteratorClose is possible
    /// — the loop always runs to `done`).
    pub(crate) fn eval_argument_list(
        &mut self,
        args: &[Expr],
        ctx: &Ctx,
    ) -> Result<Vec<Value>, Abrupt> {
        let mut argv = Vec::with_capacity(args.len());
        for a in args {
            if let Expr::Spread(inner) = a {
                let v = self.eval_expr(inner, ctx)?;
                let mut it = self.slice_iterator(&v)?;
                loop {
                    self.charge_loop()?;
                    let Some(item) = self.slice_iter_next(&mut it)? else {
                        break;
                    };
                    argv.push(item);
                }
            } else {
                argv.push(self.eval_expr(a, ctx)?);
            }
        }
        Ok(argv)
    }

    pub fn call_value(&mut self, f: &Value, this: Value, args: Vec<Value>) -> ERes {
        let Value::Obj(fid) = f else {
            return Err(self.throw_native(NativeErrorKind::TypeError));
        };
        if !self.obj(*fid).is_callable() {
            return Err(self.throw_native(NativeErrorKind::TypeError));
        }
        self.call_function(*fid, this, args, false)
    }

    pub fn call_function(
        &mut self,
        fid: ObjId,
        this: Value,
        args: Vec<Value>,
        _is_new: bool,
    ) -> ERes {
        self.call_depth += 1;
        if self.call_depth > MAX_CALL_DEPTH {
            self.call_depth -= 1;
            return Err(Abrupt::Fatal("call depth cap exceeded".to_string()));
        }
        let r = self.call_function_inner(fid, this, args);
        self.call_depth -= 1;
        r
    }

    fn call_function_inner(&mut self, fid: ObjId, this: Value, args: Vec<Value>) -> ERes {
        // A callable proxy routes [[Call]] through its `apply` trap.
        if matches!(self.obj(fid).kind, ObjKind::Proxy { .. }) {
            return self.proxy_call(fid, this, args);
        }
        let impl_ = match &self.obj(fid).kind {
            ObjKind::Function(fi) => fi.clone(),
            _ => return Err(self.throw_native(NativeErrorKind::TypeError)),
        };
        match impl_ {
            FnImpl::Builtin(b) => self.dispatch_builtin(b, fid, this, args, false),
            FnImpl::Native(nc) => self.call_native(&nc, this, args),
            FnImpl::User { lit, env, home } => {
                self.call_user(&lit, env, fid, this, args, home)
            }
            FnImpl::Arrow {
                lit,
                env,
                this_v,
                home,
                frame,
            } => {
                // An async arrow returns a promise and suspends on `await` via
                // the same resumable machine; a FDI throw rejects that promise.
                if lit.is_async {
                    let fdi = self.prepare_fn_ctx(&lit, env, fid, *this_v, &args).map(|mut c| {
                        c.home_object = home;
                        c.ctor_frame = frame;
                        c
                    });
                    return self.call_async_function(&lit, fdi);
                }
                // Arrows ignore the passed `this` entirely.
                let mut body_ctx = self.prepare_fn_ctx(&lit, env, fid, *this_v, &args)?;
                body_ctx.home_object = home;
                body_ctx.ctor_frame = frame;
                let mut v: Option<Value> = None;
                match self.eval_stmt_list(&lit.body, &body_ctx, &mut v) {
                    Ok(()) => Ok(Value::Undefined),
                    Err(Abrupt::Return(rv)) => Ok(rv),
                    Err(other) => Err(other),
                }
            }
            // Class constructors throw on [[Call]].
            FnImpl::ClassCtor(_) => Err(self.throw_native(NativeErrorKind::TypeError)),
            FnImpl::Bound {
                target,
                this_v,
                args: bound,
            } => {
                let mut all = bound.as_ref().clone();
                all.extend(args);
                self.call_function(target, *this_v, all, false)
            }
        }
    }

    fn call_user(
        &mut self,
        lit: &Rc<FuncLit>,
        env: EnvId,
        fid: ObjId,
        this: Value,
        args: Vec<Value>,
        home: Option<ObjId>,
    ) -> ERes {
        // Calling a generator function creates a generator object (suspended
        // at the start) rather than running the body.
        if lit.is_generator {
            return self.create_generator(lit, env, fid, this, args, home);
        }
        let this_val = if lit.strict {
            this
        } else {
            // OrdinaryCallBindThis (sloppy): undefined/null → the global;
            // primitives → ToObject wrappers.
            match this {
                Value::Undefined | Value::Null => Value::Obj(self.global),
                Value::Obj(_) => this,
                prim => Value::Obj(self.to_object_wrapper(&prim)?),
            }
        };
        // An async function returns a promise and runs its body up to the
        // first `await` via the resumable machine; a FunctionDeclaration-
        // Instantiation throw rejects that promise rather than escaping.
        if lit.is_async {
            let fdi = self.prepare_fn_ctx_full(lit, env, fid, this_val, &args, home, None);
            return self.call_async_function(lit, fdi);
        }
        let ctx = self.prepare_fn_ctx_full(lit, env, fid, this_val, &args, home, None)?;
        let mut v: Option<Value> = None;
        match self.eval_stmt_list(&lit.body, &ctx, &mut v) {
            Ok(()) => Ok(Value::Undefined),
            Err(Abrupt::Return(rv)) => Ok(rv),
            Err(other) => Err(other),
        }
    }

    /// FunctionDeclarationInstantiation: parameter (incl. pattern/default/
    /// rest) / arguments / var / function bindings + the body lexical scope;
    /// returns the body Ctx.
    pub(crate) fn prepare_fn_ctx(
        &mut self,
        lit: &Rc<FuncLit>,
        env: EnvId,
        fid: ObjId,
        this_val: Value,
        args: &[Value],
    ) -> Result<Ctx, Abrupt> {
        self.prepare_fn_ctx_full(lit, env, fid, this_val, args, None, None)
    }

    #[allow(clippy::too_many_arguments)]
    pub(crate) fn prepare_fn_ctx_full(
        &mut self,
        lit: &Rc<FuncLit>,
        env: EnvId,
        fid: ObjId,
        this_val: Value,
        args: &[Value],
        home: Option<ObjId>,
        frame: Option<Rc<crate::interp::CtorFrame>>,
    ) -> Result<Ctx, Abrupt> {
        // The body's PrivateEnvironment: the one captured when this function
        // object was created (a class method / any function lexically inside a
        // class body). Ordinary top-level functions have none.
        let body_priv = self.fn_priv_env.get(&fid).cloned();
        // The function's VariableEnvironment (a var-hoisting boundary that a
        // sloppy direct eval in the body targets).
        let fenv = self.alloc_var_env(Some(env));
        // 1. Bindings for every parameter bound name.
        let mut pnames: Vec<String> = Vec::new();
        for p in &lit.params {
            p.target.bound_names(&mut pnames);
        }
        if let Some(r) = &lit.rest_param {
            r.bound_names(&mut pnames);
        }
        // Non-simple lists initialize left-to-right with TDZ (a default
        // referencing a later or self parameter throws ReferenceError).
        let tdz = !lit.simple_params;
        for n in &pnames {
            self.envs[fenv.0 as usize].bindings.insert(
                n.clone(),
                Binding {
                    value: Value::Undefined,
                    mutable: true,
                    initialized: !tdz,
                    fn_name_immutable: false,
                },
            );
        }
        // 2. The arguments object (mapped only for sloppy simple lists).
        if lit.uses_arguments {
            let ao = self.create_arguments_object(lit, fenv, fid, args);
            self.envs[fenv.0 as usize]
                .bindings
                .insert("arguments".to_string(), Binding::var(Value::Obj(ao)));
        }
        // 3. Parameter initialization (defaults and patterns run with the
        // progressive param scope visible; closures/`arguments` inside
        // initializers were refused at parse).
        let pctx = Ctx {
            env: fenv,
            this_val: this_val.clone(),
            strict: lit.strict,
            home_object: home,
            ctor_frame: frame.clone(),
            priv_env: body_priv.clone(),
            in_formal_params: true,
        };
        for (i, p) in lit.params.iter().enumerate() {
            let mut v = args.get(i).cloned().unwrap_or(Value::Undefined);
            if matches!(v, Value::Undefined) {
                if let Some(d) = &p.default {
                    v = match &p.target {
                        crate::ast::BindTarget::Name(n) => {
                            self.eval_named(d, &pctx, &units_from_str(n))?
                        }
                        crate::ast::BindTarget::Pattern(_) => self.eval_expr(d, &pctx)?,
                    };
                }
            }
            match &p.target {
                crate::ast::BindTarget::Name(n) => {
                    self.initialize_binding_public(fenv, n, v);
                }
                crate::ast::BindTarget::Pattern(pat) => {
                    self.destructure(pat, &v, &pctx, crate::pattern::BindMode::Init)?;
                }
            }
        }
        if let Some(rest) = &lit.rest_param {
            let arr = self.new_array(0);
            let extra = args.iter().skip(lit.params.len());
            let mut n: u64 = 0;
            for v in extra {
                self.obj_mut(arr)
                    .props
                    .insert(units_from_str(&n.to_string()), Prop::data(v.clone()));
                n += 1;
            }
            #[allow(clippy::cast_precision_loss)]
            self.set_array_length_raw(arr, n as f64);
            match rest {
                crate::ast::BindTarget::Name(rn) => {
                    self.initialize_binding_public(fenv, rn, Value::Obj(arr));
                }
                crate::ast::BindTarget::Pattern(pat) => {
                    self.destructure(pat, &Value::Obj(arr), &pctx, crate::pattern::BindMode::Init)?;
                }
            }
        }
        for v in &lit.vars {
            self.envs[fenv.0 as usize]
                .bindings
                .entry(v.clone())
                .or_insert(Binding::var(Value::Undefined));
        }
        // The body's lexical (let/const/class, TDZ) bindings exist before
        // the function declarations are instantiated, and those functions
        // close over lexEnv — a nested function writing a sibling `let`
        // pre-initialization must throw ReferenceError.
        let lex = self.alloc_env(Some(fenv));
        let _ = self.declare_lexical(lex, &lit.body);
        for f in &lit.funcs {
            let fo = self.create_function(f, lex, true, body_priv.clone());
            self.envs[fenv.0 as usize].bindings.insert(
                f.name.clone().expect("declaration has a name"),
                Binding::var(Value::Obj(fo)),
            );
        }
        Ok(Ctx {
            env: lex,
            this_val,
            strict: lit.strict,
            home_object: home,
            ctor_frame: frame,
            priv_env: body_priv,
            in_formal_params: false,
        })
    }

    pub fn construct(&mut self, f: &Value, args: Vec<Value>) -> ERes {
        let Value::Obj(fid) = f else {
            return Err(self.throw_native(NativeErrorKind::TypeError));
        };
        if !self.obj(*fid).is_callable() {
            return Err(self.throw_native(NativeErrorKind::TypeError));
        }
        self.construct_with_target(*fid, args, *fid)
    }

    /// [[Construct]] with an explicit new.target (the prototype source for
    /// OrdinaryCreateFromConstructor; threaded through super()).
    pub(crate) fn construct_with_target(
        &mut self,
        fid: ObjId,
        args: Vec<Value>,
        new_target: ObjId,
    ) -> ERes {
        // A constructor proxy routes [[Construct]] through its `construct` trap.
        if matches!(self.obj(fid).kind, ObjKind::Proxy { .. }) {
            return self.proxy_construct(fid, args, new_target);
        }
        let impl_ = match &self.obj(fid).kind {
            ObjKind::Function(fi) => fi.clone(),
            _ => return Err(self.throw_native(NativeErrorKind::TypeError)),
        };
        match impl_ {
            FnImpl::Builtin(b) => {
                self.call_depth += 1;
                if self.call_depth > MAX_CALL_DEPTH {
                    self.call_depth -= 1;
                    return Err(Abrupt::Fatal("call depth cap exceeded".to_string()));
                }
                // Error/Object [[Construct]] honor a foreign new.target
                // (super() from a subclass).
                if new_target != fid {
                    self.pending_new_target = Some(new_target);
                }
                let r = self.dispatch_builtin(b, fid, Value::Undefined, args, true);
                self.pending_new_target = None;
                self.call_depth -= 1;
                r
            }
            FnImpl::ClassCtor(rec) => self.construct_class(fid, &rec, args, new_target),
            FnImpl::Bound {
                target,
                args: bound,
                ..
            } => {
                // 10.4.1.2: [[Construct]] forwards to the bound target with
                // the bound arguments prepended; when F == newTarget the
                // target substitutes.
                let nt = if new_target == fid { target } else { new_target };
                let mut all = bound.as_ref().clone();
                all.extend(args);
                self.construct_with_target(target, all, nt)
            }
            FnImpl::Arrow { .. } | FnImpl::Native(_) => {
                Err(self.throw_native(NativeErrorKind::TypeError))
            }
            FnImpl::User { lit, .. } => {
                // MethodDefinition functions, generator functions and async
                // functions are not constructors.
                if lit.is_method || lit.is_generator || lit.is_async {
                    return Err(self.throw_native(NativeErrorKind::TypeError));
                }
                let proto = self.proto_from_new_target(new_target, self.intr.object_proto)?;
                let obj = self.alloc(Object::new(ObjKind::Plain, Some(proto)));
                let r = self.call_function(fid, Value::Obj(obj), args, true)?;
                Ok(match r {
                    Value::Obj(_) => r,
                    _ => Value::Obj(obj),
                })
            }
        }
    }

    // -- coercions ----------------------------------------------------------

    pub fn to_boolean(&self, v: &Value) -> bool {
        match v {
            Value::Undefined | Value::Null => false,
            Value::Bool(b) => *b,
            Value::Num(n) => !(*n == 0.0 || n.is_nan()),
            // ToBoolean(BigInt): 0n is false, every other BigInt is true.
            Value::BigInt(n) => !crate::bigint::is_zero(n),
            Value::Str(s) => !s.is_empty(),
            Value::Sym(_) | Value::Obj(_) => true,
        }
    }

    pub fn to_number(&mut self, v: &Value) -> Result<f64, Abrupt> {
        match v {
            Value::Num(n) => Ok(*n),
            Value::Bool(b) => Ok(if *b { 1.0 } else { 0.0 }),
            Value::Undefined => Ok(f64::NAN),
            Value::Null => Ok(0.0),
            Value::Str(s) => {
                to_number_str(&units_to_lossy(s)).map_err(Abrupt::Fatal)
            }
            // ToNumber(symbol) and ToNumber(BigInt) are TypeErrors (7.1.4);
            // `Number(bigint)` converts through a separate path in NumberFn.
            Value::Sym(_) | Value::BigInt(_) => {
                Err(self.throw_native(NativeErrorKind::TypeError))
            }
            Value::Obj(_) => {
                let p = self.to_primitive(v, Hint::Number)?;
                self.to_number(&p)
            }
        }
    }

    /// ToNumeric (7.1.3): ToPrimitive(number hint), then a BigInt passes
    /// through unchanged while everything else is ToNumber'd. The result is
    /// always `Value::Num` or `Value::BigInt`.
    pub fn to_numeric(&mut self, v: &Value) -> ERes {
        let prim = self.to_primitive(v, Hint::Number)?;
        if matches!(prim, Value::BigInt(_)) {
            return Ok(prim);
        }
        Ok(Value::Num(self.to_number(&prim)?))
    }

    pub fn to_string_units(&mut self, v: &Value) -> Result<Units, Abrupt> {
        match v {
            Value::Str(s) => Ok(s.as_ref().clone()),
            Value::Num(n) => Ok(units_from_str(&js_number_to_string(*n))),
            // ToString(BigInt) (7.1.17): the decimal form (radix 10).
            Value::BigInt(n) => Ok(crate::bigint::to_units_decimal(n)),
            Value::Bool(b) => Ok(units_from_str(if *b { "true" } else { "false" })),
            Value::Undefined => Ok(units_from_str("undefined")),
            Value::Null => Ok(units_from_str("null")),
            // ToString(symbol) is a TypeError (7.1.17) — `String(sym)` is the
            // only path that yields the descriptive string, handled there.
            Value::Sym(_) => Err(self.throw_native(NativeErrorKind::TypeError)),
            Value::Obj(_) => {
                let p = self.to_primitive(v, Hint::String)?;
                self.to_string_units(&p)
            }
        }
    }

    /// ToPrimitive (7.1.1): honors @@toPrimitive, then OrdinaryToPrimitive.
    pub fn to_primitive(&mut self, v: &Value, hint: Hint) -> ERes {
        let Value::Obj(_) = v else {
            return Ok(v.clone());
        };
        // Step: exoticToPrim = GetMethod(input, @@toPrimitive).
        let sid = self.intr.wk(crate::builtins::WK_TO_PRIMITIVE);
        if let Some(f) = self.get_method_symbol(v, sid)? {
            let hint_str = match hint {
                Hint::String => "string",
                Hint::Number => "number",
                Hint::Default => "default",
            };
            let r = self.call_function(f, v.clone(), vec![Value::str_from(hint_str)], false)?;
            if r.is_object() {
                return Err(self.throw_native(NativeErrorKind::TypeError));
            }
            return Ok(r);
        }
        self.ordinary_to_primitive(v, hint)
    }

    /// OrdinaryToPrimitive (7.1.1.1): valueOf/toString in hint order.
    pub(crate) fn ordinary_to_primitive(&mut self, v: &Value, hint: Hint) -> ERes {
        let order: [&str; 2] = if hint == Hint::String {
            ["toString", "valueOf"]
        } else {
            ["valueOf", "toString"]
        };
        for m in order {
            let mv = self.get_prop_value(v, &units_from_str(m))?;
            if let Value::Obj(mid) = &mv {
                if self.obj(*mid).is_callable() {
                    let r = self.call_function(*mid, v.clone(), Vec::new(), false)?;
                    if !r.is_object() {
                        return Ok(r);
                    }
                }
            }
        }
        Err(self.throw_native(NativeErrorKind::TypeError))
    }

    /// ToPropertyKey (7.1.19): a symbol coerces to a symbol key; everything
    /// else to a string key.
    pub fn to_property_key(&mut self, v: &Value) -> Result<PropertyKey, Abrupt> {
        let p = self.to_primitive(v, Hint::String)?;
        if let Value::Sym(s) = p {
            return Ok(PropertyKey::Sym(s));
        }
        Ok(PropertyKey::Str(self.to_string_units(&p)?))
    }

    // -- operators ----------------------------------------------------------

    pub fn binary_op(&mut self, op: BinOp, l: &Value, r: &Value) -> ERes {
        match op {
            BinOp::Add => self.op_add(l, r),
            BinOp::Sub
            | BinOp::Mul
            | BinOp::Div
            | BinOp::Rem
            | BinOp::Exp
            | BinOp::BitAnd
            | BinOp::BitOr
            | BinOp::BitXor
            | BinOp::Shl
            | BinOp::Shr
            | BinOp::Ushr => self.numeric_binary(op, l, r),
            BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => {
                // Original left operand is coerced first for all four ops.
                let pl = self.to_primitive(l, Hint::Number)?;
                let pr = self.to_primitive(r, Hint::Number)?;
                let b = match op {
                    BinOp::Lt => self.less_than(&pl, &pr)?.unwrap_or(false),
                    BinOp::Gt => self.less_than(&pr, &pl)?.unwrap_or(false),
                    BinOp::Le => match self.less_than(&pr, &pl)? {
                        None => false,
                        Some(x) => !x,
                    },
                    _ => match self.less_than(&pl, &pr)? {
                        None => false,
                        Some(x) => !x,
                    },
                };
                Ok(Value::Bool(b))
            }
            BinOp::EqStrict => Ok(Value::Bool(strict_eq(self, l, r))),
            BinOp::NeStrict => Ok(Value::Bool(!strict_eq(self, l, r))),
            BinOp::EqLoose => Ok(Value::Bool(self.loose_eq(l, r)?)),
            BinOp::NeLoose => Ok(Value::Bool(!self.loose_eq(l, r)?)),
            BinOp::InstanceOf => self.instance_of(l, r),
            BinOp::In => {
                // 13.10.1: TypeError on a non-object RHS BEFORE the key
                // coercion of the LHS.
                let Value::Obj(oid) = r else {
                    return Err(self.throw_native(NativeErrorKind::TypeError));
                };
                let oid = *oid;
                let key = self.to_property_key(l)?;
                let has = if matches!(self.obj(oid).kind, ObjKind::Proxy { .. }) {
                    self.mop_has(oid, &key)?
                } else {
                    match key {
                        PropertyKey::Str(k) => self.has_property_checked(oid, &k)?,
                        PropertyKey::Sym(s) => self.has_property_sym(oid, s)?,
                    }
                };
                Ok(Value::Bool(has))
            }
        }
    }

    fn op_add(&mut self, l: &Value, r: &Value) -> ERes {
        let pl = self.to_primitive(l, Hint::Default)?;
        let pr = self.to_primitive(r, Hint::Default)?;
        if matches!(pl, Value::Str(_)) || matches!(pr, Value::Str(_)) {
            let mut a = self.to_string_units(&pl)?;
            let b = self.to_string_units(&pr)?;
            if a.len() + b.len() > MAX_STRING_UNITS {
                return Err(Abrupt::Fatal("string concatenation cap exceeded".to_string()));
            }
            a.extend_from_slice(&b);
            return Ok(Value::Str(Rc::new(a)));
        }
        // Non-string `+`: ToNumeric both, same-type or TypeError (13.15.3).
        let ln = self.to_numeric(&pl)?;
        let rn = self.to_numeric(&pr)?;
        match (&ln, &rn) {
            (Value::BigInt(a), Value::BigInt(b)) => self.big_res(crate::bigint::add(a, b)),
            (Value::Num(a), Value::Num(b)) => Ok(Value::Num(a + b)),
            _ => Err(self.throw_native(NativeErrorKind::TypeError)),
        }
    }

    /// The multiplicative / exponent / bitwise / shift operators
    /// (ApplyStringOrNumericBinaryOperator numeric branch, 13.15.3): ToNumeric
    /// both operands; same type dispatches to Number or BigInt semantics, a
    /// mixed pair is a TypeError, and `>>>` on any BigInt is a TypeError.
    fn numeric_binary(&mut self, op: BinOp, l: &Value, r: &Value) -> ERes {
        let ln = self.to_numeric(l)?;
        let rn = self.to_numeric(r)?;
        match (&ln, &rn) {
            (Value::BigInt(a), Value::BigInt(b)) => {
                use crate::bigint as bi;
                let res = match op {
                    BinOp::Sub => bi::sub(a, b),
                    BinOp::Mul => bi::mul(a, b),
                    BinOp::Div => bi::div(a, b),
                    BinOp::Rem => bi::rem(a, b),
                    BinOp::Exp => bi::pow(a, b),
                    BinOp::BitAnd => Ok(bi::bitand(a, b)),
                    BinOp::BitOr => Ok(bi::bitor(a, b)),
                    BinOp::BitXor => Ok(bi::bitxor(a, b)),
                    BinOp::Shl => bi::shl(a, b),
                    BinOp::Shr => bi::shr(a, b),
                    // BigInt::unsignedRightShift always throws TypeError.
                    BinOp::Ushr => Err(bi::ushr_type_error()),
                    _ => unreachable!("non-numeric op routed to numeric_binary"),
                };
                self.big_res(res)
            }
            (Value::Num(a), Value::Num(b)) => {
                let (a, b) = (*a, *b);
                let v = match op {
                    BinOp::Sub => a - b,
                    BinOp::Mul => a * b,
                    BinOp::Div => a / b,
                    BinOp::Rem => a % b,
                    BinOp::Exp => match crate::builtins::math_pow_exact(a, b) {
                        Some(v) => v,
                        None => {
                            return Err(Abrupt::Fatal(
                                "`**` on Numbers outside the exactly-determined domain (out of slice)"
                                    .to_string(),
                            ))
                        }
                    },
                    BinOp::BitAnd => f64::from(to_int32(a) & to_int32(b)),
                    BinOp::BitOr => f64::from(to_int32(a) | to_int32(b)),
                    BinOp::BitXor => f64::from(to_int32(a) ^ to_int32(b)),
                    BinOp::Shl => f64::from(to_int32(a).wrapping_shl(to_uint32(b) & 31)),
                    BinOp::Shr => f64::from(to_int32(a) >> (to_uint32(b) & 31)),
                    BinOp::Ushr => f64::from(to_uint32(a) >> (to_uint32(b) & 31)),
                    _ => unreachable!("non-numeric op routed to numeric_binary"),
                };
                Ok(Value::Num(v))
            }
            // A mixed Number/BigInt pair is always a TypeError (including `>>>`,
            // whose BigInt overload is itself a TypeError).
            _ => Err(self.throw_native(NativeErrorKind::TypeError)),
        }
    }

    /// Map a BigInt operation result to a value or the spec throw / refusal.
    fn big_res(&mut self, r: Result<num_bigint::BigInt, crate::bigint::BigErr>) -> ERes {
        match r {
            Ok(n) => Ok(Value::bigint(n)),
            Err(crate::bigint::BigErr::Range) => {
                Err(self.throw_native(NativeErrorKind::RangeError))
            }
            Err(crate::bigint::BigErr::Type) => {
                Err(self.throw_native(NativeErrorKind::TypeError))
            }
            Err(crate::bigint::BigErr::Refuse(m)) => Err(Abrupt::Fatal(m)),
        }
    }

    /// IsLessThan on primitives (7.2.13); `None` = an incomparable pair
    /// (NaN, or a String that is not a valid BigInt). `px`/`py` are already
    /// primitives (the caller ToPrimitive'd with the number hint).
    fn less_than(&mut self, px: &Value, py: &Value) -> Result<Option<bool>, Abrupt> {
        use std::cmp::Ordering;
        match (px, py) {
            (Value::Str(a), Value::Str(b)) => Ok(Some(a.as_slice() < b.as_slice())),
            (Value::BigInt(a), Value::Str(b)) => Ok(match crate::bigint::string_to_bigint(b) {
                Some(nb) => Some(a.as_ref() < &nb),
                None => None,
            }),
            (Value::Str(a), Value::BigInt(b)) => Ok(match crate::bigint::string_to_bigint(a) {
                Some(na) => Some(&na < b.as_ref()),
                None => None,
            }),
            _ => {
                let nx = self.to_numeric(px)?;
                let ny = self.to_numeric(py)?;
                match (&nx, &ny) {
                    (Value::Num(a), Value::Num(b)) => {
                        if a.is_nan() || b.is_nan() {
                            Ok(None)
                        } else {
                            Ok(Some(a < b))
                        }
                    }
                    (Value::BigInt(a), Value::BigInt(b)) => Ok(Some(a < b)),
                    (Value::BigInt(a), Value::Num(b)) => {
                        Ok(crate::bigint::cmp_f64(a, *b).map(|o| o == Ordering::Less))
                    }
                    (Value::Num(a), Value::BigInt(b)) => {
                        // a < b  ⇔  cmp(b, a) is Greater.
                        Ok(crate::bigint::cmp_f64(b, *a).map(|o| o == Ordering::Greater))
                    }
                    _ => unreachable!("to_numeric yields Num or BigInt"),
                }
            }
        }
    }

    fn loose_eq(&mut self, l: &Value, r: &Value) -> Result<bool, Abrupt> {
        match (l, r) {
            (Value::Undefined | Value::Null, Value::Undefined | Value::Null) => Ok(true),
            (Value::Num(_), Value::Num(_))
            | (Value::Str(_), Value::Str(_))
            | (Value::Bool(_), Value::Bool(_))
            | (Value::Sym(_), Value::Sym(_))
            | (Value::BigInt(_), Value::BigInt(_))
            | (Value::Obj(_), Value::Obj(_)) => Ok(strict_eq(self, l, r)),
            (Value::Num(_), Value::Str(_)) => {
                let n = self.to_number(r)?;
                Ok(strict_eq(self, l, &Value::Num(n)))
            }
            (Value::Str(_), Value::Num(_)) => {
                let n = self.to_number(l)?;
                Ok(strict_eq(self, &Value::Num(n), r))
            }
            // BigInt vs Number (7.2.15): exact ℝ(x) = ℝ(y); NaN/±∞ are false.
            (Value::BigInt(a), Value::Num(b)) => Ok(crate::bigint::eq_f64(a, *b)),
            (Value::Num(a), Value::BigInt(b)) => Ok(crate::bigint::eq_f64(b, *a)),
            // BigInt vs String: StringToBigInt, invalid → false.
            (Value::BigInt(a), Value::Str(b)) => Ok(match crate::bigint::string_to_bigint(b) {
                Some(n) => a.as_ref() == &n,
                None => false,
            }),
            (Value::Str(a), Value::BigInt(b)) => Ok(match crate::bigint::string_to_bigint(a) {
                Some(n) => &n == b.as_ref(),
                None => false,
            }),
            (Value::Bool(_), _) => {
                let n = self.to_number(l)?;
                self.loose_eq(&Value::Num(n), r)
            }
            (_, Value::Bool(_)) => {
                let n = self.to_number(r)?;
                self.loose_eq(l, &Value::Num(n))
            }
            (Value::Num(_) | Value::Str(_) | Value::Sym(_) | Value::BigInt(_), Value::Obj(_)) => {
                let p = self.to_primitive(r, Hint::Default)?;
                self.loose_eq(l, &p)
            }
            (Value::Obj(_), Value::Num(_) | Value::Str(_) | Value::Sym(_) | Value::BigInt(_)) => {
                let p = self.to_primitive(l, Hint::Default)?;
                self.loose_eq(&p, r)
            }
            _ => Ok(false),
        }
    }

    fn instance_of(&mut self, l: &Value, r: &Value) -> ERes {
        // InstanceofOperator (13.10.2): a non-object RHS is a TypeError before
        // anything else.
        if !matches!(r, Value::Obj(_)) {
            return Err(self.throw_native(NativeErrorKind::TypeError));
        }
        // GetMethod(target, @@hasInstance). For an ordinary callable this
        // resolves to %Function.prototype%[@@hasInstance] (the default) — take
        // the fast OrdinaryHasInstance path then; a USER handler is called.
        let sid = self.intr.wk(crate::builtins::WK_HAS_INSTANCE);
        let handler = self.get_method_symbol(r, sid)?;
        match handler {
            Some(h) if h != self.intr.function_proto_has_instance => {
                let res = self.call_function(h, r.clone(), vec![l.clone()], false)?;
                Ok(Value::Bool(self.to_boolean(&res)))
            }
            // None (no @@hasInstance) or the default handler: OrdinaryHasInstance
            // preceded by the IsCallable check (step 4).
            _ => {
                let Value::Obj(cid) = r else { unreachable!("checked above") };
                if !self.obj(*cid).is_callable() {
                    return Err(self.throw_native(NativeErrorKind::TypeError));
                }
                Ok(Value::Bool(self.ordinary_has_instance(r, l)?))
            }
        }
    }
}

/// ExpectedArgumentCount: formal parameters left of the first initializer
/// (rest never counts; patterns without defaults count).
pub(crate) fn expected_arg_count(lit: &FuncLit) -> f64 {
    let mut n = 0.0;
    for p in &lit.params {
        if p.default.is_some() {
            break;
        }
        n += 1.0;
    }
    n
}

/// Whether a CallExpression callee is the direct-eval syntactic form: a bare
/// `eval` IdentifierReference, possibly wrapped in transparent parentheses
/// (`(eval)(x)` is direct; `(0, eval)(x)` is not — the comma yields a value,
/// not a reference). The resolved value is checked against %eval% separately.
fn is_direct_eval_callee(callee: &Expr) -> bool {
    match callee {
        Expr::Ident(name) => name == "eval",
        Expr::Paren(inner) => is_direct_eval_callee(inner),
        _ => false,
    }
}

/// ToUint32 (7.1.7), exact for every finite f64: the low 32 bits of the
/// truncated integer value, computed on the IEEE mantissa (no `f64 as i64`
/// saturation above 2^63). NaN / ±∞ / ±0 map to 0.
pub(crate) fn to_uint32(n: f64) -> u32 {
    if !n.is_finite() || n == 0.0 {
        return 0;
    }
    let neg = n < 0.0;
    let bits = n.abs().to_bits();
    let raw_exp = ((bits >> 52) & 0x7ff) as i64;
    let mant = bits & 0x000f_ffff_ffff_ffff;
    let (m, e): (u128, i64) = if raw_exp == 0 {
        (u128::from(mant), -1074)
    } else {
        (u128::from(mant | 0x0010_0000_0000_0000), raw_exp - 1075)
    };
    let low: u32 = if e >= 32 {
        0
    } else if e >= 0 {
        #[allow(clippy::cast_possible_truncation)]
        (((m << u32::try_from(e).unwrap_or(0)) & 0xffff_ffff) as u32)
    } else {
        let sh = u32::try_from(-e).unwrap_or(u32::MAX);
        if sh >= 128 {
            0
        } else {
            #[allow(clippy::cast_possible_truncation)]
            (((m >> sh) & 0xffff_ffff) as u32)
        }
    };
    if neg {
        low.wrapping_neg()
    } else {
        low
    }
}

/// ToInt32 (7.1.6): ToUint32 reinterpreted as a signed 32-bit value.
#[allow(clippy::cast_possible_wrap)]
pub(crate) fn to_int32(n: f64) -> i32 {
    to_uint32(n) as i32
}

pub fn type_of(it: &Interp, v: &Value) -> &'static str {
    match v {
        Value::Undefined => "undefined",
        Value::Null => "object",
        Value::Bool(_) => "boolean",
        Value::Num(_) => "number",
        Value::BigInt(_) => "bigint",
        Value::Str(_) => "string",
        Value::Sym(_) => "symbol",
        Value::Obj(id) => {
            if it.obj(*id).is_callable() {
                "function"
            } else {
                "object"
            }
        }
    }
}
