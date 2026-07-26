// Dynamic code: `eval` (PerformEval / EvalDeclarationInstantiation, 19.2.1)
// and the `Function` constructor (CreateDynamicFunction, 20.2.1.1.1). Both
// parse a runtime string via the frozen trust-js-parse and evaluate the
// result in a spec-exact scope:
//
//   * direct eval  — runs in the CALLER's lexical environment; sloppy code
//     hoists var/function declarations into the caller's variable environment
//     (found via the `var_scope` marker), strict code gets its own;
//   * indirect eval — runs in the GLOBAL environment (`run_script`-equivalent);
//   * the Function constructor — assembles `function anonymous(<P>) {<body>}`,
//     parses it, and creates a function closing over the global environment.
//
// Anything the parser reports Unsupported, and any eval body whose validity
// depends on caller context we cannot pass to the parser (a direct eval using
// `super`/`new.target` supplied by an enclosing method/function), refuses with
// NoCoverage — never a guessed SyntaxError, never a mis-evaluation. Parser
// EarlyError → the exact SyntaxError; a non-string eval argument is returned
// unchanged.
//
// Author: Andrew Yates
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

use crate::interp::{hoist, Abrupt, Ctx, ERes, Interp};
use std::rc::Rc;
use trust_js_parse::ast::{Expr, Func, Stmt};
use trust_js_parse::{parse_script, ParseOutcome, Program};
use trust_js_value::{
    Binding, EnvId, ErrKind, FnData, FnFlavor, JsValue, NativeFn, ObjId, ObjKind, PropKey,
    Property, PropValue,
};

/// Where a running eval hoists its `var`/function declarations.
#[derive(Clone, Copy)]
enum VarTarget {
    /// A declarative variable environment (a function's, or a strict eval's
    /// own); vars/functions become bindings in this frame.
    Env(EnvId),
    /// The global object (sloppy eval at global scope); vars/functions become
    /// own properties of the global object.
    Global,
}

impl Interp {
    /// True iff `v` is the realm's %eval% intrinsic function object.
    pub(crate) fn is_eval_intrinsic(&self, v: &JsValue) -> bool {
        matches!(
            v,
            JsValue::Obj(o)
                if matches!(
                    &self.heap.obj(*o).kind,
                    ObjKind::Function(FnData::Native(NativeFn::EvalFn))
                )
        )
    }

    /// Indirect `eval(x)` (18.2.1): runs in the global environment, sloppy
    /// base (a `"use strict"` prologue in `x` still activates strict).
    pub(crate) fn eval_indirect(&mut self, x: JsValue) -> ERes {
        self.perform_eval(x, None)
    }

    /// Direct `eval(x)`: runs in the caller's context (`ctx`).
    pub(crate) fn eval_direct(&mut self, x: JsValue, ctx: &Ctx) -> ERes {
        self.perform_eval(x, Some(ctx))
    }

    /// PerformEval(x, strictCaller, direct) (19.2.1.1). `caller` is `Some` for
    /// a direct eval (its `.env`/`.strict` drive scope + strictness), `None`
    /// for indirect.
    fn perform_eval(&mut self, x: JsValue, caller: Option<&Ctx>) -> ERes {
        // 2. If Type(x) is not String, return x.
        let JsValue::Str(units) = &x else {
            return Ok(x);
        };
        let Ok(src) = String::from_utf16(units) else {
            return Err(Abrupt::Fatal(
                "eval source with lone surrogate (out of slice)".to_string(),
            ));
        };
        let caller_strict = caller.is_some_and(|c| c.strict);
        let prog = match parse_script(&src, caller_strict) {
            ParseOutcome::Script(p) => p,
            ParseOutcome::EarlyError { reason } => {
                // A Script early error is the exact SyntaxError — UNLESS a
                // direct eval's caller would legitimately supply the context
                // (super/new.target) that the Script grammar forbids; we can't
                // reparse in that context, so refuse rather than mis-report.
                if let Some(c) = caller {
                    if self.eval_error_needs_caller_context(&reason, c) {
                        return Err(Abrupt::Fatal(format!(
                            "eval body needs caller context (out of slice): {reason}"
                        )));
                    }
                }
                return Err(self.throw_native(ErrKind::Syntax));
            }
            ParseOutcome::Unsupported { reason } => {
                return Err(Abrupt::Fatal(format!("eval body parse: {reason}")));
            }
        };
        let prog = Rc::new(prog);
        self.eval_programs.push(Rc::clone(&prog));
        let strict = prog.strict;

        // lexEnv is always a fresh declarative environment; varEnv depends on
        // strictness + directness (PerformEval steps 12-16).
        let (lex_env, var_target) = if let Some(c) = caller {
            let lex = self.alloc_env(Some(c.env));
            if strict {
                (lex, VarTarget::Env(lex))
            } else {
                (lex, self.caller_var_target(c.env))
            }
        } else {
            let lex = self.alloc_env(Some(EnvId(0)));
            if strict {
                (lex, VarTarget::Env(lex))
            } else {
                (lex, VarTarget::Global)
            }
        };

        self.eval_declaration_instantiation(&prog.body, lex_env, var_target, strict)?;

        let ctx = Ctx {
            env: lex_env,
            strict,
        };
        let mut v: Option<JsValue> = None;
        self.eval_stmt_list(&prog.body, &ctx, &mut v)?;
        Ok(v.unwrap_or(JsValue::Undefined))
    }

    /// The nearest enclosing variable environment of `env`: a function's
    /// `var_scope` frame, or the global object when none is found.
    fn caller_var_target(&self, env: EnvId) -> VarTarget {
        let mut cur = Some(env);
        while let Some(e) = cur {
            if self.heap.env(e).var_scope {
                return VarTarget::Env(e);
            }
            cur = self.heap.env(e).parent;
        }
        VarTarget::Global
    }

    /// Is a Script EarlyError `reason` one whose validity would flip in the
    /// direct-eval caller's context (so we must refuse, not report SyntaxError)?
    fn eval_error_needs_caller_context(&self, reason: &str, caller: &Ctx) -> bool {
        if reason.contains("super") {
            // `super` is valid in a method / derived-constructor caller (a
            // [[HomeObject]] is lexically in scope there).
            return self.resolve_home_object(caller).is_some();
        }
        if reason.contains("new.target") {
            // `new.target` is valid inside any function caller.
            return self.caller_has_new_target(caller.env);
        }
        if let Some(pname) = reason.strip_prefix("reference to undeclared private name #") {
            // A direct eval body referencing a private name (`this.#m`) is VALID
            // when the caller's PrivateEnvironment declares it — the enclosing
            // class is lexically in scope, so the engines complete normally
            // (MakePrivateReference resolves `#m` in the running context's
            // PrivateEnvironment). The frozen Script parser has no view of that
            // PrivateEnvironment and rejects EVERY private reference, so we
            // cannot reparse the body in the right scope: refuse (NoCoverage)
            // rather than emit a WRONG SyntaxError. When `#m` is NOT declared in
            // the caller's scope the eval body would itself early-error, so the
            // SyntaxError we would otherwise report is the correct verdict —
            // only refuse for a name that actually resolves in scope.
            return self.resolve_priv(caller.env, pname).is_some();
        }
        false
    }

    fn caller_has_new_target(&self, env: EnvId) -> bool {
        let mut cur = Some(env);
        while let Some(e) = cur {
            if self.heap.env(e).new_target.is_some() {
                return true;
            }
            cur = self.heap.env(e).parent;
        }
        false
    }

    /// EvalDeclarationInstantiation(body, varEnv, lexEnv, strict) (19.2.1.3).
    fn eval_declaration_instantiation(
        &mut self,
        body: &[Stmt],
        lex_env: EnvId,
        var_target: VarTarget,
        strict: bool,
    ) -> Result<(), Abrupt> {
        let analysis = hoist::analyze(body, strict).map_err(Abrupt::Fatal)?;
        let lexical = hoist::lexical_decls(body).map_err(Abrupt::Fatal)?;
        let func_names: Vec<String> = analysis
            .funcs
            .iter()
            .filter_map(|f| f.name.clone())
            .collect();

        // VarDeclaredNames = var names + top-level function names.
        let mut var_names: Vec<String> = analysis.vars.clone();
        for n in &func_names {
            if !var_names.contains(n) {
                var_names.push(n.clone());
            }
        }

        // Sloppy-only guard: a var/function decl must not hoist over a
        // like-named lexical declaration in an intervening declarative env up
        // to varEnv (19.2.1.3 step 3.d) — a SyntaxError. (There are no
        // persistent global lexical bindings under the differential driver,
        // which runs every script via indirect eval, so 3.a never fires.)
        if !strict {
            let boundary = match var_target {
                VarTarget::Global => EnvId(0),
                VarTarget::Env(ve) => ve,
            };
            self.eval_conflict_walk(lex_env, boundary, &var_names)?;
        }

        // Global target: CanDeclareGlobalFunction / CanDeclareGlobalVar
        // (steps 6.b / 8.a.iii) — a non-extensible global rejects a NEW binding
        // with TypeError, before any binding is created.
        if let VarTarget::Global = var_target {
            self.can_declare_globals(&analysis.vars, &func_names)?;
        }

        // Lexical declarations (TDZ) into lexEnv.
        for (n, mutable) in &lexical {
            self.heap
                .env_mut(lex_env)
                .bindings
                .insert(n.clone(), Binding::tdz(*mutable));
        }
        // Function declarations: instantiated with lexEnv as scope, bound into
        // the variable target (last-wins already resolved by `analysis.funcs`).
        for f in &analysis.funcs {
            let fo = self.instantiate_hoisted_function(f, lex_env)?;
            let name = f.name.clone().expect("declaration has a name");
            self.eval_bind_var_function(var_target, &name, fo)?;
        }
        // Var names: create an undefined binding when absent.
        for v in &analysis.vars {
            if func_names.contains(v) {
                continue;
            }
            self.eval_declare_var(var_target, v);
        }
        Ok(())
    }

    /// Walk declarative environments from `from` up to (excluding) `boundary`,
    /// throwing SyntaxError if any binds a name in `names` (the var/let
    /// hoisting conflict, 19.2.1.3 step 3.d). Object/with environments are not
    /// modeled here (with refuses earlier), so every frame is declarative.
    fn eval_conflict_walk(
        &mut self,
        from: EnvId,
        boundary: EnvId,
        names: &[String],
    ) -> Result<(), Abrupt> {
        let mut cur = from;
        let mut guard = 0u32;
        while cur != boundary {
            for n in names {
                if self.heap.env(cur).bindings.contains_key(n) {
                    return Err(self.throw_native(ErrKind::Syntax));
                }
            }
            match self.heap.env(cur).parent {
                Some(p) => cur = p,
                None => break,
            }
            guard += 1;
            if guard > 1_000_000 {
                break;
            }
        }
        Ok(())
    }

    /// CanDeclareGlobalFunction / CanDeclareGlobalVar for a non-extensible
    /// global: a new binding cannot be added, so throw TypeError up front.
    fn can_declare_globals(&mut self, vars: &[String], func_names: &[String]) -> Result<(), Abrupt> {
        let extensible = self.heap.obj(self.global).extensible;
        for f in func_names {
            let key = PropKey::from_str(f);
            let ok = match self.heap.obj(self.global).props.get(&key) {
                None => extensible,
                Some(p) => {
                    p.configurable
                        || matches!(&p.v, PropValue::Data { writable, .. } if *writable && p.enumerable)
                }
            };
            if !ok {
                return Err(self.throw_type_error());
            }
        }
        for v in vars {
            if func_names.iter().any(|f| f == v) {
                continue;
            }
            let key = PropKey::from_str(v);
            if !self.heap.obj(self.global).props.contains_key(&key) && !extensible {
                return Err(self.throw_type_error());
            }
        }
        Ok(())
    }

    fn eval_bind_var_function(
        &mut self,
        var_target: VarTarget,
        name: &str,
        fobj: ObjId,
    ) -> Result<(), Abrupt> {
        match var_target {
            VarTarget::Global => self.create_global_function_binding(name, fobj),
            VarTarget::Env(ve) => {
                // HasBinding → SetMutableBinding (keep deletability); else
                // CreateMutableBinding(fn, true) + Initialize (deletable).
                if let Some(b) = self.heap.env_mut(ve).bindings.get_mut(name) {
                    b.value = JsValue::Obj(fobj);
                    b.initialized = true;
                } else {
                    self.heap
                        .env_mut(ve)
                        .bindings
                        .insert(name.to_string(), Binding::var_deletable(JsValue::Obj(fobj)));
                }
                Ok(())
            }
        }
    }

    fn eval_declare_var(&mut self, var_target: VarTarget, name: &str) {
        match var_target {
            VarTarget::Global => {
                let key = PropKey::from_str(name);
                if !self.heap.obj(self.global).props.contains_key(&key) {
                    self.heap
                        .obj_mut(self.global)
                        .props
                        .insert(key, Property::data(JsValue::Undefined));
                }
            }
            VarTarget::Env(ve) => {
                // A newly-created eval var in a function scope is deletable
                // (CreateMutableBinding(vn, true)).
                if !self.heap.env(ve).bindings.contains_key(name) {
                    self.heap
                        .env_mut(ve)
                        .bindings
                        .insert(name.to_string(), Binding::var_deletable(JsValue::Undefined));
                }
            }
        }
    }

    // -- the Function constructor -------------------------------------------

    /// CreateDynamicFunction for %Function% (kind = normal). Assembles the
    /// canonical `function anonymous(<P>\n) {\n<body>\n}` source, parses it,
    /// and creates a function whose scope is the global environment (it does
    /// NOT close over the caller). `new_target` sets the [[Prototype]].
    pub(crate) fn create_dynamic_function(
        &mut self,
        args: &[JsValue],
        new_target: Option<&JsValue>,
    ) -> ERes {
        self.create_dynamic_function_kind(args, new_target, false)
    }

    /// CreateDynamicFunction (19.2.1.1.1) for `%Function%` (kind "normal") and
    /// `%AsyncFunction%` (kind "async"): the async kind assembles an
    /// `async function anonymous(P) {B}` source, so `await` in `B` is valid and
    /// the created function returns a promise (via the reactor wiring).
    pub(crate) fn create_dynamic_function_kind(
        &mut self,
        args: &[JsValue],
        new_target: Option<&JsValue>,
        is_async: bool,
    ) -> ERes {
        let (params, body) = match args.split_last() {
            None => (String::new(), String::new()),
            Some((last, init)) => {
                let mut p = String::new();
                for (i, a) in init.iter().enumerate() {
                    if i > 0 {
                        p.push(',');
                    }
                    p.push_str(&self.dyn_fn_arg_string(a)?);
                }
                (p, self.dyn_fn_arg_string(last)?)
            }
        };
        // The exact spec source string (newlines fence line-comment injection),
        // wrapped in parens so it parses as a function EXPRESSION.
        let kw = if is_async { "async function" } else { "function" };
        let source = format!("({kw} anonymous({params}\n) {{\n{body}\n}})");
        let prog = match parse_script(&source, false) {
            ParseOutcome::Script(p) => p,
            ParseOutcome::EarlyError { .. } => return Err(self.throw_native(ErrKind::Syntax)),
            ParseOutcome::Unsupported { reason } => {
                return Err(Abrupt::Fatal(format!(
                    "Function constructor body (out of slice): {reason}"
                )))
            }
        };
        let prog = Rc::new(prog);
        self.eval_programs.push(Rc::clone(&prog));
        let func = Self::extract_single_function(&prog)
            .ok_or_else(|| Abrupt::Fatal("Function source shape (interp bug)".to_string()))?;
        // Created with the global environment as scope (is_decl suppresses the
        // named-function-expression self-binding — the dynamic function is not
        // a NamedEvaluation). `create_function` gives an async function the
        // %AsyncFunction.prototype% [[Prototype]] and no own `prototype`.
        let fobj = self.create_function(func, EnvId(0), true, None, FnFlavor::Normal, None)?;
        if let Some(nt) = new_target {
            let (ctor_id, default_proto) = if is_async {
                (self.intr.async_function_ctor, self.intr.async_function_proto)
            } else {
                (self.intr.function_ctor, self.intr.function_proto)
            };
            if !matches!(nt, JsValue::Obj(o) if *o == ctor_id) {
                let proto = self.get_prototype_from_constructor(nt, default_proto)?;
                self.heap.obj_mut(fobj).proto = Some(proto);
            }
        }
        Ok(JsValue::Obj(fobj))
    }

    /// ToString a Function-constructor argument to a Rust string, refusing lone
    /// surrogates (the frozen parser consumes `&str`, not WTF-16).
    fn dyn_fn_arg_string(&mut self, v: &JsValue) -> Result<String, Abrupt> {
        let u = self.to_string_units(v)?;
        String::from_utf16(&u).map_err(|_| {
            Abrupt::Fatal("Function constructor argument with lone surrogate (out of slice)".to_string())
        })
    }

    fn extract_single_function(prog: &Program) -> Option<&Func> {
        let [Stmt::Expr(e)] = prog.body.as_slice() else {
            return None;
        };
        let mut cur = e;
        while let Expr::Paren(inner) = cur {
            cur = inner;
        }
        match cur {
            Expr::Function(f) => Some(f),
            _ => None,
        }
    }
}

/// True iff `callee` is a syntactic direct-eval reference: an unqualified
/// `eval` identifier, possibly parenthesized (`(eval)(x)` is still direct).
pub(crate) fn is_syntactic_eval_callee(callee: &Expr) -> bool {
    match callee {
        Expr::Ident(n) => n == "eval",
        Expr::Paren(inner) => is_syntactic_eval_callee(inner),
        _ => false,
    }
}
