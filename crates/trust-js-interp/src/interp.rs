// The interpreter core: state, resource caps, statement evaluation with spec
// completion values (UpdateEmpty), label sets, per-iteration loop
// environments, and script/function/class declaration instantiation
// (hoisting). Everything outside the S1a/S1b slices is
// `Abrupt::Fatal(reason)` — a sound refusal, never a wrong trace. Totality:
// call-depth cap, evaluation-depth cap (Rust stack safety), loop-iteration
// cap, string cap; no unsafe, no panics on hostile input (a `catch_unwind`
// belt sits in evaluate_case).
//
// Author: Andrew Yates
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

use std::collections::HashMap;
use std::rc::Rc;
use trust_js_parse::ast::{DeclKind, Expr, ForHead, ForInit, Func, Pat, Stmt, SwitchCase};
use trust_js_parse::Program;
use trust_js_trace::HostEvent;
use trust_js_value::{
    create_realm, Binding, EnvFrame, EnvId, Heap, Intrinsics, JsValue, ObjId, Property,
};

pub const MAX_CALL_DEPTH: u32 = 256;
pub const MAX_EVAL_DEPTH: u32 = 1500;
pub const MAX_LOOP_ITERS: u64 = 1_000_000;
pub const MAX_STRING_UNITS: usize = 10_000_000;
pub const MAX_HEAP_OBJECTS: usize = 4_000_000;

/// Abrupt completions plus the out-of-slice refusal channel.
#[derive(Debug)]
pub enum Abrupt {
    Break {
        label: Option<String>,
        value: Option<JsValue>,
    },
    Continue {
        label: Option<String>,
        value: Option<JsValue>,
    },
    Return(JsValue),
    Throw(JsValue),
    /// Out of slice / resource cap: the whole case refuses (NoCoverage).
    Fatal(String),
}

/// Statement completion: Ok(None) = normal-empty, Ok(Some(v)) = normal-value.
pub type Compl = Result<Option<JsValue>, Abrupt>;
pub type ERes = Result<JsValue, Abrupt>;

/// Static execution context: environment + strictness of the running code.
#[derive(Clone)]
pub struct Ctx {
    pub env: EnvId,
    pub strict: bool,
}

pub struct Interp {
    pub heap: Heap,
    pub intr: Intrinsics,
    pub global: ObjId,
    pub events: Vec<HostEvent>,
    pub call_depth: u32,
    pub eval_depth: u32,
    pub loop_iters: u64,
    /// Address-keyed Rc cache so closures created in loops do not re-clone
    /// their AST every iteration. Keys are addresses into ASTs kept alive for the
    /// whole evaluation (the parsed Program and previously cached clones).
    pub(crate) fn_cache: HashMap<usize, Rc<Func>>,
    /// Per-class-constructor metadata (instance fields, default-ctor flag).
    /// Persists across scripts (class objects escape into globals).
    pub(crate) class_info: HashMap<ObjId, Rc<crate::class_eval::ClassInfo>>,
    /// Template-site cache (GetTemplateObject identity), keyed on the
    /// quasis' AST address; cleared per script like `fn_cache`.
    pub(crate) tpl_cache: HashMap<usize, ObjId>,
    /// The realm's GlobalSymbolRegistry (Symbol.for / Symbol.keyFor).
    pub(crate) sym_registry: Vec<(trust_js_value::Units, trust_js_value::SymId)>,
    /// The driver's deterministic clock: observations of Date.now / new
    /// Date() / Date() each advance the fixed epoch by 1ms.
    pub(crate) clock_ticks: u64,
    /// [[RegExpMatcher]] side table: the compiled trust-js-regexp Pattern for
    /// each RegExp instance (ObjKind::Regex), keyed by ObjId. `Err(reason)`
    /// records an admitted-but-unsupported pattern (Annex-B / resource-extreme)
    /// — every match attempt on it refuses (NoCoverage), never a wrong result.
    pub(crate) regex_patterns:
        HashMap<ObjId, Result<Rc<trust_js_regexp::Pattern>, String>>,
    /// PrivateEnvironment arena (class private-name scopes).
    pub(crate) priv_envs: Vec<crate::private::PrivEnvData>,
    /// A class declarative environment → its PrivateEnvironment. Private-name
    /// resolution walks the env chain to the nearest entry here.
    pub(crate) priv_env_of: HashMap<EnvId, crate::private::PrivEnvId>,
    /// [[PrivateElements]] side table, keyed by object. Private elements live
    /// OUTSIDE `obj.props`, so they never surface to enumeration, reflection,
    /// or the trace projection.
    pub(crate) priv_elements: HashMap<ObjId, Vec<(crate::private::PrivName, crate::private::PrivElem)>>,
    /// Fresh private-name identity counter.
    pub(crate) next_priv_name: crate::private::PrivName,
    /// Generator suspension state (frame stack + [[GeneratorState]]), keyed by
    /// the generator instance ObjId (ObjKind::Generator). Lives OUTSIDE the
    /// heap object so resuming can borrow `&mut Interp` and the frame stack
    /// disjointly (the stack is `mem::take`n for the duration of a resume).
    pub(crate) gen_state: HashMap<ObjId, crate::generators::GenExec>,
    /// Built-in iterator-object state (Array/String/Map/Set iterators), keyed by
    /// the iterator instance ObjId (ObjKind::Iterator). Like `gen_state`, it
    /// lives outside the heap object so `.next()` can borrow `&mut Interp` and
    /// the state disjointly (the state is `remove`d for the duration of a step,
    /// which also blocks reentrant `next()` with the spec's TypeError).
    pub(crate) iter_state: HashMap<ObjId, crate::iterobj::IterObj>,
    /// Iterator Helper state (§27.1.4 map/filter/take/drop/flatMap), keyed by the
    /// helper instance ObjId (ObjKind::Iterator with %IteratorHelperPrototype%).
    /// Like `iter_state`, it lives outside the heap object so a `.next()`/
    /// `.return()` step can borrow `&mut Interp` and the state disjointly (the
    /// state is `remove`d for the duration of a step, which also blocks a
    /// reentrant `next()` with the spec's "generator is already executing"
    /// TypeError). A completed helper keeps a `Completed`-phase entry.
    pub(crate) helper_state: HashMap<ObjId, crate::iterhelp::IterHelper>,
    /// Parsed programs from `eval` / the `Function` constructor, kept alive for
    /// the whole case. The fn/template caches key AST-node ADDRESSES, so a
    /// dropped-and-reused address would alias a stale closure body; owning the
    /// programs here (like `evaluate_case`'s `programs`) keeps addresses stable.
    pub(crate) eval_programs: Vec<Rc<Program>>,
    /// The deterministic event loop (M2 D1). Stored `Some` when not actively
    /// borrowed; every reactor operation `take`s it out so `&mut Interp` (the
    /// `Host`) and `&mut Reactor` never alias, and host callbacks PARK it back
    /// here so reentrant JS finds it (see `rx_op` / `host_park` in host.rs).
    /// It starts at virtual epoch 0, mirroring the trace driver's `virtualNow`.
    pub(crate) reactor: Option<trust_js_reactor::Reactor<JsValue, crate::host::JobFn>>,
    /// Async-function suspension records (frame stack + [[GeneratorState]] +
    /// the result promise), indexed by `AsyncId`. Lives outside the heap so a
    /// resume can `mem::take` the frame stack disjointly from `&mut Interp`.
    pub(crate) async_execs: Vec<Option<crate::host::AsyncExec>>,
    /// Async generator suspension records (§27.6): frame stack (AsyncGen mode) +
    /// [[AsyncGeneratorState]] + [[AsyncGeneratorQueue]], keyed by the async
    /// generator instance ObjId (ObjKind::AsyncGenerator). Lives outside the
    /// heap so a resume can `mem::take` the frame stack disjointly.
    pub(crate) async_gen_state: HashMap<ObjId, crate::generators::AsyncGenExec>,
    /// CreateResolvingFunctions capabilities, keyed by the resolve/reject
    /// function object's `ObjId` (the reactor holds the promise state).
    pub(crate) resolve_caps: HashMap<ObjId, crate::host::ResolveEntry>,
    /// `finally` value-transform thunk payloads: `(value, throw?)` keyed by the
    /// thunk function object's `ObjId`.
    pub(crate) thunk_values: HashMap<ObjId, (JsValue, bool)>,
    /// NewPromiseCapability GetCapabilitiesExecutor records: the shared
    /// `[[Resolve]]`/`[[Reject]]` slot a `new C(executor)` executor writes,
    /// keyed by the executor function object's `ObjId`. Present only for the
    /// duration of the enclosing `Construct(C, «executor»)`.
    pub(crate) cap_states: HashMap<ObjId, Rc<std::cell::RefCell<crate::promise::CapRecord>>>,
    /// Combinator (all / allSettled / any) per-element closure state for a
    /// non-intrinsic receiver C, keyed by the element function object's `ObjId`.
    pub(crate) comb_elements: HashMap<ObjId, crate::promise::CombElement>,
    /// Set when a mid-drain refusal (an out-of-slice async continuation, or a
    /// throwing raw microtask/timer callback) makes the whole case NoCoverage.
    /// Once set, all further host callbacks are inert so the drain quiesces.
    pub(crate) drain_fault: Option<String>,
    /// Driver-compatible 1-based timer id counter (the trace driver's
    /// `++timerSeq`): the value `setTimeout` returns and `clearTimeout` matches.
    pub(crate) timer_seq: u64,
    /// Map from a driver-compatible timer id to the reactor's `TimerId`, so
    /// `clearTimeout` cancels the right reactor timer.
    pub(crate) timer_map: HashMap<u64, u64>,
    /// `Proxy.revocable` revoker closures: the revoker function object's `ObjId`
    /// → its `[[RevocableProxy]]` (the proxy `ObjId`, or `None` once revoked).
    pub(crate) revoke_targets: HashMap<ObjId, Option<ObjId>>,
    /// §26.1 `[[WeakRefTarget]]`, keyed by the WeakRef instance's `ObjId`. The
    /// presence of the key is the brand: `deref` on an object not here throws.
    /// GC is unobservable in the synchronous slice, so the target is never
    /// cleared — `deref` always returns it.
    pub(crate) weakref_targets: HashMap<ObjId, JsValue>,
    /// §26.2 FinalizationRegistry `[[Cells]]` (the per-cell unregister tokens,
    /// `None` = registered without a token), keyed by the registry instance's
    /// `ObjId`. Presence is the brand. No cleanup callback ever runs, so only
    /// the tokens (what `unregister` observes) are retained.
    pub(crate) finreg_cells: HashMap<ObjId, Vec<Option<JsValue>>>,
    /// Explicit resource management (§14.3.3): the `[[DisposeCapability]]` of a
    /// block/function scope that carries a top-level `using`, keyed by the
    /// scope's environment `EnvId`. A `using` declaration only registers when
    /// its environment has an entry here — the scope that establishes it also
    /// runs DisposeResources on exit — so a `using` in a scope this interpreter
    /// does not dispose refuses (never leaks an undisposed resource).
    pub(crate) dispose_stacks: HashMap<EnvId, Vec<crate::dispose::DisposableResource>>,
    /// §27.3 `DisposableStack` instance state ([[DisposableState]] +
    /// [[DisposeCapability]]), keyed by the instance `ObjId`. Presence is the
    /// brand (RequireInternalSlot).
    pub(crate) disposable_stack_state: HashMap<ObjId, crate::dispose::DisposableStackData>,
}

impl Interp {
    #[must_use]
    pub fn new() -> Interp {
        let mut heap = Heap::new();
        let realm = create_realm(&mut heap);
        Interp {
            heap,
            intr: realm.intr,
            global: realm.global,
            events: Vec::new(),
            call_depth: 0,
            eval_depth: 0,
            loop_iters: 0,
            fn_cache: HashMap::new(),
            class_info: HashMap::new(),
            tpl_cache: HashMap::new(),
            sym_registry: Vec::new(),
            clock_ticks: 0,
            regex_patterns: HashMap::new(),
            priv_envs: Vec::new(),
            priv_env_of: HashMap::new(),
            priv_elements: HashMap::new(),
            next_priv_name: 0,
            gen_state: HashMap::new(),
            iter_state: HashMap::new(),
            helper_state: HashMap::new(),
            eval_programs: Vec::new(),
            reactor: Some(trust_js_reactor::Reactor::new(0)),
            async_execs: Vec::new(),
            async_gen_state: HashMap::new(),
            resolve_caps: HashMap::new(),
            thunk_values: HashMap::new(),
            cap_states: HashMap::new(),
            comb_elements: HashMap::new(),
            drain_fault: None,
            timer_seq: 0,
            timer_map: HashMap::new(),
            revoke_targets: HashMap::new(),
            weakref_targets: HashMap::new(),
            finreg_cells: HashMap::new(),
            dispose_stacks: HashMap::new(),
            disposable_stack_state: HashMap::new(),
        }
    }

    pub(crate) fn charge_loop(&mut self) -> Result<(), Abrupt> {
        self.loop_iters += 1;
        if self.loop_iters > MAX_LOOP_ITERS {
            Err(Abrupt::Fatal("loop iteration cap exceeded".to_string()))
        } else {
            Ok(())
        }
    }

    pub(crate) fn alloc_obj(&mut self, o: trust_js_value::JsObject) -> Result<ObjId, Abrupt> {
        if self.heap.objects.len() >= MAX_HEAP_OBJECTS {
            return Err(Abrupt::Fatal("heap object cap exceeded".to_string()));
        }
        Ok(self.heap.alloc(o))
    }

    pub(crate) fn alloc_env(&mut self, parent: Option<EnvId>) -> EnvId {
        self.heap.alloc_env(EnvFrame::new(parent))
    }

    /// Nearest intrinsic prototype on the chain, in the driver's list order.
    #[must_use]
    pub fn class_tag(&self, oid: ObjId) -> Option<String> {
        let mut p = self.heap.obj(oid).proto;
        let mut hops = 0;
        while let Some(id) = p {
            if hops >= 32 {
                return None;
            }
            for (proto_id, name) in self.intr.class_tag_list() {
                if id == proto_id {
                    return Some(name.to_string());
                }
            }
            p = self.heap.obj(id).proto;
            hops += 1;
        }
        None
    }

    // -- scripts ------------------------------------------------------------

    /// Evaluate one script (harness include or body) sharing this realm,
    /// mirroring the driver's indirect eval: sloppy scripts hoist functions
    /// and vars onto the global object ({w,e,c: true}); strict scripts get a
    /// fresh declarative var+lexical environment. Lexical declarations live
    /// in a fresh per-script environment either way. Returns the script
    /// completion value.
    pub fn run_script(&mut self, prog: &Program) -> ERes {
        // The fn/template caches key AST-node ADDRESSES. The caller keeps
        // every parsed Program alive for the whole case (evaluate_case's
        // `programs` vector), so addresses are never reused and cached
        // entries — including the OBSERVABLE template-site identity across
        // scripts — stay valid.
        let root = EnvId(0);
        let analysis = hoist::analyze(&prog.body, prog.strict).map_err(Abrupt::Fatal)?;
        let env = self.alloc_env(Some(root));
        // Lexical declarations first (TDZ before function instantiation).
        for (name, mutable) in hoist::lexical_decls(&prog.body).map_err(Abrupt::Fatal)? {
            self.heap
                .env_mut(env)
                .bindings
                .insert(name, Binding::tdz(mutable));
        }
        if prog.strict {
            for f in &analysis.funcs {
                let fobj = self.instantiate_hoisted_function(f, env)?;
                self.heap.env_mut(env).bindings.insert(
                    f.name.clone().expect("declaration has a name"),
                    Binding::var(JsValue::Obj(fobj)),
                );
            }
            for v in &analysis.vars {
                if !self.heap.env(env).bindings.contains_key(v) {
                    self.heap
                        .env_mut(env)
                        .bindings
                        .insert(v.clone(), Binding::var(JsValue::Undefined));
                }
            }
        } else {
            for f in &analysis.funcs {
                let fobj = self.instantiate_hoisted_function(f, env)?;
                let name = f.name.clone().expect("declaration has a name");
                self.create_global_function_binding(&name, fobj)?;
            }
            for v in &analysis.vars {
                let key = trust_js_value::PropKey::from_str(v);
                if !self.heap.obj(self.global).props.contains_key(&key) {
                    self.heap
                        .obj_mut(self.global)
                        .props
                        .insert(key, Property::data(JsValue::Undefined));
                }
            }
        }
        let ctx = Ctx {
            env,
            strict: prog.strict,
        };
        let mut v: Option<JsValue> = None;
        self.eval_stmt_list(&prog.body, &ctx, &mut v)?;
        Ok(v.unwrap_or(JsValue::Undefined))
    }

    /// CreateGlobalFunctionBinding (sloppy indirect eval): {w,e,c:true} when
    /// definable; TypeError against a non-configurable unsuitable slot.
    pub(crate) fn create_global_function_binding(&mut self, name: &str, fobj: ObjId) -> Result<(), Abrupt> {
        let key = trust_js_value::PropKey::from_str(name);
        let existing = self.heap.obj(self.global).props.get(&key);
        match existing {
            None => {
                self.heap
                    .obj_mut(self.global)
                    .props
                    .insert(key, Property::data(JsValue::Obj(fobj)));
                Ok(())
            }
            Some(p) if p.configurable => {
                self.heap
                    .obj_mut(self.global)
                    .props
                    .insert(key, Property::data(JsValue::Obj(fobj)));
                Ok(())
            }
            Some(p) => {
                let ok = match &p.v {
                    trust_js_value::PropValue::Data { writable, .. } => *writable && p.enumerable,
                    trust_js_value::PropValue::Accessor { .. } => false,
                };
                if ok {
                    if let Some(p) = self.heap.obj_mut(self.global).props.get_mut(&key) {
                        p.v = trust_js_value::PropValue::Data {
                            value: JsValue::Obj(fobj),
                            writable: true,
                        };
                        p.synthetic = false;
                    }
                    Ok(())
                } else {
                    Err(self.throw_type_error())
                }
            }
        }
    }

    // -- statement lists -----------------------------------------------------

    /// Evaluate a statement list, folding non-empty completion values into
    /// `v` and patching empty-valued break/continue with `v` (UpdateEmpty).
    pub(crate) fn eval_stmt_list(
        &mut self,
        stmts: &[Stmt],
        ctx: &Ctx,
        v: &mut Option<JsValue>,
    ) -> Result<(), Abrupt> {
        for s in stmts {
            match self.eval_stmt(s, ctx) {
                Ok(Some(val)) => *v = Some(val),
                Ok(None) => {}
                Err(a) => return Err(patch_empty(a, v)),
            }
        }
        Ok(())
    }

    pub(crate) fn eval_stmt(&mut self, s: &Stmt, ctx: &Ctx) -> Compl {
        self.eval_depth += 1;
        let r = if self.eval_depth > MAX_EVAL_DEPTH {
            Err(Abrupt::Fatal("evaluation depth cap exceeded".to_string()))
        } else {
            self.eval_stmt_labeled(s, ctx, &[])
        };
        self.eval_depth -= 1;
        r
    }

    #[allow(clippy::too_many_lines)]
    fn eval_stmt_labeled(&mut self, s: &Stmt, ctx: &Ctx, labels: &[String]) -> Compl {
        match s {
            Stmt::Empty | Stmt::FuncDecl(_) | Stmt::Debugger => Ok(None),
            // Module `import`/`export` declarations never reach the script
            // interpreter (parse_script does not produce them); the module goal
            // is out of the interpreter's slice.
            Stmt::Import(_) | Stmt::Export(_) => Err(Abrupt::Fatal(
                "module import/export declaration (out of slice)".to_string(),
            )),
            Stmt::Expr(e) => Ok(Some(self.eval_expr(e, ctx)?)),
            Stmt::Decl { kind, decls } => self.eval_decl(*kind, decls, ctx),
            Stmt::Block(body) => self.eval_block(body, ctx),
            Stmt::If { test, cons, alt } => {
                let t = self.eval_expr(test, ctx)?;
                let r = if self.to_boolean(&t) {
                    if matches!(cons.as_ref(), Stmt::FuncDecl(_)) {
                        return Err(Abrupt::Fatal(
                            "function declaration as if-branch (Annex B, out of slice)"
                                .to_string(),
                        ));
                    }
                    self.eval_stmt(cons, ctx)
                } else if let Some(a) = alt {
                    if matches!(a.as_ref(), Stmt::FuncDecl(_)) {
                        return Err(Abrupt::Fatal(
                            "function declaration as if-branch (Annex B, out of slice)"
                                .to_string(),
                        ));
                    }
                    self.eval_stmt(a, ctx)
                } else {
                    Ok(None)
                };
                update_empty(r, JsValue::Undefined)
            }
            Stmt::While { test, body } => self.eval_while(test, body, ctx, labels),
            Stmt::DoWhile { body, test } => self.eval_do_while(body, test, ctx, labels),
            Stmt::For {
                init,
                test,
                update,
                body,
            } => self.eval_for(init.as_ref(), test.as_ref(), update.as_ref(), body, ctx, labels),
            Stmt::ForIn { left, right, body } => self.eval_for_in(left, right, body, ctx, labels),
            Stmt::ForOf {
                left,
                right,
                body,
                is_await,
            } => {
                if *is_await {
                    return Err(Abrupt::Fatal("for-await-of (async, M2)".to_string()));
                }
                self.eval_for_of(left, right, body, ctx, labels)
            }
            Stmt::Return(arg) => {
                let v = match arg {
                    Some(e) => self.eval_expr(e, ctx)?,
                    None => JsValue::Undefined,
                };
                Err(Abrupt::Return(v))
            }
            Stmt::Throw(e) => {
                let v = self.eval_expr(e, ctx)?;
                Err(Abrupt::Throw(v))
            }
            Stmt::Break(l) => Err(Abrupt::Break {
                label: l.clone(),
                value: None,
            }),
            Stmt::Continue(l) => Err(Abrupt::Continue {
                label: l.clone(),
                value: None,
            }),
            Stmt::Labeled { label, body } => {
                if matches!(body.as_ref(), Stmt::FuncDecl(_)) {
                    return Err(Abrupt::Fatal(
                        "labelled function declaration (Annex B, out of slice)".to_string(),
                    ));
                }
                let mut ls = labels.to_vec();
                ls.push(label.clone());
                match self.eval_stmt_labeled(body, ctx, &ls) {
                    Err(Abrupt::Break {
                        label: Some(l),
                        value,
                    }) if l == *label => Ok(value),
                    other => other,
                }
            }
            Stmt::Switch { disc, cases } => self.eval_switch(disc, cases, ctx),
            Stmt::Try {
                block,
                catch,
                finally,
            } => self.eval_try(block, catch.as_ref(), finally.as_ref(), ctx),
            Stmt::With { .. } => Err(Abrupt::Fatal("with statement (out of slice)".to_string())),
            Stmt::ClassDecl(c) => {
                // BindingClassDeclarationEvaluation: evaluate, then
                // initialize the (TDZ-pre-declared) lexical binding.
                let v = self.eval_class(c, ctx, None)?;
                let name = c
                    .name
                    .as_deref()
                    .ok_or_else(|| Abrupt::Fatal("unnamed class declaration".to_string()))?;
                self.initialize_binding(ctx.env, name, v)?;
                Ok(None)
            }
        }
    }

    // -- declarations --------------------------------------------------------

    pub(crate) fn eval_decl(&mut self, kind: DeclKind, decls: &[(Pat, Option<Expr>)], ctx: &Ctx) -> Compl {
        match kind {
            DeclKind::Var => {
                for (pat, init) in decls {
                    match (pat, init) {
                        (Pat::Ident(name), Some(e)) => {
                            let v = self.eval_expr_named(e, name, ctx)?;
                            self.env_set(ctx, name, v)?;
                        }
                        (Pat::Ident(_), None) => {}
                        (pat, Some(e)) => {
                            let v = self.eval_expr(e, ctx)?;
                            self.bind_pattern(pat, v, None, ctx)?;
                        }
                        (_, None) => {
                            return Err(Abrupt::Fatal(
                                "var pattern without initializer (parser bug?)".to_string(),
                            ))
                        }
                    }
                }
                Ok(None)
            }
            DeclKind::Let | DeclKind::Const => {
                for (pat, init) in decls {
                    match (pat, init) {
                        (Pat::Ident(name), Some(e)) => {
                            let v = self.eval_expr_named(e, name, ctx)?;
                            self.initialize_binding(ctx.env, name, v)?;
                        }
                        (Pat::Ident(name), None) => {
                            self.initialize_binding(ctx.env, name, JsValue::Undefined)?;
                        }
                        (pat, Some(e)) => {
                            let v = self.eval_expr(e, ctx)?;
                            self.bind_pattern(pat, v, Some(ctx.env), ctx)?;
                        }
                        (_, None) => {
                            return Err(Abrupt::Fatal(
                                "lexical pattern without initializer (parser bug?)".to_string(),
                            ))
                        }
                    }
                }
                Ok(None)
            }
            DeclKind::Using => {
                // A sync `using` only registers when its environment has an
                // active DisposeCapability — the enclosing block/function scope
                // installed one (because it saw a top-level `using`) and will
                // run DisposeResources on exit. A `using` in a scope this
                // interpreter does not dispose (switch case block, for-head,
                // async/generator body, module top level) has no entry here and
                // refuses, never leaking an undisposed resource.
                if !self.dispose_stacks.contains_key(&ctx.env) {
                    return Err(Abrupt::Fatal(
                        "using declaration in a scope without an active DisposeCapability \
                         (explicit resource management, out of slice)"
                            .to_string(),
                    ));
                }
                for (pat, init) in decls {
                    let Pat::Ident(name) = pat else {
                        return Err(Abrupt::Fatal(
                            "using declaration with a non-identifier binding (parser bug?)"
                                .to_string(),
                        ));
                    };
                    let e = init.as_ref().ok_or_else(|| {
                        Abrupt::Fatal("using declaration without initializer (parser bug?)".to_string())
                    })?;
                    // BindingEvaluation: evaluate initializer, InitializeReferencedBinding,
                    // then AddDisposableResource (sync-dispose). A bad @@dispose
                    // throws here AFTER earlier bindings were registered, so the
                    // scope's DisposeResources still disposes them.
                    let v = self.eval_expr_named(e, name, ctx)?;
                    self.initialize_binding(ctx.env, name, v.clone())?;
                    if let Some(resource) = self.create_sync_disposable_resource(&v)? {
                        self.dispose_stacks
                            .get_mut(&ctx.env)
                            .expect("dispose capability present")
                            .push(resource);
                    }
                }
                Ok(None)
            }
            DeclKind::AwaitUsing => Err(Abrupt::Fatal(
                "await using declaration (async explicit resource management, out of slice)"
                    .to_string(),
            )),
        }
    }

    // -- blocks --------------------------------------------------------------

    /// Block evaluation with lexical instantiation: let/const enter TDZ, then
    /// (strict code) block-level function declarations are instantiated.
    /// Sloppy block-level function declarations carry Annex B semantics and
    /// were already refused during hoisting.
    fn eval_block(&mut self, body: &[Stmt], ctx: &Ctx) -> Compl {
        let inner = self.enter_block_scope(body, ctx)?;
        // §14.2.2: a block with a top-level `using` establishes a
        // DisposeCapability and runs DisposeResources over its own completion
        // on exit (normal AND abrupt).
        let has_using = hoist::has_top_level_sync_using(body);
        if has_using {
            self.dispose_stacks.insert(inner.env, Vec::new());
        }
        let mut v: Option<JsValue> = None;
        let completion = self.eval_stmt_list(body, &inner, &mut v).map(|()| v);
        if has_using {
            let resources = self.dispose_stacks.remove(&inner.env).unwrap_or_default();
            self.dispose_resources(resources, completion)
        } else {
            completion
        }
    }

    pub(crate) fn enter_block_scope(&mut self, body: &[Stmt], ctx: &Ctx) -> Result<Ctx, Abrupt> {
        let env = self.alloc_env(Some(ctx.env));
        for (name, mutable) in hoist::lexical_decls(body).map_err(Abrupt::Fatal)? {
            self.heap
                .env_mut(env)
                .bindings
                .insert(name, Binding::tdz(mutable));
        }
        if ctx.strict {
            for f in hoist::direct_func_decls(body) {
                let fobj = self.instantiate_hoisted_function(f, env)?;
                self.heap.env_mut(env).bindings.insert(
                    f.name.clone().expect("declaration has a name"),
                    Binding::var(JsValue::Obj(fobj)),
                );
            }
        }
        Ok(Ctx {
            env,
            strict: ctx.strict,
        })
    }

    // -- loops ---------------------------------------------------------------

    fn eval_while(&mut self, test: &Expr, body: &Stmt, ctx: &Ctx, labels: &[String]) -> Compl {
        let mut v = JsValue::Undefined;
        loop {
            let t = self.eval_expr(test, ctx)?;
            if !self.to_boolean(&t) {
                return Ok(Some(v));
            }
            self.charge_loop()?;
            match self.loop_body_step(body, ctx, labels, &mut v)? {
                LoopFlow::Continue => {}
                LoopFlow::Break(bv) => return Ok(Some(bv.unwrap_or(v))),
            }
        }
    }

    fn eval_do_while(&mut self, body: &Stmt, test: &Expr, ctx: &Ctx, labels: &[String]) -> Compl {
        let mut v = JsValue::Undefined;
        loop {
            self.charge_loop()?;
            match self.loop_body_step(body, ctx, labels, &mut v)? {
                LoopFlow::Continue => {}
                LoopFlow::Break(bv) => return Ok(Some(bv.unwrap_or(v))),
            }
            let t = self.eval_expr(test, ctx)?;
            if !self.to_boolean(&t) {
                return Ok(Some(v));
            }
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn eval_for(
        &mut self,
        init: Option<&ForInit>,
        test: Option<&Expr>,
        update: Option<&Expr>,
        body: &Stmt,
        ctx: &Ctx,
        labels: &[String],
    ) -> Compl {
        let mut cur = ctx.clone();
        let mut per_iter: Vec<String> = Vec::new();
        match init {
            Some(ForInit::Decl(DeclKind::Var, decls)) => {
                self.eval_decl(DeclKind::Var, decls, ctx)?;
            }
            Some(ForInit::Decl(kind @ (DeclKind::Let | DeclKind::Const), decls)) => {
                let env = self.alloc_env(Some(ctx.env));
                let mutable = *kind == DeclKind::Let;
                let mut names = Vec::new();
                for (pat, _) in decls {
                    hoist::pat_bound_names(pat, &mut names);
                }
                for n in &names {
                    self.heap
                        .env_mut(env)
                        .bindings
                        .insert(n.clone(), Binding::tdz(mutable));
                }
                cur = Ctx {
                    env,
                    strict: ctx.strict,
                };
                self.eval_decl(*kind, decls, &cur)?;
                if mutable {
                    per_iter = names;
                }
            }
            Some(ForInit::Decl(DeclKind::Using | DeclKind::AwaitUsing, _)) => {
                return Err(Abrupt::Fatal("using declaration (out of slice)".to_string()))
            }
            Some(ForInit::Expr(e)) => {
                self.eval_expr(e, &cur)?;
            }
            None => {}
        }
        if !per_iter.is_empty() {
            cur = self.copy_per_iteration_env(&cur, &per_iter, ctx.env)?;
        }
        let mut v = JsValue::Undefined;
        loop {
            if let Some(t) = test {
                let tv = self.eval_expr(t, &cur)?;
                if !self.to_boolean(&tv) {
                    return Ok(Some(v));
                }
            }
            self.charge_loop()?;
            match self.loop_body_step(body, &cur, labels, &mut v)? {
                LoopFlow::Continue => {}
                LoopFlow::Break(bv) => return Ok(Some(bv.unwrap_or(v))),
            }
            if !per_iter.is_empty() {
                cur = self.copy_per_iteration_env(&cur, &per_iter, ctx.env)?;
            }
            if let Some(u) = update {
                self.eval_expr(u, &cur)?;
            }
        }
    }

    /// CreatePerIterationEnvironment: fresh env (child of the loop's OUTER
    /// env) carrying copies of the per-iteration bindings.
    pub(crate) fn copy_per_iteration_env(
        &mut self,
        cur: &Ctx,
        names: &[String],
        outer: EnvId,
    ) -> Result<Ctx, Abrupt> {
        let fresh = self.alloc_env(Some(outer));
        for n in names {
            let b = self
                .lookup_binding_value(cur.env, n)
                .ok_or_else(|| Abrupt::Fatal(format!("per-iteration binding `{n}` missing")))?;
            self.heap
                .env_mut(fresh)
                .bindings
                .insert(n.clone(), Binding::var(b));
        }
        Ok(Ctx {
            env: fresh,
            strict: cur.strict,
        })
    }

    fn lookup_binding_value(&self, env: EnvId, name: &str) -> Option<JsValue> {
        let mut cur = Some(env);
        while let Some(e) = cur {
            if let Some(b) = self.heap.env(e).bindings.get(name) {
                return Some(b.value.clone());
            }
            cur = self.heap.env(e).parent;
        }
        None
    }

    fn loop_body_step(
        &mut self,
        body: &Stmt,
        ctx: &Ctx,
        labels: &[String],
        v: &mut JsValue,
    ) -> Result<LoopFlow, Abrupt> {
        match self.eval_stmt(body, ctx) {
            Ok(Some(val)) => {
                *v = val;
                Ok(LoopFlow::Continue)
            }
            Ok(None) => Ok(LoopFlow::Continue),
            Err(Abrupt::Continue { label, value }) => {
                if label.as_ref().is_none_or(|l| labels.contains(l)) {
                    if let Some(cv) = value {
                        *v = cv;
                    }
                    Ok(LoopFlow::Continue)
                } else {
                    Err(Abrupt::Continue { label, value })
                }
            }
            Err(Abrupt::Break { label, value }) => {
                if label.as_ref().is_none_or(|l| labels.contains(l)) {
                    Ok(LoopFlow::Break(value))
                } else {
                    Err(Abrupt::Break { label, value })
                }
            }
            Err(a) => Err(a),
        }
    }

    // -- for-in / for-of -----------------------------------------------------

    /// ForIn/OfHeadEvaluation (14.7.5.6): when the head is a lexical
    /// ForDeclaration, the iterated expression evaluates inside a fresh
    /// environment whose bound names exist but are UNINITIALIZED (TDZ) —
    /// `for (let x of [x])` throws ReferenceError, and closures created
    /// during the head expression keep seeing that TDZ scope.
    pub(crate) fn head_expr_ctx(&mut self, left: &ForHead, ctx: &Ctx) -> Ctx {
        if let ForHead::Decl(DeclKind::Let | DeclKind::Const, pat) = left {
            let env = self.alloc_env(Some(ctx.env));
            let mut names = Vec::new();
            hoist::pat_bound_names(pat, &mut names);
            for n in names {
                // Spec: CreateMutableBinding for BOTH let and const here
                // (never initialized; only the TDZ state is observable).
                self.heap
                    .env_mut(env)
                    .bindings
                    .insert(n, Binding::tdz(true));
            }
            Ctx {
                env,
                strict: ctx.strict,
            }
        } else {
            ctx.clone()
        }
    }

    fn eval_for_in(
        &mut self,
        left: &ForHead,
        right: &Expr,
        body: &Stmt,
        ctx: &Ctx,
        labels: &[String],
    ) -> Compl {
        let head_ctx = self.head_expr_ctx(left, ctx);
        let rv = self.eval_expr(right, &head_ctx)?;
        if rv.is_nullish() {
            return Ok(Some(JsValue::Undefined));
        }
        let oid = self.to_object(&rv)?;
        let keys = self.for_in_keys(oid)?;
        let mut v = JsValue::Undefined;
        for key in keys {
            self.charge_loop()?;
            // Skip keys deleted (from the whole chain) before their visit.
            if !self.has_property(oid, &trust_js_value::PropKey::Str(key.clone()))? {
                continue;
            }
            let kv = JsValue::Str(Rc::new(key));
            let inner = self.bind_for_head(left, kv, ctx)?;
            match self.loop_body_step(body, &inner, labels, &mut v)? {
                LoopFlow::Continue => {}
                LoopFlow::Break(bv) => return Ok(Some(bv.unwrap_or(v))),
            }
        }
        Ok(Some(v))
    }

    fn eval_for_of(
        &mut self,
        left: &ForHead,
        right: &Expr,
        body: &Stmt,
        ctx: &Ctx,
        labels: &[String],
    ) -> Compl {
        let head_ctx = self.head_expr_ctx(left, ctx);
        let rv = self.eval_expr(right, &head_ctx)?;
        let mut it = self.get_iterator_or_type_error(&rv)?;
        let mut v = JsValue::Undefined;
        loop {
            self.charge_loop()?;
            // IteratorStep: a step throw leaves the iterator done — propagate
            // WITHOUT IteratorClose (spec sets [[Done]] on a `next` throw).
            let nv = match self.fast_iter_next(&mut it) {
                Ok(Some(nv)) => nv,
                Ok(None) => return Ok(Some(v)),
                Err(a) => return Err(a),
            };
            // Head binding + body: any abrupt here runs IteratorClose (14.7.5.7
            // ForIn/OfBodyEvaluation closes the iterator on an abrupt body/
            // binding completion).
            let step = (|it: &mut Self| -> Result<LoopFlow, Abrupt> {
                let inner = it.bind_for_head(left, nv, ctx)?;
                it.loop_body_step(body, &inner, labels, &mut v)
            })(self);
            match step {
                Ok(LoopFlow::Continue) => {}
                Ok(LoopFlow::Break(bv)) => {
                    // A matched break is a normal (non-throw) completion.
                    self.iterator_close(&it, false)?;
                    return Ok(Some(bv.unwrap_or(v)));
                }
                Err(a) => return Err(self.close_after_body_abrupt(&it, a)),
            }
        }
    }

    /// Bind one iteration value to a for-in/for-of head, returning the body
    /// context (fresh per-iteration env for lexical heads).
    pub(crate) fn bind_for_head(&mut self, left: &ForHead, v: JsValue, ctx: &Ctx) -> Result<Ctx, Abrupt> {
        match left {
            ForHead::Decl(DeclKind::Var, pat) => {
                self.bind_pattern(pat, v, None, ctx)?;
                Ok(ctx.clone())
            }
            ForHead::Decl(kind @ (DeclKind::Let | DeclKind::Const), pat) => {
                let env = self.alloc_env(Some(ctx.env));
                let mut names = Vec::new();
                hoist::pat_bound_names(pat, &mut names);
                for n in &names {
                    self.heap
                        .env_mut(env)
                        .bindings
                        .insert(n.clone(), Binding::tdz(*kind == DeclKind::Let));
                }
                let inner = Ctx {
                    env,
                    strict: ctx.strict,
                };
                self.bind_pattern(pat, v, Some(env), &inner)?;
                Ok(inner)
            }
            ForHead::Decl(DeclKind::Using | DeclKind::AwaitUsing, _) => {
                Err(Abrupt::Fatal("using for-head (out of slice)".to_string()))
            }
            ForHead::Pat(pat) => {
                self.bind_pattern(pat, v, None, ctx)?;
                Ok(ctx.clone())
            }
        }
    }

    // -- switch --------------------------------------------------------------

    fn eval_switch(&mut self, disc: &Expr, cases: &[SwitchCase], ctx: &Ctx) -> Compl {
        let d = self.eval_expr(disc, ctx)?;
        // One block scope for the whole case block. Scope entry iterates the
        // ORIGINAL case bodies (never a temporary clone: function objects
        // must close over AST nodes that stay alive).
        let env = self.alloc_env(Some(ctx.env));
        for case in cases {
            for (name, mutable) in hoist::lexical_decls(&case.body).map_err(Abrupt::Fatal)? {
                self.heap
                    .env_mut(env)
                    .bindings
                    .insert(name, Binding::tdz(mutable));
            }
        }
        if ctx.strict {
            for case in cases {
                for f in hoist::direct_func_decls(&case.body) {
                    let fobj = self.instantiate_hoisted_function(f, env)?;
                    self.heap.env_mut(env).bindings.insert(
                        f.name.clone().expect("declaration has a name"),
                        Binding::var(JsValue::Obj(fobj)),
                    );
                }
            }
        }
        let inner = Ctx {
            env,
            strict: ctx.strict,
        };
        let mut start: Option<usize> = None;
        for (i, case) in cases.iter().enumerate() {
            if let Some(t) = &case.test {
                let tv = self.eval_expr(t, &inner)?;
                if crate::ops::strict_eq(&d, &tv) {
                    start = Some(i);
                    break;
                }
            }
        }
        if start.is_none() {
            start = cases.iter().position(|c| c.test.is_none());
        }
        let Some(start) = start else {
            return Ok(Some(JsValue::Undefined));
        };
        let mut v = JsValue::Undefined;
        for case in &cases[start..] {
            let mut lv: Option<JsValue> = Some(v.clone());
            match self.eval_stmt_list(&case.body, &inner, &mut lv) {
                Ok(()) => {
                    if let Some(val) = lv {
                        v = val;
                    }
                }
                Err(Abrupt::Break { label: None, value }) => {
                    return Ok(Some(value.or(lv).unwrap_or(JsValue::Undefined)));
                }
                Err(a) => return Err(a),
            }
        }
        Ok(Some(v))
    }

    // -- try -----------------------------------------------------------------

    fn eval_try(
        &mut self,
        block: &[Stmt],
        catch: Option<&(Option<Pat>, Vec<Stmt>)>,
        finally: Option<&Vec<Stmt>>,
        ctx: &Ctx,
    ) -> Compl {
        let b = self.eval_block(block, ctx);
        let handled = match b {
            Err(Abrupt::Throw(exc)) => {
                if let Some((param, cbody)) = catch {
                    self.eval_catch(param.as_ref(), cbody, exc, ctx)
                } else {
                    Err(Abrupt::Throw(exc))
                }
            }
            other => other,
        };
        // A Fatal (out-of-slice refusal) from the guarded block/catch is NOT a
        // JS completion `finally` may override: the finally block's own behavior
        // generally depends on the unmodeled effects we just refused (e.g. a
        // counter the refused call would have incremented), so running it — and
        // letting an abrupt finally replace the refusal — would fabricate a
        // trace. Propagate the refusal immediately, without running `finally`.
        if matches!(handled, Err(Abrupt::Fatal(_))) {
            return handled;
        }
        let result = if let Some(fbody) = finally {
            match self.eval_block(fbody, ctx) {
                Ok(_) => handled, // finally's normal completion is discarded
                Err(fa) => Err(fa),
            }
        } else {
            handled
        };
        update_empty(result, JsValue::Undefined)
    }

    fn eval_catch(
        &mut self,
        param: Option<&Pat>,
        body: &[Stmt],
        exc: JsValue,
        ctx: &Ctx,
    ) -> Compl {
        let cenv = self.alloc_env(Some(ctx.env));
        let cctx = Ctx {
            env: cenv,
            strict: ctx.strict,
        };
        if let Some(pat) = param {
            let mut names = Vec::new();
            hoist::pat_bound_names(pat, &mut names);
            for n in &names {
                self.heap
                    .env_mut(cenv)
                    .bindings
                    .insert(n.clone(), Binding::tdz(true));
            }
            self.bind_pattern(pat, exc, Some(cenv), &cctx)?;
        }
        self.eval_block(body, &cctx)
    }

    // -- bindings ------------------------------------------------------------

    pub(crate) fn initialize_binding(
        &mut self,
        env: EnvId,
        name: &str,
        val: JsValue,
    ) -> Result<(), Abrupt> {
        let mut cur = Some(env);
        while let Some(e) = cur {
            if let Some(b) = self.heap.env_mut(e).bindings.get_mut(name) {
                b.value = val;
                b.initialized = true;
                return Ok(());
            }
            cur = self.heap.env(e).parent;
        }
        Err(Abrupt::Fatal(format!(
            "lexical binding `{name}` not pre-declared (interpreter bug)"
        )))
    }

    // -- module bodies (multi-module linking, increment 2b-part-3) ----------

    /// Evaluate one module body (an export-stripped, always-strict Program)
    /// with its resolved named-import bindings pre-installed, sharing this
    /// realm. The module environment is a fresh child of the shared root
    /// (`NewModuleEnvironment(realm.[[GlobalEnv]])`), so each module's
    /// top-level `var`/`let`/`const`/`function`/`class` bindings are private to
    /// that module — never leaking to a sibling or the global object (strict
    /// hoisting keeps `var`/`function` in the module env). Import bindings are
    /// installed as immutable, initialized bindings (`CreateImportBinding` +
    /// the captured value). Returns the module env so the caller can read the
    /// exported bindings' final values; any abrupt/refusal propagates.
    pub fn run_module_body(
        &mut self,
        prog: &Program,
        imports: &[(String, JsValue)],
    ) -> Result<EnvId, Abrupt> {
        let root = EnvId(0);
        let analysis = hoist::analyze(&prog.body, true).map_err(Abrupt::Fatal)?;
        let env = self.alloc_env(Some(root));

        // Import bindings first (immutable indirect bindings, modeled as an
        // immutable initialized binding over the captured value). A collision
        // with a top-level declaration is a module early error parse_module
        // catches; refuse defensively rather than silently shadow.
        let mut import_names: std::collections::HashSet<String> = std::collections::HashSet::new();
        for (name, val) in imports {
            import_names.insert(name.clone());
            self.heap.env_mut(env).bindings.insert(
                name.clone(),
                Binding {
                    value: val.clone(),
                    mutable: false,
                    initialized: true,
                    strict_immutable: true,
                    deletable: false,
                },
            );
        }
        let collides = |name: &str| import_names.contains(name);

        // Lexical declarations (TDZ) — let/const/class.
        for (name, mutable) in hoist::lexical_decls(&prog.body).map_err(Abrupt::Fatal)? {
            if collides(&name) {
                return Err(Abrupt::Fatal(format!(
                    "module lexical `{name}` collides with an import (out of slice)"
                )));
            }
            self.heap
                .env_mut(env)
                .bindings
                .insert(name, Binding::tdz(mutable));
        }
        // Function declarations (strict: into the module env).
        for f in &analysis.funcs {
            let name = f.name.clone().expect("declaration has a name");
            if collides(&name) {
                return Err(Abrupt::Fatal(format!(
                    "module function `{name}` collides with an import (out of slice)"
                )));
            }
            let fobj = self.instantiate_hoisted_function(f, env)?;
            self.heap
                .env_mut(env)
                .bindings
                .insert(name, Binding::var(JsValue::Obj(fobj)));
        }
        // Var declarations (strict: into the module env).
        for v in &analysis.vars {
            if collides(v) {
                return Err(Abrupt::Fatal(format!(
                    "module var `{v}` collides with an import (out of slice)"
                )));
            }
            if !self.heap.env(env).bindings.contains_key(v) {
                self.heap
                    .env_mut(env)
                    .bindings
                    .insert(v.clone(), Binding::var(JsValue::Undefined));
            }
        }

        let ctx = Ctx { env, strict: true };
        let mut v: Option<JsValue> = None;
        self.eval_stmt_list(&prog.body, &ctx, &mut v)?;
        Ok(env)
    }

    /// Read the final value of an initialized top-level binding of a module
    /// environment (export capture). `None` if the binding is absent or still
    /// uninitialized (TDZ) — the caller refuses rather than fabricate a value.
    pub fn module_export_value(&self, env: EnvId, local: &str) -> Option<JsValue> {
        self.heap
            .env(env)
            .bindings
            .get(local)
            .filter(|b| b.initialized)
            .map(|b| b.value.clone())
    }

    /// Build a Module Namespace Exotic Object (§10.4.6) from a dependency's
    /// fully-evaluated `(export_name, value)` set — the object bound by
    /// `import * as ns from '...'`. Faithful to what Node/Bun expose: a
    /// null-prototype, non-extensible object whose exported names are ordinary
    /// own data properties in SORTED (UTF-16 code-unit) order with
    /// {writable:true, enumerable:true, configurable:false}, plus a frozen
    /// `@@toStringTag` = "Module" ({w:false,e:false,c:false}). Its exotic
    /// [[Set]] (always fails) and [[DefineOwnProperty]] (no-op redefine only)
    /// are enforced by the `ObjKind::ModuleNamespace` interceptions in props.rs;
    /// every other internal method is the ordinary method over these props.
    ///
    /// Refuses (sound `Abrupt::Fatal`) if any export name is a canonical array
    /// index — those would reorder ahead of the sorted string keys under the
    /// ordinary [[OwnPropertyKeys]], diverging from the exotic's sorted order.
    /// (Identifier export names never are; the guard is defensive.)
    pub(crate) fn make_module_namespace(
        &mut self,
        exports: &[(String, JsValue)],
    ) -> Result<ObjId, Abrupt> {
        use trust_js_value::{units_from_str, JsObject, ObjKind, PropKey, SymId, WkSym};
        let mut sorted: Vec<&(String, JsValue)> = exports.iter().collect();
        // Sort by UTF-16 code units (the spec's SortStringList order), not UTF-8
        // bytes — they differ for astral characters.
        sorted.sort_by(|a, b| {
            let ua: Vec<u16> = a.0.encode_utf16().collect();
            let ub: Vec<u16> = b.0.encode_utf16().collect();
            ua.cmp(&ub)
        });
        let oid = self.alloc_obj(JsObject::new(ObjKind::ModuleNamespace, None))?;
        for (name, value) in &sorted {
            let key_units = units_from_str(name);
            if trust_js_value::array_index_of(&key_units).is_some() {
                return Err(Abrupt::Fatal(format!(
                    "module namespace export name `{name}` is an array index (out of slice)"
                )));
            }
            self.heap.obj_mut(oid).props.insert(
                PropKey::Str(key_units),
                Property::with_attrs((*value).clone(), true, true, false),
            );
        }
        // @@toStringTag = "Module", frozen (non-writable/enumerable/configurable).
        self.heap.obj_mut(oid).props.insert(
            PropKey::Sym(SymId::WellKnown(WkSym::ToStringTag)),
            Property::with_attrs(JsValue::str_from("Module"), false, false, false),
        );
        self.heap.obj_mut(oid).extensible = false;
        Ok(oid)
    }
}

enum LoopFlow {
    Continue,
    Break(Option<JsValue>),
}

/// UpdateEmpty: fill an EMPTY completion value (normal or break/continue)
/// with `v`.
fn update_empty(r: Compl, v: JsValue) -> Compl {
    match r {
        Ok(None) => Ok(Some(v)),
        Err(Abrupt::Break { label, value: None }) => Err(Abrupt::Break {
            label,
            value: Some(v),
        }),
        Err(Abrupt::Continue { label, value: None }) => Err(Abrupt::Continue {
            label,
            value: Some(v),
        }),
        other => other,
    }
}

/// Statement-list UpdateEmpty: patch an empty break/continue with the running
/// completion value, when one exists.
fn patch_empty(a: Abrupt, v: &Option<JsValue>) -> Abrupt {
    match (a, v) {
        (Abrupt::Break { label, value: None }, Some(val)) => Abrupt::Break {
            label,
            value: Some(val.clone()),
        },
        (Abrupt::Continue { label, value: None }, Some(val)) => Abrupt::Continue {
            label,
            value: Some(val.clone()),
        },
        (other, _) => other,
    }
}

// ---------------------------------------------------------------------------
// Hoisting analysis
// ---------------------------------------------------------------------------

pub(crate) mod hoist {
    use super::{DeclKind, ForHead, ForInit, Func, Pat, Stmt};

    pub struct Analysis<'a> {
        pub vars: Vec<String>,
        /// Top-level function declarations, deduplicated last-wins, in the
        /// source order of the kept declarations.
        pub funcs: Vec<&'a Func>,
    }

    /// VarScopedDeclarations of a script/function body: var names plus
    /// top-level function declarations. `Err` = the body uses out-of-slice
    /// hoisting surface (sloppy block-level / labelled function declarations,
    /// class declarations, `using`).
    pub fn analyze(stmts: &[Stmt], strict: bool) -> Result<Analysis<'_>, String> {
        let mut vars = Vec::new();
        let mut funcs_raw: Vec<&Func> = Vec::new();
        for s in stmts {
            if let Stmt::FuncDecl(f) = s {
                funcs_raw.push(f);
                continue;
            }
            collect_stmt(s, strict, &mut vars)?;
        }
        // Last declaration per name wins, kept in its source position.
        let mut funcs: Vec<&Func> = Vec::new();
        for (i, f) in funcs_raw.iter().enumerate() {
            let name = f.name.as_deref().ok_or("unnamed function declaration")?;
            let later = funcs_raw[i + 1..]
                .iter()
                .any(|g| g.name.as_deref() == Some(name));
            if !later {
                funcs.push(f);
            }
        }
        Ok(Analysis { vars, funcs })
    }

    fn collect_stmt(s: &Stmt, strict: bool, vars: &mut Vec<String>) -> Result<(), String> {
        match s {
            Stmt::Decl { kind, decls } => {
                match kind {
                    DeclKind::Var => {
                        for (pat, _) in decls {
                            pat_bound_names(pat, vars);
                        }
                    }
                    // `using` / `await using` are LEXICAL declarations (they
                    // contribute no var-scoped names), exactly like let/const.
                    DeclKind::Let
                    | DeclKind::Const
                    | DeclKind::Using
                    | DeclKind::AwaitUsing => {}
                }
                Ok(())
            }
            Stmt::FuncDecl(_) => {
                if strict {
                    Ok(()) // block-level lexical function, handled at block entry
                } else {
                    Err("sloppy block-level function declaration (Annex B, out of slice)"
                        .to_string())
                }
            }
            // Class declarations are lexically scoped (no var names).
            Stmt::ClassDecl(_) => Ok(()),
            Stmt::Block(b) => collect_list(b, strict, vars),
            Stmt::If { cons, alt, .. } => {
                collect_stmt(cons, strict, vars)?;
                if let Some(a) = alt {
                    collect_stmt(a, strict, vars)?;
                }
                Ok(())
            }
            Stmt::While { body, .. } | Stmt::DoWhile { body, .. } | Stmt::With { body, .. } => {
                collect_stmt(body, strict, vars)
            }
            Stmt::Labeled { body, .. } => {
                if matches!(body.as_ref(), Stmt::FuncDecl(_)) {
                    return Err(
                        "labelled function declaration (Annex B, out of slice)".to_string()
                    );
                }
                collect_stmt(body, strict, vars)
            }
            Stmt::For { init, body, .. } => {
                if let Some(ForInit::Decl(DeclKind::Var, decls)) = init {
                    for (pat, _) in decls {
                        pat_bound_names(pat, vars);
                    }
                }
                collect_stmt(body, strict, vars)
            }
            Stmt::ForIn { left, body, .. } | Stmt::ForOf { left, body, .. } => {
                if let ForHead::Decl(DeclKind::Var, pat) = left {
                    pat_bound_names(pat, vars);
                }
                collect_stmt(body, strict, vars)
            }
            Stmt::Switch { cases, .. } => {
                for c in cases {
                    collect_list(&c.body, strict, vars)?;
                }
                Ok(())
            }
            Stmt::Try {
                block,
                catch,
                finally,
            } => {
                collect_list(block, strict, vars)?;
                if let Some((_, cbody)) = catch {
                    collect_list(cbody, strict, vars)?;
                }
                if let Some(f) = finally {
                    collect_list(f, strict, vars)?;
                }
                Ok(())
            }
            Stmt::Import(_) | Stmt::Export(_) => {
                Err("module import/export declaration (out of slice)".to_string())
            }
            Stmt::Expr(_)
            | Stmt::Empty
            | Stmt::Debugger
            | Stmt::Return(_)
            | Stmt::Throw(_)
            | Stmt::Break(_)
            | Stmt::Continue(_) => Ok(()),
        }
    }

    fn collect_list(stmts: &[Stmt], strict: bool, vars: &mut Vec<String>) -> Result<(), String> {
        for s in stmts {
            collect_stmt(s, strict, vars)?;
        }
        Ok(())
    }

    /// Direct let/const/class/using declarations of a statement list (TDZ
    /// names), plus the mutability flag (`using` binds immutably, like const).
    /// `Err` on out-of-slice declaration kinds.
    pub fn lexical_decls(stmts: &[Stmt]) -> Result<Vec<(String, bool)>, String> {
        let mut out = Vec::new();
        for s in stmts {
            match s {
                Stmt::Decl { kind, decls } if *kind != DeclKind::Var => {
                    for (pat, _) in decls {
                        let mut names = Vec::new();
                        pat_bound_names(pat, &mut names);
                        for n in names {
                            out.push((n, *kind == DeclKind::Let));
                        }
                    }
                }
                // ClassDeclaration binds a MUTABLE lexical name (let-like).
                Stmt::ClassDecl(c) => {
                    if let Some(n) = &c.name {
                        out.push((n.clone(), true));
                    }
                }
                _ => {}
            }
        }
        Ok(out)
    }

    /// Does this statement list carry a direct (top-level) SYNC `using`
    /// declaration? Such a scope must establish a DisposeCapability and run
    /// DisposeResources on exit. `await using` is not counted here — it refuses
    /// at evaluation (the async disposal surface is out of slice).
    pub fn has_top_level_sync_using(stmts: &[Stmt]) -> bool {
        stmts.iter().any(|s| {
            matches!(
                s,
                Stmt::Decl {
                    kind: DeclKind::Using,
                    ..
                }
            )
        })
    }

    /// Direct function declarations of a statement list (strict block-level
    /// lexical functions).
    pub fn direct_func_decls(stmts: &[Stmt]) -> Vec<&Func> {
        let mut raw: Vec<&Func> = stmts
            .iter()
            .filter_map(|s| match s {
                Stmt::FuncDecl(f) => Some(f),
                _ => None,
            })
            .collect();
        // Last-wins per name, kept in source position of the kept one.
        let names: Vec<Option<&str>> = raw.iter().map(|f| f.name.as_deref()).collect();
        let mut keep = vec![true; raw.len()];
        for i in 0..raw.len() {
            if names[i + 1..].contains(&names[i]) {
                keep[i] = false;
            }
        }
        let mut idx = 0;
        raw.retain(|_| {
            let k = keep[idx];
            idx += 1;
            k
        });
        raw
    }

    /// All identifiers bound by a binding pattern.
    pub fn pat_bound_names(p: &Pat, out: &mut Vec<String>) {
        match p {
            Pat::Ident(n) => out.push(n.clone()),
            Pat::Expr(_) => {}
            Pat::Array { elems, rest } => {
                for e in elems.iter().flatten() {
                    pat_bound_names(e, out);
                }
                if let Some(r) = rest {
                    pat_bound_names(r, out);
                }
            }
            Pat::Object { props, rest } => {
                for pp in props {
                    pat_bound_names(&pp.value, out);
                }
                if let Some(r) = rest {
                    pat_bound_names(r, out);
                }
            }
            Pat::Default(inner, _) | Pat::Rest(inner) => pat_bound_names(inner, out),
        }
    }
}
