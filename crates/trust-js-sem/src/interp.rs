// The evaluator: ECMA-262 statement/expression semantics for the bootstrap
// slice, written from the spec (completion values with UpdateEmpty, abstract
// equality, ToPrimitive/ToNumber/ToString, ordinary [[Get]]/[[Set]], function
// and constructor invocation, for-in enumeration with the spec's
// EnumerateObjectProperties visited/shadow discipline, for-of over provably
// untampered intrinsic iterables). Everything outside the slice is
// Abrupt::Fatal(reason) — a sound refusal, never a wrong trace. The
// interpreter is total: call-depth cap 512, loop-iteration cap 1_000_000,
// string cap 10M units.
//
// Author: Andrew Yates
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

use crate::ast::{BindTarget, DeclKind, Expr, ForInOfLeft, ForInit, Program, Stmt};
use crate::builtins::Intrinsics;
use crate::value::{
    array_index_of, units_from_str, units_to_lossy, Binding, EnvFrame, EnvId, NativeErrorKind,
    ObjId, ObjKind, Object, Prop, PropVal, Units, Value,
};
use std::collections::{HashMap, HashSet};
use std::rc::Rc;
use trust_js_trace::HostEvent;

pub const MAX_CALL_DEPTH: u32 = 512;
pub const MAX_LOOP_ITERS: u64 = 1_000_000;
pub const MAX_STRING_UNITS: usize = 10_000_000;

/// Abrupt completions plus the out-of-slice refusal channel.
#[derive(Debug)]
pub enum Abrupt {
    Break(Option<Value>),
    Continue(Option<Value>),
    Return(Value),
    Throw(Value),
    /// Out of slice / resource cap: the whole case refuses (NoCoverage).
    Fatal(String),
}

/// Statement completion: Ok(None) = normal-empty, Ok(Some(v)) = normal-value.
pub type Compl = Result<Option<Value>, Abrupt>;
pub type ERes = Result<Value, Abrupt>;

#[derive(Clone)]
pub struct Ctx {
    pub env: EnvId,
    pub this_val: Value,
    pub strict: bool,
    /// [[HomeObject]] of the running method (super.x resolution).
    pub home_object: Option<ObjId>,
    /// The derived-constructor frame: the this-TDZ cell, the original
    /// new.target, and the active class constructor (for super()).
    pub ctor_frame: Option<Rc<CtorFrame>>,
    /// The running execution context's PrivateEnvironment (9.4): resolves
    /// `#name` references lexically. None outside all class bodies.
    pub priv_env: Option<Rc<PrivEnvFrame>>,
    /// True while a formal-parameter initializer (default value) is being
    /// evaluated. A direct eval here (`function f(a = eval("var a")){}`) runs
    /// against a separate parameter environment whose var/parameter-shadow
    /// semantics we do not model — such an eval refuses soundly rather than
    /// risk a wrong trace.
    pub in_formal_params: bool,
}

/// A PrivateEnvironment (9.2): one frame per class, mapping each declared
/// `#name` to its fresh PrivateName, with a parent chain up the enclosing
/// classes (nested-class resolution).
#[derive(Debug)]
pub struct PrivEnvFrame {
    pub parent: Option<Rc<PrivEnvFrame>>,
    pub names: HashMap<String, crate::value::PrivName>,
}

/// The FunctionEnvironmentRecord state a derived constructor carries.
#[derive(Debug)]
pub struct CtorFrame {
    /// None = this is uninitialized (TDZ); super() initializes it.
    pub cell: std::cell::RefCell<Option<Value>>,
    pub new_target: ObjId,
    pub active: ObjId,
}

pub struct Interp {
    pub heap: Vec<Object>,
    pub envs: Vec<EnvFrame>,
    pub global: ObjId,
    pub intr: Intrinsics,
    pub events: Vec<HostEvent>,
    pub call_depth: u32,
    pub loop_iters: u64,
    /// The new.target a builtin [[Construct]] dispatch should honor
    /// (super() into Error/Object parents); taken by the consuming arm.
    pub(crate) pending_new_target: Option<ObjId>,
    /// Resumable generator states, indexed by `GenId` (see
    /// `ObjKind::Generator`). Kept out of the heap so the resumable VM can
    /// mutate the heap while a generator runs.
    pub(crate) generators: Vec<crate::generator::GenState>,
    /// The next fresh PrivateName id (monotone per realm).
    pub(crate) next_priv_name: u32,
    /// The captured PrivateEnvironment of a function object (methods and any
    /// function/arrow lexically inside a class body): consulted at call time
    /// to establish the body's `ctx.priv_env`. Absent = None.
    pub(crate) fn_priv_env: HashMap<ObjId, Rc<PrivEnvFrame>>,
    /// The Symbol arena (6.1.5): every Symbol value indexes here. The first
    /// entries are the well-known symbols (allocated at realm construction).
    pub(crate) symbols: Vec<crate::value::SymData>,
    /// The GlobalSymbolRegistry (20.4.2): `Symbol.for` key → symbol.
    pub(crate) sym_registry: HashMap<crate::value::Units, crate::value::SymId>,
    /// The deterministic clock (mirrors the driver firewall's `clockTicks`):
    /// `Date.now()`, `new Date()` (0 args) and `Date()`-as-function each read
    /// FIXED_EPOCH + (++clock_ticks). Kept in lockstep with the driver.
    pub(crate) clock_ticks: i64,
    /// Promise instance state (27.2), indexed by `PromiseId` (see
    /// `ObjKind::Promise`). Kept out of the heap so resolve/reject/reactions
    /// can mutate a promise while other user code runs.
    pub(crate) promises: Vec<crate::promise::PromiseState>,
    /// The microtask (Promise-job) FIFO queue (9.5): drained to empty after the
    /// script body, and again between virtual-timer callbacks.
    pub(crate) microtasks: std::collections::VecDeque<crate::promise::Job>,
    /// The virtual-timer queue (setTimeout/setInterval): drained
    /// earliest-deadline-then-insertion after the microtask queue is empty.
    pub(crate) timers: Vec<crate::promise::Timer>,
    /// Monotone timer id/insertion counter (mirrors the driver's `timerSeq`).
    pub(crate) timer_seq: u64,
    /// The virtual clock (mirrors the driver's `virtualNow`), starting at 0 and
    /// advanced to each fired timer's deadline.
    pub(crate) virtual_now: f64,
    /// Jobs run across the post-body drain, bounded by `JOB_BUDGET`.
    pub(crate) job_steps: u64,
}

/// The deterministic epoch the driver firewall pins the clock to.
pub const FIXED_EPOCH: f64 = 1_700_000_000_000.0;

/// The target VariableEnvironment for an eval body's `var`/function
/// declarations: a declarative frame, or the global object's variable record.
#[derive(Clone, Copy)]
enum VarTarget {
    Frame(EnvId),
    Global,
}

/// A resolved reference (spec Reference Record).
///
/// Per ES2021+ reference semantics, evaluating a MemberExpression neither
/// validates the base (RequireObjectCoercible/ToObject is deferred to
/// GetValue/PutValue) nor coerces a computed key (ToPropertyKey is deferred
/// likewise). GetValue and PutValue EACH coerce a raw key — a compound
/// assignment or update observably runs the key's toString twice (verified
/// against Node).
pub enum JsRef {
    Env(String),
    Member { base: Value, key: RefKey },
    /// A super property reference: [[HomeObject]].[[GetPrototypeOf]] base
    /// with the method's `this` as receiver.
    SuperMember {
        start: Option<ObjId>,
        this_v: Value,
        key: RefKey,
    },
    /// A private reference `obj.#name` (6.2.5): resolved to a PrivateName;
    /// GetValue/PutValue route through PrivateGet/PrivateSet.
    PrivateMember {
        base: Value,
        key: crate::value::PrivName,
    },
}

/// The [[ReferencedName]] of a property reference: a property key already
/// (dot access), or the raw computed-key value coerced by ToPropertyKey at
/// each GetValue/PutValue.
pub enum RefKey {
    Key(Units),
    Raw(Value),
}

/// One prototype-chain hop of a for-in enumeration.
enum EnumHop {
    /// A modeled heap object.
    Real(ObjId),
    /// The string exotic's own surface (indices + length) for a primitive
    /// string receiver; the snapshot carries the concrete keys.
    StrOwn,
    /// An unmodeled-own-surface hop (Number.prototype / Boolean.prototype
    /// behind a primitive receiver): yields nothing itself (all its real own
    /// properties are spec-pinned non-enumerable) and any later yield must
    /// refuse (its non-enumerable own properties would still shadow).
    OpaqueSurface,
}

/// Upfront-snapshotted for-in enumeration state. Snapshots are taken at head
/// evaluation for every hop: own keys ADDED during enumeration are spec
/// latitude ("not guaranteed to be visited"), so any detected addition
/// refuses the case at the end of the affected hop.
pub(crate) struct ForInState {
    hops: Vec<(EnumHop, Vec<Units>)>,
    cur: usize,
    idx: usize,
    visited: HashSet<Units>,
}

impl Interp {
    #[must_use]
    pub fn new() -> Interp {
        crate::builtins::create_interp()
    }

    #[must_use]
    pub fn obj(&self, id: ObjId) -> &Object {
        &self.heap[id.0 as usize]
    }

    pub fn obj_mut(&mut self, id: ObjId) -> &mut Object {
        &mut self.heap[id.0 as usize]
    }

    pub fn alloc(&mut self, o: Object) -> ObjId {
        let id = ObjId(u32::try_from(self.heap.len()).expect("heap bounded by caps"));
        self.heap.push(o);
        id
    }

    /// Allocate a fresh Symbol value.
    pub(crate) fn alloc_symbol(&mut self, data: crate::value::SymData) -> crate::value::SymId {
        let id = crate::value::SymId(
            u32::try_from(self.symbols.len()).expect("symbols bounded by caps"),
        );
        self.symbols.push(data);
        id
    }

    #[must_use]
    pub(crate) fn sym_data(&self, s: crate::value::SymId) -> &crate::value::SymData {
        &self.symbols[s.0 as usize]
    }

    /// The next tick of the pinned clock (mirrors the driver's `now()`).
    pub(crate) fn clock_now(&mut self) -> f64 {
        self.clock_ticks += 1;
        #[allow(clippy::cast_precision_loss)]
        {
            FIXED_EPOCH + self.clock_ticks as f64
        }
    }

    pub fn alloc_env(&mut self, parent: Option<EnvId>) -> EnvId {
        let id = EnvId(u32::try_from(self.envs.len()).expect("envs bounded by caps"));
        self.envs.push(EnvFrame {
            parent,
            bindings: HashMap::new(),
            var_boundary: false,
            deletable: HashSet::new(),
        });
        id
    }

    /// Allocate a function VariableEnvironment frame (a var-hoisting boundary
    /// for a sloppy direct eval).
    pub fn alloc_var_env(&mut self, parent: Option<EnvId>) -> EnvId {
        let e = self.alloc_env(parent);
        self.envs[e.0 as usize].var_boundary = true;
        e
    }

    /// The nearest VariableEnvironment frame at or above `env`, or None when
    /// the chain bottoms out at the global environment (whose variable record
    /// is the global object).
    pub(crate) fn nearest_var_env(&self, env: EnvId) -> Option<EnvId> {
        let mut cur = Some(env);
        while let Some(e) = cur {
            if self.envs[e.0 as usize].var_boundary {
                return Some(e);
            }
            cur = self.envs[e.0 as usize].parent;
        }
        None
    }

    /// Nearest intrinsic prototype on the chain, in the driver's list order.
    #[must_use]
    pub fn class_tag(&self, oid: ObjId) -> Option<String> {
        let mut p = self.obj(oid).proto;
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
            p = self.obj(id).proto;
            hops += 1;
        }
        None
    }

    pub(crate) fn charge_loop(&mut self) -> Result<(), Abrupt> {
        self.loop_iters += 1;
        if self.loop_iters > MAX_LOOP_ITERS {
            Err(Abrupt::Fatal("loop iteration cap exceeded".to_string()))
        } else {
            Ok(())
        }
    }

    // -- native error throws ------------------------------------------------

    /// Allocate a native error with an engine-specific (synthetic) message:
    /// its identity projects exactly; reading its message text refuses.
    pub fn make_native_error(&mut self, kind: NativeErrorKind, synthetic: bool) -> ObjId {
        let proto = self.intr.error_proto_for(kind);
        let oid = self.alloc(Object::new(ObjKind::Error, Some(proto)));
        let p = Prop {
            val: PropVal::Data {
                value: Value::str_from("[trust-js-sem synthetic message]"),
                writable: true,
            },
            enumerable: false,
            configurable: true,
            synthetic,
        };
        self.obj_mut(oid).props.insert(units_from_str("message"), p);
        oid
    }

    pub fn throw_native(&mut self, kind: NativeErrorKind) -> Abrupt {
        let oid = self.make_native_error(kind, true);
        Abrupt::Throw(Value::Obj(oid))
    }

    // -- scripts ------------------------------------------------------------

    /// Evaluate one script (harness include or body) sharing this realm.
    /// Returns the script completion value.
    ///
    /// Instantiation order per GlobalDeclarationInstantiation /
    /// EvalDeclarationInstantiation: the lexical (let/const, TDZ) bindings
    /// exist BEFORE function objects are instantiated, and function
    /// declarations close over the environment CONTAINING them — a function
    /// body writing a sibling `let` before its initializer runs must throw
    /// ReferenceError, and after initialization must succeed.
    pub fn run_script(&mut self, prog: &Program) -> ERes {
        let base = EnvId(0); // the global-fallback root frame
        let lex = if prog.strict {
            // Strict indirect eval: one declarative env holds lexical
            // declarations, functions, and vars (varEnv = lexEnv).
            let e = self.alloc_env(Some(base));
            self.declare_lexical(e, &prog.body)?;
            for f in &prog.funcs {
                let fobj = self.create_function(f, e, true, None);
                self.envs[e.0 as usize].bindings.insert(
                    f.name.clone().expect("declaration has a name"),
                    Binding::var(Value::Obj(fobj)),
                );
            }
            for v in &prog.vars {
                self.envs[e.0 as usize]
                    .bindings
                    .entry(v.clone())
                    .or_insert(Binding::var(Value::Undefined));
            }
            e
        } else {
            // Sloppy indirect eval: lexical declarations get the script's
            // declarative env; functions and vars become global properties
            // (writable, enumerable, configurable). Functions close over the
            // lexical env so sibling let/const (incl. TDZ) are visible.
            let lex = self.alloc_env(Some(base));
            self.declare_lexical(lex, &prog.body)?;
            for f in &prog.funcs {
                let fobj = self.create_function(f, lex, true, None);
                let key = units_from_str(f.name.as_ref().expect("declaration has a name"));
                self.obj_mut(self.global)
                    .props
                    .insert(key, Prop::data(Value::Obj(fobj)));
            }
            for v in &prog.vars {
                let key = units_from_str(v);
                if !self.obj(self.global).props.contains_key(&key) {
                    self.obj_mut(self.global)
                        .props
                        .insert(key, Prop::data(Value::Undefined));
                }
            }
            lex
        };
        let ctx = Ctx {
            env: lex,
            this_val: Value::Obj(self.global),
            strict: prog.strict,
            home_object: None,
            ctor_frame: None,
            priv_env: None,
            in_formal_params: false,
        };
        let mut v: Option<Value> = None;
        self.eval_stmt_list(&prog.body, &ctx, &mut v)?;
        Ok(v.unwrap_or(Value::Undefined))
    }

    /// PerformEval (19.2.1.1): evaluate `x` as eval code and return its
    /// completion value. `caller` is `Some` for a DIRECT eval — its lexical
    /// environment, `this`, `[[HomeObject]]`, derived-constructor frame and
    /// PrivateEnvironment are inherited, and a sloppy body hoists `var`/function
    /// declarations into the caller's VariableEnvironment. `None` is an INDIRECT
    /// eval, evaluated in the global scope. A non-string argument is returned
    /// unchanged; a parse-time SyntaxError THROWS (catchable); an out-of-slice
    /// body REFUSES (Fatal) — never a wrong trace and never a guessed error.
    pub(crate) fn perform_eval(&mut self, x: Value, caller: Option<Ctx>, direct: bool) -> ERes {
        // 19.2.1 step 2 / PerformEval step 2: only a String is eval'd.
        let Value::Str(s) = &x else {
            return Ok(x);
        };
        let src = match String::from_utf16(s) {
            Ok(t) => t,
            Err(_) => {
                return Err(Abrupt::Fatal(
                    "eval source contains a lone surrogate (out of slice)".to_string(),
                ))
            }
        };
        // A direct eval evaluated inside a formal-parameter initializer runs
        // against a separate parameter environment (its var/parameter-shadow
        // early errors are a spec corner we do not model) — refuse soundly.
        if direct && caller.as_ref().is_some_and(|c| c.in_formal_params) {
            return Err(Abrupt::Fatal(
                "direct eval in a formal-parameter initializer (parameter scope out of slice)"
                    .to_string(),
            ));
        }
        let caller_strict = caller.as_ref().is_some_and(|c| c.strict);
        // strictEval = the eval code is strict, OR (direct AND caller strict).
        let force_strict = direct && caller_strict;
        let prog = match crate::parser::parse_program_ext(&src, force_strict) {
            Ok(p) => p,
            Err(crate::parser::ParseFail::EarlySyntaxError(_)) => {
                // A direct eval inherits its caller's [[HomeObject]] (so
                // `super.x` is legal), derived-constructor frame (`super()`)
                // and PrivateEnvironment (`#name`) — all of which our parser,
                // lacking that context, reports as early errors. In any such
                // context, refuse rather than risk a wrong SyntaxError throw:
                // a genuine early error is then only lost to a sound refusal,
                // never turned into a wrong trace.
                let inherits_method_ctx = caller.as_ref().is_some_and(|c| {
                    c.home_object.is_some() || c.ctor_frame.is_some() || c.priv_env.is_some()
                });
                if direct && inherits_method_ctx {
                    return Err(Abrupt::Fatal(
                        "direct eval inside a method/class body (super/private parse ambiguity)"
                            .to_string(),
                    ));
                }
                return Err(self.throw_native(NativeErrorKind::SyntaxError));
            }
            Err(e) => return Err(Abrupt::Fatal(format!("eval body parse: {e}"))),
        };
        let strict_eval = prog.strict;

        // The lexical environment: a fresh declarative env over the caller's
        // lexical env (direct) or the global lexical env (indirect).
        let outer_lex = caller.as_ref().map_or(EnvId(0), |c| c.env);
        let lex = self.alloc_env(Some(outer_lex));

        // The variable environment (var/function hoisting target).
        let var_target = if strict_eval {
            // Strict eval is fully isolated: varEnv = lexEnv.
            VarTarget::Frame(lex)
        } else if direct {
            match self.nearest_var_env(outer_lex) {
                Some(fe) => VarTarget::Frame(fe),
                None => VarTarget::Global,
            }
        } else {
            VarTarget::Global
        };

        // EvalDeclarationInstantiation.
        self.eval_declaration_instantiation(&prog, lex, var_target, strict_eval)?;

        let ctx = match &caller {
            Some(c) => Ctx {
                env: lex,
                this_val: c.this_val.clone(),
                strict: strict_eval,
                home_object: c.home_object,
                ctor_frame: c.ctor_frame.clone(),
                priv_env: c.priv_env.clone(),
                in_formal_params: false,
            },
            None => Ctx {
                env: lex,
                this_val: Value::Obj(self.global),
                strict: strict_eval,
                home_object: None,
                ctor_frame: None,
                priv_env: None,
                in_formal_params: false,
            },
        };
        let mut v: Option<Value> = None;
        self.eval_stmt_list(&prog.body, &ctx, &mut v)?;
        Ok(v.unwrap_or(Value::Undefined))
    }

    /// EvalDeclarationInstantiation (19.2.1.3): declare the eval body's
    /// lexical bindings into `lex` (TDZ), run the sloppy var/function
    /// name-collision check against the surrounding scopes, then instantiate
    /// functions and `var` bindings into the variable environment.
    fn eval_declaration_instantiation(
        &mut self,
        prog: &Program,
        lex: EnvId,
        var_target: VarTarget,
        strict_eval: bool,
    ) -> Result<(), Abrupt> {
        // Lexical (let/const/class) declarations of the eval body → lex, TDZ.
        self.declare_lexical(lex, &prog.body)?;

        // Sloppy collision check (19.2.1.3 step 5): a var-scoped name that
        // clashes with a lexical binding in a surrounding declarative scope
        // between lexEnv and varEnv (or a global lexical declaration) is a
        // SyntaxError. Strict eval is isolated, so the check does not apply.
        if !strict_eval {
            let mut var_names: Vec<&str> = prog.vars.iter().map(String::as_str).collect();
            for f in &prog.funcs {
                if let Some(n) = &f.name {
                    var_names.push(n);
                }
            }
            let stop = match var_target {
                VarTarget::Frame(fe) => Some(fe),
                VarTarget::Global => None,
            };
            let mut cur = self.envs[lex.0 as usize].parent;
            while let Some(e) = cur {
                if Some(e) == stop {
                    break;
                }
                for name in &var_names {
                    if self.envs[e.0 as usize].bindings.contains_key(*name) {
                        return Err(self.throw_native(NativeErrorKind::SyntaxError));
                    }
                }
                cur = self.envs[e.0 as usize].parent;
            }
        }

        // CanDeclareGlobalFunction (9.1.1.4.16): a global function binding may
        // not overwrite a non-configurable property that is not a plain
        // writable+enumerable data property — `eval("function NaN(){}")` is a
        // TypeError. Checked BEFORE any binding is created (all-or-nothing).
        if matches!(var_target, VarTarget::Global) {
            for f in &prog.funcs {
                let name = f.name.as_ref().expect("declaration has a name");
                let key = units_from_str(name);
                if let Some(p) = self.obj(self.global).props.get(&key) {
                    let ok = p.configurable
                        || matches!(
                            &p.val,
                            PropVal::Data { writable: true, .. } if p.enumerable
                        );
                    if !ok {
                        return Err(self.throw_native(NativeErrorKind::TypeError));
                    }
                }
            }
        }

        // Function declarations → varEnv (overwriting any prior binding).
        for f in &prog.funcs {
            let fobj = self.create_function(f, lex, true, None);
            let name = f.name.clone().expect("declaration has a name");
            match var_target {
                VarTarget::Frame(fe) => {
                    // A freshly-created (not pre-existing param/var) function
                    // binding from a sloppy direct eval is deletable.
                    let existed = self.envs[fe.0 as usize].bindings.contains_key(&name);
                    self.envs[fe.0 as usize]
                        .bindings
                        .insert(name.clone(), Binding::var(Value::Obj(fobj)));
                    if !existed {
                        self.envs[fe.0 as usize].deletable.insert(name);
                    }
                }
                VarTarget::Global => {
                    let key = units_from_str(&name);
                    self.obj_mut(self.global)
                        .props
                        .insert(key, Prop::data(Value::Obj(fobj)));
                }
            }
        }
        // `var` declarations → varEnv (undefined, only if not already bound).
        for name in &prog.vars {
            match var_target {
                VarTarget::Frame(fe) => {
                    if !self.envs[fe.0 as usize].bindings.contains_key(name) {
                        self.envs[fe.0 as usize]
                            .bindings
                            .insert(name.clone(), Binding::var(Value::Undefined));
                        // A sloppy direct eval's var binding is deletable.
                        self.envs[fe.0 as usize].deletable.insert(name.clone());
                    }
                }
                VarTarget::Global => {
                    let key = units_from_str(name);
                    if !self.obj(self.global).props.contains_key(&key) {
                        self.obj_mut(self.global)
                            .props
                            .insert(key, Prop::data(Value::Undefined));
                    }
                }
            }
        }
        Ok(())
    }

    /// Pre-declare direct let/const of a statement list into `env` (TDZ).
    pub(crate) fn declare_lexical(&mut self, env: EnvId, stmts: &[Stmt]) -> Result<(), Abrupt> {
        for s in stmts {
            match s {
                Stmt::VarDecl { kind, decls } => {
                    if *kind != DeclKind::Var {
                        for (t, _) in decls {
                            let mut ns = Vec::new();
                            t.bound_names(&mut ns);
                            for n in ns {
                                self.envs[env.0 as usize].bindings.insert(
                                    n,
                                    Binding {
                                        value: Value::Undefined,
                                        mutable: *kind == DeclKind::Let,
                                        initialized: false,
                                        fn_name_immutable: false,
                                    },
                                );
                            }
                        }
                    }
                }
                Stmt::ClassDecl { name, .. } => {
                    self.envs[env.0 as usize].bindings.insert(
                        name.clone(),
                        Binding {
                            value: Value::Undefined,
                            mutable: true,
                            initialized: false,
                            fn_name_immutable: false,
                        },
                    );
                }
                _ => {}
            }
        }
        Ok(())
    }

    // -- statements ---------------------------------------------------------

    /// Evaluate a statement list, folding non-empty completion values into
    /// `v` and patching empty-valued break/continue with `v` (UpdateEmpty).
    pub(crate) fn eval_stmt_list(
        &mut self,
        stmts: &[Stmt],
        ctx: &Ctx,
        v: &mut Option<Value>,
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

    #[allow(clippy::too_many_lines)]
    fn eval_stmt(&mut self, s: &Stmt, ctx: &Ctx) -> Compl {
        match s {
            Stmt::Empty | Stmt::FuncDecl(_) => Ok(None),
            Stmt::ClassDecl { name, class } => {
                let f = self.eval_class(class, ctx)?;
                self.initialize_binding(ctx.env, name, f);
                Ok(None)
            }
            Stmt::Expr(e) => Ok(Some(self.eval_expr(e, ctx)?)),
            Stmt::VarDecl { kind, decls } => {
                for (target, init) in decls {
                    match (kind, target) {
                        (DeclKind::Var, BindTarget::Name(name)) => {
                            if let Some(e) = init {
                                let val = self.eval_expr(e, ctx)?;
                                self.env_set(ctx, name, val)?;
                            }
                        }
                        (DeclKind::Var, BindTarget::Pattern(p)) => {
                            let e = init.as_ref().expect("parser: pattern has initializer");
                            let val = self.eval_expr(e, ctx)?;
                            self.destructure(p, &val, ctx, crate::pattern::BindMode::Var)?;
                        }
                        (_, BindTarget::Name(name)) => {
                            let val = match init {
                                Some(e) => self.eval_expr(e, ctx)?,
                                None => Value::Undefined,
                            };
                            self.initialize_binding(ctx.env, name, val);
                        }
                        (_, BindTarget::Pattern(p)) => {
                            let e = init.as_ref().expect("parser: pattern has initializer");
                            let val = self.eval_expr(e, ctx)?;
                            self.destructure(p, &val, ctx, crate::pattern::BindMode::Init)?;
                        }
                    }
                }
                Ok(None)
            }
            Stmt::Block(body) => {
                let env = self.alloc_env(Some(ctx.env));
                self.declare_lexical(env, body)?;
                let inner = Ctx {
                    env,
                    ..ctx.clone()
                };
                let mut v: Option<Value> = None;
                self.eval_stmt_list(body, &inner, &mut v)?;
                Ok(v)
            }
            Stmt::If { test, cons, alt } => {
                let t = self.eval_expr(test, ctx)?;
                let r = if self.to_boolean(&t) {
                    self.eval_stmt(cons, ctx)
                } else if let Some(a) = alt {
                    self.eval_stmt(a, ctx)
                } else {
                    Ok(None)
                };
                update_empty(r, Value::Undefined)
            }
            Stmt::While { test, body } => {
                let mut v = Value::Undefined;
                loop {
                    let t = self.eval_expr(test, ctx)?;
                    if !self.to_boolean(&t) {
                        return Ok(Some(v));
                    }
                    self.charge_loop()?;
                    match self.eval_stmt(body, ctx) {
                        Ok(Some(val)) => v = val,
                        Ok(None) => {}
                        Err(Abrupt::Continue(cv)) => {
                            if let Some(cv) = cv {
                                v = cv;
                            }
                        }
                        Err(Abrupt::Break(bv)) => return Ok(Some(bv.unwrap_or(v))),
                        Err(a) => return Err(a),
                    }
                }
            }
            Stmt::DoWhile { body, test } => {
                let mut v = Value::Undefined;
                loop {
                    self.charge_loop()?;
                    match self.eval_stmt(body, ctx) {
                        Ok(Some(val)) => v = val,
                        Ok(None) => {}
                        Err(Abrupt::Continue(cv)) => {
                            if let Some(cv) = cv {
                                v = cv;
                            }
                        }
                        Err(Abrupt::Break(bv)) => return Ok(Some(bv.unwrap_or(v))),
                        Err(a) => return Err(a),
                    }
                    let t = self.eval_expr(test, ctx)?;
                    if !self.to_boolean(&t) {
                        return Ok(Some(v));
                    }
                }
            }
            Stmt::For {
                init,
                test,
                update,
                body,
            } => {
                let mut loop_ctx = ctx.clone();
                let mut per_iter: Option<Vec<String>> = None;
                match init {
                    Some(ForInit::Var(decls)) => {
                        for (target, ie) in decls {
                            match target {
                                BindTarget::Name(name) => {
                                    if let Some(e) = ie {
                                        let val = self.eval_expr(e, ctx)?;
                                        self.env_set(ctx, name, val)?;
                                    }
                                }
                                BindTarget::Pattern(p) => {
                                    let e =
                                        ie.as_ref().expect("parser: pattern has initializer");
                                    let val = self.eval_expr(e, ctx)?;
                                    self.destructure(
                                        p,
                                        &val,
                                        ctx,
                                        crate::pattern::BindMode::Var,
                                    )?;
                                }
                            }
                        }
                    }
                    Some(ForInit::Lex { is_const, decls }) => {
                        // A fresh loop scope; bindings are TDZ until their
                        // initializer runs (`for (let a = b, b = 1;;)` is a
                        // ReferenceError).
                        let loop_env = self.alloc_env(Some(ctx.env));
                        let mut all_names: Vec<String> = Vec::new();
                        for (t, _) in decls {
                            t.bound_names(&mut all_names);
                        }
                        for n in &all_names {
                            self.envs[loop_env.0 as usize].bindings.insert(
                                n.clone(),
                                Binding {
                                    value: Value::Undefined,
                                    mutable: !is_const,
                                    initialized: false,
                                    fn_name_immutable: false,
                                },
                            );
                        }
                        loop_ctx = Ctx {
                            env: loop_env,
                            ..ctx.clone()
                        };
                        for (t, ie) in decls {
                            match t {
                                BindTarget::Name(n) => {
                                    let val = match ie {
                                        Some(e) => self.eval_expr(e, &loop_ctx)?,
                                        None => Value::Undefined,
                                    };
                                    self.initialize_binding(loop_env, n, val);
                                }
                                BindTarget::Pattern(p) => {
                                    let e =
                                        ie.as_ref().expect("parser: pattern has initializer");
                                    let val = self.eval_expr(e, &loop_ctx)?;
                                    self.destructure(
                                        p,
                                        &val,
                                        &loop_ctx,
                                        crate::pattern::BindMode::Init,
                                    )?;
                                }
                            }
                        }
                        if !is_const {
                            // CreatePerIterationEnvironment runs once BEFORE
                            // the first test, and again before each update.
                            let names: Vec<String> = all_names;
                            let e = self.copy_iteration_env(loop_env, &names, ctx.env);
                            loop_ctx = Ctx {
                                env: e,
                                ..ctx.clone()
                            };
                            per_iter = Some(names);
                        }
                    }
                    Some(ForInit::Expr(e)) => {
                        self.eval_expr(e, ctx)?;
                    }
                    None => {}
                }
                let mut v = Value::Undefined;
                loop {
                    if let Some(t) = test {
                        let tv = self.eval_expr(t, &loop_ctx)?;
                        if !self.to_boolean(&tv) {
                            return Ok(Some(v));
                        }
                    }
                    self.charge_loop()?;
                    match self.eval_stmt(body, &loop_ctx) {
                        Ok(Some(val)) => v = val,
                        Ok(None) => {}
                        Err(Abrupt::Continue(cv)) => {
                            if let Some(cv) = cv {
                                v = cv;
                            }
                        }
                        Err(Abrupt::Break(bv)) => return Ok(Some(bv.unwrap_or(v))),
                        Err(a) => return Err(a),
                    }
                    if let Some(names) = &per_iter {
                        let e = self.copy_iteration_env(loop_ctx.env, names, ctx.env);
                        loop_ctx = Ctx {
                            env: e,
                            ..ctx.clone()
                        };
                    }
                    if let Some(u) = update {
                        self.eval_expr(u, &loop_ctx)?;
                    }
                }
            }
            Stmt::ForIn { left, obj, body } => self.eval_for_in(left, obj, body, ctx),
            Stmt::ForOf { left, expr, body } => self.eval_for_of(left, expr, body, ctx),
            Stmt::Return(arg) => {
                let v = match arg {
                    Some(e) => self.eval_expr(e, ctx)?,
                    None => Value::Undefined,
                };
                Err(Abrupt::Return(v))
            }
            Stmt::Throw(e) => {
                let v = self.eval_expr(e, ctx)?;
                Err(Abrupt::Throw(v))
            }
            Stmt::Break => Err(Abrupt::Break(None)),
            Stmt::Continue => Err(Abrupt::Continue(None)),
            Stmt::Try {
                block,
                catch,
                finally,
            } => {
                let b = self.eval_block_scoped(block, ctx);
                let handled = match b {
                    Err(Abrupt::Throw(exc)) => {
                        if let Some((param, cbody)) = catch {
                            let cenv = self.alloc_env(Some(ctx.env));
                            let cctx = Ctx {
                                env: cenv,
                                ..ctx.clone()
                            };
                            match param {
                                None => {}
                                Some(BindTarget::Name(p)) => {
                                    self.envs[cenv.0 as usize]
                                        .bindings
                                        .insert(p.clone(), Binding::var(exc));
                                }
                                Some(BindTarget::Pattern(p)) => {
                                    let mut ns = Vec::new();
                                    crate::ast::pattern_bound_names(p, &mut ns);
                                    for n in ns {
                                        self.envs[cenv.0 as usize]
                                            .bindings
                                            .insert(n, Binding::var(Value::Undefined));
                                    }
                                    if let Err(a) = self.destructure(
                                        p,
                                        &exc,
                                        &cctx,
                                        crate::pattern::BindMode::Init,
                                    ) {
                                        return update_empty(Err(a), Value::Undefined);
                                    }
                                }
                            }
                            self.eval_block_scoped(cbody, &cctx)
                        } else {
                            Err(Abrupt::Throw(exc))
                        }
                    }
                    other => other,
                };
                let result = if let Some(fbody) = finally {
                    match self.eval_block_scoped(fbody, ctx) {
                        Ok(_) => handled, // finally's normal value is discarded
                        Err(fa) => Err(fa),
                    }
                } else {
                    handled
                };
                update_empty(result, Value::Undefined)
            }
            Stmt::Switch { disc, cases } => self.eval_switch(disc, cases, ctx),
        }
    }

    fn eval_block_scoped(&mut self, body: &[Stmt], ctx: &Ctx) -> Compl {
        let env = self.alloc_env(Some(ctx.env));
        self.declare_lexical(env, body)?;
        let inner = Ctx {
            env,
            ..ctx.clone()
        };
        let mut v: Option<Value> = None;
        self.eval_stmt_list(body, &inner, &mut v)?;
        Ok(v)
    }

    fn eval_switch(&mut self, disc: &Expr, cases: &[(Option<Expr>, Vec<Stmt>)], ctx: &Ctx) -> Compl {
        let d = self.eval_expr(disc, ctx)?;
        // One block scope for the whole case block.
        let env = self.alloc_env(Some(ctx.env));
        for (_, b) in cases {
            self.declare_lexical(env, b)?;
        }
        let inner = Ctx {
            env,
            ..ctx.clone()
        };
        // Selector search: source order, skipping default.
        let mut start: Option<usize> = None;
        for (i, (test, _)) in cases.iter().enumerate() {
            if let Some(t) = test {
                let tv = self.eval_expr(t, &inner)?;
                if strict_eq(self, &d, &tv) {
                    start = Some(i);
                    break;
                }
            }
        }
        if start.is_none() {
            start = cases.iter().position(|(t, _)| t.is_none());
        }
        let Some(start) = start else {
            return Ok(Some(Value::Undefined));
        };
        let mut v = Value::Undefined;
        for (_, stmts) in &cases[start..] {
            let mut lv: Option<Value> = Some(v.clone());
            match self.eval_stmt_list(stmts, &inner, &mut lv) {
                Ok(()) => {
                    if let Some(val) = lv {
                        v = val;
                    }
                }
                Err(Abrupt::Break(bv)) => {
                    return Ok(Some(bv.or(lv).unwrap_or(Value::Undefined)));
                }
                Err(a) => return Err(a),
            }
        }
        Ok(Some(v))
    }

    // -- for-in / for-of ----------------------------------------------------

    /// ForIn/OfHeadEvaluation: a lexical left gets a fresh TDZ environment
    /// for the head expression; the environment is dropped afterwards.
    fn eval_forinof_head(&mut self, left: &ForInOfLeft, e: &Expr, ctx: &Ctx) -> ERes {
        match left {
            ForInOfLeft::Lex(target, _) => {
                let head_env = self.alloc_env(Some(ctx.env));
                let mut ns = Vec::new();
                target.bound_names(&mut ns);
                for n in ns {
                    self.envs[head_env.0 as usize].bindings.insert(
                        n,
                        Binding {
                            value: Value::Undefined,
                            mutable: true,
                            initialized: false,
                            fn_name_immutable: false,
                        },
                    );
                }
                let hctx = Ctx {
                    env: head_env,
                    ..ctx.clone()
                };
                self.eval_expr(e, &hctx)
            }
            _ => self.eval_expr(e, ctx),
        }
    }

    /// Bind one iteration value to the left-hand side; returns the body ctx.
    fn bind_forinof_left(
        &mut self,
        left: &ForInOfLeft,
        val: Value,
        ctx: &Ctx,
    ) -> Result<Ctx, Abrupt> {
        match left {
            ForInOfLeft::Var(BindTarget::Name(name)) => {
                self.env_set(ctx, name, val)?;
                Ok(ctx.clone())
            }
            ForInOfLeft::Var(BindTarget::Pattern(p)) => {
                self.destructure(p, &val, ctx, crate::pattern::BindMode::Var)?;
                Ok(ctx.clone())
            }
            ForInOfLeft::Target(e) => {
                // The reference re-evaluates every iteration (13.7.5.13).
                let r = self.eval_ref_assign(e, ctx)?;
                self.ref_set(&r, val, ctx)?;
                Ok(ctx.clone())
            }
            ForInOfLeft::TargetPattern(p) => {
                self.destructure(p, &val, ctx, crate::pattern::BindMode::Assign)?;
                Ok(ctx.clone())
            }
            ForInOfLeft::Lex(target, is_const) => {
                let env = self.alloc_env(Some(ctx.env));
                let ictx = Ctx {
                    env,
                    ..ctx.clone()
                };
                match target {
                    BindTarget::Name(name) => {
                        self.envs[env.0 as usize].bindings.insert(
                            name.clone(),
                            Binding {
                                value: val,
                                mutable: !is_const,
                                initialized: true,
                                fn_name_immutable: false,
                            },
                        );
                    }
                    BindTarget::Pattern(p) => {
                        let mut ns = Vec::new();
                        crate::ast::pattern_bound_names(p, &mut ns);
                        for n in ns {
                            self.envs[env.0 as usize].bindings.insert(
                                n,
                                Binding {
                                    value: Value::Undefined,
                                    mutable: !is_const,
                                    initialized: false,
                                    fn_name_immutable: false,
                                },
                            );
                        }
                        self.destructure(p, &val, &ictx, crate::pattern::BindMode::Init)?;
                    }
                }
                Ok(ictx)
            }
        }
    }

    fn eval_for_in(
        &mut self,
        left: &ForInOfLeft,
        obj: &Expr,
        body: &Stmt,
        ctx: &Ctx,
    ) -> Compl {
        let expr_val = self.eval_forinof_head(left, obj, ctx)?;
        let Some(mut st) = self.build_for_in_state(&expr_val)? else {
            // undefined/null: the head returns a break completion, which the
            // loop evaluation converts to normal undefined.
            return Ok(Some(Value::Undefined));
        };
        let mut v = Value::Undefined;
        loop {
            let Some(k) = self.next_for_in_key(&mut st)? else {
                return Ok(Some(v));
            };
            self.charge_loop()?;
            let body_ctx = self.bind_forinof_left(left, Value::Str(Rc::new(k)), ctx)?;
            match self.eval_stmt(body, &body_ctx) {
                Ok(Some(val)) => v = val,
                Ok(None) => {}
                Err(Abrupt::Continue(cv)) => {
                    if let Some(cv) = cv {
                        v = cv;
                    }
                }
                Err(Abrupt::Break(bv)) => return Ok(Some(bv.unwrap_or(v))),
                Err(a) => return Err(a),
            }
        }
    }

    /// Build the upfront-snapshotted enumeration state; None = skip the loop
    /// entirely (undefined/null head value).
    fn build_for_in_state(&mut self, v: &Value) -> Result<Option<ForInState>, Abrupt> {
        let mut hops: Vec<(EnumHop, Vec<Units>)> = Vec::new();
        let mut cur: Option<ObjId>;
        match v {
            Value::Undefined | Value::Null => return Ok(None),
            Value::Obj(o) => {
                cur = Some(*o);
            }
            Value::Str(s) => {
                let mut snap: Vec<Units> = (0..s.len())
                    .map(|i| units_from_str(&i.to_string()))
                    .collect();
                snap.push(units_from_str("length"));
                hops.push((EnumHop::StrOwn, snap));
                cur = Some(self.intr.string_proto);
            }
            Value::Num(_) | Value::Bool(_) | Value::BigInt(_) => {
                // The wrapper's own surface is empty; its prototype
                // (Number/Boolean/BigInt.prototype) is spec-pinned
                // all-non-enumerable, so for-in enumerates nothing.
                hops.push((EnumHop::OpaqueSurface, Vec::new()));
                cur = Some(self.intr.object_proto);
            }
            Value::Sym(_) => {
                // A Symbol wrapper has no own enumerable surface; its prototype
                // chain (Symbol.prototype → Object.prototype) is all
                // non-enumerable. The OpaqueSurface marker makes any yield from
                // a later hop (e.g. a user-added enumerable Symbol.prototype
                // property) a sound refusal.
                hops.push((EnumHop::OpaqueSurface, Vec::new()));
                cur = Some(self.intr.symbol_proto);
            }
        }
        let mut n = 0;
        while let Some(o) = cur {
            if n >= 64 {
                return Err(Abrupt::Fatal("prototype chain too deep".to_string()));
            }
            if o == self.global {
                return Err(Abrupt::Fatal(
                    "for-in over the global object (engine global surface unmodeled)".to_string(),
                ));
            }
            if o == self.intr.console {
                return Err(Abrupt::Fatal(
                    "for-in over console (host object with enumerable unmodeled surface)"
                        .to_string(),
                ));
            }
            if matches!(self.obj(o).kind, ObjKind::Error) {
                return Err(Abrupt::Fatal(
                    "for-in over an error instance (engine-incidental own properties)".to_string(),
                ));
            }
            if matches!(self.obj(o).kind, ObjKind::TypedArray { .. }) {
                return Err(Abrupt::Fatal(
                    "for-in over a typed array (element-index enumeration out of slice)".to_string(),
                ));
            }
            if matches!(self.obj(o).kind, ObjKind::Proxy { .. }) {
                return Err(Abrupt::Fatal(
                    "for-in over a proxy (ownKeys/getOwnPropertyDescriptor trap enumeration out of slice)"
                        .to_string(),
                ));
            }
            let snap = crate::value::ordered_own_keys(self.obj(o));
            hops.push((EnumHop::Real(o), snap));
            cur = self.obj(o).proto;
            n += 1;
        }
        Ok(Some(ForInState {
            hops,
            cur: 0,
            idx: 0,
            visited: HashSet::new(),
        }))
    }

    /// The next for-in key, with the spec's visited/shadow discipline and the
    /// miss-danger refusals.
    fn next_for_in_key(&mut self, st: &mut ForInState) -> Result<Option<Units>, Abrupt> {
        loop {
            if st.cur >= st.hops.len() {
                return Ok(None);
            }
            let snap_len = st.hops[st.cur].1.len();
            if st.idx >= snap_len {
                // End of this hop: any own key added since the snapshot is
                // spec latitude ("not guaranteed to be visited") — refuse.
                if let EnumHop::Real(o) = st.hops[st.cur].0 {
                    if !matches!(self.obj(o).kind, ObjKind::IntrinsicOpaque) {
                        for k in self.obj(o).props.keys() {
                            if !st.hops[st.cur].1.contains(k) {
                                return Err(Abrupt::Fatal(
                                    "own property added during for-in enumeration (spec latitude)"
                                        .to_string(),
                                ));
                            }
                        }
                    }
                }
                st.cur += 1;
                st.idx = 0;
                continue;
            }
            let k = st.hops[st.cur].1[st.idx].clone();
            st.idx += 1;
            if st.visited.contains(&k) {
                continue;
            }
            // Spec 14.7.5.10: a key whose descriptor is gone at visit time is
            // NOT added to `visited` — a same-named proto key can still be
            // yielded later.
            let yielded = match &st.hops[st.cur].0 {
                EnumHop::Real(o) => match self.obj(*o).props.get(&k) {
                    None => continue, // deleted before visited: not recorded
                    Some(p) => {
                        st.visited.insert(k.clone());
                        p.enumerable
                    }
                },
                EnumHop::StrOwn => {
                    st.visited.insert(k.clone());
                    array_index_of(&k).is_some()
                }
                EnumHop::OpaqueSurface => false,
            };
            if !yielded {
                continue;
            }
            // Shadow soundness: every EARLIER hop must be model-complete for
            // this name (a real engine's unmodeled own property there —
            // enumerable or not — would have shadowed it).
            let name = units_to_lossy(&k);
            for (ph, _) in &st.hops[..st.cur] {
                match ph {
                    EnumHop::Real(o) => {
                        if let Some(gap) = self.own_miss_gap(*o, &name) {
                            return Err(Abrupt::Fatal(format!("for-in shadow: {gap}")));
                        }
                    }
                    EnumHop::StrOwn => {}
                    EnumHop::OpaqueSurface => {
                        return Err(Abrupt::Fatal(
                            "for-in shadow surface unmodeled (primitive wrapper prototype)"
                                .to_string(),
                        ));
                    }
                }
            }
            return Ok(Some(k));
        }
    }

    fn eval_for_of(
        &mut self,
        left: &ForInOfLeft,
        expr: &Expr,
        body: &Stmt,
        ctx: &Ctx,
    ) -> Compl {
        let val = self.eval_forinof_head(left, expr, ctx)?;
        let mut iter = self.slice_iterator(&val)?;
        let mut v = Value::Undefined;
        loop {
            let next = self.slice_iter_next(&mut iter)?;
            let Some(el) = next else {
                return Ok(Some(v));
            };
            self.charge_loop()?;
            // Binding/assigning the iteration value to the LHS can be an abrupt
            // completion (a non-writable target, a destructuring fault); per
            // 13.7.5.13 the iterator is not done, so IteratorClose runs before
            // the throw propagates (a throw completion swallows the close).
            let body_ctx = match self.bind_forinof_left(left, el, ctx) {
                Ok(c) => c,
                Err(a) => {
                    let _ = self.slice_iterator_close(&mut iter);
                    return Err(a);
                }
            };
            match self.eval_stmt(body, &body_ctx) {
                Ok(Some(val)) => v = val,
                Ok(None) => {}
                Err(Abrupt::Continue(cv)) => {
                    if let Some(cv) = cv {
                        v = cv;
                    }
                }
                // IteratorClose on early exit (7.4.11). For a NON-throw
                // completion (break / return) a throwing or non-object
                // `iterator.return()` PREEMPTS the completion (steps 5-6), so
                // propagate the close result via `?`. For a THROW completion the
                // original throw always wins (step 4), so the close is
                // best-effort (swallowed); a Fatal refusal likewise stands.
                Err(Abrupt::Break(bv)) => {
                    self.slice_iterator_close(&mut iter)?;
                    return Ok(Some(bv.unwrap_or(v)));
                }
                Err(Abrupt::Return(rv)) => {
                    self.slice_iterator_close(&mut iter)?;
                    return Err(Abrupt::Return(rv));
                }
                Err(a) => {
                    let _ = self.slice_iterator_close(&mut iter);
                    return Err(a);
                }
            }
        }
    }

    /// CreatePerIterationEnvironment (14.7.4.3): a fresh declarative frame
    /// (parented on the loop's OUTER env) with each binding copied from the
    /// previous iteration's frame.
    fn copy_iteration_env(&mut self, prev: EnvId, names: &[String], parent: EnvId) -> EnvId {
        let e = self.alloc_env(Some(parent));
        for n in names {
            let val = self.envs[prev.0 as usize]
                .bindings
                .get(n)
                .map_or(Value::Undefined, |b| b.value.clone());
            self.envs[e.0 as usize]
                .bindings
                .insert(n.clone(), Binding::var(val));
        }
        e
    }

    pub(crate) fn initialize_binding_public(&mut self, env: EnvId, name: &str, val: Value) {
        self.initialize_binding(env, name, val);
    }

    // -- generator-machine hooks (delegate to the verified tree-walker) -----

    /// Run one statement atomically (used by the generator machine for
    /// yield-free sub-statements).
    pub(crate) fn eval_stmt_public(&mut self, s: &Stmt, ctx: &Ctx) -> Compl {
        self.eval_stmt(s, ctx)
    }

    /// Evaluate one expression atomically.
    pub(crate) fn eval_expr_public(&mut self, e: &Expr, ctx: &Ctx) -> ERes {
        self.eval_expr(e, ctx)
    }

    /// Pre-declare a statement list's lexical (let/const/class) bindings.
    pub(crate) fn declare_lexical_public(
        &mut self,
        env: EnvId,
        stmts: &[Stmt],
    ) -> Result<(), Abrupt> {
        self.declare_lexical(env, stmts)
    }

    /// GetIterator over a slice iterable (arrays/strings/arguments/own
    /// generators).
    pub(crate) fn slice_iterator_public(
        &mut self,
        v: &Value,
    ) -> Result<crate::pattern::SliceIter, Abrupt> {
        self.slice_iterator(v)
    }

    /// One IteratorStep over a slice iterator.
    pub(crate) fn slice_iter_next_public(
        &mut self,
        it: &mut crate::pattern::SliceIter,
    ) -> Result<Option<Value>, Abrupt> {
        self.slice_iter_next(it)
    }

    /// Bind one for-of iteration value to a `var`/target head (the generator
    /// machine refuses lexical heads, whose per-iteration env is out of slice).
    pub(crate) fn bind_forinof_left_public(
        &mut self,
        left: &ForInOfLeft,
        val: Value,
        ctx: &Ctx,
    ) -> Result<(), Abrupt> {
        self.bind_forinof_left(left, val, ctx).map(|_| ())
    }

    fn initialize_binding(&mut self, env: EnvId, name: &str, val: Value) {
        let mut cur = Some(env);
        while let Some(e) = cur {
            if let Some(b) = self.envs[e.0 as usize].bindings.get_mut(name) {
                b.value = val;
                b.initialized = true;
                return;
            }
            cur = self.envs[e.0 as usize].parent;
        }
        // Parser guarantees the binding was pre-declared.
        unreachable!("lexical binding `{name}` not pre-declared");
    }
}

/// UpdateEmpty: fill an EMPTY completion value (normal or break/continue)
/// with `v`.
fn update_empty(r: Compl, v: Value) -> Compl {
    match r {
        Ok(None) => Ok(Some(v)),
        Err(Abrupt::Break(None)) => Err(Abrupt::Break(Some(v))),
        Err(Abrupt::Continue(None)) => Err(Abrupt::Continue(Some(v))),
        other => other,
    }
}

/// Statement-list UpdateEmpty: patch an empty break/continue with the running
/// completion value, when one exists.
fn patch_empty(a: Abrupt, v: &Option<Value>) -> Abrupt {
    match (a, v) {
        (Abrupt::Break(None), Some(val)) => Abrupt::Break(Some(val.clone())),
        (Abrupt::Continue(None), Some(val)) => Abrupt::Continue(Some(val.clone())),
        (other, _) => other,
    }
}

/// SameValueNonNumber + number strict equality (===).
pub fn strict_eq(it: &Interp, a: &Value, b: &Value) -> bool {
    let _ = it;
    match (a, b) {
        (Value::Undefined, Value::Undefined) | (Value::Null, Value::Null) => true,
        (Value::Bool(x), Value::Bool(y)) => x == y,
        (Value::Num(x), Value::Num(y)) => x == y, // NaN != NaN, +0 == -0
        // BigInt::equal — exact value equality (no ±0/NaN corner).
        (Value::BigInt(x), Value::BigInt(y)) => x == y,
        (Value::Str(x), Value::Str(y)) => x == y,
        (Value::Sym(x), Value::Sym(y)) => x == y,
        (Value::Obj(x), Value::Obj(y)) => x == y,
        _ => false,
    }
}
