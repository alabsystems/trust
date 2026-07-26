// Generators (ECMA-262 §27.3-27.5): the intrinsic object graph
// (%GeneratorFunction% / %GeneratorFunction.prototype% / %GeneratorPrototype%
// / %IteratorPrototype%) and a resumable evaluator for generator bodies.
//
// ARCHITECTURE (declared, with its bound). A tree-walking interpreter cannot
// suspend mid-expression on the native Rust stack. OS-thread-per-generator
// (the channel-baton design) is rejected here: the value model is `Rc`-based
// (`!Send`) and the heap holds `RefCell`s (`!Sync`), so sharing/moving the
// interpreter across threads needs `unsafe impl Send` transfer wrappers and a
// raw-pointer aliasing discipline — a memory-safety hazard inappropriate for a
// soundness-critical reference oracle. Step-limited replay is exact only for
// pure prefixes (too narrow). We therefore use a BOUNDED SAME-THREAD STATE
// MACHINE (option b): a small-step executor over an explicit frame stack that
// is preserved across suspension. Every yield-FREE sub-statement and every
// operand expression is delegated wholesale to the existing, adversarially
// verified `eval_stmt`/`eval_expr` — so their semantics are automatically as
// correct as the rest of the crate — and only the control-flow skeleton around
// suspension points (yield/yield* plumbing, loops, try/finally completion
// dispatch, for-of IteratorClose) is new. Anything the executor cannot lower to
// this skeleton is a sound `Abrupt::Fatal` (→ NoCoverage) refusal, never a
// wrong trace.
//
// BOUND. Supported yield-bearing constructs: statement sequences / lexical
// blocks, if/else, while / do-while / C-for, for-of over slice iterables and
// own untampered generators, try/catch/finally, return/throw/break/continue
// (unlabeled), and `yield`/`yield*` only in SIMPLE positions (expression
// statement, plain-identifier assignment RHS, single var/let/const initializer,
// return argument). A `yield` anywhere else (call argument, operator operand,
// computed key, multi-declarator, member-target assignment, for-in body, switch
// with yield, labeled statement, per-iteration `let` loop head) refuses the
// whole case. Step budget is charged against the shared loop-iteration cap.
//
// Author: Andrew Yates
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

use crate::ast::{
    BindTarget, DeclKind, Expr, ForInOfLeft, ForInit, FuncLit, Stmt,
};
use crate::interp::{Abrupt, Ctx, ERes, Interp};
use crate::pattern::SliceIter;
use crate::promise::NativeClosure;
use crate::value::{
    units_from_str, EnvId, GenId, NativeErrorKind, ObjId, ObjKind, Object, Prop, Value,
};
use std::rc::Rc;

/// How a suspended generator is resumed.
#[derive(Debug, Clone)]
pub(crate) enum Resumption {
    /// `next(v)` — the yield expression evaluates to `v`.
    Normal(Value),
    /// `return(v)` — a return completion is injected at the yield point.
    Return(Value),
    /// `throw(e)` — a throw completion is injected at the yield point.
    Throw(Value),
}

/// Observable generator state (27.5.1 [[GeneratorState]]).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum GenExec {
    SuspendedStart,
    SuspendedYield,
    Executing,
    Completed,
}

/// One outcome of a single machine step.
enum Step {
    /// Advance; call step again.
    Continue,
    /// A yield surfaced: suspend and return `{value, done:false}`.
    Yield(Value),
    /// An `await` surfaced (async function bodies only): suspend on the awaited
    /// value's promise.
    Await(Value),
    /// The body completed normally with this return value.
    Return(Value),
    /// The body threw (or an uncaught injected throw): propagate.
    Throw(Value),
    /// Out of slice / cap: refuse the whole case.
    Fatal(String),
}

/// The action a `PostYield` frame performs with the resume value.
enum PostAction {
    /// Bare `yield e;` — discard the resume value.
    Discard,
    /// `x = yield e` — assign the resume value to an existing binding.
    AssignName(String),
    /// `var/let/const x = yield e` — initialize/set a declared binding.
    BindName { name: String, init: bool },
    /// `return yield e` — return the resume value.
    Return,
}

/// The result of driving one `yield*` inner-iterator step.
enum YsOutcome {
    /// Yield this value to the outer consumer; the delegation continues.
    Yielded(Value),
    /// The inner iterator is exhausted; this is the `yield*` expression value.
    Done(Value),
    /// The delegation completed with a return: the outer generator returns v.
    ReturnOut(Value),
}

/// A completion being propagated up the frame stack (abrupt unwinding). The
/// value fields carry the payload.
enum Prop2 {
    Return(Value),
    Throw(Value),
    Break,
    Continue,
}

/// One resumable control-flow frame. The stack top is the current position;
/// yields leave it intact and resumes re-enter it.
enum Frame {
    /// Execute `stmts[idx..]`.
    Seq { stmts: Rc<Vec<Stmt>>, idx: usize },
    /// Restore `ctx.env` to this value when popped (a block/loop scope end).
    RestoreEnv(EnvId),
    /// `while (test) body` — re-evaluated each time control returns here.
    While { test: Rc<Expr>, body: Rc<Stmt> },
    /// `do body while (test)`.
    DoWhile { body: Rc<Stmt>, test: Rc<Expr>, started: bool },
    /// `for (init; test; update) body` (init already run).
    For {
        test: Option<Rc<Expr>>,
        update: Option<Rc<Expr>>,
        body: Rc<Stmt>,
        started: bool,
    },
    /// `for (left of iter) body` over a slice iterator.
    ForOf {
        iter: SliceIter,
        left: ForInOfLeft,
        body: Rc<Stmt>,
    },
    /// A yield in progress: consumes the resumption on resume.
    PostYield(PostAction),
    /// A `yield*` delegation in progress over a slice iterator: forwards
    /// next/return/throw to the inner iterator until it is done.
    YieldStar { iter: SliceIter, dest: PostAction },
    /// A `try` body guarded by a catch clause (finally is desugared to an
    /// enclosing TryFinally). Intercepts a Throw completion once.
    TryCatch {
        param: Option<BindTarget>,
        body: Rc<Vec<Stmt>>,
    },
    /// A `try`/`finally` guard. On ANY completion crossing it, the finally
    /// body runs; a normal finally resumes the saved completion, an abrupt
    /// finally overrides.
    TryFinally { body: Rc<Vec<Stmt>> },
    /// The finally body is running with a saved pending completion to resume.
    RunFinally { saved: Option<Prop2> },
}

/// The resumable state behind one generator OR async-function instance. Async
/// functions reuse the same small-step machine: an `await` suspends exactly the
/// way a `yield` does, but instead of surfacing a value to a `.next()` consumer
/// it registers promise reactions that resume the machine on a microtask tick.
pub(crate) struct GenState {
    pub exec: GenExec,
    ctx: Ctx,
    lit: Rc<FuncLit>,
    frames: Vec<Frame>,
    /// The resumption delivered into a pending yield/await.
    incoming: Option<Resumption>,
    /// For an async function: the (resolve, reject) resolving functions of the
    /// result promise, called when the body completes/throws. None = a plain
    /// generator.
    async_cap: Option<(Value, Value)>,
}

impl GenState {
    /// A placeholder swapped into the arena while a generator is running (its
    /// `Executing` state makes any re-entrant next/return/throw a TypeError).
    fn placeholder() -> GenState {
        GenState {
            exec: GenExec::Executing,
            ctx: Ctx {
                env: EnvId(0),
                this_val: Value::Undefined,
                strict: false,
                home_object: None,
                ctor_frame: None,
                priv_env: None,
                in_formal_params: false,
            },
            lit: Rc::new(dummy_lit()),
            frames: Vec::new(),
            incoming: None,
            async_cap: None,
        }
    }
}

fn dummy_lit() -> FuncLit {
    FuncLit {
        name: None,
        inferred_name: false,
        params: Vec::new(),
        rest_param: None,
        simple_params: true,
        body: Vec::new(),
        strict: false,
        vars: Vec::new(),
        funcs: Vec::new(),
        uses_arguments: false,
        is_method: false,
        is_arrow: false,
        is_generator: true,
        is_async: false,
    }
}

// ---------------------------------------------------------------------------
// yield detection (position validity is judged lazily during execution)
// ---------------------------------------------------------------------------

/// True when `e` contains a top-level suspension point (a `yield` in a
/// generator body or an `await` in an async body) that the small-step machine
/// must lower. (A generator body never contains `await` and an async body never
/// contains `yield`, so treating both as suspension points is safe for each.)
fn expr_has_yield(e: &Expr) -> bool {
    match e {
        Expr::Yield { .. } | Expr::Await(_) => true,
        Expr::Num(_)
        | Expr::BigInt(_)
        | Expr::Str(_)
        | Expr::Bool(_)
        | Expr::Null
        | Expr::Regex { .. }
        | Expr::This
        | Expr::Ident(_)
        | Expr::Function(_)
        | Expr::Arrow(_)
        | Expr::SpreadTrailingComma
        | Expr::Class(_) => false,
        Expr::Array(elems) => elems.iter().flatten().any(expr_has_yield),
        Expr::Seq(es) => es.iter().any(expr_has_yield),
        Expr::Object(_) => obj_has_yield(e),
        Expr::PatternAssign { value, .. } => expr_has_yield(value),
        Expr::Spread(x) | Expr::Paren(x) | Expr::Unary { expr: x, .. } | Expr::Delete(x) => {
            expr_has_yield(x)
        }
        Expr::Template(parts) => parts.iter().any(|p| match p {
            crate::ast::TplPart::Expr(e) => expr_has_yield(e),
            crate::ast::TplPart::Str(_) => false,
        }),
        Expr::SuperMember { prop } => member_prop_has_yield(prop),
        Expr::SuperCall { args } => args.iter().any(expr_has_yield),
        Expr::Member { obj, prop } => expr_has_yield(obj) || member_prop_has_yield(prop),
        Expr::Call { callee, args } | Expr::New { callee, args } => {
            expr_has_yield(callee) || args.iter().any(expr_has_yield)
        }
        Expr::Update { target, .. } => expr_has_yield(target),
        Expr::Binary { left, right, .. } | Expr::Logical { left, right, .. } => {
            expr_has_yield(left) || expr_has_yield(right)
        }
        Expr::Cond { test, cons, alt } => {
            expr_has_yield(test) || expr_has_yield(cons) || expr_has_yield(alt)
        }
        Expr::Assign { target, value, .. } => expr_has_yield(target) || expr_has_yield(value),
        // A `#name in obj` operand may contain a yield in its object operand.
        Expr::PrivateIn { obj, .. } => expr_has_yield(obj),
    }
}

fn member_prop_has_yield(p: &crate::ast::MemberProp) -> bool {
    match p {
        crate::ast::MemberProp::Dot(_) | crate::ast::MemberProp::Private(_) => false,
        crate::ast::MemberProp::Computed(e) => expr_has_yield(e),
    }
}

fn obj_has_yield(e: &Expr) -> bool {
    let Expr::Object(defs) = e else { return false };
    for d in defs {
        match d {
            crate::ast::PropDef::Data(k, v) => {
                if objkey_has_yield(k) || expr_has_yield(v) {
                    return true;
                }
            }
            crate::ast::PropDef::ProtoData(v) => {
                if expr_has_yield(v) {
                    return true;
                }
            }
            crate::ast::PropDef::Method(k, _)
            | crate::ast::PropDef::Getter(k, _)
            | crate::ast::PropDef::Setter(k, _) => {
                if objkey_has_yield(k) {
                    return true;
                }
            }
        }
    }
    false
}

fn objkey_has_yield(k: &crate::ast::ObjKey) -> bool {
    matches!(k, crate::ast::ObjKey::Computed(e) if expr_has_yield(e))
}

fn stmt_has_yield(s: &Stmt) -> bool {
    match s {
        Stmt::Empty | Stmt::FuncDecl(_) | Stmt::ClassDecl { .. } | Stmt::Break | Stmt::Continue => {
            false
        }
        Stmt::Expr(e) | Stmt::Throw(e) => expr_has_yield(e),
        Stmt::Return(e) => e.as_ref().is_some_and(expr_has_yield),
        Stmt::VarDecl { decls, .. } => decls
            .iter()
            .any(|(_, init)| init.as_ref().is_some_and(expr_has_yield)),
        Stmt::Block(b) => b.iter().any(stmt_has_yield),
        Stmt::If { test, cons, alt } => {
            expr_has_yield(test)
                || stmt_has_yield(cons)
                || alt.as_ref().is_some_and(|a| stmt_has_yield(a))
        }
        Stmt::While { test, body } => expr_has_yield(test) || stmt_has_yield(body),
        Stmt::DoWhile { body, test } => stmt_has_yield(body) || expr_has_yield(test),
        Stmt::For {
            init,
            test,
            update,
            body,
        } => {
            init.as_ref().is_some_and(forinit_has_yield)
                || test.as_ref().is_some_and(expr_has_yield)
                || update.as_ref().is_some_and(expr_has_yield)
                || stmt_has_yield(body)
        }
        Stmt::ForIn { obj, body, .. } => expr_has_yield(obj) || stmt_has_yield(body),
        Stmt::ForOf { expr, body, .. } => expr_has_yield(expr) || stmt_has_yield(body),
        Stmt::Try {
            block,
            catch,
            finally,
        } => {
            block.iter().any(stmt_has_yield)
                || catch.as_ref().is_some_and(|(_, b)| b.iter().any(stmt_has_yield))
                || finally.as_ref().is_some_and(|b| b.iter().any(stmt_has_yield))
        }
        Stmt::Switch { disc, cases } => {
            expr_has_yield(disc)
                || cases
                    .iter()
                    .any(|(t, b)| t.as_ref().is_some_and(expr_has_yield) || b.iter().any(stmt_has_yield))
        }
    }
}

fn forinit_has_yield(f: &ForInit) -> bool {
    match f {
        ForInit::Var(decls) | ForInit::Lex { decls, .. } => decls
            .iter()
            .any(|(_, init)| init.as_ref().is_some_and(expr_has_yield)),
        ForInit::Expr(e) => expr_has_yield(e),
    }
}

// ---------------------------------------------------------------------------
// generator creation + resume entry points
// ---------------------------------------------------------------------------

impl Interp {
    /// GeneratorStart-adjacent: run FunctionDeclarationInstantiation eagerly
    /// (parameter side effects happen at call time, per spec), then create a
    /// suspendedStart generator object whose [[Prototype]] is the function's
    /// `.prototype` at call time.
    pub(crate) fn create_generator(
        &mut self,
        lit: &Rc<FuncLit>,
        env: EnvId,
        fid: ObjId,
        this: Value,
        args: Vec<Value>,
        home: Option<ObjId>,
    ) -> ERes {
        let this_val = if lit.strict {
            this
        } else {
            match this {
                Value::Undefined | Value::Null => Value::Obj(self.global),
                Value::Obj(_) => this,
                prim => Value::Obj(self.to_object_wrapper(&prim)?),
            }
        };
        // The generator's [[Prototype]] comes from Get(fid, "prototype"). The
        // spec reads it AFTER FunctionDeclarationInstantiation, but real
        // engines diverge when a parameter default mutates the function's own
        // `.prototype` mid-instantiation — a spec-vs-engine ordering quirk. We
        // read it before and after FDI and refuse if a default changed it (the
        // only case where the create-order is observable); otherwise the value
        // is unambiguous.
        let proto_before = self.gen_prototype_slot(fid);
        let ctx = self.prepare_fn_ctx_full(lit, env, fid, this_val, &args, home, None)?;
        let proto_after = self.gen_prototype_slot(fid);
        let unchanged = match (&proto_before, &proto_after) {
            (None, None) => true,
            (Some(a), Some(b)) => crate::interp::strict_eq(self, a, b),
            _ => false,
        };
        if !unchanged {
            return Err(Abrupt::Fatal(
                "generator `.prototype` mutated during FunctionDeclarationInstantiation \
                 (engine-divergent create order)"
                    .to_string(),
            ));
        }
        // gen.[[Prototype]] = Get(fid, "prototype") if object, else the
        // intrinsic %GeneratorPrototype%.
        let proto = match proto_after {
            Some(Value::Obj(p)) => p,
            _ => self.intr.generator_proto,
        };
        let gid = GenId(u32::try_from(self.generators.len()).expect("generators bounded"));
        self.generators.push(GenState {
            exec: GenExec::SuspendedStart,
            ctx,
            lit: Rc::clone(lit),
            frames: Vec::new(),
            incoming: None,
            async_cap: None,
        });
        let oid = self.alloc(Object::new(ObjKind::Generator(gid), Some(proto)));
        Ok(Value::Obj(oid))
    }

    /// The own `prototype` data-slot value of a function object (None if
    /// absent or an accessor).
    fn gen_prototype_slot(&self, fid: ObjId) -> Option<Value> {
        self.obj(fid)
            .props
            .get(&units_from_str("prototype"))
            .and_then(Prop::data_value)
            .cloned()
    }

    /// The generator id behind a value, if it is a generator instance.
    pub(crate) fn as_generator(&self, v: &Value) -> Option<GenId> {
        match v {
            Value::Obj(o) => match self.obj(*o).kind {
                ObjKind::Generator(g) => Some(g),
                _ => None,
            },
            _ => None,
        }
    }

    /// GeneratorResume / GeneratorResumeAbrupt (27.5.3.3-4): resume `gid` with
    /// `r`, returning the iterator-result object value (or propagating a throw
    /// the body did not catch).
    pub(crate) fn generator_resume(&mut self, gid: GenId, r: Resumption) -> ERes {
        let exec = self.generators[gid.0 as usize].exec;
        match exec {
            GenExec::Executing => Err(self.throw_native(NativeErrorKind::TypeError)),
            GenExec::Completed => self.resume_completed(r),
            GenExec::SuspendedStart => {
                match r {
                    Resumption::Return(v) => {
                        self.generators[gid.0 as usize].exec = GenExec::Completed;
                        Ok(self.iter_result(v, true))
                    }
                    Resumption::Throw(e) => {
                        self.generators[gid.0 as usize].exec = GenExec::Completed;
                        Err(Abrupt::Throw(e))
                    }
                    Resumption::Normal(_) => {
                        // Start: push the body sequence and run.
                        let body = {
                            let g = &mut self.generators[gid.0 as usize];
                            g.exec = GenExec::Executing;
                            Rc::clone(&g.lit)
                        };
                        let mut local = std::mem::replace(
                            &mut self.generators[gid.0 as usize],
                            GenState::placeholder(),
                        );
                        local.frames.push(Frame::Seq {
                            stmts: Rc::new(body.body.clone()),
                            idx: 0,
                        });
                        self.run_generator(gid, local)
                    }
                }
            }
            GenExec::SuspendedYield => {
                let mut local = std::mem::replace(
                    &mut self.generators[gid.0 as usize],
                    GenState::placeholder(),
                );
                local.exec = GenExec::Executing;
                local.incoming = Some(r);
                self.run_generator(gid, local)
            }
        }
    }

    /// next/return/throw on an already-completed generator (27.5.1.2-4).
    fn resume_completed(&mut self, r: Resumption) -> ERes {
        match r {
            Resumption::Normal(_) => Ok(self.iter_result(Value::Undefined, true)),
            Resumption::Return(v) => Ok(self.iter_result(v, true)),
            Resumption::Throw(e) => Err(Abrupt::Throw(e)),
        }
    }

    /// Drive the step loop to the next suspension/termination, then write the
    /// generator state back into the arena.
    fn run_generator(&mut self, gid: GenId, mut local: GenState) -> ERes {
        let outcome = loop {
            if let Err(a) = self.charge_loop() {
                break Err(a);
            }
            match self.gen_step(&mut local) {
                Step::Continue => {}
                Step::Yield(v) => {
                    local.exec = GenExec::SuspendedYield;
                    break Ok(self.iter_result(v, false));
                }
                Step::Await(_) => {
                    break Err(Abrupt::Fatal(
                        "await in a generator body (async generator out of slice)".into(),
                    ))
                }
                Step::Return(v) => {
                    local.exec = GenExec::Completed;
                    break Ok(self.iter_result(v, true));
                }
                Step::Throw(e) => {
                    local.exec = GenExec::Completed;
                    break Err(Abrupt::Throw(e));
                }
                Step::Fatal(s) => break Err(Abrupt::Fatal(s)),
            }
        };
        // Restore the (updated) state; on Fatal the case refuses regardless.
        self.generators[gid.0 as usize] = local;
        outcome
    }

    // -- async functions ----------------------------------------------------

    /// EvaluateAsyncFunctionBody (27.7.5)-adjacent: create the result promise;
    /// a FunctionDeclarationInstantiation THROW (`fdi`) rejects it, an
    /// out-of-slice FDI refuses; otherwise build the resumable machine over the
    /// body context and run it up to the first `await` or to completion. Always
    /// returns the result promise. A Fatal from the body refuses the whole case.
    pub(crate) fn call_async_function(
        &mut self,
        lit: &Rc<FuncLit>,
        fdi: Result<Ctx, Abrupt>,
    ) -> ERes {
        let (pid, oid) = self.alloc_promise(self.intr.promise_proto);
        let (resolve, reject) = self.create_resolving_functions(pid);
        let ctx = match fdi {
            Ok(c) => c,
            Err(Abrupt::Throw(e)) => {
                self.call_value(&reject, Value::Undefined, vec![e])?;
                return Ok(Value::Obj(oid));
            }
            Err(other) => return Err(other),
        };
        let gid = GenId(u32::try_from(self.generators.len()).expect("generators bounded"));
        self.generators.push(GenState {
            exec: GenExec::Executing,
            ctx,
            lit: Rc::clone(lit),
            frames: Vec::new(),
            incoming: None,
            async_cap: Some((resolve, reject)),
        });
        let mut local =
            std::mem::replace(&mut self.generators[gid.0 as usize], GenState::placeholder());
        let body = Rc::new(local.lit.body.clone());
        local.frames.push(Frame::Seq { stmts: body, idx: 0 });
        self.async_run(gid, local)?;
        Ok(Value::Obj(oid))
    }

    /// GeneratorResume-adjacent for async: deliver a resumption (from an await
    /// reaction job) and drive the machine to the next suspension/completion.
    pub(crate) fn async_resume(&mut self, gid: GenId, r: Resumption) -> Result<(), Abrupt> {
        match self.generators[gid.0 as usize].exec {
            GenExec::Completed => Ok(()),
            GenExec::Executing => Err(Abrupt::Fatal("re-entrant async resume".into())),
            GenExec::SuspendedStart | GenExec::SuspendedYield => {
                let mut local = std::mem::replace(
                    &mut self.generators[gid.0 as usize],
                    GenState::placeholder(),
                );
                local.exec = GenExec::Executing;
                local.incoming = Some(r);
                self.async_run(gid, local)
            }
        }
    }

    /// Drive an async machine to its next `await` suspension or to completion,
    /// then act: on await, wrap the value with PromiseResolve and attach resume
    /// reactions; on return/throw, resolve/reject the result promise.
    fn async_run(&mut self, gid: GenId, mut local: GenState) -> Result<(), Abrupt> {
        enum Term {
            Await(Value),
            Resolve(Value),
            Reject(Value),
        }
        let outcome: Result<Term, Abrupt> = loop {
            if let Err(a) = self.charge_loop() {
                break Err(a);
            }
            match self.gen_step(&mut local) {
                Step::Continue => {}
                Step::Await(v) => {
                    local.exec = GenExec::SuspendedYield;
                    break Ok(Term::Await(v));
                }
                Step::Return(v) => {
                    local.exec = GenExec::Completed;
                    break Ok(Term::Resolve(v));
                }
                Step::Throw(e) => {
                    local.exec = GenExec::Completed;
                    break Ok(Term::Reject(e));
                }
                Step::Yield(_) => {
                    break Err(Abrupt::Fatal(
                        "yield in an async function (async generator out of slice)".into(),
                    ))
                }
                Step::Fatal(s) => break Err(Abrupt::Fatal(s)),
            }
        };
        self.generators[gid.0 as usize] = local;
        match outcome {
            Err(a) => Err(a),
            Ok(Term::Await(v)) => {
                // Await (27.7.5.3): promise = PromiseResolve(%Promise%, v),
                // then attach the resume handlers with no capability.
                let promise = self.promise_resolve_default(v)?;
                let Some(pid) = self.as_promise(&promise) else {
                    return Err(Abrupt::Fatal(
                        "await: PromiseResolve did not yield a promise".into(),
                    ));
                };
                let on_f = self.alloc_native(NativeClosure::AsyncResume {
                    gid,
                    is_throw: false,
                });
                let on_r = self.alloc_native(NativeClosure::AsyncResume { gid, is_throw: true });
                self.perform_promise_then(pid, on_f, on_r, None);
                Ok(())
            }
            Ok(Term::Resolve(v)) => {
                let resolve = self.generators[gid.0 as usize]
                    .async_cap
                    .as_ref()
                    .expect("async cap")
                    .0
                    .clone();
                self.call_value(&resolve, Value::Undefined, vec![v])?;
                Ok(())
            }
            Ok(Term::Reject(e)) => {
                let reject = self.generators[gid.0 as usize]
                    .async_cap
                    .as_ref()
                    .expect("async cap")
                    .1
                    .clone();
                self.call_value(&reject, Value::Undefined, vec![e])?;
                Ok(())
            }
        }
    }

    /// CreateIterResultObject (7.4.13): `{ value, done }` with value then done,
    /// both enumerable/writable/configurable, proto %Object.prototype%.
    pub(crate) fn iter_result(&mut self, value: Value, done: bool) -> Value {
        let oid = self.alloc(Object::new(ObjKind::Plain, Some(self.intr.object_proto)));
        self.obj_mut(oid)
            .props
            .insert(units_from_str("value"), Prop::data(value));
        self.obj_mut(oid)
            .props
            .insert(units_from_str("done"), Prop::data(Value::Bool(done)));
        Value::Obj(oid)
    }

    // -- the small-step executor -------------------------------------------

    fn gen_step(&mut self, g: &mut GenState) -> Step {
        let Some(top) = g.frames.last_mut() else {
            // No frames left: normal completion, undefined return value.
            return Step::Return(Value::Undefined);
        };
        match top {
            Frame::RestoreEnv(env) => {
                let env = *env;
                g.ctx.env = env;
                g.frames.pop();
                Step::Continue
            }
            Frame::PostYield(_) => self.step_post_yield(g),
            Frame::YieldStar { .. } => self.step_yield_star(g),
            Frame::Seq { .. } => self.step_seq(g),
            Frame::While { .. } => self.step_while(g),
            Frame::DoWhile { .. } => self.step_dowhile(g),
            Frame::For { .. } => self.step_for(g),
            Frame::ForOf { .. } => self.step_for_of(g),
            Frame::TryCatch { .. } => {
                // Entering the try body: descend into it (a nested Seq was
                // pushed at frame creation); reaching the TryCatch frame again
                // means the body completed normally — pop the handler.
                g.frames.pop();
                Step::Continue
            }
            Frame::TryFinally { body } => {
                // Try body completed normally: run finally with no saved
                // completion, then continue.
                let body = Rc::clone(body);
                g.frames.pop();
                self.enter_finally(g, body, None)
            }
            Frame::RunFinally { saved } => {
                // Finally body completed normally: resume the saved completion.
                let saved = saved.take();
                g.frames.pop();
                match saved {
                    None => Step::Continue,
                    Some(p) => self.dispatch(g, p),
                }
            }
        }
    }

    fn step_seq(&mut self, g: &mut GenState) -> Step {
        let (stmts, idx) = match g.frames.last() {
            Some(Frame::Seq { stmts, idx }) => (Rc::clone(stmts), *idx),
            _ => return Step::Fatal("gen: seq frame vanished".into()),
        };
        if idx >= stmts.len() {
            g.frames.pop();
            return Step::Continue;
        }
        // Advance the cursor before entering the statement, so resuming after a
        // suspension continues past it.
        if let Some(Frame::Seq { idx: i, .. }) = g.frames.last_mut() {
            *i += 1;
        }
        let s = stmts[idx].clone();
        self.enter_stmt(g, &s)
    }

    /// Enter one statement: run it atomically if it is yield-free, otherwise
    /// lower the supported yield-bearing shapes (or refuse).
    fn enter_stmt(&mut self, g: &mut GenState, s: &Stmt) -> Step {
        if !stmt_has_yield(s) {
            return match self.eval_stmt_public(s, &g.ctx) {
                Ok(_) => Step::Continue,
                Err(a) => self.abrupt_to_step(g, a),
            };
        }
        match s {
            Stmt::Expr(e) => match e {
                Expr::Yield { .. } | Expr::Await(_) => {
                    self.enter_suspend_expr(g, e, PostAction::Discard)
                }
                // `x = yield e` / `x = await e` — plain identifier target only
                // (a member target must evaluate its reference before the
                // operand, which the machine does not thread through the
                // suspension yet).
                Expr::Assign {
                    op: None,
                    target,
                    value,
                } if matches!(**value, Expr::Yield { .. } | Expr::Await(_)) => {
                    match target.as_ref() {
                        Expr::Ident(name) => {
                            self.enter_suspend_expr(g, value, PostAction::AssignName(name.clone()))
                        }
                        _ => Step::Fatal(
                            "gen: yield/await assigned to a non-identifier target (out of slice)"
                                .into(),
                        ),
                    }
                }
                _ => Step::Fatal(
                    "gen: yield/await in an unsupported expression-statement position (out of slice)"
                        .into(),
                ),
            },
            Stmt::Return(Some(e)) => {
                if matches!(e, Expr::Yield { .. } | Expr::Await(_)) {
                    self.enter_suspend_expr(g, e, PostAction::Return)
                } else {
                    Step::Fatal("gen: yield/await nested in return operand (out of slice)".into())
                }
            }
            Stmt::VarDecl { kind, decls } => self.enter_yield_vardecl(g, *kind, decls),
            Stmt::Block(body) => self.enter_block(g, Rc::new(body.clone())),
            Stmt::If { test, cons, alt } => {
                match self.eval_expr_public(test, &g.ctx) {
                    Ok(v) => {
                        if self.to_boolean(&v) {
                            self.enter_stmt(g, cons)
                        } else if let Some(a) = alt {
                            self.enter_stmt(g, a)
                        } else {
                            Step::Continue
                        }
                    }
                    Err(a) => self.abrupt_to_step(g, a),
                }
            }
            Stmt::While { test, body } => {
                g.frames.push(Frame::While {
                    test: Rc::new(test.clone()),
                    body: Rc::new((**body).clone()),
                });
                Step::Continue
            }
            Stmt::DoWhile { body, test } => {
                g.frames.push(Frame::DoWhile {
                    body: Rc::new((**body).clone()),
                    test: Rc::new(test.clone()),
                    started: false,
                });
                Step::Continue
            }
            Stmt::For {
                init,
                test,
                update,
                body,
            } => self.enter_for(g, init.as_ref(), test.as_ref(), update.as_ref(), body),
            Stmt::ForOf { left, expr, body } => self.enter_for_of(g, left, expr, body),
            Stmt::Try {
                block,
                catch,
                finally,
            } => self.enter_try(g, block, catch, finally),
            _ => Step::Fatal("gen: yield in an unsupported statement position (out of slice)".into()),
        }
    }

    /// Dispatch a suspension expression (yield or await) in a simple position.
    fn enter_suspend_expr(&mut self, g: &mut GenState, e: &Expr, action: PostAction) -> Step {
        match e {
            Expr::Yield { .. } => self.enter_yield_expr(g, e, action),
            Expr::Await(_) => self.enter_await_expr(g, e, action),
            _ => Step::Fatal("gen: expected a yield/await expression".into()),
        }
    }

    /// An `await UnaryExpression` in a simple position: evaluate the operand
    /// atomically, push the PostYield action (the resume handling is identical
    /// to a yield), and surface `Step::Await` so the async driver attaches the
    /// promise reactions.
    fn enter_await_expr(&mut self, g: &mut GenState, e: &Expr, action: PostAction) -> Step {
        let Expr::Await(arg) = e else {
            return Step::Fatal("gen: expected an await expression".into());
        };
        if expr_has_yield(arg) {
            return Step::Fatal("gen: nested await/yield operand (out of slice)".into());
        }
        let val = match self.eval_expr_public(arg, &g.ctx) {
            Ok(v) => v,
            Err(a) => return self.abrupt_to_step(g, a),
        };
        g.frames.push(Frame::PostYield(action));
        Step::Await(val)
    }

    /// A yield/yield* expression in a simple position: evaluate the operand
    /// atomically, push the PostYield action, and suspend.
    fn enter_yield_expr(&mut self, g: &mut GenState, e: &Expr, action: PostAction) -> Step {
        let Expr::Yield { delegate, arg } = e else {
            return Step::Fatal("gen: expected a yield expression".into());
        };
        if arg.as_ref().is_some_and(|a| expr_has_yield(a)) {
            return Step::Fatal("gen: nested yield operand (out of slice)".into());
        }
        let val = match arg {
            Some(a) => match self.eval_expr_public(a, &g.ctx) {
                Ok(v) => v,
                Err(a) => return self.abrupt_to_step(g, a),
            },
            None => Value::Undefined,
        };
        if *delegate {
            // yield* AssignmentExpression: GetIterator over the (slice)
            // iterable, then drive it, forwarding completions.
            let iter = match self.slice_iterator_public(&val) {
                Ok(it) => it,
                Err(a) => return self.abrupt_to_step(g, a),
            };
            g.frames.push(Frame::YieldStar { iter, dest: action });
            return Step::Continue;
        }
        g.frames.push(Frame::PostYield(action));
        Step::Yield(val)
    }

    /// One step of a `yield*` delegation: forward the received completion to
    /// the inner iterator and either yield its value or finish.
    fn step_yield_star(&mut self, g: &mut GenState) -> Step {
        let received = g.incoming.take().unwrap_or(Resumption::Normal(Value::Undefined));
        // Take the iterator + destination out to drive the inner iterator.
        let (mut iter, dest) = match g.frames.last_mut() {
            Some(Frame::YieldStar { iter, dest }) => (
                std::mem::replace(iter, SliceIter::Str(Rc::new(Vec::new()), 0)),
                std::mem::replace(dest, PostAction::Discard),
            ),
            _ => return Step::Fatal("gen: yield* frame vanished".into()),
        };
        // Drive one iteration based on the received completion kind.
        let outcome = match &received {
            Resumption::Normal(v) => self.ys_next(&mut iter, v.clone()),
            Resumption::Throw(e) => self.ys_throw(&mut iter, e.clone()),
            Resumption::Return(v) => self.ys_return(&mut iter, v.clone()),
        };
        match outcome {
            Err(a) => {
                // A propagated throw from the inner iterator (uncaught).
                g.frames.pop();
                self.abrupt_to_step(g, a)
            }
            Ok(YsOutcome::Yielded(v)) => {
                // Suspend again, keeping the yield* frame (restore iter/dest).
                if let Some(Frame::YieldStar { iter: slot, dest: d }) = g.frames.last_mut() {
                    *slot = iter;
                    *d = dest;
                }
                Step::Yield(v)
            }
            Ok(YsOutcome::Done(v)) => {
                g.frames.pop();
                self.apply_yield_dest(g, dest, v)
            }
            Ok(YsOutcome::ReturnOut(v)) => {
                // The delegation itself completed with a return (received a
                // return, or the inner iterator returned): the outer generator
                // returns this value.
                g.frames.pop();
                Step::Return(v)
            }
        }
    }

    /// Perform the destination binding for a completed `yield*` value.
    fn apply_yield_dest(&mut self, g: &mut GenState, dest: PostAction, v: Value) -> Step {
        match dest {
            PostAction::Discard => Step::Continue,
            PostAction::Return => Step::Return(v),
            PostAction::AssignName(name) => match self.env_set(&g.ctx, &name, v) {
                Ok(()) => Step::Continue,
                Err(a) => self.abrupt_to_step(g, a),
            },
            PostAction::BindName { name, init } => {
                if init {
                    self.initialize_binding_public(g.ctx.env, &name, v);
                } else if let Err(a) = self.env_set(&g.ctx, &name, v) {
                    return self.abrupt_to_step(g, a);
                }
                Step::Continue
            }
        }
    }

    /// yield* inner.next(v): Ok(Yielded/Done) or Err(propagated throw).
    fn ys_next(&mut self, iter: &mut SliceIter, v: Value) -> Result<YsOutcome, Abrupt> {
        match iter {
            SliceIter::Generator(gid) => {
                let gid = *gid;
                let res = self.generator_resume(gid, Resumption::Normal(v))?;
                self.ys_read_result(res)
            }
            SliceIter::ArrayLike(..) | SliceIter::Str(..) | SliceIter::IterObj(..) | SliceIter::StringIterObj(..) | SliceIter::RegExpStringIter(..) => {
                match self.slice_iter_next(iter)? {
                    Some(val) => Ok(YsOutcome::Yielded(val)),
                    None => Ok(YsOutcome::Done(Value::Undefined)),
                }
            }
            // `yield*` delegation to a general user iterable needs the full
            // next/throw/return forwarding protocol (14.4.14) over user methods
            // — out of the current slice; refuse soundly.
            SliceIter::General { .. } => Err(Abrupt::Fatal(
                "yield* over a general (non-intrinsic) iterable (out of slice)".to_string(),
            )),
        }
    }

    /// yield* forwarding of a throw completion (14.4.14 step for throw).
    fn ys_throw(&mut self, iter: &mut SliceIter, e: Value) -> Result<YsOutcome, Abrupt> {
        match iter {
            SliceIter::Generator(gid) => {
                let gid = *gid;
                // Forward to the inner generator's `throw` (our generators
                // always have a throw method).
                let res = self.generator_resume(gid, Resumption::Throw(e))?;
                self.ys_read_result(res)
            }
            // The array/string iterators have no `throw` method: IteratorClose
            // (a no-op) then throw a TypeError.
            SliceIter::ArrayLike(..) | SliceIter::Str(..) | SliceIter::IterObj(..) | SliceIter::StringIterObj(..) | SliceIter::RegExpStringIter(..) => {
                self.slice_iterator_close(iter)?;
                Err(self.throw_native(NativeErrorKind::TypeError))
            }
            SliceIter::General { .. } => Err(Abrupt::Fatal(
                "yield* throw over a general (non-intrinsic) iterable (out of slice)".to_string(),
            )),
        }
    }

    /// yield* forwarding of a return completion (14.4.14 step for return).
    fn ys_return(&mut self, iter: &mut SliceIter, v: Value) -> Result<YsOutcome, Abrupt> {
        match iter {
            SliceIter::Generator(gid) => {
                let gid = *gid;
                let res = self.generator_resume(gid, Resumption::Return(v))?;
                // On the inner iterator's return: if done, the delegation
                // returns its value; otherwise keep yielding.
                let (done, value) = self.read_iter_result(res)?;
                if done {
                    Ok(YsOutcome::ReturnOut(value))
                } else {
                    Ok(YsOutcome::Yielded(value))
                }
            }
            SliceIter::General { .. } => Err(Abrupt::Fatal(
                "yield* return over a general (non-intrinsic) iterable (out of slice)".to_string(),
            )),
            // No `return` method: the return propagates unchanged.
            SliceIter::ArrayLike(..) | SliceIter::Str(..) | SliceIter::IterObj(..) | SliceIter::StringIterObj(..) | SliceIter::RegExpStringIter(..) => {
                Ok(YsOutcome::ReturnOut(v))
            }
        }
    }

    /// Interpret a generator iter-result object as a normal next/throw outcome.
    fn ys_read_result(&mut self, res: Value) -> Result<YsOutcome, Abrupt> {
        let (done, value) = self.read_iter_result(res)?;
        if done {
            Ok(YsOutcome::Done(value))
        } else {
            Ok(YsOutcome::Yielded(value))
        }
    }

    /// Read `{done, value}` off an iterator-result object.
    fn read_iter_result(&mut self, res: Value) -> Result<(bool, Value), Abrupt> {
        let Value::Obj(roid) = res else {
            return Err(Abrupt::Fatal("generator result not an object".into()));
        };
        let done = self.get_from_object(roid, &units_from_str("done"))?;
        let value = self.get_from_object(roid, &units_from_str("value"))?;
        Ok((self.to_boolean(&done), value))
    }

    fn step_post_yield(&mut self, g: &mut GenState) -> Step {
        let incoming = g.incoming.take();
        let action = match g.frames.pop() {
            Some(Frame::PostYield(a)) => a,
            _ => return Step::Fatal("gen: post-yield frame vanished".into()),
        };
        match incoming {
            None | Some(Resumption::Normal(_)) => {
                let v = match incoming {
                    Some(Resumption::Normal(v)) => v,
                    _ => Value::Undefined,
                };
                match action {
                    PostAction::Discard => Step::Continue,
                    PostAction::Return => Step::Return(v),
                    PostAction::AssignName(name) => match self.env_set(&g.ctx, &name, v) {
                        Ok(()) => Step::Continue,
                        Err(a) => self.abrupt_to_step(g, a),
                    },
                    PostAction::BindName { name, init } => {
                        if init {
                            self.initialize_binding_public(g.ctx.env, &name, v);
                        } else if let Err(a) = self.env_set(&g.ctx, &name, v) {
                            return self.abrupt_to_step(g, a);
                        }
                        Step::Continue
                    }
                }
            }
            Some(Resumption::Return(v)) => self.dispatch(g, Prop2::Return(v)),
            Some(Resumption::Throw(e)) => self.dispatch(g, Prop2::Throw(e)),
        }
    }

    fn enter_yield_vardecl(
        &mut self,
        g: &mut GenState,
        kind: DeclKind,
        decls: &[(BindTarget, Option<Expr>)],
    ) -> Step {
        if decls.len() != 1 {
            return Step::Fatal("gen: yield in a multi-declarator declaration (out of slice)".into());
        }
        let (target, init) = &decls[0];
        let BindTarget::Name(name) = target else {
            return Step::Fatal("gen: yield initializer for a pattern binding (out of slice)".into());
        };
        let Some(init) = init else {
            return Step::Fatal("gen: declaration yield/await without initializer".into());
        };
        if !matches!(init, Expr::Yield { .. } | Expr::Await(_)) {
            return Step::Fatal(
                "gen: yield/await nested in a declaration initializer (out of slice)".into(),
            );
        }
        let action = PostAction::BindName {
            name: name.clone(),
            init: kind != DeclKind::Var,
        };
        self.enter_suspend_expr(g, init, action)
    }

    fn enter_block(&mut self, g: &mut GenState, body: Rc<Vec<Stmt>>) -> Step {
        // A yield-bearing block with function declarations would need hoisted
        // instantiation we do not perform here — refuse.
        if body.iter().any(|s| matches!(s, Stmt::FuncDecl(_))) {
            return Step::Fatal("gen: function declaration in a yield-bearing block (out of slice)".into());
        }
        let parent = g.ctx.env;
        let env = self.alloc_env(Some(parent));
        if let Err(a) = self.declare_lexical_public(env, &body) {
            return self.abrupt_to_step(g, a);
        }
        g.ctx.env = env;
        g.frames.push(Frame::RestoreEnv(parent));
        g.frames.push(Frame::Seq {
            stmts: body,
            idx: 0,
        });
        Step::Continue
    }

    fn enter_for(
        &mut self,
        g: &mut GenState,
        init: Option<&ForInit>,
        test: Option<&Expr>,
        update: Option<&Expr>,
        body: &Stmt,
    ) -> Step {
        // Only `var` / expression / empty init is supported for a yield-bearing
        // for-loop; per-iteration `let` scoping is out of slice.
        match init {
            None => {}
            Some(ForInit::Expr(e)) => {
                if let Err(a) = self.eval_expr_public(e, &g.ctx) {
                    return self.abrupt_to_step(g, a);
                }
            }
            Some(ForInit::Var(_)) => {
                // Run the var-init atomically via a synthesized statement.
                let s = Stmt::VarDecl {
                    kind: DeclKind::Var,
                    decls: match init {
                        Some(ForInit::Var(d)) => d.clone(),
                        _ => unreachable!(),
                    },
                };
                if stmt_has_yield(&s) {
                    return Step::Fatal("gen: yield in a for-loop initializer (out of slice)".into());
                }
                if let Err(a) = self.eval_stmt_public(&s, &g.ctx) {
                    return self.abrupt_to_step(g, a);
                }
            }
            Some(ForInit::Lex { .. }) => {
                return Step::Fatal("gen: lexical for-loop head with yield body (out of slice)".into());
            }
        }
        g.frames.push(Frame::For {
            test: test.map(|e| Rc::new(e.clone())),
            update: update.map(|e| Rc::new(e.clone())),
            body: Rc::new(body.clone()),
            started: false,
        });
        Step::Continue
    }

    fn step_while(&mut self, g: &mut GenState) -> Step {
        let (test, body) = match g.frames.last() {
            Some(Frame::While { test, body }) => (Rc::clone(test), Rc::clone(body)),
            _ => return Step::Fatal("gen: while frame vanished".into()),
        };
        match self.eval_expr_public(&test, &g.ctx) {
            Ok(v) => {
                if self.to_boolean(&v) {
                    self.enter_stmt(g, &body)
                } else {
                    g.frames.pop();
                    Step::Continue
                }
            }
            Err(a) => self.abrupt_to_step(g, a),
        }
    }

    fn step_dowhile(&mut self, g: &mut GenState) -> Step {
        let (body, test, started) = match g.frames.last() {
            Some(Frame::DoWhile { body, test, started }) => {
                (Rc::clone(body), Rc::clone(test), *started)
            }
            _ => return Step::Fatal("gen: do-while frame vanished".into()),
        };
        if !started {
            if let Some(Frame::DoWhile { started, .. }) = g.frames.last_mut() {
                *started = true;
            }
            return self.enter_stmt(g, &body);
        }
        match self.eval_expr_public(&test, &g.ctx) {
            Ok(v) => {
                if self.to_boolean(&v) {
                    self.enter_stmt(g, &body)
                } else {
                    g.frames.pop();
                    Step::Continue
                }
            }
            Err(a) => self.abrupt_to_step(g, a),
        }
    }

    fn step_for(&mut self, g: &mut GenState) -> Step {
        let (test, update, body, started) = match g.frames.last() {
            Some(Frame::For {
                test,
                update,
                body,
                started,
            }) => (
                test.clone(),
                update.clone(),
                Rc::clone(body),
                *started,
            ),
            _ => return Step::Fatal("gen: for frame vanished".into()),
        };
        if started {
            if let Some(u) = &update {
                if let Err(a) = self.eval_expr_public(u, &g.ctx) {
                    return self.abrupt_to_step(g, a);
                }
            }
        }
        if let Some(Frame::For { started, .. }) = g.frames.last_mut() {
            *started = true;
        }
        let go = match &test {
            Some(t) => match self.eval_expr_public(t, &g.ctx) {
                Ok(v) => self.to_boolean(&v),
                Err(a) => return self.abrupt_to_step(g, a),
            },
            None => true,
        };
        if go {
            self.enter_stmt(g, &body)
        } else {
            g.frames.pop();
            Step::Continue
        }
    }

    // -- abrupt completion dispatch (break/continue/return/throw) -----------

    fn abrupt_to_step(&mut self, g: &mut GenState, a: Abrupt) -> Step {
        match a {
            Abrupt::Return(v) => self.dispatch(g, Prop2::Return(v)),
            Abrupt::Throw(v) => self.dispatch(g, Prop2::Throw(v)),
            Abrupt::Break(_) => self.dispatch(g, Prop2::Break),
            Abrupt::Continue(_) => self.dispatch(g, Prop2::Continue),
            Abrupt::Fatal(s) => Step::Fatal(s),
        }
    }

    /// Unwind the frame stack to handle an abrupt completion, running finally
    /// blocks and honoring catch/loop handlers.
    fn dispatch(&mut self, g: &mut GenState, comp: Prop2) -> Step {
        loop {
            let Some(top) = g.frames.last() else {
                // Escaped the generator body.
                return match comp {
                    Prop2::Return(v) => Step::Return(v),
                    Prop2::Throw(e) => Step::Throw(e),
                    Prop2::Break | Prop2::Continue => {
                        Step::Fatal("gen: break/continue escaped the generator body".into())
                    }
                };
            };
            match top {
                Frame::RestoreEnv(env) => {
                    g.ctx.env = *env;
                    g.frames.pop();
                }
                Frame::Seq { .. } | Frame::PostYield(_) => {
                    g.frames.pop();
                }
                Frame::YieldStar { .. } => {
                    // Defensive: a yield* frame is normally a leaf handled by
                    // its own step. If an abrupt completion unwinds through it,
                    // close its iterator and keep unwinding.
                    if let Some(Frame::YieldStar { iter, .. }) = g.frames.last_mut() {
                        let mut it =
                            std::mem::replace(iter, SliceIter::Str(Rc::new(Vec::new()), 0));
                        g.frames.pop();
                        if let Err(a) = self.slice_iterator_close(&mut it) {
                            return self.abrupt_to_step(g, a);
                        }
                    }
                }
                Frame::While { .. } | Frame::DoWhile { .. } | Frame::For { .. } => {
                    match comp {
                        Prop2::Break => {
                            g.frames.pop();
                            return Step::Continue;
                        }
                        Prop2::Continue => {
                            // Keep the loop frame; the loop advances next step.
                            return Step::Continue;
                        }
                        _ => {
                            g.frames.pop();
                        }
                    }
                }
                Frame::ForOf { .. } => match comp {
                    Prop2::Break => {
                        // IteratorClose on early exit.
                        if let Some(Frame::ForOf { iter, .. }) = g.frames.last_mut() {
                            let mut it = std::mem::replace(iter, SliceIter::Str(Rc::new(Vec::new()), 0));
                            g.frames.pop();
                            if let Err(a) = self.slice_iterator_close(&mut it) {
                                return self.abrupt_to_step(g, a);
                            }
                        }
                        return Step::Continue;
                    }
                    Prop2::Continue => return Step::Continue,
                    _ => {
                        // return/throw: close the iterator, then keep unwinding.
                        if let Some(Frame::ForOf { iter, .. }) = g.frames.last_mut() {
                            let mut it = std::mem::replace(iter, SliceIter::Str(Rc::new(Vec::new()), 0));
                            g.frames.pop();
                            if let Err(a) = self.slice_iterator_close(&mut it) {
                                return self.abrupt_to_step(g, a);
                            }
                        }
                    }
                },
                Frame::TryCatch { .. } => {
                    // A catch handles a throw once; other completions pass.
                    if let Prop2::Throw(e) = &comp {
                        let e = e.clone();
                        let (param, body) = match g.frames.pop() {
                            Some(Frame::TryCatch { param, body }) => (param, body),
                            _ => return Step::Fatal("gen: try-catch frame vanished".into()),
                        };
                        return self.enter_catch(g, param.as_ref(), body, e);
                    }
                    g.frames.pop();
                }
                Frame::TryFinally { body } => {
                    let body = Rc::clone(body);
                    g.frames.pop();
                    return self.enter_finally(g, body, Some(comp));
                }
                Frame::RunFinally { .. } => {
                    // An abrupt completion inside a finally overrides the saved
                    // one: drop the saved completion and keep unwinding with
                    // the new one.
                    g.frames.pop();
                }
            }
        }
    }

    fn enter_catch(
        &mut self,
        g: &mut GenState,
        param: Option<&BindTarget>,
        body: Rc<Vec<Stmt>>,
        exc: Value,
    ) -> Step {
        let parent = g.ctx.env;
        let env = self.alloc_env(Some(parent));
        g.ctx.env = env;
        match param {
            None => {}
            Some(BindTarget::Name(p)) => {
                self.envs[env.0 as usize]
                    .bindings
                    .insert(p.clone(), crate::value::Binding::var(exc));
            }
            Some(BindTarget::Pattern(_)) => {
                return Step::Fatal("gen: destructuring catch parameter with yield (out of slice)".into());
            }
        }
        if let Err(a) = self.declare_lexical_public(env, &body) {
            return self.abrupt_to_step(g, a);
        }
        g.frames.push(Frame::RestoreEnv(parent));
        g.frames.push(Frame::Seq { stmts: body, idx: 0 });
        Step::Continue
    }

    fn enter_finally(
        &mut self,
        g: &mut GenState,
        body: Rc<Vec<Stmt>>,
        saved: Option<Prop2>,
    ) -> Step {
        if body.iter().any(|s| matches!(s, Stmt::FuncDecl(_))) {
            return Step::Fatal("gen: function declaration in a finally block (out of slice)".into());
        }
        let parent = g.ctx.env;
        let env = self.alloc_env(Some(parent));
        if let Err(a) = self.declare_lexical_public(env, &body) {
            return self.abrupt_to_step(g, a);
        }
        g.ctx.env = env;
        g.frames.push(Frame::RunFinally { saved });
        g.frames.push(Frame::RestoreEnv(parent));
        g.frames.push(Frame::Seq { stmts: body, idx: 0 });
        Step::Continue
    }

    fn enter_try(
        &mut self,
        g: &mut GenState,
        block: &[Stmt],
        catch: &Option<(Option<BindTarget>, Vec<Stmt>)>,
        finally: &Option<Vec<Stmt>>,
    ) -> Step {
        // Desugar try-catch-finally as try { try B catch C } finally F, so each
        // frame guards exactly one concern.
        let block = Rc::new(block.to_vec());
        if let Some(fin) = finally {
            g.frames.push(Frame::TryFinally {
                body: Rc::new(fin.clone()),
            });
        }
        if let Some((param, cbody)) = catch {
            g.frames.push(Frame::TryCatch {
                param: param.clone(),
                body: Rc::new(cbody.clone()),
            });
        }
        // Enter the try body inside its own lexical scope.
        self.enter_block(g, block)
    }

    // -- for-of over slice iterables ---------------------------------------

    fn enter_for_of(
        &mut self,
        g: &mut GenState,
        left: &ForInOfLeft,
        expr: &Expr,
        body: &Stmt,
    ) -> Step {
        // Lexical `let`/`const` for-of heads need per-iteration scoping; a
        // simple `var`/target head is supported. The head expression must be
        // yield-free (it is evaluated once, atomically).
        if expr_has_yield(expr) {
            return Step::Fatal("gen: yield in a for-of head expression (out of slice)".into());
        }
        if matches!(left, ForInOfLeft::Lex(..)) {
            return Step::Fatal("gen: lexical for-of head with yield body (out of slice)".into());
        }
        let iterable = match self.eval_expr_public(expr, &g.ctx) {
            Ok(v) => v,
            Err(a) => return self.abrupt_to_step(g, a),
        };
        let iter = match self.slice_iterator_public(&iterable) {
            Ok(it) => it,
            Err(a) => return self.abrupt_to_step(g, a),
        };
        g.frames.push(Frame::ForOf {
            iter,
            left: left.clone(),
            body: Rc::new(body.clone()),
        });
        Step::Continue
    }

    fn step_for_of(&mut self, g: &mut GenState) -> Step {
        // Take the iterator out to step it, then put it back.
        let mut iter = match g.frames.last_mut() {
            Some(Frame::ForOf { iter, .. }) => {
                std::mem::replace(iter, SliceIter::Str(Rc::new(Vec::new()), 0))
            }
            _ => return Step::Fatal("gen: for-of frame vanished".into()),
        };
        let next = self.slice_iter_next_public(&mut iter);
        match next {
            Err(a) => {
                if let Some(Frame::ForOf { iter: slot, .. }) = g.frames.last_mut() {
                    *slot = iter;
                }
                self.abrupt_to_step(g, a)
            }
            Ok(None) => {
                g.frames.pop();
                Step::Continue
            }
            Ok(Some(el)) => {
                let (left, body) = match g.frames.last_mut() {
                    Some(Frame::ForOf {
                        iter: slot,
                        left,
                        body,
                    }) => {
                        *slot = iter;
                        (left.clone(), Rc::clone(body))
                    }
                    _ => return Step::Fatal("gen: for-of frame vanished".into()),
                };
                // Bind the value to the (var/target) head, then enter the body.
                match self.bind_forinof_left_public(&left, el, &g.ctx) {
                    Ok(()) => self.enter_stmt(g, &body),
                    Err(a) => self.abrupt_to_step(g, a),
                }
            }
        }
    }
}
