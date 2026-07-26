// Generators (§27.5) as a bounded, same-thread, small-step state machine over
// an explicit heap frame stack. The tier-0 interpreter is a natively-recursive
// tree-walker that cannot suspend mid-body; this module runs a generator's
// control-flow skeleton (blocks, if, while/do/for, for-of, try/catch/finally,
// labelled statements) step-by-step, delegating every yield-FREE
// sub-statement/sub-expression to the existing `eval_stmt`/`eval_expr` so their
// semantics stay exactly as correct as the rest of the crate. Only the spine
// around a yield point is new. Any `yield` in a position this machine cannot
// suspend at (call arguments, operator operands, computed keys,
// multi-declarators, switch/with bodies, …) is reached wholesale and refuses
// (`Abrupt::Fatal`) — a sound NoCoverage, never a wrong trace.
//
// Author: Andrew Yates
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

use crate::destr::FastIter;
use crate::expr::JsRef;
use crate::host::{AsyncExec, AsyncId, JobFn};
use crate::interp::{Abrupt, Compl, Ctx, ERes, Interp};
use std::rc::Rc;
use trust_js_parse::ast::{DeclKind, Expr, ForHead, ForInit, ObjProp, Pat, PropKey as AstKey, Stmt};
use trust_js_value::{JsObject, JsValue, ObjKind, ObjId, PropKey, Property};

/// Cap on the generator frame-stack depth (heap-allocated, so this is a
/// resource bound, not a Rust-stack bound).
const MAX_GEN_STACK: usize = 20_000;

/// [[GeneratorState]].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum GenState {
    SuspendedStart,
    SuspendedYield,
    Executing,
    Completed,
}

/// The suspension flavour a resumable body uses: a generator suspends at
/// `yield`/`yield*`; an async function at `await`. The two never coexist in one
/// body in this slice (async generators refuse), so one mode drives a whole
/// resumption. The control-flow frames (Seq/While/For/Try/…) are shared; only
/// the suspension point (`YieldPoint`/`YieldStar` vs `AwaitPoint`) differs, and
/// the scanners key on this mode so a body is stepped only where the machine
/// can actually suspend.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum SuspendKind {
    Yield,
    Await,
    /// An async generator body (§27.6): suspends at BOTH `yield` and `await`.
    /// The driver distinguishes the two via distinct `Step`/`DriveResult`
    /// variants (`YieldComplete` vs `Awaited`). Per AsyncGeneratorYield, a
    /// `yield e` first `Await`s `e`, then completes the pending request's step.
    AsyncGen,
}

impl SuspendKind {
    /// Is `yield` a suspension point in this mode?
    fn yields(self) -> bool {
        matches!(self, SuspendKind::Yield | SuspendKind::AsyncGen)
    }
    /// Is `await` a suspension point in this mode?
    fn awaits(self) -> bool {
        matches!(self, SuspendKind::Await | SuspendKind::AsyncGen)
    }
}

/// The abrupt completion injected at a suspended yield point by a resume.
#[derive(Clone)]
pub(crate) enum ResumeInput {
    Next(JsValue),
    Throw(JsValue),
    Return(JsValue),
}

/// Persisted generator / async execution state (lives in `Interp::gen_state`
/// for generators, `Interp::async_execs` for async functions).
pub(crate) struct GenExec {
    pub(crate) state: GenState,
    pub(crate) stack: Vec<GenFrame>,
    pub(crate) kind: SuspendKind,
}

/// [[AsyncGeneratorState]] (§27.6).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum AsyncGenState {
    SuspendedStart,
    SuspendedYield,
    Executing,
    Completed,
}

/// An AsyncGeneratorRequest: a queued `.next`/`.return`/`.throw` completion plus
/// the capability that settles the returned promise (§27.6.3.1).
pub(crate) struct AsyncGenRequest {
    pub(crate) completion: ResumeInput,
    pub(crate) cap: trust_js_reactor::Capability,
}

/// Persisted async generator execution state (lives in `Interp::async_gen_state`
/// keyed by the AsyncGenerator instance ObjId). The frame stack drives in
/// `SuspendKind::AsyncGen` mode.
pub(crate) struct AsyncGenExec {
    pub(crate) stack: Vec<GenFrame>,
    pub(crate) state: AsyncGenState,
    pub(crate) queue: std::collections::VecDeque<AsyncGenRequest>,
}

/// The three async-generator prototype methods (§27.6.1).
pub(crate) enum AsyncGenReq {
    Next(JsValue),
    Return(JsValue),
    Throw(JsValue),
}

/// What a resume produced.
enum DriveResult {
    Yielded(JsValue),
    /// An async-function / async-generator body suspended at an `await`.
    Awaited(JsValue),
    /// An async generator body reached the completion of a `yield` (the operand
    /// has already been `Await`ed): the driver runs AsyncGeneratorCompleteStep.
    YieldComplete(JsValue),
    Returned(JsValue),
    Threw(JsValue),
    Refuse(String),
}

/// The value delivered to a frame's `step`.
enum Feed {
    Start,
    Resume(ResumeInput),
    Child(Compl),
}

/// What a frame's `step` returns to the driver.
enum Step {
    /// Suspend the whole machine, yielding this value (a generator `yield`, or a
    /// pure-async `await` re-used as the suspension mechanism).
    Yield(JsValue),
    /// Suspend at an `await` (async / async-generator bodies): the driver does
    /// PromiseResolve + schedules the resumption reactions.
    Await(JsValue),
    /// An async generator `yield` whose operand has been `Await`ed: the driver
    /// runs AsyncGeneratorCompleteStep on this value, then resumes or suspends.
    YieldComplete(JsValue),
    /// This frame completed; pop it and deliver the completion to the parent.
    Done(Compl),
    /// Retain this frame; push these children (bottom-to-top) and start the top.
    Push(Vec<GenFrame>),
}

/// The pending assignment target of a spine `x = yield …` continuation.
pub(crate) enum AssignTarget {
    Ident(String),
    Ref(JsRef),
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) enum TryPhase {
    Start,
    Block,
    Catch,
    Finally,
}

/// One resumable control node.
pub(crate) enum GenFrame {
    /// A statement list executed sequentially in `ctx`.
    Seq {
        stmts: Rc<Vec<Stmt>>,
        idx: usize,
        ctx: Ctx,
    },
    /// A `yield <arg>` point: eval the operand on Start, suspend, resume→value.
    YieldPoint {
        arg: Option<Rc<Expr>>,
        ctx: Ctx,
    },
    /// A `yield* <arg>` delegation.
    YieldStar {
        arg: Rc<Expr>,
        ctx: Ctx,
        it: Option<FastIter>,
    },
    /// An `await <arg>` point: eval the operand on Start, suspend (the async
    /// driver does PromiseResolve + reaction scheduling), resume→resolved value
    /// (or a throw at the await point on rejection).
    AwaitPoint {
        arg: Rc<Expr>,
        ctx: Ctx,
    },
    /// `await <value-from-child>`: the operand was produced by a sub-spine (a
    /// nested suspend, e.g. `await await e`, or the AsyncGeneratorYield await of
    /// a suspendable yield operand). On the child value, suspend at an `await`;
    /// resume→resolved value.
    AwaitFromChild,
    /// An async generator `yield`'s completion point: the operand has already
    /// been `Await`ed (by an `AwaitPoint`/`AwaitFromChild` child). On the child
    /// value, signal `YieldComplete` (the driver runs AsyncGeneratorCompleteStep
    /// + resumes/suspends); resume→the resumption value.
    AsyncGenYieldComplete,
    /// Assign the produced value to a target, then pass it upward.
    AssignCont {
        target: AssignTarget,
        ctx: Ctx,
    },
    /// Initialize a single declaration binding with the produced value.
    DeclInit {
        name: String,
        kind: DeclKind,
        ctx: Ctx,
    },
    /// `return <spine>`: turn the produced value into a Return completion.
    ReturnCont,
    /// A yield-free statement, evaluated wholesale.
    Wholesale {
        stmt: Rc<Stmt>,
        ctx: Ctx,
    },
    /// Deliver a fixed completion immediately (empty if-branch, etc.).
    Immediate(Option<Compl>),
    /// while / do-while (test is yield-free; body stepped).
    While {
        test: Rc<Expr>,
        body: Rc<Stmt>,
        ctx: Ctx,
        labels: Vec<String>,
        is_do: bool,
    },
    /// C-style for. `ctx` is the (possibly per-iteration) loop environment.
    For {
        test: Option<Rc<Expr>>,
        update: Option<Rc<Expr>>,
        body: Rc<Stmt>,
        ctx: Ctx,
        labels: Vec<String>,
        per_iter: Rc<Vec<String>>,
        outer: trust_js_value::EnvId,
        started: bool,
    },
    /// for-of over `it` (the iterator captured at head evaluation).
    ForOf {
        it: FastIter,
        left: Rc<ForHead>,
        body: Rc<Stmt>,
        ctx: Ctx,
        labels: Vec<String>,
    },
    /// A labelled statement wrapper (catches `break <label>`).
    Labeled {
        label: String,
        body: Rc<Stmt>,
        ctx: Ctx,
        labels: Vec<String>,
    },
    /// try/catch/finally.
    Try {
        phase: TryPhase,
        block: Rc<Vec<Stmt>>,
        catch: Option<Rc<(Option<Pat>, Vec<Stmt>)>>,
        finally: Option<Rc<Vec<Stmt>>>,
        ctx: Ctx,
        saved: Option<Compl>,
    },
}

/// Does an unlabeled/labelled break/continue target a loop carrying `labels`?
fn label_matches(label: &Option<String>, labels: &[String]) -> bool {
    label.as_ref().is_none_or(|l| labels.contains(l))
}

impl Interp {
    // -- public entry points (native next/return/throw) ----------------------

    /// GeneratorResume for `.next(v)` / GeneratorResumeAbrupt for
    /// `.return(v)` / `.throw(e)`. Returns the iterator-result object, or an
    /// abrupt completion (Throw / Fatal refusal).
    pub(crate) fn gen_resume(&mut self, oid: ObjId, input: ResumeInput) -> ERes {
        let state = match self.gen_state.get(&oid) {
            Some(e) => e.state,
            None => return Err(self.throw_type_error()),
        };
        // Reentrancy + already-completed + suspendedStart abrupt shortcuts.
        match (state, &input) {
            (GenState::Executing, _) => return Err(self.throw_type_error()),
            (GenState::Completed, ResumeInput::Next(_)) => {
                return self.create_iter_result(JsValue::Undefined, true)
            }
            (GenState::Completed, ResumeInput::Return(v)) => {
                let v = v.clone();
                return self.create_iter_result(v, true);
            }
            (GenState::Completed, ResumeInput::Throw(e)) => return Err(Abrupt::Throw(e.clone())),
            (GenState::SuspendedStart, ResumeInput::Return(v)) => {
                let v = v.clone();
                self.gen_set_state(oid, GenState::Completed);
                return self.create_iter_result(v, true);
            }
            (GenState::SuspendedStart, ResumeInput::Throw(e)) => {
                let e = e.clone();
                self.gen_set_state(oid, GenState::Completed);
                return Err(Abrupt::Throw(e));
            }
            _ => {}
        }
        let feed = match (state, input) {
            // The first `.next(v)` discards v (spec: GeneratorStart ignores it).
            (GenState::SuspendedStart, _) => Feed::Start,
            (GenState::SuspendedYield, inp) => Feed::Resume(inp),
            _ => unreachable!("shortcut states handled above"),
        };
        // Mark executing and borrow the frame stack out for the drive.
        let entry = self.gen_state.get_mut(&oid).expect("checked");
        entry.state = GenState::Executing;
        let mode = entry.kind;
        let mut stack = std::mem::take(&mut entry.stack);
        let result = self.gen_drive(&mut stack, feed, mode);
        let entry = self.gen_state.get_mut(&oid).expect("still present");
        match result {
            DriveResult::Yielded(v) => {
                entry.state = GenState::SuspendedYield;
                entry.stack = stack;
                self.create_iter_result(v, false)
            }
            DriveResult::Returned(v) => {
                entry.state = GenState::Completed;
                self.create_iter_result(v, true)
            }
            DriveResult::Threw(v) => {
                entry.state = GenState::Completed;
                Err(Abrupt::Throw(v))
            }
            DriveResult::Refuse(s) => {
                entry.state = GenState::Completed;
                Err(Abrupt::Fatal(s))
            }
            // A plain (sync) generator body never awaits or async-yields.
            DriveResult::Awaited(_) | DriveResult::YieldComplete(_) => {
                entry.state = GenState::Completed;
                Err(Abrupt::Fatal("await in a sync generator (interpreter invariant)".to_string()))
            }
        }
    }

    fn gen_set_state(&mut self, oid: ObjId, s: GenState) {
        if let Some(e) = self.gen_state.get_mut(&oid) {
            e.state = s;
        }
    }

    /// Brand check: `this` must be a generator instance with live state.
    pub(crate) fn this_generator(&mut self, this: &JsValue) -> Result<ObjId, Abrupt> {
        if let JsValue::Obj(oid) = this {
            if matches!(self.heap.obj(*oid).kind, ObjKind::Generator)
                && self.gen_state.contains_key(oid)
            {
                return Ok(*oid);
            }
        }
        Err(self.throw_type_error())
    }

    /// CreateIterResultObject (7.4.9): ordinary object, `value` then `done`.
    pub(crate) fn create_iter_result(&mut self, value: JsValue, done: bool) -> ERes {
        let o = self.new_plain()?;
        self.heap
            .obj_mut(o)
            .props
            .insert(PropKey::from_str("value"), Property::data(value));
        self.heap
            .obj_mut(o)
            .props
            .insert(PropKey::from_str("done"), Property::data(JsValue::Bool(done)));
        Ok(JsValue::Obj(o))
    }

    /// Build a fresh generator object (suspendedStart) for a generator-function
    /// [[Call]]. FunctionDeclarationInstantiation has already run in `body_ctx`.
    pub(crate) fn make_generator(
        &mut self,
        fid: ObjId,
        body: &[Stmt],
        body_ctx: Ctx,
    ) -> ERes {
        let proto =
            self.get_prototype_from_constructor(&JsValue::Obj(fid), self.intr.generator_proto)?;
        let gobj = self.alloc_obj(JsObject::new(ObjKind::Generator, Some(proto)))?;
        let initial = GenFrame::Seq {
            stmts: Rc::new(body.to_vec()),
            idx: 0,
            ctx: body_ctx,
        };
        self.gen_state.insert(
            gobj,
            GenExec {
                state: GenState::SuspendedStart,
                stack: vec![initial],
                kind: SuspendKind::Yield,
            },
        );
        Ok(JsValue::Obj(gobj))
    }

    // -- async functions -----------------------------------------------------

    /// An async-function [[Call]]: create the result promise, seed the
    /// resumable frame stack (Await mode), run the synchronous prefix, and
    /// return the result Promise object. `expr_body` is `Some` for a concise
    /// async-arrow body (`=> expr`), desugared to `return expr;`.
    pub(crate) fn make_async(
        &mut self,
        body: &[Stmt],
        expr_body: Option<&Expr>,
        body_ctx: Ctx,
    ) -> ERes {
        let initial = if let Some(e) = expr_body {
            GenFrame::Seq {
                stmts: Rc::new(vec![Stmt::Return(Some(e.clone()))]),
                idx: 0,
                ctx: body_ctx,
            }
        } else {
            GenFrame::Seq {
                stmts: Rc::new(body.to_vec()),
                idx: 0,
                ctx: body_ctx,
            }
        };
        let (result_obj, _pid, cap) = self.new_promise_object()?;
        let id = self.async_execs.len();
        self.async_execs.push(Some(AsyncExec {
            machine: GenExec {
                state: GenState::SuspendedStart,
                stack: vec![initial],
                kind: SuspendKind::Await,
            },
            cap,
        }));
        // AsyncFunctionStart: run the body synchronously up to the first await.
        self.async_drive(id, Feed::Start)?;
        Ok(JsValue::Obj(result_obj))
    }

    /// EvaluateAsyncFunctionBody step 3: an abrupt FunctionDeclarationInstantiation
    /// rejects a fresh result promise with `reason` (the async function returns
    /// that already-rejected promise instead of throwing). No body machine is
    /// created — the body never runs.
    pub(crate) fn async_reject(&mut self, reason: JsValue) -> ERes {
        let (result_obj, _pid, cap) = self.new_promise_object()?;
        self.rx_op(|it, rx| rx.reject(it, &cap, reason));
        Ok(JsValue::Obj(result_obj))
    }

    /// Resume a suspended async execution with the awaited promise's outcome.
    pub(crate) fn async_resume(&mut self, id: AsyncId, input: ResumeInput) -> Result<(), Abrupt> {
        self.async_drive(id, Feed::Resume(input))
    }

    /// Drive one async step: run the frame machine, then either suspend at the
    /// next `await` (scheduling its resumption reactions), settle the result
    /// promise, or refuse (an out-of-slice position mid-body).
    fn async_drive(&mut self, id: AsyncId, feed: Feed) -> Result<(), Abrupt> {
        {
            let Some(Some(exec)) = self.async_execs.get_mut(id) else {
                return Err(Abrupt::Fatal("async execution vanished".to_string()));
            };
            if exec.machine.state == GenState::Executing {
                return Err(Abrupt::Fatal("reentrant async resume".to_string()));
            }
            exec.machine.state = GenState::Executing;
        }
        let mut stack = {
            let exec = self.async_execs[id].as_mut().expect("async exec present");
            std::mem::take(&mut exec.machine.stack)
        };
        let result = self.gen_drive(&mut stack, feed, SuspendKind::Await);
        match result {
            DriveResult::Awaited(awaited) => {
                {
                    let exec = self.async_execs[id].as_mut().expect("async exec present");
                    exec.machine.state = GenState::SuspendedYield;
                    exec.machine.stack = stack;
                }
                // await v == PromiseResolve(v).then(<resume next>, <resume throw>).
                self.rx_op(|it, rx| {
                    let p = rx.promise_resolve(it, awaited);
                    let _dep = rx.then(it, p, Some(JobFn::AsyncNext(id)), Some(JobFn::AsyncThrow(id)));
                });
                Ok(())
            }
            // A plain async function body never `yield`s.
            DriveResult::Yielded(_) | DriveResult::YieldComplete(_) => {
                let exec = self.async_execs[id].as_mut().expect("async exec present");
                exec.machine.state = GenState::Completed;
                Err(Abrupt::Fatal("yield in an async function (interpreter invariant)".to_string()))
            }
            DriveResult::Returned(v) => {
                let cap = {
                    let exec = self.async_execs[id].as_mut().expect("async exec present");
                    exec.machine.state = GenState::Completed;
                    exec.cap.clone()
                };
                self.rx_op(|it, rx| rx.resolve(it, &cap, v));
                Ok(())
            }
            DriveResult::Threw(e) => {
                let cap = {
                    let exec = self.async_execs[id].as_mut().expect("async exec present");
                    exec.machine.state = GenState::Completed;
                    exec.cap.clone()
                };
                self.rx_op(|it, rx| rx.reject(it, &cap, e));
                Ok(())
            }
            DriveResult::Refuse(s) => {
                let exec = self.async_execs[id].as_mut().expect("async exec present");
                exec.machine.state = GenState::Completed;
                Err(Abrupt::Fatal(s))
            }
        }
    }

    // -- async generators (§27.6) --------------------------------------------

    /// An async-generator-function [[Call]]: create the AsyncGenerator object
    /// (suspendedStart, empty queue). FunctionDeclarationInstantiation has
    /// already run in `body_ctx`; the body runs on the first `.next()`.
    pub(crate) fn make_async_generator(
        &mut self,
        fid: ObjId,
        body: &[Stmt],
        body_ctx: Ctx,
    ) -> ERes {
        let proto = self.get_prototype_from_constructor(
            &JsValue::Obj(fid),
            self.intr.async_generator_proto,
        )?;
        let gobj = self.alloc_obj(JsObject::new(ObjKind::AsyncGenerator, Some(proto)))?;
        let initial = GenFrame::Seq {
            stmts: Rc::new(body.to_vec()),
            idx: 0,
            ctx: body_ctx,
        };
        self.async_gen_state.insert(
            gobj,
            AsyncGenExec {
                stack: vec![initial],
                state: AsyncGenState::SuspendedStart,
                queue: std::collections::VecDeque::new(),
            },
        );
        Ok(JsValue::Obj(gobj))
    }

    /// %AsyncGeneratorPrototype%.next / .return / .throw — returns a Promise
    /// (§27.6.1.2 / .3 / .4). `.return()` refuses (its AwaitReturn / yield-
    /// resumption-unwrap interleaving is out of slice).
    pub(crate) fn async_gen_method(&mut self, this: &JsValue, req: AsyncGenReq) -> ERes {
        // `.return()` — refuse before any observable side effect (sound).
        if matches!(req, AsyncGenReq::Return(_)) {
            return Err(Abrupt::Fatal(
                "async generator .return() (out of slice)".to_string(),
            ));
        }
        // NewPromiseCapability(%Promise%).
        let (pobj, _pid, cap) = self.new_promise_object()?;
        // AsyncGeneratorValidate → IfAbruptRejectPromise: a non-async-generator
        // receiver rejects the returned promise with a TypeError.
        let oid = match this {
            JsValue::Obj(o)
                if matches!(self.heap.obj(*o).kind, ObjKind::AsyncGenerator)
                    && self.async_gen_state.contains_key(o) =>
            {
                *o
            }
            _ => {
                let te = self.make_native_error(trust_js_value::ErrKind::Type, false)?;
                self.rx_op(|it, rx| rx.reject(it, &cap, JsValue::Obj(te)));
                return Ok(JsValue::Obj(pobj));
            }
        };
        match req {
            AsyncGenReq::Next(v) => {
                let state = self.async_gen_state[&oid].state;
                if state == AsyncGenState::Completed {
                    let ir = self.create_iter_result(JsValue::Undefined, true)?;
                    self.rx_op(|it, rx| rx.resolve(it, &cap, ir));
                    return Ok(JsValue::Obj(pobj));
                }
                self.async_gen_enqueue(oid, ResumeInput::Next(v), cap);
                if matches!(
                    state,
                    AsyncGenState::SuspendedStart | AsyncGenState::SuspendedYield
                ) {
                    self.async_gen_resume(oid)?;
                }
                Ok(JsValue::Obj(pobj))
            }
            AsyncGenReq::Throw(e) => {
                let mut state = self.async_gen_state[&oid].state;
                if state == AsyncGenState::SuspendedStart {
                    self.async_gen_state.get_mut(&oid).expect("present").state =
                        AsyncGenState::Completed;
                    state = AsyncGenState::Completed;
                }
                if state == AsyncGenState::Completed {
                    self.rx_op(|it, rx| rx.reject(it, &cap, e));
                    return Ok(JsValue::Obj(pobj));
                }
                self.async_gen_enqueue(oid, ResumeInput::Throw(e), cap);
                if state == AsyncGenState::SuspendedYield {
                    self.async_gen_resume(oid)?;
                }
                Ok(JsValue::Obj(pobj))
            }
            AsyncGenReq::Return(_) => unreachable!("handled above"),
        }
    }

    fn async_gen_enqueue(
        &mut self,
        oid: ObjId,
        completion: ResumeInput,
        cap: trust_js_reactor::Capability,
    ) {
        self.async_gen_state
            .get_mut(&oid)
            .expect("present")
            .queue
            .push_back(AsyncGenRequest { completion, cap });
    }

    /// AsyncGeneratorResume: drive from suspendedStart/suspendedYield using the
    /// front request's completion (the first resume from suspendedStart discards
    /// the value, per GeneratorStart).
    fn async_gen_resume(&mut self, oid: ObjId) -> Result<(), Abrupt> {
        let feed = {
            let exec = self.async_gen_state.get_mut(&oid).expect("present");
            let start = exec.state == AsyncGenState::SuspendedStart;
            if start {
                Feed::Start
            } else {
                let front = exec.queue.front().expect("resume with a queued request");
                Feed::Resume(front.completion.clone())
            }
        };
        self.async_gen_drive(oid, feed)
    }

    /// Resume the machine after an internal `await` inside the body (the async
    /// generator state stays `executing` across an await).
    pub(crate) fn async_gen_await_resume(
        &mut self,
        oid: ObjId,
        input: ResumeInput,
    ) -> Result<(), Abrupt> {
        // A refusal may have completed and removed the exec; ignore stale resumes.
        if !self.async_gen_state.contains_key(&oid) {
            return Ok(());
        }
        self.async_gen_drive(oid, Feed::Resume(input))
    }

    /// Drive the async generator machine one span: run to the next `await`
    /// (schedule a reactor resumption), `yield` completion (CompleteStep then
    /// continue/suspend), or body completion (CompleteStep + DrainQueue).
    fn async_gen_drive(&mut self, oid: ObjId, mut feed: Feed) -> Result<(), Abrupt> {
        let mut stack = {
            let exec = self.async_gen_state.get_mut(&oid).expect("present");
            exec.state = AsyncGenState::Executing;
            std::mem::take(&mut exec.stack)
        };
        loop {
            let result = self.gen_drive(&mut stack, feed, SuspendKind::AsyncGen);
            match result {
                // An `await` inside the body: state stays executing.
                DriveResult::Awaited(v) => {
                    self.async_gen_state.get_mut(&oid).expect("present").stack = stack;
                    self.rx_op(|it, rx| {
                        let p = rx.promise_resolve(it, v);
                        let _dep = rx.then(
                            it,
                            p,
                            Some(JobFn::AsyncGenAwaitNext(oid)),
                            Some(JobFn::AsyncGenAwaitThrow(oid)),
                        );
                    });
                    return Ok(());
                }
                // A `yield` (operand already awaited): AsyncGeneratorCompleteStep,
                // then continue with the next queued request or suspend.
                DriveResult::YieldComplete(v) => {
                    self.async_gen_complete_step(oid, Ok(v), false)?;
                    let next = {
                        let exec = self.async_gen_state.get_mut(&oid).expect("present");
                        match exec.queue.front() {
                            None => {
                                exec.state = AsyncGenState::SuspendedYield;
                                exec.stack = std::mem::take(&mut stack);
                                None
                            }
                            Some(req) => match req.completion.clone() {
                                ResumeInput::Next(v2) => Some(Ok(ResumeInput::Next(v2))),
                                ResumeInput::Throw(e2) => Some(Ok(ResumeInput::Throw(e2))),
                                // A queued `.return()` needs the yield-resumption
                                // unwrap (Await) — refuse (sound NoCoverage).
                                ResumeInput::Return(_) => Some(Err(())),
                            },
                        }
                    };
                    match next {
                        None => return Ok(()),
                        Some(Ok(input)) => {
                            feed = Feed::Resume(input);
                            // continue driving without suspending
                        }
                        Some(Err(())) => {
                            self.async_gen_state.get_mut(&oid).expect("present").stack = stack;
                            return Err(Abrupt::Fatal(
                                "async generator return-resumption at a yield (out of slice)"
                                    .to_string(),
                            ));
                        }
                    }
                }
                // Body completed normally / via return: state=completed,
                // CompleteStep(Ok(v), true) for the front request, then DrainQueue.
                DriveResult::Returned(v) => {
                    {
                        let exec = self.async_gen_state.get_mut(&oid).expect("present");
                        exec.state = AsyncGenState::Completed;
                        exec.stack = std::mem::take(&mut stack);
                    }
                    self.async_gen_complete_step(oid, Ok(v), true)?;
                    return self.async_gen_drain_queue(oid);
                }
                // Body threw: state=completed, CompleteStep(Err(e), true) for the
                // front request (reject), then DrainQueue.
                DriveResult::Threw(e) => {
                    {
                        let exec = self.async_gen_state.get_mut(&oid).expect("present");
                        exec.state = AsyncGenState::Completed;
                        exec.stack = std::mem::take(&mut stack);
                    }
                    self.async_gen_complete_step(oid, Err(e), true)?;
                    return self.async_gen_drain_queue(oid);
                }
                DriveResult::Yielded(_) => {
                    self.async_gen_state.get_mut(&oid).expect("present").state =
                        AsyncGenState::Completed;
                    return Err(Abrupt::Fatal(
                        "raw yield in an async generator (interpreter invariant)".to_string(),
                    ));
                }
                DriveResult::Refuse(s) => {
                    self.async_gen_state.get_mut(&oid).expect("present").state =
                        AsyncGenState::Completed;
                    return Err(Abrupt::Fatal(s));
                }
            }
        }
    }

    /// AsyncGeneratorCompleteStep (§27.6.3.6): dequeue the front request and
    /// settle its promise. `completion` = Ok(value) → resolve {value, done};
    /// Err(reason) → reject.
    fn async_gen_complete_step(
        &mut self,
        oid: ObjId,
        completion: Result<JsValue, JsValue>,
        done: bool,
    ) -> Result<(), Abrupt> {
        let req = self
            .async_gen_state
            .get_mut(&oid)
            .expect("present")
            .queue
            .pop_front();
        let Some(req) = req else {
            return Ok(());
        };
        let cap = req.cap;
        match completion {
            Ok(v) => {
                let ir = self.create_iter_result(v, done)?;
                self.rx_op(|it, rx| rx.resolve(it, &cap, ir));
            }
            Err(e) => {
                self.rx_op(|it, rx| rx.reject(it, &cap, e));
            }
        }
        Ok(())
    }

    /// AsyncGeneratorDrainQueue (§27.6.3.9): after completion, settle every
    /// remaining request — a `.next()` resolves {undefined, true}, a `.throw()`
    /// rejects with its reason, a `.return()` refuses (AwaitReturn out of slice).
    fn async_gen_drain_queue(&mut self, oid: ObjId) -> Result<(), Abrupt> {
        loop {
            let front = self
                .async_gen_state
                .get(&oid)
                .and_then(|e| e.queue.front().map(|r| r.completion.clone()));
            let Some(completion) = front else {
                return Ok(());
            };
            match completion {
                ResumeInput::Next(_) => {
                    self.async_gen_complete_step(oid, Ok(JsValue::Undefined), true)?;
                }
                ResumeInput::Throw(e) => {
                    self.async_gen_complete_step(oid, Err(e), true)?;
                }
                ResumeInput::Return(_) => {
                    return Err(Abrupt::Fatal(
                        "async generator .return() drain (out of slice)".to_string(),
                    ));
                }
            }
        }
    }

    // -- the driver ----------------------------------------------------------

    fn gen_drive(
        &mut self,
        stack: &mut Vec<GenFrame>,
        initial: Feed,
        mode: SuspendKind,
    ) -> DriveResult {
        let mut feed = initial;
        loop {
            let Some(mut frame) = stack.pop() else {
                // Stack empty: `feed` carries the outermost completion.
                return match feed {
                    Feed::Child(Ok(_)) => DriveResult::Returned(JsValue::Undefined),
                    Feed::Child(Err(Abrupt::Return(v))) => DriveResult::Returned(v),
                    Feed::Child(Err(Abrupt::Throw(v))) => DriveResult::Threw(v),
                    Feed::Child(Err(Abrupt::Fatal(s))) => DriveResult::Refuse(s),
                    Feed::Child(Err(_)) => {
                        DriveResult::Refuse("break/continue escaped generator body".to_string())
                    }
                    _ => DriveResult::Refuse("generator driver invariant".to_string()),
                };
            };
            match self.gen_frame_step(&mut frame, feed, mode) {
                Step::Yield(v) => {
                    stack.push(frame);
                    return DriveResult::Yielded(v);
                }
                Step::Await(v) => {
                    stack.push(frame);
                    return DriveResult::Awaited(v);
                }
                Step::YieldComplete(v) => {
                    stack.push(frame);
                    return DriveResult::YieldComplete(v);
                }
                Step::Done(compl) => {
                    feed = Feed::Child(compl);
                }
                Step::Push(children) => {
                    if stack.len() + children.len() + 1 > MAX_GEN_STACK {
                        return DriveResult::Refuse("generator frame-stack cap exceeded".to_string());
                    }
                    stack.push(frame);
                    stack.extend(children);
                    feed = Feed::Start;
                }
            }
        }
    }

    // -- per-frame stepping --------------------------------------------------

    #[allow(clippy::too_many_lines)]
    fn gen_frame_step(&mut self, frame: &mut GenFrame, feed: Feed, mode: SuspendKind) -> Step {
        match frame {
            GenFrame::Seq { stmts, idx, ctx } => {
                // A child just completed abruptly → propagate; normal → continue.
                if let Feed::Child(Err(a)) = feed {
                    return Step::Done(Err(a));
                }
                // (Feed::Start or Feed::Child(Ok(_))): run wholesale statements
                // until a suspension-bearing one or the end.
                let ctx = ctx.clone();
                while *idx < stmts.len() {
                    let s = &stmts[*idx];
                    *idx += 1;
                    if stmt_has_suspend(s, mode) {
                        return match self.step_into_stmt(s, &ctx, &[], mode) {
                            Ok(frames) => Step::Push(frames),
                            Err(a) => Step::Done(Err(a)),
                        };
                    }
                    if let Err(a) = self.eval_stmt(s, &ctx) {
                        return Step::Done(Err(a));
                    }
                }
                Step::Done(Ok(None))
            }

            GenFrame::YieldPoint { arg, ctx } => match feed {
                Feed::Start => {
                    let y = match arg {
                        Some(e) => match self.eval_expr(e, ctx) {
                            Ok(v) => v,
                            Err(a) => return Step::Done(Err(a)),
                        },
                        None => JsValue::Undefined,
                    };
                    Step::Yield(y)
                }
                Feed::Resume(ResumeInput::Next(v)) => Step::Done(Ok(Some(v))),
                Feed::Resume(ResumeInput::Throw(e)) => Step::Done(Err(Abrupt::Throw(e))),
                Feed::Resume(ResumeInput::Return(r)) => Step::Done(Err(Abrupt::Return(r))),
                Feed::Child(_) => {
                    Step::Done(Err(Abrupt::Fatal("child delivered to yield point".to_string())))
                }
            },

            GenFrame::YieldStar { arg, ctx, it } => {
                let r = self.yieldstar_step(arg, ctx, it, feed);
                match r {
                    Ok(s) => s,
                    Err(a) => Step::Done(Err(a)),
                }
            }

            GenFrame::AwaitPoint { arg, ctx } => match feed {
                // Evaluate the operand, then suspend: the async driver does
                // PromiseResolve(operand) and schedules the resumption reactions.
                Feed::Start => match self.eval_expr(arg, ctx) {
                    Ok(v) => Step::Await(v),
                    Err(a) => Step::Done(Err(a)),
                },
                // Resumed with the awaited promise's outcome.
                Feed::Resume(ResumeInput::Next(v)) => Step::Done(Ok(Some(v))),
                Feed::Resume(ResumeInput::Throw(e)) => Step::Done(Err(Abrupt::Throw(e))),
                Feed::Resume(ResumeInput::Return(r)) => Step::Done(Err(Abrupt::Return(r))),
                Feed::Child(_) => {
                    Step::Done(Err(Abrupt::Fatal("child delivered to await point".to_string())))
                }
            },

            // `await <value-from-child>`: first entry delivers the operand value
            // as a child completion → suspend at await; resumption delivers the
            // resolved value / rejection.
            GenFrame::AwaitFromChild => match feed {
                Feed::Child(Ok(v)) => Step::Await(v.unwrap_or(JsValue::Undefined)),
                Feed::Child(Err(a)) => Step::Done(Err(a)),
                Feed::Resume(ResumeInput::Next(v)) => Step::Done(Ok(Some(v))),
                Feed::Resume(ResumeInput::Throw(e)) => Step::Done(Err(Abrupt::Throw(e))),
                Feed::Resume(ResumeInput::Return(r)) => Step::Done(Err(Abrupt::Return(r))),
                Feed::Start => {
                    Step::Done(Err(Abrupt::Fatal("await-from-child started".to_string())))
                }
            },

            // Async generator yield completion: first entry (child) carries the
            // already-awaited operand value → YieldComplete; the driver runs
            // AsyncGeneratorCompleteStep. Resumption delivers the yield result.
            GenFrame::AsyncGenYieldComplete => match feed {
                Feed::Child(Ok(v)) => Step::YieldComplete(v.unwrap_or(JsValue::Undefined)),
                Feed::Child(Err(a)) => Step::Done(Err(a)),
                Feed::Resume(ResumeInput::Next(v)) => Step::Done(Ok(Some(v))),
                Feed::Resume(ResumeInput::Throw(e)) => Step::Done(Err(Abrupt::Throw(e))),
                // A `return` resumption at a yield requires AsyncGeneratorUnwrap-
                // YieldResumption (an Await of the return value) — refuse (sound).
                Feed::Resume(ResumeInput::Return(_)) => Step::Done(Err(Abrupt::Fatal(
                    "async generator return-resumption at a yield (out of slice)".to_string(),
                ))),
                Feed::Start => {
                    Step::Done(Err(Abrupt::Fatal("yield-complete started".to_string())))
                }
            },

            GenFrame::AssignCont { target, ctx } => match feed {
                Feed::Child(Ok(Some(v))) => {
                    let r = match target {
                        AssignTarget::Ident(name) => self.env_set(ctx, name, v.clone()),
                        AssignTarget::Ref(rf) => self.ref_set(rf, v.clone(), ctx),
                    };
                    match r {
                        Ok(()) => Step::Done(Ok(Some(v))),
                        Err(a) => Step::Done(Err(a)),
                    }
                }
                Feed::Child(Err(a)) => Step::Done(Err(a)),
                _ => Step::Done(Ok(None)),
            },

            GenFrame::DeclInit { name, kind, ctx } => match feed {
                Feed::Child(Ok(Some(v))) => {
                    let r = match kind {
                        DeclKind::Var => self.env_set(ctx, name, v),
                        DeclKind::Let | DeclKind::Const => {
                            self.initialize_binding(ctx.env, name, v)
                        }
                        DeclKind::Using | DeclKind::AwaitUsing => Err(Abrupt::Fatal(
                            "using declaration with yield (out of slice)".to_string(),
                        )),
                    };
                    match r {
                        Ok(()) => Step::Done(Ok(None)),
                        Err(a) => Step::Done(Err(a)),
                    }
                }
                Feed::Child(Err(a)) => Step::Done(Err(a)),
                _ => Step::Done(Ok(None)),
            },

            GenFrame::ReturnCont => match feed {
                Feed::Child(Ok(Some(v))) => Step::Done(Err(Abrupt::Return(v))),
                Feed::Child(Err(a)) => Step::Done(Err(a)),
                _ => Step::Done(Ok(None)),
            },

            GenFrame::Wholesale { stmt, ctx } => Step::Done(self.eval_stmt(stmt, ctx)),

            GenFrame::Immediate(c) => Step::Done(c.take().unwrap_or(Ok(None))),

            GenFrame::While {
                test,
                body,
                ctx,
                labels,
                is_do,
            } => {
                // Decide whether to (re)run the body this round.
                let proceed = match feed {
                    Feed::Start => {
                        if *is_do {
                            // do-while runs the body before the first test.
                            if let Err(a) = self.charge_loop() {
                                return Step::Done(Err(a));
                            }
                            return push_body(self, body, ctx, mode);
                        }
                        true
                    }
                    Feed::Child(Ok(_)) => true,
                    Feed::Child(Err(Abrupt::Continue { label, .. })) => {
                        if label_matches(&label, labels) {
                            true
                        } else {
                            return Step::Done(Err(Abrupt::Continue { label, value: None }));
                        }
                    }
                    Feed::Child(Err(Abrupt::Break { label, .. })) => {
                        if label_matches(&label, labels) {
                            return Step::Done(Ok(None));
                        }
                        return Step::Done(Err(Abrupt::Break { label, value: None }));
                    }
                    Feed::Child(Err(a)) => return Step::Done(Err(a)),
                    Feed::Resume(_) => {
                        return Step::Done(Err(Abrupt::Fatal("resume to while".to_string())))
                    }
                };
                if !proceed {
                    return Step::Done(Ok(None));
                }
                let t = match self.eval_expr(test, ctx) {
                    Ok(v) => v,
                    Err(a) => return Step::Done(Err(a)),
                };
                if !self.to_boolean(&t) {
                    return Step::Done(Ok(None));
                }
                if let Err(a) = self.charge_loop() {
                    return Step::Done(Err(a));
                }
                push_body(self, body, ctx, mode)
            }

            GenFrame::For {
                test,
                update,
                body,
                ctx,
                labels,
                per_iter,
                outer,
                started,
            } => {
                // React to the previous body completion.
                match feed {
                    Feed::Start => {}
                    Feed::Child(Ok(_)) => {}
                    Feed::Child(Err(Abrupt::Continue { label, .. })) => {
                        if !label_matches(&label, labels) {
                            return Step::Done(Err(Abrupt::Continue { label, value: None }));
                        }
                    }
                    Feed::Child(Err(Abrupt::Break { label, .. })) => {
                        if label_matches(&label, labels) {
                            return Step::Done(Ok(None));
                        }
                        return Step::Done(Err(Abrupt::Break { label, value: None }));
                    }
                    Feed::Child(Err(a)) => return Step::Done(Err(a)),
                    Feed::Resume(_) => {
                        return Step::Done(Err(Abrupt::Fatal("resume to for".to_string())))
                    }
                }
                // After the first iteration: fresh per-iteration env, then update.
                if *started {
                    if !per_iter.is_empty() {
                        match self.copy_per_iteration_env(ctx, per_iter, *outer) {
                            Ok(c) => *ctx = c,
                            Err(a) => return Step::Done(Err(a)),
                        }
                    }
                    if let Some(u) = update {
                        if let Err(a) = self.eval_expr(u, ctx) {
                            return Step::Done(Err(a));
                        }
                    }
                }
                *started = true;
                if let Some(t) = test {
                    let tv = match self.eval_expr(t, ctx) {
                        Ok(v) => v,
                        Err(a) => return Step::Done(Err(a)),
                    };
                    if !self.to_boolean(&tv) {
                        return Step::Done(Ok(None));
                    }
                }
                if let Err(a) = self.charge_loop() {
                    return Step::Done(Err(a));
                }
                push_body(self, body, ctx, mode)
            }

            GenFrame::ForOf {
                it,
                left,
                body,
                ctx,
                labels,
            } => {
                match feed {
                    Feed::Start | Feed::Child(Ok(_)) => {}
                    Feed::Child(Err(Abrupt::Continue { label, .. })) => {
                        if !label_matches(&label, labels) {
                            return Step::Done(Err(Abrupt::Continue { label, value: None }));
                        }
                    }
                    Feed::Child(Err(Abrupt::Break { label, .. })) => {
                        if label_matches(&label, labels) {
                            if let Err(a) = self.iterator_close(it, false) {
                                return Step::Done(Err(a));
                            }
                            return Step::Done(Ok(None));
                        }
                        let a = self.close_after_body_abrupt(it, Abrupt::Break { label, value: None });
                        return Step::Done(Err(a));
                    }
                    Feed::Child(Err(a)) => {
                        let a = self.close_after_body_abrupt(it, a);
                        return Step::Done(Err(a));
                    }
                    Feed::Resume(_) => {
                        return Step::Done(Err(Abrupt::Fatal("resume to for-of".to_string())))
                    }
                }
                if let Err(a) = self.charge_loop() {
                    return Step::Done(Err(a));
                }
                let nv = match self.fast_iter_next(it) {
                    Ok(Some(nv)) => nv,
                    Ok(None) => return Step::Done(Ok(None)),
                    // A step throw leaves the iterator done: propagate WITHOUT close.
                    Err(a) => return Step::Done(Err(a)),
                };
                let inner = match self.bind_for_head(left, nv, ctx) {
                    Ok(c) => c,
                    Err(a) => return Step::Done(Err(self.close_after_body_abrupt(it, a))),
                };
                match self.step_or_wholesale(body, &inner, &[], mode) {
                    Ok(frames) => Step::Push(frames),
                    Err(a) => Step::Done(Err(self.close_after_body_abrupt(it, a))),
                }
            }

            GenFrame::Labeled {
                label,
                body,
                ctx,
                labels,
            } => match feed {
                Feed::Start => {
                    let mut ls = labels.clone();
                    ls.push(label.clone());
                    match self.step_or_wholesale(body, ctx, &ls, mode) {
                        Ok(frames) => Step::Push(frames),
                        Err(a) => Step::Done(Err(a)),
                    }
                }
                Feed::Child(Err(Abrupt::Break { label: Some(l), .. })) if l == *label => {
                    Step::Done(Ok(None))
                }
                Feed::Child(c) => Step::Done(c),
                Feed::Resume(_) => {
                    Step::Done(Err(Abrupt::Fatal("resume to labelled".to_string())))
                }
            },

            GenFrame::Try {
                phase,
                block,
                catch,
                finally,
                ctx,
                saved,
            } => self.try_step(phase, block, catch, finally, ctx, saved, feed),
        }
    }

    // -- try/catch/finally ---------------------------------------------------

    #[allow(clippy::too_many_arguments)]
    fn try_step(
        &mut self,
        phase: &mut TryPhase,
        block: &Rc<Vec<Stmt>>,
        catch: &Option<Rc<(Option<Pat>, Vec<Stmt>)>>,
        finally: &Option<Rc<Vec<Stmt>>>,
        ctx: &Ctx,
        saved: &mut Option<Compl>,
        feed: Feed,
    ) -> Step {
        match feed {
            Feed::Start => {
                *phase = TryPhase::Block;
                let inner = match self.enter_block_scope(block, ctx) {
                    Ok(c) => c,
                    Err(a) => return Step::Done(Err(a)),
                };
                Step::Push(vec![GenFrame::Seq {
                    stmts: Rc::clone(block),
                    idx: 0,
                    ctx: inner,
                }])
            }
            Feed::Child(result) => match *phase {
                TryPhase::Block => match result {
                    Err(Abrupt::Throw(exc)) if catch.is_some() => {
                        *phase = TryPhase::Catch;
                        let (param, cbody) = &**catch.as_ref().expect("some");
                        match self.gen_enter_catch(param.as_ref(), cbody, exc, ctx) {
                            Ok(frames) => Step::Push(frames),
                            Err(a) => {
                                *saved = Some(Err(a));
                                self.try_goto_finally(phase, finally, ctx, saved)
                            }
                        }
                    }
                    other => {
                        *saved = Some(other);
                        self.try_goto_finally(phase, finally, ctx, saved)
                    }
                },
                TryPhase::Catch => {
                    *saved = Some(result);
                    self.try_goto_finally(phase, finally, ctx, saved)
                }
                TryPhase::Finally => match result {
                    // finally's normal completion is discarded; re-raise saved.
                    Ok(_) => Step::Done(saved.take().unwrap_or(Ok(None))),
                    // an abrupt finally overrides the saved completion.
                    Err(fa) => Step::Done(Err(fa)),
                },
                TryPhase::Start => {
                    Step::Done(Err(Abrupt::Fatal("try phase invariant".to_string())))
                }
            },
            Feed::Resume(_) => Step::Done(Err(Abrupt::Fatal("resume to try".to_string()))),
        }
    }

    fn try_goto_finally(
        &mut self,
        phase: &mut TryPhase,
        finally: &Option<Rc<Vec<Stmt>>>,
        ctx: &Ctx,
        saved: &mut Option<Compl>,
    ) -> Step {
        // A Fatal (out-of-slice refusal) is not a JS completion `finally` may
        // override: the finally block's behavior generally depends on the
        // unmodeled effects we just refused, so running it — and letting an
        // abrupt finally replace the refusal — would fabricate a trace.
        // Propagate the refusal immediately (mirrors the direct interpreter's
        // `eval_try`).
        if matches!(saved, Some(Err(Abrupt::Fatal(_)))) {
            return Step::Done(saved.take().expect("fatal completion present"));
        }
        match finally {
            Some(fbody) => {
                *phase = TryPhase::Finally;
                let inner = match self.enter_block_scope(fbody, ctx) {
                    Ok(c) => c,
                    Err(a) => return Step::Done(Err(a)),
                };
                Step::Push(vec![GenFrame::Seq {
                    stmts: Rc::clone(fbody),
                    idx: 0,
                    ctx: inner,
                }])
            }
            None => Step::Done(saved.take().unwrap_or(Ok(None))),
        }
    }

    /// Catch-clause entry: fresh param environment + binding, then a block Seq.
    fn gen_enter_catch(
        &mut self,
        param: Option<&Pat>,
        body: &[Stmt],
        exc: JsValue,
        ctx: &Ctx,
    ) -> Result<Vec<GenFrame>, Abrupt> {
        let cenv = self.alloc_env(Some(ctx.env));
        let cctx = Ctx {
            env: cenv,
            strict: ctx.strict,
        };
        if let Some(pat) = param {
            let mut names = Vec::new();
            crate::interp::hoist::pat_bound_names(pat, &mut names);
            for n in &names {
                self.heap
                    .env_mut(cenv)
                    .bindings
                    .insert(n.clone(), trust_js_value::Binding::tdz(true));
            }
            self.bind_pattern(pat, exc, Some(cenv), &cctx)?;
        }
        let inner = self.enter_block_scope(body, &cctx)?;
        Ok(vec![GenFrame::Seq {
            stmts: Rc::new(body.to_vec()),
            idx: 0,
            ctx: inner,
        }])
    }

    // -- statement dispatch --------------------------------------------------

    /// Frames to push for a yield-BEARING statement, or `Err(Fatal)` refusal.
    fn step_into_stmt(
        &mut self,
        s: &Stmt,
        ctx: &Ctx,
        labels: &[String],
        mode: SuspendKind,
    ) -> Result<Vec<GenFrame>, Abrupt> {
        match s {
            Stmt::Block(body) => {
                let inner = self.enter_block_scope(body, ctx)?;
                Ok(vec![GenFrame::Seq {
                    stmts: Rc::new(body.clone()),
                    idx: 0,
                    ctx: inner,
                }])
            }
            Stmt::Expr(e) => self.build_spine_frames(e, ctx, mode),
            Stmt::Decl { kind, decls } => {
                if decls.len() == 1 {
                    if let (Pat::Ident(name), Some(init)) = (&decls[0].0, &decls[0].1) {
                        let mut frames = vec![GenFrame::DeclInit {
                            name: name.clone(),
                            kind: *kind,
                            ctx: ctx.clone(),
                        }];
                        frames.extend(self.build_spine_frames(init, ctx, mode)?);
                        return Ok(frames);
                    }
                }
                Err(Abrupt::Fatal(
                    "yield in a multi-declarator or destructuring declaration (out of slice)"
                        .to_string(),
                ))
            }
            Stmt::Return(Some(e)) => {
                let mut frames = vec![GenFrame::ReturnCont];
                if mode == SuspendKind::AsyncGen {
                    // `return e` awaits e, then returns the awaited value.
                    frames.extend(self.build_await_spine(e, ctx, mode)?);
                } else {
                    frames.extend(self.build_spine_frames(e, ctx, mode)?);
                }
                Ok(frames)
            }
            Stmt::If { test, cons, alt } => {
                if expr_has_suspend(test, mode) {
                    return Err(Abrupt::Fatal(suspend_pos_msg(mode, "an if test")));
                }
                let t = self.eval_expr(test, ctx)?;
                let branch = if self.to_boolean(&t) {
                    Some(cons.as_ref())
                } else {
                    alt.as_deref()
                };
                match branch {
                    None => Ok(vec![GenFrame::Immediate(Some(Ok(None)))]),
                    Some(b) => self.step_or_wholesale(b, ctx, &[], mode),
                }
            }
            Stmt::While { test, body } => {
                if expr_has_suspend(test, mode) {
                    return Err(Abrupt::Fatal(suspend_pos_msg(mode, "a while test")));
                }
                Ok(vec![GenFrame::While {
                    test: Rc::new(test.clone()),
                    body: Rc::new((**body).clone()),
                    ctx: ctx.clone(),
                    labels: labels.to_vec(),
                    is_do: false,
                }])
            }
            Stmt::DoWhile { body, test } => {
                if expr_has_suspend(test, mode) {
                    return Err(Abrupt::Fatal(suspend_pos_msg(mode, "a do-while test")));
                }
                Ok(vec![GenFrame::While {
                    test: Rc::new(test.clone()),
                    body: Rc::new((**body).clone()),
                    ctx: ctx.clone(),
                    labels: labels.to_vec(),
                    is_do: true,
                }])
            }
            Stmt::For {
                init,
                test,
                update,
                body,
            } => self.step_into_for(init.as_ref(), test.as_ref(), update.as_ref(), body, ctx, labels, mode),
            Stmt::ForOf {
                left,
                right,
                body,
                is_await,
            } => {
                if *is_await {
                    return Err(Abrupt::Fatal("for-await-of (async, M2)".to_string()));
                }
                if expr_has_suspend(right, mode) {
                    return Err(Abrupt::Fatal(suspend_pos_msg(mode, "a for-of iterable")));
                }
                let head_ctx = self.head_expr_ctx(left, ctx);
                let rv = self.eval_expr(right, &head_ctx)?;
                let it = self.get_iterator_or_type_error(&rv)?;
                Ok(vec![GenFrame::ForOf {
                    it,
                    left: Rc::new(left.clone()),
                    body: Rc::new((**body).clone()),
                    ctx: ctx.clone(),
                    labels: labels.to_vec(),
                }])
            }
            Stmt::Labeled { label, body } => Ok(vec![GenFrame::Labeled {
                label: label.clone(),
                body: Rc::new((**body).clone()),
                ctx: ctx.clone(),
                labels: labels.to_vec(),
            }]),
            Stmt::Try {
                block,
                catch,
                finally,
            } => Ok(vec![GenFrame::Try {
                phase: TryPhase::Start,
                block: Rc::new(block.clone()),
                catch: catch.clone().map(Rc::new),
                finally: finally.clone().map(Rc::new),
                ctx: ctx.clone(),
                saved: None,
            }]),
            Stmt::ForIn { .. } => Err(Abrupt::Fatal(
                "yield in a for-in body (out of slice)".to_string(),
            )),
            Stmt::Switch { .. } => Err(Abrupt::Fatal(
                "yield in a switch statement (out of slice)".to_string(),
            )),
            Stmt::With { .. } => {
                Err(Abrupt::Fatal("with statement (out of slice)".to_string()))
            }
            _ => Err(Abrupt::Fatal(
                "yield in an unsupported statement position (out of slice)".to_string(),
            )),
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn step_into_for(
        &mut self,
        init: Option<&ForInit>,
        test: Option<&Expr>,
        update: Option<&Expr>,
        body: &Stmt,
        ctx: &Ctx,
        labels: &[String],
        mode: SuspendKind,
    ) -> Result<Vec<GenFrame>, Abrupt> {
        if test.is_some_and(|e| expr_has_suspend(e, mode)) || update.is_some_and(|e| expr_has_suspend(e, mode)) {
            return Err(Abrupt::Fatal(
                "yield in a for test/update (out of slice)".to_string(),
            ));
        }
        let mut cur = ctx.clone();
        let mut per_iter: Vec<String> = Vec::new();
        match init {
            Some(ForInit::Decl(DeclKind::Var, decls)) => {
                if decls.iter().any(|(_, e)| e.as_ref().is_some_and(|e| expr_has_suspend(e, mode))) {
                    return Err(Abrupt::Fatal("yield in a for init (out of slice)".to_string()));
                }
                self.eval_decl(DeclKind::Var, decls, ctx)?;
            }
            Some(ForInit::Decl(kind @ (DeclKind::Let | DeclKind::Const), decls)) => {
                if decls.iter().any(|(_, e)| e.as_ref().is_some_and(|e| expr_has_suspend(e, mode))) {
                    return Err(Abrupt::Fatal("yield in a for init (out of slice)".to_string()));
                }
                let env = self.alloc_env(Some(ctx.env));
                let mutable = *kind == DeclKind::Let;
                let mut names = Vec::new();
                for (pat, _) in decls {
                    crate::interp::hoist::pat_bound_names(pat, &mut names);
                }
                for n in &names {
                    self.heap
                        .env_mut(env)
                        .bindings
                        .insert(n.clone(), trust_js_value::Binding::tdz(mutable));
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
                if expr_has_suspend(e, mode) {
                    return Err(Abrupt::Fatal(suspend_pos_msg(mode, "a for init")));
                }
                self.eval_expr(e, &cur)?;
            }
            None => {}
        }
        if !per_iter.is_empty() {
            cur = self.copy_per_iteration_env(&cur, &per_iter, ctx.env)?;
        }
        Ok(vec![GenFrame::For {
            test: test.map(|e| Rc::new(e.clone())),
            update: update.map(|e| Rc::new(e.clone())),
            body: Rc::new(body.clone()),
            ctx: cur,
            labels: labels.to_vec(),
            per_iter: Rc::new(per_iter),
            outer: ctx.env,
            started: false,
        }])
    }

    /// Step into a statement if it bears a yield, else wrap it wholesale.
    fn step_or_wholesale(
        &mut self,
        s: &Stmt,
        ctx: &Ctx,
        labels: &[String],
        mode: SuspendKind,
    ) -> Result<Vec<GenFrame>, Abrupt> {
        if stmt_has_suspend(s, mode) {
            self.step_into_stmt(s, ctx, labels, mode)
        } else {
            Ok(vec![GenFrame::Wholesale {
                stmt: Rc::new(s.clone()),
                ctx: ctx.clone(),
            }])
        }
    }

    // -- spine expressions ---------------------------------------------------

    /// Frames for a spine expression (a yield/await, possibly wrapped in `=`
    /// assigns). In `AsyncGen` mode the operand of a `yield`/`await` may itself
    /// be a spine (e.g. `yield await e`), so those recurse.
    fn build_spine_frames(&mut self, e: &Expr, ctx: &Ctx, mode: SuspendKind) -> Result<Vec<GenFrame>, Abrupt> {
        let mut inner = e;
        while let Expr::Paren(p) = inner {
            inner = p;
        }
        match inner {
            // `await <operand>`.
            Expr::Await(a) if mode.awaits() => self.build_await_spine(a, ctx, mode),
            // `yield <operand>` (non-delegating).
            Expr::Yield {
                arg,
                delegate: false,
            } if mode.yields() => {
                if mode == SuspendKind::AsyncGen {
                    // AsyncGeneratorYield: evaluate the operand (which may itself
                    // suspend), Await the result, then complete the step.
                    return self.build_async_yield_spine(arg.as_deref(), ctx);
                }
                if let Some(a) = arg {
                    if expr_has_suspend(a, mode) {
                        return Err(Abrupt::Fatal(
                            "nested yield in a yield operand (out of slice)".to_string(),
                        ));
                    }
                }
                Ok(vec![GenFrame::YieldPoint {
                    arg: arg.as_ref().map(|b| Rc::new((**b).clone())),
                    ctx: ctx.clone(),
                }])
            }
            // `yield* <operand>` — sync generators only; async delegation refuses.
            Expr::Yield { delegate: true, .. } if mode == SuspendKind::AsyncGen => Err(
                Abrupt::Fatal("async generator yield* delegation (out of slice)".to_string()),
            ),
            Expr::Yield {
                arg,
                delegate: true,
            } if mode == SuspendKind::Yield => {
                let a = arg
                    .as_ref()
                    .ok_or_else(|| Abrupt::Fatal("yield* without operand".to_string()))?;
                if expr_has_suspend(a, mode) {
                    return Err(Abrupt::Fatal(
                        "nested yield in a yield* operand (out of slice)".to_string(),
                    ));
                }
                Ok(vec![GenFrame::YieldStar {
                    arg: Rc::new((**a).clone()),
                    ctx: ctx.clone(),
                    it: None,
                }])
            }
            Expr::Assign {
                op: "=",
                target,
                value,
            } => {
                let tgt = self.resolve_assign_target(target, ctx, mode)?;
                let mut frames = vec![GenFrame::AssignCont {
                    target: tgt,
                    ctx: ctx.clone(),
                }];
                frames.extend(self.build_spine_frames(value, ctx, mode)?);
                Ok(frames)
            }
            _ => Err(Abrupt::Fatal(
                "yield in an unsupported expression position (out of slice)".to_string(),
            )),
        }
    }

    /// Spine for `await <operand>`: if the operand is suspend-free, a direct
    /// `AwaitPoint`; otherwise evaluate the operand spine then await its value.
    fn build_await_spine(&mut self, a: &Expr, ctx: &Ctx, mode: SuspendKind) -> Result<Vec<GenFrame>, Abrupt> {
        if expr_has_suspend(a, mode) {
            let mut frames = vec![GenFrame::AwaitFromChild];
            frames.extend(self.build_spine_frames(a, ctx, mode)?);
            Ok(frames)
        } else {
            Ok(vec![GenFrame::AwaitPoint {
                arg: Rc::new(a.clone()),
                ctx: ctx.clone(),
            }])
        }
    }

    /// Spine for an async generator `yield <operand>`: evaluate the operand,
    /// `Await` the result (AsyncGeneratorYield step), then AsyncGeneratorComplete-
    /// Step. Frames run top-first: operand → await → complete.
    fn build_async_yield_spine(&mut self, arg: Option<&Expr>, ctx: &Ctx) -> Result<Vec<GenFrame>, Abrupt> {
        let mut frames = vec![GenFrame::AsyncGenYieldComplete];
        match arg {
            // `yield` (no operand): AsyncGeneratorYield(undefined) — Await(undefined).
            None => {
                frames.push(GenFrame::AwaitFromChild);
                frames.push(GenFrame::Immediate(Some(Ok(Some(JsValue::Undefined)))));
            }
            Some(a) if expr_has_suspend(a, SuspendKind::AsyncGen) => {
                // Suspendable operand: [complete, await-result, ...operand-spine].
                frames.push(GenFrame::AwaitFromChild);
                frames.extend(self.build_spine_frames(a, ctx, SuspendKind::AsyncGen)?);
            }
            Some(a) => {
                // Simple operand: an AwaitPoint evaluates and awaits it directly.
                frames.push(GenFrame::AwaitPoint {
                    arg: Rc::new(a.clone()),
                    ctx: ctx.clone(),
                });
            }
        }
        Ok(frames)
    }

    /// Resolve a `=`-assignment target's reference now (spec order: LHS before
    /// the RHS yield). Only plain identifiers and member expressions qualify.
    fn resolve_assign_target(&mut self, target: &Pat, ctx: &Ctx, mode: SuspendKind) -> Result<AssignTarget, Abrupt> {
        match target {
            Pat::Ident(name) => Ok(AssignTarget::Ident(name.clone())),
            Pat::Expr(m) => {
                if expr_has_suspend(m, mode) {
                    return Err(Abrupt::Fatal(suspend_pos_msg(mode, "an assignment target")));
                }
                Ok(AssignTarget::Ref(self.expr_ref(m, ctx)?))
            }
            _ => Err(Abrupt::Fatal(
                "yield assigned to a destructuring target (out of slice)".to_string(),
            )),
        }
    }

    // -- yield* delegation ---------------------------------------------------

    fn yieldstar_step(
        &mut self,
        arg: &Rc<Expr>,
        ctx: &Ctx,
        it: &mut Option<FastIter>,
        feed: Feed,
    ) -> Result<Step, Abrupt> {
        match feed {
            Feed::Start => {
                let v = self.eval_expr(arg, ctx)?;
                let iter = self.get_iterator_or_type_error(&v)?;
                *it = Some(iter);
                let iter = it.as_mut().expect("just set");
                self.ys_next(iter, JsValue::Undefined)
            }
            Feed::Resume(ResumeInput::Next(v)) => {
                let iter = it
                    .as_mut()
                    .ok_or_else(|| Abrupt::Fatal("yield* resume before init".to_string()))?;
                self.ys_next(iter, v)
            }
            Feed::Resume(ResumeInput::Throw(e)) => {
                let iter = it
                    .as_mut()
                    .ok_or_else(|| Abrupt::Fatal("yield* resume before init".to_string()))?;
                self.ys_throw(iter, e)
            }
            Feed::Resume(ResumeInput::Return(r)) => {
                let iter = it
                    .as_mut()
                    .ok_or_else(|| Abrupt::Fatal("yield* resume before init".to_string()))?;
                self.ys_return(iter, r)
            }
            Feed::Child(_) => Err(Abrupt::Fatal("child delivered to yield*".to_string())),
        }
    }

    /// case a: call inner `next(received)`; done→yield* value, else suspend.
    fn ys_next(&mut self, it: &mut FastIter, recv: JsValue) -> Result<Step, Abrupt> {
        match it {
            FastIter::User { iter, next, done } => {
                if *done {
                    return Ok(Step::Done(Ok(Some(JsValue::Undefined))));
                }
                let iter = *iter;
                let next = next.clone();
                let result = self.call_value(&next, JsValue::Obj(iter), vec![recv])?;
                let (value, is_done) = self.ys_read_result(&result)?;
                if is_done {
                    if let FastIter::User { done, .. } = it {
                        *done = true;
                    }
                    Ok(Step::Done(Ok(Some(value))))
                } else {
                    Ok(Step::Yield(value))
                }
            }
            _ => match self.fast_iter_next(it)? {
                Some(v) => Ok(Step::Yield(v)),
                None => Ok(Step::Done(Ok(Some(JsValue::Undefined)))),
            },
        }
    }

    /// case b: forward `throw`; absent → IteratorClose then TypeError.
    fn ys_throw(&mut self, it: &mut FastIter, e: JsValue) -> Result<Step, Abrupt> {
        let throw_m = if let FastIter::User { iter, .. } = it {
            self.get_method(&JsValue::Obj(*iter), &PropKey::from_str("throw"))?
        } else {
            None
        };
        match throw_m {
            None => {
                self.iterator_close(it, false)?;
                Err(self.throw_type_error())
            }
            Some(m) => {
                let iter_val = ys_iter_val(it);
                let result = self.call_value(&m, iter_val, vec![e])?;
                let (value, is_done) = self.ys_read_result(&result)?;
                if is_done {
                    if let FastIter::User { done, .. } = it {
                        *done = true;
                    }
                    Ok(Step::Done(Ok(Some(value))))
                } else {
                    Ok(Step::Yield(value))
                }
            }
        }
    }

    /// case c: forward `return`; absent → return the received value.
    fn ys_return(&mut self, it: &mut FastIter, r: JsValue) -> Result<Step, Abrupt> {
        let return_m = if let FastIter::User { iter, .. } = it {
            self.get_method(&JsValue::Obj(*iter), &PropKey::from_str("return"))?
        } else {
            None
        };
        match return_m {
            None => Ok(Step::Done(Err(Abrupt::Return(r)))),
            Some(m) => {
                let iter_val = ys_iter_val(it);
                let result = self.call_value(&m, iter_val, vec![r])?;
                let (value, is_done) = self.ys_read_result(&result)?;
                if is_done {
                    if let FastIter::User { done, .. } = it {
                        *done = true;
                    }
                    Ok(Step::Done(Err(Abrupt::Return(value))))
                } else {
                    Ok(Step::Yield(value))
                }
            }
        }
    }

    /// Validate an iterator result object and read (value, done) in spec order
    /// (IteratorComplete before IteratorValue).
    fn ys_read_result(&mut self, result: &JsValue) -> Result<(JsValue, bool), Abrupt> {
        let JsValue::Obj(ro) = result else {
            return Err(self.throw_type_error());
        };
        let done_v = self.get_from_object(*ro, &PropKey::from_str("done"), result.clone())?;
        let is_done = self.to_boolean(&done_v);
        let value = self.get_from_object(*ro, &PropKey::from_str("value"), result.clone())?;
        Ok((value, is_done))
    }
}

/// The receiver for a yield* method forward (only User iterators reach here).
fn ys_iter_val(it: &FastIter) -> JsValue {
    match it {
        FastIter::User { iter, .. } => JsValue::Obj(*iter),
        _ => JsValue::Undefined,
    }
}

/// Push the loop body (stepped if it bears a yield, else wholesale).
/// Push a loop body. The enclosing loop labels are NOT forwarded: a labelled
/// `break`/`continue` targeting the loop propagates up as an abrupt completion
/// and is matched by the loop frame itself (which carries the labels).
fn push_body(it: &mut Interp, body: &Rc<Stmt>, ctx: &Ctx, mode: SuspendKind) -> Step {
    match it.step_or_wholesale(body, ctx, &[], mode) {
        Ok(frames) => Step::Push(frames),
        Err(a) => Step::Done(Err(a)),
    }
}

// ---------------------------------------------------------------------------
// Yield scanners: does a statement/expression contain a `yield` that belongs to
// THIS generator? The walk stops at nested function/arrow/class boundaries (a
// `yield` there belongs to that inner function). A false negative only costs
// coverage (the statement is run wholesale and refuses on the yield); a false
// positive only costs coverage (an unhandled shape refuses) — never soundness.
// ---------------------------------------------------------------------------

/// A refusal message for a suspension in a position the machine cannot step at,
/// naming the suspension flavour (`yield`/`await`).
fn suspend_pos_msg(mode: SuspendKind, pos: &str) -> String {
    let kw = match mode {
        SuspendKind::Yield => "yield",
        SuspendKind::Await => "await",
        SuspendKind::AsyncGen => "yield/await",
    };
    format!("{kw} in {pos} (out of slice)")
}

/// Does `e` contain a suspension point (`yield` in `Yield` mode, `await` in
/// `Await` mode) belonging to THIS body? The walk stops at nested
/// function/arrow/class boundaries.
fn expr_has_suspend(e: &Expr, mode: SuspendKind) -> bool {
    let has = |x: &Expr| expr_has_suspend(x, mode);
    match e {
        Expr::Yield { arg, .. } => mode.yields() || arg.as_ref().is_some_and(|a| has(a)),
        Expr::Await(inner) => mode.awaits() || has(inner),
        // Boundaries: inner functions/classes own their own yields/awaits.
        Expr::Function(_) | Expr::Arrow(_) | Expr::Class(_) => false,
        Expr::Ident(_)
        | Expr::This
        | Expr::Null
        | Expr::Bool(_)
        | Expr::Num(_)
        | Expr::BigInt(_)
        | Expr::Str { .. }
        | Expr::Regex { .. }
        | Expr::NewTarget
        | Expr::ImportMeta
        | Expr::SuperProp(_)
        | Expr::PrivateRef(_) => false,
        Expr::Template { exprs, .. } => exprs.iter().any(has),
        Expr::TaggedTemplate { tag, exprs, .. } => has(tag) || exprs.iter().any(has),
        Expr::Array { elems, .. } => elems.iter().flatten().any(|a| arg_has_suspend(a, mode)),
        Expr::Object(props) => props.iter().any(|p| obj_prop_has_suspend(p, mode)),
        Expr::Paren(inner) => has(inner),
        Expr::Seq(list) => list.iter().any(has),
        Expr::Unary { arg, .. } | Expr::Update { arg, .. } => has(arg),
        Expr::Binary { left, right, .. } | Expr::Logical { left, right, .. } => {
            has(left) || has(right)
        }
        Expr::Assign { target, value, .. } => pat_has_suspend(target, mode) || has(value),
        Expr::Cond { test, cons, alt } => has(test) || has(cons) || has(alt),
        Expr::Member { obj, prop, .. } => has(obj) || key_has_suspend(prop, mode),
        Expr::Call { callee, args, .. } => has(callee) || args.iter().any(|a| arg_has_suspend(a, mode)),
        Expr::New { callee, args } => has(callee) || args.iter().any(|a| arg_has_suspend(a, mode)),
        Expr::ImportCall(list) => list.iter().any(has),
        Expr::SuperCall(args) => args.iter().any(|a| arg_has_suspend(a, mode)),
    }
}

fn arg_has_suspend(a: &trust_js_parse::ast::Arg, mode: SuspendKind) -> bool {
    match a {
        trust_js_parse::ast::Arg::Expr(e) | trust_js_parse::ast::Arg::Spread(e) => {
            expr_has_suspend(e, mode)
        }
    }
}

fn key_has_suspend(k: &AstKey, mode: SuspendKind) -> bool {
    matches!(k, AstKey::Computed(e) if expr_has_suspend(e, mode))
}

fn obj_prop_has_suspend(p: &ObjProp, mode: SuspendKind) -> bool {
    match p {
        ObjProp::KeyValue { key, value } => {
            key_has_suspend(key, mode) || expr_has_suspend(value, mode)
        }
        ObjProp::Shorthand(_) => false,
        ObjProp::CoverInit(_, e) => expr_has_suspend(e, mode),
        ObjProp::Spread(e) => expr_has_suspend(e, mode),
        // A method's own body is a function boundary.
        ObjProp::Method { key, .. } => key_has_suspend(key, mode),
    }
}

fn pat_has_suspend(p: &Pat, mode: SuspendKind) -> bool {
    match p {
        Pat::Ident(_) => false,
        Pat::Expr(e) => expr_has_suspend(e, mode),
        Pat::Default(inner, e) => pat_has_suspend(inner, mode) || expr_has_suspend(e, mode),
        Pat::Rest(inner) => pat_has_suspend(inner, mode),
        Pat::Array { elems, rest } => {
            elems.iter().flatten().any(|p| pat_has_suspend(p, mode))
                || rest.as_deref().is_some_and(|p| pat_has_suspend(p, mode))
        }
        Pat::Object { props, rest } => {
            props
                .iter()
                .any(|pp| key_has_suspend(&pp.key, mode) || pat_has_suspend(&pp.value, mode))
                || rest.as_deref().is_some_and(|p| pat_has_suspend(p, mode))
        }
    }
}

fn stmt_has_suspend(s: &Stmt, mode: SuspendKind) -> bool {
    let se = |e: &Expr| expr_has_suspend(e, mode);
    let ss = |s: &Stmt| stmt_has_suspend(s, mode);
    match s {
        Stmt::Empty | Stmt::Debugger | Stmt::Break(_) | Stmt::Continue(_) => false,
        // A nested function/class declaration is a boundary.
        Stmt::FuncDecl(_) | Stmt::ClassDecl(_) => false,
        // Module import/export declarations never occur in a function body.
        Stmt::Import(_) | Stmt::Export(_) => false,
        Stmt::Expr(e) | Stmt::Throw(e) => se(e),
        // In an async generator, `return e` implicitly `Await`s e
        // (ReturnStatement step: GetGeneratorKind is async), so it must be
        // stepped even when e itself is suspend-free. `return;` does not await.
        Stmt::Return(e) => {
            (mode == SuspendKind::AsyncGen && e.is_some()) || e.as_ref().is_some_and(se)
        }
        Stmt::Block(body) => body.iter().any(ss),
        Stmt::Decl { decls, .. } => decls
            .iter()
            .any(|(p, e)| pat_has_suspend(p, mode) || e.as_ref().is_some_and(se)),
        Stmt::If { test, cons, alt } => {
            se(test) || ss(cons) || alt.as_deref().is_some_and(ss)
        }
        Stmt::DoWhile { body, test } | Stmt::While { test, body } => se(test) || ss(body),
        Stmt::For {
            init,
            test,
            update,
            body,
        } => {
            init.as_ref().is_some_and(|i| for_init_has_suspend(i, mode))
                || test.as_ref().is_some_and(se)
                || update.as_ref().is_some_and(se)
                || ss(body)
        }
        Stmt::ForIn { left, right, body } | Stmt::ForOf { left, right, body, .. } => {
            for_head_has_suspend(left, mode) || se(right) || ss(body)
        }
        Stmt::With { obj, body } => se(obj) || ss(body),
        Stmt::Labeled { body, .. } => ss(body),
        Stmt::Switch { disc, cases } => {
            se(disc)
                || cases.iter().any(|c| {
                    c.test.as_ref().is_some_and(se) || c.body.iter().any(ss)
                })
        }
        Stmt::Try {
            block,
            catch,
            finally,
        } => {
            block.iter().any(ss)
                || catch.as_ref().is_some_and(|(_, b)| b.iter().any(ss))
                || finally.as_ref().is_some_and(|b| b.iter().any(ss))
        }
    }
}

fn for_init_has_suspend(init: &ForInit, mode: SuspendKind) -> bool {
    match init {
        ForInit::Decl(_, decls) => decls
            .iter()
            .any(|(p, e)| pat_has_suspend(p, mode) || e.as_ref().is_some_and(|e| expr_has_suspend(e, mode))),
        ForInit::Expr(e) => expr_has_suspend(e, mode),
    }
}

fn for_head_has_suspend(h: &ForHead, mode: SuspendKind) -> bool {
    match h {
        ForHead::Decl(_, p) | ForHead::Pat(p) => pat_has_suspend(p, mode),
    }
}
