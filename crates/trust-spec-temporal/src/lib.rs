// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates
//
//! Derived TLA+: one source of truth for a state machine, two faithful backends.
//!
//! A hand-written `.tla` file can drift from the code it is supposed to
//! describe. This module removes that gap: a [`Model`] is a first-class Rust
//! value describing a bounded state machine (constants, variables, guarded
//! actions, invariants) over a small expression language [`Expr`]. From that ONE
//! source we generate BOTH:
//!
//!   - [`Model::to_tla`] / [`Model::to_cfg`] — a complete, `ty`-checkable TLA+
//!     module + config (the embedded spec), and
//!   - [`Model::fire`] — the executable transition semantics (a real interpreter,
//!     using TLA+ primed semantics: every right-hand side is evaluated against the
//!     pre-state, then applied).
//!
//! Because both backends consume the same `Expr` trees, a change to the model
//! changes the spec AND the executable semantics together — they cannot drift.
//! The generated spec is exhaustively checked by `ty` (Tier 0); the same model
//! is what a Tier 1 conformance test would replay against real code.
//!
//! The expression language is intentionally small (what the bounded-ring model
//! needs); it grows as real models demand. The translation is mechanical:
//! `<=` ⇒ `=<`, `if/else` ⇒ `IF/THEN/ELSE`, `&&`/`||` ⇒ `/\`/`\/`.

// Let the `trust_model!` macro's absolute `::trust_spec_temporal::*` paths resolve
// to THIS crate, so the macro works inside this crate's own tests too (not only in
// downstream crates that name the dependency).
extern crate self as trust_spec_temporal;

mod certified_temporal;
mod clean_model_lane;
mod clean_surface;
mod clean_ty_lane;
mod dependency_coherence;
mod r5_parity;
mod r5_scorecard;

use std::collections::{BTreeMap, BTreeSet};

// Serialize the embedded ty parse/lower/check transaction.
//
// `tla_core` and `tla_check` intentionally retain process-global interning and
// run-scoped caches.  The upstream run guard begins inside `check_module`,
// after the caller has already parsed and lowered a module.  Letting sibling
// Trust certification calls overlap that pre-guard window has produced a
// wrong cross-run `Success` for a `Buggy = 1` model.  Keep the whole
// parse/lower/check/replay transaction atomic as well as reset-safe. ty's
// pre-parse guard prevents destructive resets, while this lock also excludes
// overlapping Trust-owned transactions from shared engine state whose
// concurrent semantics are not part of the embedded lane's contract.
//
// This lock covers every in-crate entry point. The pinned ty revision now also
// exposes a production pre-parse lifecycle guard and uses its reset sentinel in
// production, so an external `reset_global_state` cannot invalidate a live
// Trust transaction. Arbitrary embedders that bypass the public pre-parse guard
// remain responsible for their own parse/reset ordering.
thread_local! {
    static IN_PROCESS_TY_TRANSACTION_DEPTH: std::cell::Cell<usize> = const {
        std::cell::Cell::new(0)
    };
}

#[must_use]
pub(crate) struct InProcessTyTransactionGuard {
    _outer_lock: Option<std::sync::MutexGuard<'static, ()>>,
    ty_context: Option<tla_check::ModelCheckContextGuard>,
}

impl Drop for InProcessTyTransactionGuard {
    fn drop(&mut self) {
        IN_PROCESS_TY_TRANSACTION_DEPTH.with(|depth| {
            let current = depth.get();
            debug_assert!(current > 0, "embedded ty transaction depth underflow");
            depth.set(current.saturating_sub(1));
        });
        // End ty's reset-safe parse/check context before releasing Trust's
        // outer serialization lock. Nested guards borrow the outer context and
        // therefore carry no independent lifecycle token.
        drop(self.ty_context.take());
        // `outer_lock` drops after this method returns. The thread-local depth
        // reaches zero before the process-global mutex is released.
    }
}

pub(crate) fn in_process_ty_transaction_lock() -> InProcessTyTransactionGuard {
    static LOCK: std::sync::OnceLock<std::sync::Mutex<()>> = std::sync::OnceLock::new();
    let nested = IN_PROCESS_TY_TRANSACTION_DEPTH.with(|depth| depth.get() > 0);
    let outer_lock = if nested {
        None
    } else {
        Some(LOCK.get_or_init(|| std::sync::Mutex::new(())).lock().expect(
            "an earlier embedded ty transaction panicked; refusing to reuse its global state",
        ))
    };
    let ty_context = (!nested).then(tla_check::enter_model_check_context);
    IN_PROCESS_TY_TRANSACTION_DEPTH.with(|depth| {
        depth.set(depth.get().checked_add(1).expect("embedded ty transaction depth overflow"));
    });
    let guard = InProcessTyTransactionGuard { _outer_lock: outer_lock, ty_context };
    // Every nested acquisition marks a new, independently parsed semantic
    // input. Clear ty's pointer-keyed and liveness evaluation caches before it
    // can reuse an address from the preceding positive/negative leg. This API
    // is explicitly concurrency-safe and does not clear global name/value
    // interners held by an unrelated caller.
    tla_check::clear_thread_local_eval_caches();
    guard
}

#[cfg(test)]
mod in_process_ty_transaction_tests {
    use std::sync::mpsc;
    use std::time::Duration;

    use super::*;

    #[test]
    fn transaction_guard_excludes_sibling_semantic_input() {
        const WORKER_ENV: &str = "TRUST_TEMPORAL_TY_TRANSACTION_TEST_WORKER";
        const TEST_NAME: &str =
            "in_process_ty_transaction_tests::transaction_guard_excludes_sibling_semantic_input";
        if std::env::var_os(WORKER_ENV).is_none() {
            let output = std::process::Command::new(
                std::env::current_exe().expect("the current Rust test binary has a path"),
            )
            .env(WORKER_ENV, "1")
            .args(["--exact", TEST_NAME, "--nocapture", "--test-threads=1"])
            .output()
            .expect("isolated transaction-guard worker must launch");
            assert!(
                output.status.success(),
                "isolated transaction-guard worker failed\nstdout:\n{}\nstderr:\n{}",
                String::from_utf8_lossy(&output.stdout),
                String::from_utf8_lossy(&output.stderr),
            );
            return;
        }

        let (holder_ready_tx, holder_ready_rx) = mpsc::channel();
        let (release_holder_tx, release_holder_rx) = mpsc::channel();
        let (waiter_started_tx, waiter_started_rx) = mpsc::channel();
        let (waiter_acquired_tx, waiter_acquired_rx) = mpsc::channel();

        std::thread::scope(|scope| {
            scope.spawn(move || {
                let _ty_transaction = in_process_ty_transaction_lock();
                holder_ready_tx.send(()).expect("holder readiness channel remains open");
                release_holder_rx.recv().expect("holder release channel remains open");
            });

            holder_ready_rx.recv().expect("holder must acquire the transaction first");
            scope.spawn(move || {
                waiter_started_tx.send(()).expect("waiter-start channel remains open");
                let _ty_transaction = in_process_ty_transaction_lock();
                waiter_acquired_tx.send(()).expect("waiter result channel remains open");
            });

            waiter_started_rx.recv().expect("waiter must reach the lock attempt");
            let before_release = waiter_acquired_rx.recv_timeout(Duration::from_millis(100));
            // Always release the holder before asserting. If the exclusion
            // contract regresses, a panic inside this scoped thread block must
            // still join both workers instead of hanging the test process.
            release_holder_tx.send(()).expect("holder release channel remains open");
            assert!(
                matches!(before_release, Err(mpsc::RecvTimeoutError::Timeout)),
                "a sibling thread acquired TY semantic-input authority before the holder released it",
            );
            waiter_acquired_rx
                .recv_timeout(Duration::from_secs(5))
                .expect("the sibling transaction must proceed after the holder releases it");
        });
    }
}

pub use certified_temporal::{
    CERTIFIED_TEMPORAL_EVIDENCE_SCHEMA_V1, CertifiedTemporalError, CertifiedTemporalEvidence,
    CertifiedTemporalPropertyClass, certify_liveness_with_ty, recheck_certified_temporal_evidence,
};
pub use clean_model_lane::{
    CLEAN_SCALAR_MODEL_SCHEMA_V1, CleanScalarAction, CleanScalarConstant, CleanScalarExpr,
    CleanScalarInvariant, CleanScalarModel, CleanScalarModelArtifact, CleanScalarModelCertificate,
    CleanScalarModelError, CleanScalarStateVar, CleanScalarUpdate, FINITE_MODEL_PRELUDE,
    certify_clean_scalar_model_with_ty, extract_clean_scalar_model,
    recheck_clean_scalar_model_artifact, recheck_clean_scalar_model_with_ty,
};
pub use clean_surface::{
    CLEAN_TEMPORAL_CERT_SCHEMA_V1, CLEAN_TEMPORAL_PRELUDE, CleanTemporalCertificate,
    CleanTemporalCertificateError, certify_clean_temporal_source,
    recheck_clean_temporal_certificate,
};
pub use clean_ty_lane::{
    CLEAN_TY_COUNTDOWN_SCHEMA_V2, CleanTyCountdownCertificate, CleanTyCountdownError,
    certify_clean_countdown_with_ty, recheck_clean_countdown_with_ty,
};
pub use r5_parity::{
    R5_MODEL_ABI_AMBITION_BLOCKERS, R5_TEMPORAL_MACRO_DEPRECATION_ALLOWED,
    R5_TEMPORAL_MACRO_RETIREMENT_ALLOWED, R5_TEMPORAL_PARITY_BLOCKERS,
    R5_TEMPORAL_PARITY_REPORT_SCHEMA_V1, R5_TEMPORAL_PARITY_REPORT_SCHEMA_V2,
    R5_TEMPORAL_RETIREMENT_BLOCKERS, R5TemporalParityBlocker, R5TemporalParityReport,
    R5TemporalParityReportValidationError, R5TemporalParityStatus, r5_temporal_parity_report,
};
pub use r5_scorecard::{
    CapabilityReplacementStatus, R5_MACRO_CAPABILITY_SCORECARD,
    R5_MACRO_CAPABILITY_SCORECARD_SCHEMA_V1, R5CapabilityRow, R5MacroCapability,
    R5MacroCapabilityRecord, R5MacroCapabilityScorecard, R5MacroCapabilityScorecardError,
    R5MacroSurface, capability_row, macro_surface_emits_deprecation, r5_macro_capability_scorecard,
};

/// A value in the model's (bounded-integer / boolean) semantics.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Value {
    Int(i64),
    Bool(bool),
}

impl Value {
    fn as_int(self) -> i64 {
        match self {
            Value::Int(i) => i,
            Value::Bool(_) => panic!("expected Int, got Bool — model type error"),
        }
    }
    fn as_bool(self) -> bool {
        match self {
            Value::Bool(b) => b,
            Value::Int(_) => panic!("expected Bool, got Int — model type error"),
        }
    }
}

/// A small expression language shared by the TLA+ generator and the interpreter.
/// `Var`/`ConstRef` both resolve from the evaluation environment; arithmetic and
/// comparison map 1:1 to TLA+.
///
/// The NAME REPRESENTATION is generic: the legacy public ABI (macro expansions,
/// hand-written models, the convenience constructors below) stays `&'static str`
/// through the default parameter, while the Clean decode lane feeds the SAME
/// renderer/validator/certifier with owned `String` names — one shared
/// certification core, no second semantic object, and no process-global name
/// interner. Destruction is iterative even for the deepest Clean-admitted tree.
/// The derived `Debug` and `Clone` implementations remain structurally
/// recursive convenience APIs; they are not used on adversarially deep values
/// by the Clean certification path and are not promised stack safety.
#[derive(Debug, Clone)]
pub enum Expr<S = &'static str> {
    /// An integer literal.
    Int(i64),
    /// A state variable reference (resolves from the current state).
    Var(S),
    /// A TLA+ CONSTANT reference (resolves from the model's constants).
    ConstRef(S),
    Add(Box<Expr<S>>, Box<Expr<S>>),
    Sub(Box<Expr<S>>, Box<Expr<S>>),
    /// `a > b` (boolean).
    Gt(Box<Expr<S>>, Box<Expr<S>>),
    /// `a <= b` (boolean) — emits TLA+ `=<`.
    Le(Box<Expr<S>>, Box<Expr<S>>),
    /// `a = b` (boolean, integer operands) — emits TLA+ `=`.
    Eq(Box<Expr<S>>, Box<Expr<S>>),
    /// `a \/ b` (boolean disjunction) — emits parenthesized TLA+ `(a \/ b)` so it
    /// composes correctly when used as an action guard (which is conjoined with
    /// the update conjuncts, and `/\` binds tighter than `\/`).
    Or(Box<Expr<S>>, Box<Expr<S>>),
    /// `a /\ b` (boolean conjunction) — emits TLA+ `a /\ b` (unparenthesized; `/\`
    /// is associative with the action-level conjunction it joins, so a guard built
    /// from `And` composes correctly without parens).
    And(Box<Expr<S>>, Box<Expr<S>>),
    /// `IF cond THEN a ELSE b` (condition boolean; arms have one common scalar sort).
    If(Box<Expr<S>>, Box<Expr<S>>, Box<Expr<S>>),
    /// `a <=> b` (boolean iff) — emits parenthesized `(a <=> b)`.
    Iff(Box<Expr<S>>, Box<Expr<S>>),
    /// `\A n \in lo..hi : body` (universal quantifier; `body` boolean, may
    /// reference the bound index by name). Scalar bodies are interpreter-evaluable.
    Forall(S, Box<Expr<S>>, Box<Expr<S>>, Box<Expr<S>>),
    // ---- function-valued (TLA+ generation only; see eval note) ----
    /// `fn[index]` — access a function-valued (`[1..N -> BOOLEAN]`) state variable.
    FnAccess(S, Box<Expr<S>>),
    /// `[fn EXCEPT ![index] = value]` — a point update of a function variable.
    Except(S, Box<Expr<S>>, Box<Expr<S>>),
    /// `[n \in lo..hi |-> body]` — a function comprehension (`body` may reference
    /// the bound index by name); used for whole-function updates.
    Comprehension(S, Box<Expr<S>>, Box<Expr<S>>, Box<Expr<S>>),
    /// `TRUE` / `FALSE`.
    Bool(bool),
    /// `a # b` (integer inequality).
    Neq(Box<Expr<S>>, Box<Expr<S>>),
}

impl<S> Expr<S> {
    /// Detach direct children without recursively dropping their subtrees.
    ///
    /// Each existing box retains a scalar placeholder, so its eventual drop is
    /// constant-depth. The detached value moves to the caller's heap-backed
    /// worklist. This is the safe counterpart of taking fields out of a type
    /// that implements `Drop`.
    fn detach_children_for_drop(&mut self, pending: &mut Vec<Self>) {
        fn detach<S>(child: &mut Box<Expr<S>>) -> Expr<S> {
            std::mem::replace(child.as_mut(), Expr::Int(0))
        }

        match self {
            Expr::Add(left, right)
            | Expr::Sub(left, right)
            | Expr::Gt(left, right)
            | Expr::Le(left, right)
            | Expr::Eq(left, right)
            | Expr::Or(left, right)
            | Expr::And(left, right)
            | Expr::Iff(left, right)
            | Expr::Except(_, left, right)
            | Expr::Neq(left, right) => {
                pending.push(detach(left));
                pending.push(detach(right));
            }
            Expr::If(first, second, third)
            | Expr::Forall(_, first, second, third)
            | Expr::Comprehension(_, first, second, third) => {
                pending.push(detach(first));
                pending.push(detach(second));
                pending.push(detach(third));
            }
            Expr::FnAccess(_, child) => pending.push(detach(child)),
            Expr::Int(_) | Expr::Var(_) | Expr::ConstRef(_) | Expr::Bool(_) => {}
        }
    }
}

impl<S> Drop for Expr<S> {
    fn drop(&mut self) {
        let mut pending = Vec::new();
        self.detach_children_for_drop(&mut pending);
        while let Some(mut child) = pending.pop() {
            child.detach_children_for_drop(&mut pending);
        }
    }
}

/// Convenience constructors (keep model definitions terse).
pub fn int(i: i64) -> Expr {
    Expr::Int(i)
}
pub fn var(n: &'static str) -> Expr {
    Expr::Var(n)
}
pub fn cst(n: &'static str) -> Expr {
    Expr::ConstRef(n)
}
pub fn add(a: Expr, b: Expr) -> Expr {
    Expr::Add(Box::new(a), Box::new(b))
}
pub fn sub(a: Expr, b: Expr) -> Expr {
    Expr::Sub(Box::new(a), Box::new(b))
}
pub fn gt(a: Expr, b: Expr) -> Expr {
    Expr::Gt(Box::new(a), Box::new(b))
}
pub fn le(a: Expr, b: Expr) -> Expr {
    Expr::Le(Box::new(a), Box::new(b))
}
pub fn eq(a: Expr, b: Expr) -> Expr {
    Expr::Eq(Box::new(a), Box::new(b))
}
pub fn or_(a: Expr, b: Expr) -> Expr {
    Expr::Or(Box::new(a), Box::new(b))
}
pub fn and_(a: Expr, b: Expr) -> Expr {
    Expr::And(Box::new(a), Box::new(b))
}
pub fn if_(c: Expr, a: Expr, b: Expr) -> Expr {
    Expr::If(Box::new(c), Box::new(a), Box::new(b))
}
pub fn iff(a: Expr, b: Expr) -> Expr {
    Expr::Iff(Box::new(a), Box::new(b))
}
pub fn forall(idx: &'static str, lo: Expr, hi: Expr, body: Expr) -> Expr {
    Expr::Forall(idx, Box::new(lo), Box::new(hi), Box::new(body))
}
pub fn fn_access(f: &'static str, index: Expr) -> Expr {
    Expr::FnAccess(f, Box::new(index))
}
pub fn except(f: &'static str, index: Expr, value: Expr) -> Expr {
    Expr::Except(f, Box::new(index), Box::new(value))
}
pub fn comprehension(idx: &'static str, lo: Expr, hi: Expr, body: Expr) -> Expr {
    Expr::Comprehension(idx, Box::new(lo), Box::new(hi), Box::new(body))
}
pub fn bool_lit(b: bool) -> Expr {
    Expr::Bool(b)
}
pub fn neq(a: Expr, b: Expr) -> Expr {
    Expr::Neq(Box::new(a), Box::new(b))
}

impl Expr {
    /// Evaluate against an environment (state variables + constants).
    ///
    /// This legacy executable projection has an exact `i64` carrier while TLA+
    /// integers are unbounded. It therefore fails stop if an arithmetic result
    /// leaves `i64`; wrapping would silently give the two backends different
    /// transitions. Certification is performed by the ty/Clean lane, not by
    /// this compatibility interpreter.
    ///
    /// Depth note: this walk is deliberately still recursive. It is monomorphic
    /// to the legacy `&'static str` carrier and certification never routes
    /// through it (see the interpreter `impl Model` below), so it is NOT
    /// reachable from decoded Clean input — the only inputs are macro/hand
    /// -written expressions whose nesting is bounded by compile-time source
    /// shape, far below any stack limit. If a `String`-named → `&'static str`
    /// bridge is ever reintroduced, this walk must be converted to an explicit
    /// heap stack like `to_tla`/`model_expr_sort` first.
    pub fn eval(&self, env: &BTreeMap<&'static str, i64>) -> Value {
        match self {
            Expr::Int(i) => Value::Int(*i),
            Expr::Var(n) | Expr::ConstRef(n) => Value::Int(
                *env.get(n)
                    .unwrap_or_else(|| panic!("unbound identifier `{n}` in model evaluation")),
            ),
            Expr::Add(a, b) => Value::Int(
                a.eval(env)
                    .as_int()
                    .checked_add(b.eval(env).as_int())
                    .expect("model addition left the exact i64 interpreter domain"),
            ),
            Expr::Sub(a, b) => Value::Int(
                a.eval(env)
                    .as_int()
                    .checked_sub(b.eval(env).as_int())
                    .expect("model subtraction left the exact i64 interpreter domain"),
            ),
            Expr::Gt(a, b) => Value::Bool(a.eval(env).as_int() > b.eval(env).as_int()),
            Expr::Le(a, b) => Value::Bool(a.eval(env).as_int() <= b.eval(env).as_int()),
            Expr::Eq(a, b) => Value::Bool(a.eval(env).as_int() == b.eval(env).as_int()),
            Expr::Neq(a, b) => Value::Bool(a.eval(env).as_int() != b.eval(env).as_int()),
            Expr::Bool(b) => Value::Bool(*b),
            Expr::Or(a, b) => Value::Bool(a.eval(env).as_bool() || b.eval(env).as_bool()),
            Expr::And(a, b) => Value::Bool(a.eval(env).as_bool() && b.eval(env).as_bool()),
            Expr::If(c, a, b) => {
                if c.eval(env).as_bool() {
                    a.eval(env)
                } else {
                    b.eval(env)
                }
            }
            Expr::Iff(a, b) => Value::Bool(a.eval(env).as_bool() == b.eval(env).as_bool()),
            Expr::Forall(idx, lo, hi, body) => {
                let (l, h) = (lo.eval(env).as_int(), hi.eval(env).as_int());
                let mut e = env.clone();
                for n in l..=h {
                    e.insert(idx, n);
                    if !body.eval(&e).as_bool() {
                        return Value::Bool(false);
                    }
                }
                Value::Bool(true)
            }
            // Function-valued exprs are TLA+-generation only: the faithful models
            // that use them are Tier-0 ty-checked, not run through this scalar
            // interpreter (whose env is integer-valued). A scalar model never
            // contains these, so these arms are unreachable in practice.
            Expr::FnAccess(..) | Expr::Except(..) | Expr::Comprehension(..) => {
                panic!(
                    "function-valued Expr is TLA+-generation only (Tier-0 ty-checked, not interpreter-evaluable)"
                )
            }
        }
    }
}

impl<S: AsRef<str>> Expr<S> {
    /// Render as a TLA+ expression while preserving this AST's grouping. In
    /// particular, arithmetic nodes and quantifiers are parenthesized so that a
    /// surrounding expression cannot change their interpreter semantics.
    ///
    /// The walk is iterative with an explicit heap stack (post-order: a node is
    /// combined after its children were rendered left-to-right), so rendering
    /// depth is bounded by heap, not the Rust stack — this renderer is reachable
    /// from decoded Clean input, whose nesting is capped only by the Clean
    /// lane's decode-cost guard. The emission is byte-identical to the original
    /// recursive formatting.
    pub fn to_tla(&self) -> String {
        enum Task<'e, T> {
            Render(&'e Expr<T>),
            Combine(&'e Expr<T>),
        }
        let mut tasks: Vec<Task<'_, S>> = vec![Task::Render(self)];
        let mut rendered: Vec<String> = Vec::new();
        while let Some(task) = tasks.pop() {
            match task {
                Task::Render(node) => match node {
                    Expr::Int(i) => rendered.push(i.to_string()),
                    Expr::Var(n) | Expr::ConstRef(n) => rendered.push(n.as_ref().to_string()),
                    Expr::Bool(b) => rendered.push(if *b { "TRUE" } else { "FALSE" }.to_string()),
                    Expr::Add(a, b)
                    | Expr::Sub(a, b)
                    | Expr::Gt(a, b)
                    | Expr::Le(a, b)
                    | Expr::Eq(a, b)
                    | Expr::Neq(a, b)
                    | Expr::Or(a, b)
                    | Expr::And(a, b)
                    | Expr::Iff(a, b) => {
                        tasks.push(Task::Combine(node));
                        tasks.push(Task::Render(b));
                        tasks.push(Task::Render(a));
                    }
                    Expr::If(c, a, b) => {
                        tasks.push(Task::Combine(node));
                        tasks.push(Task::Render(b));
                        tasks.push(Task::Render(a));
                        tasks.push(Task::Render(c));
                    }
                    Expr::Forall(_, lo, hi, body) | Expr::Comprehension(_, lo, hi, body) => {
                        tasks.push(Task::Combine(node));
                        tasks.push(Task::Render(body));
                        tasks.push(Task::Render(hi));
                        tasks.push(Task::Render(lo));
                    }
                    Expr::FnAccess(_, index) => {
                        tasks.push(Task::Combine(node));
                        tasks.push(Task::Render(index));
                    }
                    Expr::Except(_, index, value) => {
                        tasks.push(Task::Combine(node));
                        tasks.push(Task::Render(value));
                        tasks.push(Task::Render(index));
                    }
                },
                Task::Combine(node) => {
                    // Children were rendered left-to-right, so the LAST operand
                    // is on top of `rendered`.
                    let mut operand = || rendered.pop().expect("operand was rendered");
                    let text = match node {
                        Expr::Add(..) => {
                            let (b, a) = (operand(), operand());
                            format!("({} + {})", a, b)
                        }
                        Expr::Sub(..) => {
                            let (b, a) = (operand(), operand());
                            format!("({} - {})", a, b)
                        }
                        Expr::Gt(..) => {
                            let (b, a) = (operand(), operand());
                            format!("{} > {}", a, b)
                        }
                        Expr::Le(..) => {
                            let (b, a) = (operand(), operand());
                            format!("{} =< {}", a, b)
                        }
                        Expr::Eq(..) => {
                            let (b, a) = (operand(), operand());
                            format!("{} = {}", a, b)
                        }
                        Expr::Neq(..) => {
                            let (b, a) = (operand(), operand());
                            format!("{} # {}", a, b)
                        }
                        // Parenthesized: `\/` binds looser than the `/\` it is
                        // conjoined with.
                        Expr::Or(..) => {
                            let (b, a) = (operand(), operand());
                            format!("({} \\/ {})", a, b)
                        }
                        Expr::And(..) => {
                            let (b, a) = (operand(), operand());
                            format!("{} /\\ {}", a, b)
                        }
                        // Parenthesized: an `IF`'s `ELSE` extends as far right as
                        // possible, so an IF-valued update that is NOT the last
                        // action conjunct would otherwise swallow the following
                        // `/\ ...`.
                        Expr::If(..) => {
                            let (b, a, c) = (operand(), operand(), operand());
                            format!("(IF {} THEN {} ELSE {})", c, a, b)
                        }
                        Expr::Iff(..) => {
                            let (b, a) = (operand(), operand());
                            format!("({} <=> {})", a, b)
                        }
                        Expr::Forall(idx, ..) => {
                            let (body, hi, lo) = (operand(), operand(), operand());
                            format!("(\\A {} \\in {}..{} : {})", idx.as_ref(), lo, hi, body)
                        }
                        Expr::FnAccess(f, _) => {
                            let index = operand();
                            format!("{}[{}]", f.as_ref(), index)
                        }
                        Expr::Except(f, ..) => {
                            let (value, index) = (operand(), operand());
                            format!("[{} EXCEPT ![{}] = {}]", f.as_ref(), index, value)
                        }
                        Expr::Comprehension(idx, ..) => {
                            let (body, hi, lo) = (operand(), operand(), operand());
                            format!("[{} \\in {}..{} |-> {}]", idx.as_ref(), lo, hi, body)
                        }
                        Expr::Int(_) | Expr::Var(_) | Expr::ConstRef(_) | Expr::Bool(_) => {
                            unreachable!("leaves render directly and are never combined")
                        }
                    };
                    rendered.push(text);
                }
            }
        }
        let root = rendered.pop().expect("iterative rendering produced exactly one root");
        debug_assert!(rendered.is_empty(), "renderer consumed every operand");
        root
    }
}

/// `var' = expr`: an action's update to one state variable.
#[derive(Debug, Clone)]
pub struct Update<S = &'static str> {
    pub var: S,
    pub expr: Expr<S>,
}

/// A guarded action (a disjunct of `Next`). Variables not updated stay UNCHANGED.
#[derive(Debug, Clone)]
pub struct Action<S = &'static str> {
    pub name: S,
    pub guard: Option<Expr<S>>,
    pub updates: Vec<Update<S>>,
}

/// A named safety invariant.
#[derive(Debug, Clone)]
pub struct Invariant<S = &'static str> {
    pub name: S,
    pub expr: Expr<S>,
}

/// A state variable with its `Init` value.
#[derive(Debug, Clone)]
pub struct StateVar<S = &'static str> {
    pub name: S,
    pub init: i64,
}

/// A function-valued state variable `[1..range -> BOOLEAN]`, initialized all-FALSE.
/// Used for per-element models (e.g. a ring's live-set) that the scalar projection
/// cannot express. Certification routes these finite products through the Clean S4
/// exhaustive reconstruction instead of the scalar integer interpreter.
#[derive(Debug, Clone)]
pub struct FnVar<S = &'static str> {
    pub name: S,
    /// Upper bound of the index domain (a CONSTANT name); the domain is `1..range`.
    pub range: S,
}

/// A bounded state machine — the single source for both the TLA+ spec and the
/// executable semantics.
///
/// Like [`Expr`], the name representation is generic with a `&'static str`
/// default: every legacy constructor keeps its exact source shape, while the
/// Clean lane's decoded `String`-named form drives the same renderer and
/// certification chain byte-identically.
#[derive(Debug, Clone)]
pub struct Model<S = &'static str> {
    pub name: S,
    pub consts: Vec<(S, i64)>,
    pub vars: Vec<StateVar<S>>,
    /// Function-valued variables (`[1..range -> BOOLEAN]`). Usually empty (scalar
    /// models); non-empty only for per-element Tier-0 models.
    pub fn_vars: Vec<FnVar<S>>,
    pub actions: Vec<Action<S>>,
    pub invariants: Vec<Invariant<S>>,
}

impl<S: AsRef<str>> Model<S> {
    /// All state-variable names, scalar then function-valued (the order used in
    /// `VARIABLES`, `vars`, and `UNCHANGED`).
    fn all_var_names(&self) -> Vec<&str> {
        let mut v: Vec<&str> = self.vars.iter().map(|x| x.name.as_ref()).collect();
        v.extend(self.fn_vars.iter().map(|f| f.name.as_ref()));
        v
    }

    /// Generate the complete TLA+ module text (the embedded, `ty`-checkable spec)
    /// with the model's concrete `Init` (variables start at their declared values).
    pub fn to_tla(&self) -> String {
        let const_names: Vec<String> =
            self.consts.iter().map(|(n, _)| n.as_ref().to_string()).collect();
        let mut init_parts: Vec<String> =
            self.vars.iter().map(|v| format!("{} = {}", v.name.as_ref(), v.init)).collect();
        // Function vars initialize to the all-FALSE function over `1..range`.
        for f in &self.fn_vars {
            init_parts.push(format!(
                "{} = [n \\in 1..{} |-> FALSE]",
                f.name.as_ref(),
                f.range.as_ref()
            ));
        }
        let init = init_parts.join(" /\\ ");
        self.render(&const_names, &init)
    }

    /// Generate the module with a PARAMETERIZED `Init`: each variable starts at a
    /// fresh CONSTANT `<var>_init`. This lets any predecessor state be the start —
    /// used for strict per-transition conformance against real code (Tier 1):
    /// validating a two-step trace `[prev, next]` with `Init` pinned to `prev`
    /// strictly checks that `Next` admits the real `prev -> next` transition.
    pub fn transition_spec(&self) -> String {
        let mut const_names: Vec<String> =
            self.consts.iter().map(|(n, _)| n.as_ref().to_string()).collect();
        for v in &self.vars {
            const_names.push(format!("{}_init", v.name.as_ref()));
        }
        let init = self
            .vars
            .iter()
            .map(|v| format!("{} = {}_init", v.name.as_ref(), v.name.as_ref()))
            .collect::<Vec<_>>()
            .join(" /\\ ");
        self.render(&const_names, &init)
    }

    /// Shared renderer: emit the module given the CONSTANT names and the `Init`
    /// body. Actions, `Next`, `Spec`, and invariants are identical across the
    /// concrete and parameterized-`Init` forms — one source for both.
    fn render(&self, const_names: &[String], init_line: &str) -> String {
        let vars = self.all_var_names();
        let mut s = String::new();
        s.push_str(&format!("---- MODULE {} ----\n", self.name.as_ref()));
        s.push_str("EXTENDS Naturals\n");
        if !const_names.is_empty() {
            s.push_str(&format!("CONSTANT {}\n", const_names.join(", ")));
        }
        s.push_str(&format!("VARIABLES {}\n", vars.join(", ")));
        s.push_str(&format!("vars == << {} >>\n", vars.join(", ")));
        s.push_str(&format!("Init == {init_line}\n"));

        // Actions
        for a in &self.actions {
            let mut conj: Vec<String> = Vec::new();
            if let Some(g) = &a.guard {
                conj.push(g.to_tla());
            }
            for u in &a.updates {
                conj.push(format!("{}' = {}", u.var.as_ref(), u.expr.to_tla()));
            }
            // UNCHANGED for variables this action does not update.
            let updated: Vec<&str> = a.updates.iter().map(|u| u.var.as_ref()).collect();
            let unchanged: Vec<&str> =
                vars.iter().copied().filter(|v| !updated.contains(v)).collect();
            if !unchanged.is_empty() {
                conj.push(format!("UNCHANGED << {} >>", unchanged.join(", ")));
            }
            s.push_str(&format!("{} == {}\n", a.name.as_ref(), conj.join(" /\\ ")));
        }

        let action_names: Vec<&str> = self.actions.iter().map(|a| a.name.as_ref()).collect();
        s.push_str(&format!("Next == {}\n", action_names.join(" \\/ ")));
        s.push_str("Spec == Init /\\ [][Next]_vars\n");

        for inv in &self.invariants {
            s.push_str(&format!("{} == {}\n", inv.name.as_ref(), inv.expr.to_tla()));
        }
        s.push_str("====\n");
        s
    }

    /// Generate the `.cfg`: constant bindings, the specification, and every
    /// invariant. Bounded constants keep `ty check` exhaustive + terminating.
    pub fn to_cfg(&self) -> String {
        self.to_cfg_with(&[])
    }

    /// Like [`to_cfg`](Self::to_cfg) but with constant `overrides` — e.g. flip a
    /// `Buggy` flag to 1 to check that an invariant is non-trivial (the buggy
    /// variant must yield a counterexample), the in-spec analogue of the
    /// `Buggy`-constant convention used by the hand-written specs.
    pub fn to_cfg_with(&self, overrides: &[(&'static str, i64)]) -> String {
        let mut s = String::new();
        for (n, default) in &self.consts {
            let n = n.as_ref();
            let val = overrides.iter().find(|(o, _)| *o == n).map(|(_, v)| *v).unwrap_or(*default);
            s.push_str(&format!("CONSTANT {n} = {val}\n"));
        }
        s.push_str("SPECIFICATION Spec\n");
        for inv in &self.invariants {
            s.push_str(&format!("INVARIANT {}\n", inv.name.as_ref()));
        }
        s.push_str("CHECK_DEADLOCK FALSE\n");
        s
    }

    /// Generate a semantically equivalent config whose transition operators
    /// are explicit.  Proof envelopes embed this form because their independent
    /// replay verifier deliberately reparses the config without performing the
    /// higher-level `SPECIFICATION` decomposition used by the model-checking
    /// driver.
    fn to_replay_cfg_with(&self, overrides: &[(&'static str, i64)]) -> String {
        let mut s = String::new();
        for (n, default) in &self.consts {
            let n = n.as_ref();
            let val = overrides.iter().find(|(o, _)| *o == n).map(|(_, v)| *v).unwrap_or(*default);
            s.push_str(&format!("CONSTANT {n} = {val}\n"));
        }
        s.push_str("INIT Init\nNEXT Next\n");
        for inv in &self.invariants {
            s.push_str(&format!("INVARIANT {}\n", inv.name.as_ref()));
        }
        s.push_str("CHECK_DEADLOCK FALSE\n");
        s
    }

    /// Config for [`transition_spec`](Self::transition_spec): binds each model
    /// constant (with optional `overrides`, e.g. the real ring capacity instead of
    /// the small exhaustive-check bound) and pins each `<var>_init` to `init`. Used
    /// for per-transition conformance — `ty trace validate --spec` then strictly
    /// checks the real `prev -> next` step against the derived `Next`.
    pub fn transition_cfg(
        &self,
        init: &BTreeMap<&'static str, i64>,
        overrides: &[(&'static str, i64)],
    ) -> String {
        let mut s = String::new();
        for (n, default) in &self.consts {
            let n = n.as_ref();
            let val = overrides.iter().find(|(o, _)| *o == n).map(|(_, v)| *v).unwrap_or(*default);
            s.push_str(&format!("CONSTANT {n} = {val}\n"));
        }
        for v in &self.vars {
            let val = init.get(v.name.as_ref()).copied().unwrap_or(v.init);
            s.push_str(&format!("CONSTANT {}_init = {val}\n", v.name.as_ref()));
        }
        s.push_str("SPECIFICATION Spec\nCHECK_DEADLOCK FALSE\n");
        s
    }
}

/// The executable (interpreter) surface stays on the legacy `&'static str`
/// carrier: its evaluation environments are keyed by `&'static str` and every
/// caller is a legacy model. Certification never routes through it.
impl Model {
    /// Constants as an evaluation environment base.
    fn const_env(&self) -> BTreeMap<&'static str, i64> {
        self.consts.iter().copied().collect()
    }

    /// The initial concrete state (variable -> value).
    pub fn init_state(&self) -> BTreeMap<&'static str, i64> {
        self.vars.iter().map(|v| (v.name, v.init)).collect()
    }

    /// Fire a named action against `state` (TLA+ primed semantics: all RHS are
    /// evaluated against the pre-state, then applied atomically). Returns `false`
    /// without mutating if the action's guard is unsatisfied. This is the
    /// executable twin of the generated TLA+ action.
    pub fn fire(&self, action: &str, state: &mut BTreeMap<&'static str, i64>) -> bool {
        let act = self
            .actions
            .iter()
            .find(|a| a.name == action)
            .unwrap_or_else(|| panic!("no action `{action}` in model `{}`", self.name));
        let mut env = self.const_env();
        env.extend(state.iter().map(|(k, v)| (*k, *v)));
        if act.guard.as_ref().is_some_and(|g| !g.eval(&env).as_bool()) {
            return false;
        }
        let news: Vec<(&'static str, i64)> =
            act.updates.iter().map(|u| (u.var, u.expr.eval(&env).as_int())).collect();
        for (v, val) in news {
            state.insert(v, val);
        }
        true
    }

    /// Whether `action`'s guard is satisfied in `state` (no guard ⇒ always
    /// enabled). This lets real code be checked against the model's ACTUAL guard
    /// expression — e.g. a conformance test can assert the real subscriber gaps
    /// exactly when `PollGap` is enabled — rather than re-stating the predicate.
    pub fn action_enabled(&self, action: &str, state: &BTreeMap<&'static str, i64>) -> bool {
        let act = self
            .actions
            .iter()
            .find(|a| a.name == action)
            .unwrap_or_else(|| panic!("no action `{action}` in model `{}`", self.name));
        let mut env = self.const_env();
        env.extend(state.iter().map(|(k, v)| (*k, *v)));
        act.guard.as_ref().map(|g| g.eval(&env).as_bool()).unwrap_or(true)
    }

    /// Evaluate a named invariant against a concrete state.
    pub fn check_invariant(&self, name: &str, state: &BTreeMap<&'static str, i64>) -> bool {
        let inv = self
            .invariants
            .iter()
            .find(|i| i.name == name)
            .unwrap_or_else(|| panic!("no invariant `{name}`"));
        let mut env = self.const_env();
        env.extend(state.iter().map(|(k, v)| (*k, *v)));
        inv.expr.eval(&env).as_bool()
    }
}

/// The bounded event-log ring as a derived model — the single source the spec in
/// `Evict.tla` hand-encodes, scalar-projected to `<<seq, lo>>`. `Push` advances
/// `seq` and evicts the oldest live event (`lo`) exactly when the live window
/// would exceed `Cap`. `MaxSeq` bounds the state space so `ty check` is
/// exhaustive + terminating; `Cap` is the ring capacity. Action name is `Push`
/// (not `Append`, which clashes with ty's Sequences builtin).
pub fn ring_model() -> Model {
    Model {
        name: "Ring",
        consts: vec![("MaxSeq", 6), ("Cap", 3)],
        vars: vec![StateVar { name: "seq", init: 0 }, StateVar { name: "lo", init: 1 }],
        fn_vars: vec![],
        actions: vec![Action {
            name: "Push",
            guard: Some(le(var("seq"), sub(cst("MaxSeq"), int(1)))), // seq <= MaxSeq - 1
            updates: vec![
                Update { var: "seq", expr: add(var("seq"), int(1)) },
                Update {
                    var: "lo",
                    // IF (seq + 1) - lo + 1 > Cap THEN lo + 1 ELSE lo
                    expr: if_(
                        gt(add(sub(add(var("seq"), int(1)), var("lo")), int(1)), cst("Cap")),
                        add(var("lo"), int(1)),
                        var("lo"),
                    ),
                },
            ],
        }],
        invariants: vec![Invariant {
            name: "LenBounded",
            // seq - lo + 1 <= Cap
            expr: le(add(sub(var("seq"), var("lo")), int(1)), cst("Cap")),
        }],
    }
}

/// A second derived model — a writer/subscriber cursor — chosen because it
/// exercises derivation paths the ring does not: TWO actions (so `Next` is a
/// disjunction) and PARTIAL updates (so each action emits an `UNCHANGED` clause
/// for the variable it leaves alone). `Grow` advances the writer `seq`; `Deliver`
/// catches the reader `cursor` up to `seq`. Invariant: the reader never passes the
/// writer (`cursor <= seq`). This is the Subscribe/Kernel family in miniature, and
/// it proves the derivation engine generalizes beyond the single-action ring.
pub fn cursor_model() -> Model {
    Model {
        name: "Cursor",
        consts: vec![("MaxSeq", 4)],
        vars: vec![StateVar { name: "seq", init: 0 }, StateVar { name: "cursor", init: 0 }],
        fn_vars: vec![],
        actions: vec![
            Action {
                name: "Grow", // writer appends; cursor is UNCHANGED
                guard: Some(le(var("seq"), sub(cst("MaxSeq"), int(1)))),
                updates: vec![Update { var: "seq", expr: add(var("seq"), int(1)) }],
            },
            Action {
                name: "Deliver", // reader catches up; seq is UNCHANGED
                guard: Some(gt(var("seq"), var("cursor"))),
                updates: vec![Update { var: "cursor", expr: var("seq") }],
            },
        ],
        invariants: vec![Invariant {
            name: "CursorBounded",
            expr: le(var("cursor"), var("seq")), // cursor <= seq
        }],
    }
}

/// A third derived model — the subscriber's NO-SILENT-LOSS / gap discipline, the
/// kernel family's most important correctness property: a reader that has fallen
/// behind the live ring window MUST receive a Gap (resync) and must NEVER be
/// silently delivered events as if nothing was lost. Scalar projection over
/// `<<seq, lo, cursor, lost>>`: `Grow` advances the writer and evicts the oldest
/// when over `Cap`; `PollGap` resyncs a fallen-behind reader (`lo > cursor + 1`);
/// `PollDeliver` delivers while the reader is still within the live window.
///
/// The `Buggy` constant flips `PollDeliver`'s guard: with `Buggy = 0` (committed)
/// it is correctly guarded and `lost` stays 0; with `Buggy = 1` it fires even when
/// the reader is behind, silently skipping evicted events — so `lost` becomes 1
/// and `NoSilentLoss` is violated. Thus `ty` both PROVES the property (Buggy=0)
/// and, via a `Buggy=1` cfg, shows it genuinely CATCHES the silent-loss bug.
/// Exercises the `Expr` disjunction (`\/`) and equality (`=`) operators.
pub fn subscribe_model() -> Model {
    Model {
        name: "Subscribe",
        consts: vec![("MaxSeq", 4), ("Cap", 2), ("Buggy", 0)],
        vars: vec![
            StateVar { name: "seq", init: 0 },
            StateVar { name: "lo", init: 1 },
            StateVar { name: "cursor", init: 0 },
            StateVar { name: "lost", init: 0 },
        ],
        fn_vars: vec![],
        actions: vec![
            Action {
                name: "Grow", // writer appends + evicts oldest when over Cap
                guard: Some(le(var("seq"), sub(cst("MaxSeq"), int(1)))),
                updates: vec![
                    Update { var: "seq", expr: add(var("seq"), int(1)) },
                    Update {
                        var: "lo",
                        expr: if_(
                            gt(add(sub(add(var("seq"), int(1)), var("lo")), int(1)), cst("Cap")),
                            add(var("lo"), int(1)),
                            var("lo"),
                        ),
                    },
                ], // cursor, lost UNCHANGED
            },
            Action {
                name: "PollGap", // reader fell behind (lo > cursor + 1): resync, no loss
                guard: Some(gt(var("lo"), add(var("cursor"), int(1)))),
                updates: vec![Update { var: "cursor", expr: var("seq") }], // seq, lo, lost UNCHANGED
            },
            Action {
                name: "PollDeliver", // deliver; correct iff the reader is still in window
                // Buggy = 1 \/ lo =< cursor + 1  (Buggy removes the in-window guard)
                guard: Some(or_(
                    eq(cst("Buggy"), int(1)),
                    le(var("lo"), add(var("cursor"), int(1))),
                )),
                updates: vec![
                    Update { var: "cursor", expr: var("seq") },
                    // lost' = IF lo > cursor + 1 THEN 1 ELSE lost  (records a silent skip)
                    Update {
                        var: "lost",
                        expr: if_(gt(var("lo"), add(var("cursor"), int(1))), int(1), var("lost")),
                    },
                ], // seq, lo UNCHANGED
            },
        ],
        invariants: vec![Invariant {
            name: "NoSilentLoss",
            expr: eq(var("lost"), int(0)), // lost = 0
        }],
    }
}

/// A fourth derived model — TRANSACTION ATOMICITY / no-lost-update under
/// optimistic concurrency (the `Transact` kernel-family property). A transaction
/// reads the head at `tbase` (`Begin`); concurrent `Write`s may advance `seq`. At
/// commit, the correct discipline is: commit only if no write intervened
/// (`seq = tbase`), otherwise ABORT — committing against a stale `tbase` would
/// clobber the concurrent write (a lost update). Scalar projection over
/// `<<seq, tbase, active, lost>>`, edits-per-txn `K`.
///
/// `Buggy` gates the bad path: with `Buggy = 0` (committed) a conflict can only
/// `Abort`, so `lost` stays 0; with `Buggy = 1` the txn may commit despite a
/// conflict (`seq' = tbase + K`, overwriting the intervening write) and sets
/// `lost = 1`. So `ty` proves `NoLostUpdate` (Buggy=0) and catches it (Buggy=1).
/// Exercises the `Expr` conjunction (`/\`) operator in guards.
pub fn transact_model() -> Model {
    Model {
        name: "Transact",
        consts: vec![("MaxSeq", 4), ("K", 2), ("Buggy", 0)],
        vars: vec![
            StateVar { name: "seq", init: 0 },
            StateVar { name: "tbase", init: 0 },
            StateVar { name: "active", init: 0 },
            StateVar { name: "lost", init: 0 },
        ],
        fn_vars: vec![],
        actions: vec![
            Action {
                name: "Write", // a concurrent writer advances the committed head
                guard: Some(le(var("seq"), sub(cst("MaxSeq"), int(1)))),
                updates: vec![Update { var: "seq", expr: add(var("seq"), int(1)) }],
            },
            Action {
                name: "Begin", // a txn reads the current head as its base version
                guard: Some(eq(var("active"), int(0))),
                updates: vec![
                    Update { var: "active", expr: int(1) },
                    Update { var: "tbase", expr: var("seq") },
                ],
            },
            Action {
                name: "CommitClean", // no write intervened: commit K edits atomically
                guard: Some(and_(
                    and_(eq(var("active"), int(1)), eq(var("seq"), var("tbase"))),
                    le(var("seq"), sub(cst("MaxSeq"), cst("K"))),
                )),
                updates: vec![
                    Update { var: "seq", expr: add(var("seq"), cst("K")) },
                    Update { var: "active", expr: int(0) },
                ],
            },
            Action {
                name: "Abort", // a write intervened (seq > tbase): correct path aborts
                guard: Some(and_(eq(var("active"), int(1)), gt(var("seq"), var("tbase")))),
                updates: vec![Update { var: "active", expr: int(0) }],
            },
            Action {
                name: "BuggyCommit", // conflict committed anyway -> clobbers, lost update
                guard: Some(and_(
                    and_(
                        and_(eq(var("active"), int(1)), gt(var("seq"), var("tbase"))),
                        eq(cst("Buggy"), int(1)),
                    ),
                    le(var("tbase"), sub(cst("MaxSeq"), cst("K"))),
                )),
                updates: vec![
                    Update { var: "seq", expr: add(var("tbase"), cst("K")) },
                    Update { var: "active", expr: int(0) },
                    Update { var: "lost", expr: int(1) },
                ],
            },
        ],
        invariants: vec![Invariant {
            name: "NoLostUpdate",
            expr: eq(var("lost"), int(0)), // lost = 0
        }],
    }
}

/// A fifth derived model — the event-log SPINE: gap-free, monotone, `seq == count`
/// (the `Kernel` family property). Each `Append` assigns the next contiguous seq
/// and bumps the count, so the head seq always equals the number of events — no
/// gaps, no duplicates. `Buggy` makes an append jump seq by 2 (a gap), so
/// `seq != count` and `SeqIsCount` is violated. ty proves it (Buggy=0) and catches
/// the gap (Buggy=1).
pub fn kernel_model() -> Model {
    Model {
        name: "Kernel",
        consts: vec![("MaxSeq", 5), ("Buggy", 0)],
        vars: vec![StateVar { name: "seq", init: 0 }, StateVar { name: "count", init: 0 }],
        // Action `Emit` (not `Append`, which clashes with ty's Sequences builtin in
        // a single-action spec — see the ring's `Push`).
        fn_vars: vec![],
        actions: vec![Action {
            name: "Emit",
            guard: Some(le(var("seq"), sub(cst("MaxSeq"), int(1)))),
            updates: vec![
                Update { var: "count", expr: add(var("count"), int(1)) },
                // seq' = IF Buggy = 1 THEN seq + 2 ELSE seq + 1   (Buggy opens a gap)
                Update {
                    var: "seq",
                    expr: if_(
                        eq(cst("Buggy"), int(1)),
                        add(var("seq"), int(2)),
                        add(var("seq"), int(1)),
                    ),
                },
            ],
        }],
        invariants: vec![Invariant {
            name: "SeqIsCount",
            expr: eq(var("seq"), var("count")), // seq = count (gap-free, monotone spine)
        }],
    }
}

/// A sixth derived model — SNAPSHOT isolation (the `Snapshot` family property): a
/// snapshot, once taken, is isolated from later writes; a write must NOT leak into
/// an active snapshot's view. Scalar projection over `<<seq, snapped, leaked>>`:
/// `Snap` activates a snapshot; `Write` advances the head and, in the BUGGY case
/// (`Buggy = 1 /\ snapped = 1`), leaks into the snapshot (`leaked = 1`). ty proves
/// `SnapshotIsolated` (Buggy=0) and catches the leak (Buggy=1).
pub fn snapshot_model() -> Model {
    Model {
        name: "Snapshot",
        consts: vec![("MaxSeq", 4), ("Buggy", 0)],
        vars: vec![
            StateVar { name: "seq", init: 0 },
            StateVar { name: "snapped", init: 0 },
            StateVar { name: "leaked", init: 0 },
        ],
        fn_vars: vec![],
        actions: vec![
            Action {
                name: "Snap", // take a single snapshot of the current head
                guard: Some(eq(var("snapped"), int(0))),
                updates: vec![Update { var: "snapped", expr: int(1) }], // seq, leaked UNCHANGED
            },
            Action {
                name: "Write", // advance the head; must not leak into an active snapshot
                guard: Some(le(var("seq"), sub(cst("MaxSeq"), int(1)))),
                updates: vec![
                    Update { var: "seq", expr: add(var("seq"), int(1)) },
                    // leaked' = IF Buggy = 1 /\ snapped = 1 THEN 1 ELSE leaked
                    Update {
                        var: "leaked",
                        expr: if_(
                            and_(eq(cst("Buggy"), int(1)), eq(var("snapped"), int(1))),
                            int(1),
                            var("leaked"),
                        ),
                    },
                ], // snapped UNCHANGED
            },
        ],
        invariants: vec![Invariant {
            name: "SnapshotIsolated",
            expr: eq(var("leaked"), int(0)), // leaked = 0
        }],
    }
}

/// A FAITHFUL per-element ring model with a function-valued live-set
/// `live: [1..MaxSeq -> BOOLEAN]` — the property the scalar `ring_model` cannot
/// express. It proves `EvictOldestContiguous`: the live region is EXACTLY the
/// contiguous window `[lo, seq]`, so eviction removes precisely the oldest event,
/// never a hole and never two. This is the function-valued twin of the
/// hand-written `Evict.tla`'s operational `live` discipline. Because it is
/// function-valued, it is Tier-0 `ty`-checked (TLA+ generation), not run through
/// the scalar interpreter.
pub fn evict_full_model() -> Model {
    // (seq + 1) - lo + 1 > Cap : the eviction condition (over the pre-state seq).
    let evicting = || gt(add(sub(add(var("seq"), int(1)), var("lo")), int(1)), cst("Cap"));
    Model {
        name: "EvictFull",
        consts: vec![("MaxSeq", 5), ("Cap", 3)],
        vars: vec![StateVar { name: "seq", init: 0 }, StateVar { name: "lo", init: 1 }],
        fn_vars: vec![FnVar { name: "live", range: "MaxSeq" }],
        actions: vec![Action {
            name: "Push",
            guard: Some(le(var("seq"), sub(cst("MaxSeq"), int(1)))),
            updates: vec![
                Update { var: "seq", expr: add(var("seq"), int(1)) },
                Update { var: "lo", expr: if_(evicting(), add(var("lo"), int(1)), var("lo")) },
                Update {
                    var: "live",
                    // Evicting: rebuild the live-set as (old minus the evicted `lo`)
                    // plus the new event `seq+1`. Non-evicting: just mark `seq+1`.
                    expr: if_(
                        evicting(),
                        comprehension(
                            "n",
                            int(1),
                            cst("MaxSeq"),
                            if_(
                                eq(var("n"), add(var("seq"), int(1))),
                                bool_lit(true),
                                and_(fn_access("live", var("n")), neq(var("n"), var("lo"))),
                            ),
                        ),
                        except("live", add(var("seq"), int(1)), bool_lit(true)),
                    ),
                },
            ],
        }],
        invariants: vec![Invariant {
            name: "EvictOldestContiguous",
            // \A n \in 1..MaxSeq : live[n] <=> (lo =< n /\ n =< seq)
            expr: forall(
                "n",
                int(1),
                cst("MaxSeq"),
                iff(
                    fn_access("live", var("n")),
                    and_(le(var("lo"), var("n")), le(var("n"), var("seq"))),
                ),
            ),
        }],
    }
}

// ---------------------------------------------------------------------------
// Deprecated macro compatibility integration (docs/TY_ANNOTATION_FEATURE.md).
// `trust_model!` still expands to a `Model`, while `check_model` delegates to
// the pinned in-process certificate, exact-binding, kernel-recheck, and
// replayed-non-vacuity lane below. New temporal models use the Clean scalar
// surface instead of this macro DSL.
// ---------------------------------------------------------------------------

#[cfg(test)]
use std::path::{Path, PathBuf};
#[cfg(test)]
use std::process::Command;

/// Compatibility macros that expand the legacy inline DSL to a [`Model`]
/// literal. Re-exported from `trust-spec-temporal-macros`. The deprecation
/// policy is **per capability**: see [`r5_macro_capability_scorecard`].
///
/// `trust_model!`'s capability — a bounded scalar-integer SAFETY machine — is
/// `FullyReplaced` (owner policy flip 2026-07-21): the live Clean lane
/// certifies byte-identically (author a temporal [`Model`], or a `clean { … }`
/// island, and certify with [`certify_clean_scalar_model_with_ty`]), and its
/// formerly narrower admission domain now covers the owner-ratified
/// operational macro-parity domain (interner + name caps deleted, depth cap
/// widened to a decode-cost guard, positive near-cap vectors certified
/// end-to-end). Both macros therefore carry the advisory `#[deprecated]`
/// nudge — the D1+ ratchet. Expansion is unchanged: every existing use keeps
/// compiling and behaving identically; a legacy call site that must stay
/// warning-free acknowledges the nudge explicitly:
///
/// ```no_run
/// #![allow(deprecated)] // legacy compatibility surface, advisory nudge acknowledged
/// use trust_spec_temporal::{Model, trust_model};
///
/// fn legacy_model() -> Model {
///     trust_model! {
///         Legacy {
///             const Buggy = 0;
///             var x = 0;
///             action Step { x = x; }
///             invariant Stable: x == x;
///         }
///     }
/// }
///
/// fn main() {}
/// ```
///
/// `temporal_model!` is the item-position spelling and expands to a model
/// constructor fn. Its former automatic link-time inventory registration was
/// deleted as extraneous (owner ruling 2026-07-20) — the live Targo gates never
/// trusted the linked registry, and callers enumerate the definitions they
/// certify explicitly. It exercises the same `FullyReplaced` scalar-safety
/// core and carries the same advisory nudge:
///
/// ```no_run
/// #![allow(deprecated)] // legacy compatibility surface, advisory nudge acknowledged
/// use trust_spec_temporal::temporal_model;
///
/// temporal_model! {
///     LegacyItem {
///         const Buggy = 0;
///         var x = 0;
///         action Step { x = x; }
///         invariant Stable: x == x;
///     }
/// }
///
/// fn main() {}
/// ```
#[allow(deprecated)]
pub use trust_spec_temporal_macros::{temporal_model, trust_model};

/// Diagnostic result for one model.
///
/// [`check_model`] and [`certify_model`] return [`ModelVerdict::Proved`] only
/// after source/config binding, kernel replay, and non-vacuity gates all close.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ModelVerdict {
    /// Certified result from [`certify_model`].
    Proved,
    /// Internal exploratory exhaustive result without a `Buggy` dial.
    ProvedNoDial,
    /// The committed invariant was violated; carries the offending invariant name.
    Failed(String),
    /// The `Buggy = 1` config did NOT break — the invariant proves nothing.
    Vacuous,
    /// Could not be decided (no embedded ty, spawn/parse error, non-exhaustive,
    /// limit reached). FAIL-CLOSED: never read as `ok`.
    Unknown(String),
}

impl ModelVerdict {
    /// Whether this value is a `Proved*` variant. Callers needing proof credit
    /// must obtain it from [`certify_model`], not from an internal helper.
    pub fn is_proved(&self) -> bool {
        matches!(self, ModelVerdict::Proved | ModelVerdict::ProvedNoDial)
    }
}

// ===========================================================================
// The `ty certify` invocation lane (R5 non-P1 step 2).
//
// `ty certify <spec> --config <cfg> --out <cert.json>` runs ty's certifying
// verification and, on success (exit 0), WRITES a self-contained `ty.cert/v1`
// JSON certificate to `--out` (it is NOT printed to stdout). The certificate
// embeds `spec_src` — the full TLA+ module text ty certified — plus the
// configured invariant names and per-obligation proof legs.
//
// This lane parses that certificate and BINDS it to Trust's inputs:
//   (a) the JSON must parse with the `ty.cert/v1` schema tag,
//   (b) `cert.spec_src` must BYTE-match the TLA+ module Trust generated and
//       handed to ty (the input binding — what makes the cert evidence about
//       OUR model rather than about whatever file the checker happened to
//       read), and
//   (c) the certified invariant names must match what the caller expected.
// Any mismatch is a structured [`TyCertifyError`] naming WHICH binding
// failed — never a silent fallback to the text-parse (`run_ty`) lane.
//
// Byte-matching (b) is achievable because our generated modules are already
// self-contained: they extend only the stdlib `Naturals` (so ty's certify-side
// EXTENDS flattening is the identity) and use NAMED `Init`/`Next` operators
// (so SPECIFICATION-form resolution never injects a synthetic `TyInlineNext`
// operator into the embedded source).
//
// PROOF CREDIT is capability-gated. [`certify_model`] promotes only when the
// certificate binds to the generated source AND committed configuration, the
// repository-pinned independent verifier reconstructs and kernel-checks its
// proof, and a replay-verified `Buggy = 1` counterexample breaks a committed
// invariant. Unsupported fragments remain fail-closed.
// ===========================================================================

/// The certificate schema tag this lane accepts (`first-party/ty`,
/// `tla-check/src/cert.rs::SCHEMA_V1`).
const TY_CERT_SCHEMA_V1: &str = "ty.cert/v1";

/// Local transport of the `ty.cert/v1` certificate. Only fields needed for
/// exact binding, fail-closed fragment selection, or audit are modeled here;
/// unknown proof-leg details remain in [`BoundTyCert::raw_json`]. A shared
/// trust-types transport type can replace this later.
#[derive(Debug, Clone, PartialEq, Eq, serde::Deserialize)]
pub struct TyCertV1 {
    /// Schema tag; must equal `ty.cert/v1`. Defaulted so an ABSENT tag is
    /// rejected as a schema mismatch (naming the binding), not a parse error.
    #[serde(default)]
    pub schema: String,
    /// The verdict ty certified (e.g. `inductive-safe`,
    /// `explicit-state-fixpoint-safe`).
    #[serde(default)]
    pub verdict: String,
    /// The FULL spec source the certificate is about (self-contained). Required:
    /// a cert without one cannot be bound to anything.
    pub spec_src: String,
    /// `INIT` / `NEXT` operator names ty resolved.
    #[serde(default)]
    pub init: Option<String>,
    #[serde(default)]
    pub next: Option<String>,
    /// Configured safety invariant names the certificate covers.
    #[serde(default)]
    pub invariants: Vec<String>,
    /// Configured constant bindings. These are part of the semantic input: the
    /// same module under `Buggy = 0` and `Buggy = 1` is not the same claim.
    #[serde(default)]
    pub constants: Vec<(String, TyConfigConstant)>,
    /// The proven inductive invariant `J`, as TLA+ text (empty in the
    /// explicit-state fixpoint lane).
    #[serde(default)]
    pub invariant_j_tla: String,
    /// `sha256` hex over the cert's canonical body. This producer-authored
    /// digest is retained for audit but is not trusted as a verdict; Trust
    /// independently binds the source/config and reconstructs the theorem.
    #[serde(default)]
    pub digest: String,
    /// Per-obligation proof transport retained for audit. The current closed
    /// Clean reconstruction does not trust these producer-authored fields.
    #[serde(default)]
    pub ay_proof_obligations: Vec<TyCertObligation>,
    /// Explicit reachable-set certificate from ty's alternative lane. Trust
    /// reparses the full object with the pinned verifier and reruns its
    /// reachable-set and Clean-kernel legs before promotion.
    #[serde(default)]
    pub explicit_fixpoint: Option<serde_json::Value>,
}

/// The configured-constant transport used by `ty.cert/v1`.
///
/// TWO producers write the `constants` field with DIFFERENT-but-disjoint JSON
/// encodings, and this one transport must decode both fail-closed:
///
///   * ty's `SafetyCertificate` (the explicit-fixpoint lane) writes its
///     `ConstantValue` enum in serde's default EXTERNALLY-TAGGED form —
///     `Value(s)` → `{"Value": s}`, the unit `ModelValue` → the bare string
///     `"ModelValue"`, `ModelValueSet(v)` → `{"ModelValueSet": v}`,
///     `Replacement(s)` → `{"Replacement": s}`;
///   * a clean-tla `ty.cert/v1` (the S4 finite-fragment lane) writes each
///     configured constant as a BARE JSON integer — `"constants": [["Buggy", 0]]`
///     — which the finite enumerator keys its exhaustive exploration on.
///
/// A bare number is neither a string (unit variant) nor a map (tagged variant),
/// so serde's derived externally-tagged `Deserialize` rejects it outright. The
/// hand-written impl below dispatches on the THREE disjoint JSON shapes
/// (number / string / object) instead: a number decodes to [`Int`], the bare
/// string `"ModelValue"` to the unit variant, and a single-key object to the
/// externally-tagged variant it names. Every pre-existing externally-tagged
/// encoding therefore decodes byte-identically, while the clean-tla bare-integer
/// wire form is now accepted. Unknown shapes/keys are refused (fail-closed) —
/// this is deliberately NOT `#[serde(untagged)]`, which would silently change
/// the wire format of the four ty variants.
///
/// [`Int`]: TyConfigConstant::Int
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TyConfigConstant {
    Value(String),
    ModelValue,
    ModelValueSet(Vec<String>),
    Replacement(String),
    /// A bare integer constant, as clean-tla `ty.cert/v1` writes it (the finite
    /// enumerator keys its exhaustive exploration on these values).
    Int(i64),
}

impl<'de> serde::Deserialize<'de> for TyConfigConstant {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        use serde::de::Error;
        // `ty.cert/v1` is always JSON, so collecting the self-describing value
        // and dispatching on its shape is exact. The three shapes are disjoint,
        // so the dispatch is deterministic and cannot conflate two producers.
        let value = serde_json::Value::deserialize(deserializer)?;
        match value {
            serde_json::Value::Number(number) => {
                number.as_i64().map(TyConfigConstant::Int).ok_or_else(|| {
                    D::Error::custom(format!("ty.cert constant `{number}` is not an i64"))
                })
            }
            serde_json::Value::String(tag) if tag == "ModelValue" => {
                Ok(TyConfigConstant::ModelValue)
            }
            serde_json::Value::String(tag) => Err(D::Error::custom(format!(
                "unknown ty.cert unit constant tag `{tag}` (expected `ModelValue`)"
            ))),
            serde_json::Value::Object(map) => {
                let mut entries = map.into_iter();
                let (key, payload) = entries
                    .next()
                    .ok_or_else(|| D::Error::custom("empty ty.cert constant object"))?;
                if entries.next().is_some() {
                    return Err(D::Error::custom(
                        "ty.cert constant object carries more than one variant tag",
                    ));
                }
                match key.as_str() {
                    "Value" => {
                        payload.as_str().map(|s| TyConfigConstant::Value(s.to_owned())).ok_or_else(
                            || D::Error::custom("ty.cert constant `Value` payload is not a string"),
                        )
                    }
                    "Replacement" => payload
                        .as_str()
                        .map(|s| TyConfigConstant::Replacement(s.to_owned()))
                        .ok_or_else(|| {
                            D::Error::custom(
                                "ty.cert constant `Replacement` payload is not a string",
                            )
                        }),
                    "ModelValueSet" => {
                        let array = payload.as_array().ok_or_else(|| {
                            D::Error::custom(
                                "ty.cert constant `ModelValueSet` payload is not an array",
                            )
                        })?;
                        let mut members = Vec::with_capacity(array.len());
                        for element in array {
                            members.push(
                                element
                                    .as_str()
                                    .ok_or_else(|| {
                                        D::Error::custom(
                                            "ty.cert constant `ModelValueSet` member is not a string",
                                        )
                                    })?
                                    .to_owned(),
                            );
                        }
                        Ok(TyConfigConstant::ModelValueSet(members))
                    }
                    other => Err(D::Error::custom(format!(
                        "unknown ty.cert constant variant tag `{other}`"
                    ))),
                }
            }
            other => Err(D::Error::custom(format!(
                "ty.cert constant has an unsupported JSON shape: {other}"
            ))),
        }
    }
}

/// Minimal obligation transport retained for audit compatibility.
#[derive(Debug, Clone, PartialEq, Eq, serde::Deserialize)]
pub struct TyCertObligation {
    pub name: String,
    #[serde(default)]
    pub clean_cic_term: Vec<u8>,
}

/// A parsed `ty.cert/v1` whose initial input bindings held: schema tag,
/// byte-exact `spec_src`, and expected invariant names. This becomes a
/// proof-bearing result only after configuration binding and independent Clean
/// kernel rechecking set [`BoundTyCert::kernel_rechecked`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BoundTyCert {
    /// The bound transport fields.
    pub cert: TyCertV1,
    /// The certificate exactly as ty wrote it (embedded proof legs included),
    /// consumed by independent reconstruction and retained for offline audit.
    pub raw_json: String,
    /// True only after clean-tla independently reconstructed the theorem and
    /// clean-kernel accepted its closed proof term in-process.
    pub kernel_rechecked: bool,
    /// Auditable verifier diagnostic (never parsed as the verdict).
    pub recheck_detail: String,
}

/// A structured `ty certify`-lane failure naming WHICH step or binding failed.
/// FAIL-CLOSED: every variant means "no certificate evidence"; none of them
/// falls back to the text-parse lane.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TyCertifyError {
    /// Pre-run setup failed (invalid model name, temp dir, spec/cfg write).
    Setup(String),
    /// The ty process could not be spawned.
    Spawn(String),
    /// ty ran but DECLINED to certify (non-zero exit; e.g. `NOT CERTIFIED`,
    /// spec outside the inductive-safety provable class, reachable deadlock).
    Declined { code: Option<i32>, output: String },
    /// ty exited 0 but the `--out` certificate file is missing or unreadable.
    MissingCertificate(String),
    /// The certificate is not parseable as `ty.cert/v1`-shaped JSON.
    MalformedJson(String),
    /// Parsed, but the schema tag is not `ty.cert/v1` (empty = absent).
    SchemaMismatch { found: String },
    /// `cert.spec_src` does not BYTE-match the generated TLA+ module — the
    /// certificate is not evidence about OUR model.
    SpecSrcMismatch { expected_len: usize, found_len: usize, first_divergence: usize },
    /// The certified invariant names differ from what the caller expected
    /// (order-insensitive comparison; both sides sorted).
    InvariantsMismatch { expected: Vec<String>, found: Vec<String> },
    /// INIT/NEXT or configured constants differ from the committed model.
    ConfigurationMismatch { expected: String, found: String },
    /// The certificate is accepted only by a non-kernel proof leg. It can be a
    /// useful lower grade, but never the Certified R5 lane.
    KernelFragmentNotClosed(String),
    /// Clean reconstructed a theorem only under a semantic approximation.
    SemanticFidelity(String),
    /// The independent Clean reconstruction or kernel check declined.
    KernelRecheckDeclined(String),
    /// The repository-owned verifier image changed during the evidence run.
    CheckerChanged,
}

impl std::fmt::Display for TyCertifyError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TyCertifyError::Setup(e) => write!(f, "certify lane setup failed: {e}"),
            TyCertifyError::Spawn(e) => write!(f, "ty certify spawn failed: {e}"),
            TyCertifyError::Declined { code, output } => {
                write!(f, "ty certify declined (exit {code:?}): {output}")
            }
            TyCertifyError::MissingCertificate(e) => {
                write!(f, "ty certify exited 0 but the --out certificate is unreadable: {e}")
            }
            TyCertifyError::MalformedJson(e) => {
                write!(f, "certificate binding FAILED (parse): not valid ty.cert JSON: {e}")
            }
            TyCertifyError::SchemaMismatch { found } => write!(
                f,
                "certificate binding FAILED (schema): expected `{TY_CERT_SCHEMA_V1}`, found `{}`",
                if found.is_empty() { "(absent)" } else { found }
            ),
            TyCertifyError::SpecSrcMismatch { expected_len, found_len, first_divergence } => {
                write!(
                    f,
                    "certificate input binding FAILED (spec_src): the cert's embedded spec does \
                     not byte-match the generated TLA+ module (generated {expected_len} bytes, \
                     cert embeds {found_len} bytes, first divergence at byte {first_divergence})"
                )
            }
            TyCertifyError::InvariantsMismatch { expected, found } => write!(
                f,
                "certificate input binding FAILED (invariants): expected {expected:?}, the cert \
                 certifies {found:?}"
            ),
            TyCertifyError::ConfigurationMismatch { expected, found } => write!(
                f,
                "certificate input binding FAILED (configuration): expected {expected}; found {found}"
            ),
            TyCertifyError::KernelFragmentNotClosed(reason) => write!(
                f,
                "certificate is outside the fully kernel-closed temporal fragment: {reason}"
            ),
            TyCertifyError::SemanticFidelity(reason) => {
                write!(f, "Clean temporal reconstruction is not semantically exact: {reason}")
            }
            TyCertifyError::KernelRecheckDeclined(reason) => {
                write!(f, "independent Clean kernel recheck declined: {reason}")
            }
            TyCertifyError::CheckerChanged => {
                write!(f, "repository-owned ty executable changed during temporal certification")
            }
        }
    }
}

impl std::error::Error for TyCertifyError {}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ModelExprSort<'m> {
    Int,
    Bool,
    /// A function over the canonical `1..range` domain.
    Function(&'m str),
}

fn model_setup_error(detail: impl Into<String>) -> TyCertifyError {
    TyCertifyError::Setup(detail.into())
}

fn expect_model_expr_sort(
    found: ModelExprSort<'_>,
    expected: ModelExprSort<'_>,
    context: &str,
) -> Result<(), TyCertifyError> {
    if found == expected {
        Ok(())
    } else {
        Err(model_setup_error(format!("{context} has sort {found:?}, expected {expected:?}")))
    }
}

/// Sort-check one model expression with an explicit heap stack.
///
/// The walk is iterative (same depth-first, left-to-right node and
/// error-discovery order as the recursive original), so checking depth is
/// bounded by heap, not the Rust stack — this preflight is reachable from
/// decoded Clean input, whose nesting is capped only by the Clean lane's
/// decode-cost guard.
fn model_expr_sort<'m, S: AsRef<str>>(
    model: &'m Model<S>,
    expression: &'m Expr<S>,
    globals: &BTreeSet<&str>,
    bound: &mut Vec<&'m str>,
) -> Result<ModelExprSort<'m>, TyCertifyError> {
    use Expr as E;
    enum Task<'e, 'r, T> {
        Sort(&'e Expr<T>),
        /// Pop one computed sort and require it under the shared error shape.
        Expect(ModelExprSort<'r>, &'static str),
        /// Pop the two branch sorts of an `If` and require they agree.
        MatchIfArms,
        PushBinder(&'e str),
        PopBinder,
        Emit(ModelExprSort<'r>),
        /// The scheduled bound checks passed; the domain shape did not.
        FailComprehensionDomain,
    }

    let mut tasks: Vec<Task<'m, 'm, S>> = vec![Task::Sort(expression)];
    let mut sorts: Vec<ModelExprSort<'m>> = Vec::new();
    while let Some(task) = tasks.pop() {
        let expression = match task {
            Task::Expect(wanted, context) => {
                let found = sorts.pop().expect("a sort was scheduled before every Expect");
                expect_model_expr_sort(found, wanted, context)?;
                continue;
            }
            Task::MatchIfArms => {
                let else_sort = sorts.pop().expect("if scheduled both branch sorts");
                let then_sort = sorts.pop().expect("if scheduled both branch sorts");
                if then_sort != else_sort {
                    return Err(model_setup_error(format!(
                        "if branches have different sorts ({then_sort:?} and {else_sort:?})"
                    )));
                }
                sorts.push(then_sort);
                continue;
            }
            Task::PushBinder(index) => {
                bound.push(index);
                continue;
            }
            Task::PopBinder => {
                bound.pop();
                continue;
            }
            Task::Emit(sort) => {
                sorts.push(sort);
                continue;
            }
            Task::FailComprehensionDomain => {
                return Err(model_setup_error(
                    "function comprehension domain must be exactly `1..RangeConstant`",
                ));
            }
            Task::Sort(expression) => expression,
        };
        match expression {
            E::Int(_) => sorts.push(ModelExprSort::Int),
            E::Bool(_) => sorts.push(ModelExprSort::Bool),
            E::Var(name) => {
                let name = name.as_ref();
                if model.vars.iter().any(|variable| variable.name.as_ref() == name)
                    || bound.iter().any(|binder| *binder == name)
                {
                    sorts.push(ModelExprSort::Int);
                } else if let Some(variable) =
                    model.fn_vars.iter().find(|variable| variable.name.as_ref() == name)
                {
                    sorts.push(ModelExprSort::Function(variable.range.as_ref()));
                } else {
                    return Err(model_setup_error(format!(
                        "unknown state/bound variable `{name}` in model expression"
                    )));
                }
            }
            E::ConstRef(name) => {
                let name = name.as_ref();
                if model.consts.iter().any(|(constant, _)| constant.as_ref() == name) {
                    sorts.push(ModelExprSort::Int);
                } else {
                    return Err(model_setup_error(format!(
                        "unknown constant `{name}` in model expression"
                    )));
                }
            }
            E::Add(left, right) | E::Sub(left, right) => {
                tasks.push(Task::Emit(ModelExprSort::Int));
                tasks.push(Task::Expect(ModelExprSort::Int, "arithmetic rhs"));
                tasks.push(Task::Sort(right));
                tasks.push(Task::Expect(ModelExprSort::Int, "arithmetic lhs"));
                tasks.push(Task::Sort(left));
            }
            E::Gt(left, right) | E::Le(left, right) | E::Eq(left, right) | E::Neq(left, right) => {
                tasks.push(Task::Emit(ModelExprSort::Bool));
                tasks.push(Task::Expect(ModelExprSort::Int, "comparison rhs"));
                tasks.push(Task::Sort(right));
                tasks.push(Task::Expect(ModelExprSort::Int, "comparison lhs"));
                tasks.push(Task::Sort(left));
            }
            E::Or(left, right) | E::And(left, right) | E::Iff(left, right) => {
                tasks.push(Task::Emit(ModelExprSort::Bool));
                tasks.push(Task::Expect(ModelExprSort::Bool, "Boolean expression rhs"));
                tasks.push(Task::Sort(right));
                tasks.push(Task::Expect(ModelExprSort::Bool, "Boolean expression lhs"));
                tasks.push(Task::Sort(left));
            }
            E::If(condition, then_value, else_value) => {
                tasks.push(Task::MatchIfArms);
                tasks.push(Task::Sort(else_value));
                tasks.push(Task::Sort(then_value));
                tasks.push(Task::Expect(ModelExprSort::Bool, "if condition"));
                tasks.push(Task::Sort(condition));
            }
            E::Forall(index, low, high, body) => {
                let index = index.as_ref();
                validate_temporal_identifier(index, "quantifier index")
                    .map_err(model_setup_error)?;
                if globals.contains(index) || bound.iter().any(|binder| *binder == index) {
                    return Err(model_setup_error(format!(
                        "quantifier index `{index}` shadows another model identifier"
                    )));
                }
                tasks.push(Task::Emit(ModelExprSort::Bool));
                tasks.push(Task::Expect(ModelExprSort::Bool, "forall body"));
                tasks.push(Task::PopBinder);
                tasks.push(Task::Sort(body));
                tasks.push(Task::PushBinder(index));
                tasks.push(Task::Expect(ModelExprSort::Int, "forall upper bound"));
                tasks.push(Task::Sort(high));
                tasks.push(Task::Expect(ModelExprSort::Int, "forall lower bound"));
                tasks.push(Task::Sort(low));
            }
            E::FnAccess(function, index) => {
                let function = function.as_ref();
                if !model.fn_vars.iter().any(|variable| variable.name.as_ref() == function) {
                    return Err(model_setup_error(format!(
                        "function access names unknown function variable `{function}`"
                    )));
                }
                tasks.push(Task::Emit(ModelExprSort::Bool));
                tasks.push(Task::Expect(ModelExprSort::Int, "function index"));
                tasks.push(Task::Sort(index));
            }
            E::Except(function, index, value) => {
                let function = function.as_ref();
                let variable = model
                    .fn_vars
                    .iter()
                    .find(|variable| variable.name.as_ref() == function)
                    .ok_or_else(|| {
                        model_setup_error(format!(
                            "EXCEPT names unknown function variable `{function}`"
                        ))
                    })?;
                tasks.push(Task::Emit(ModelExprSort::Function(variable.range.as_ref())));
                tasks.push(Task::Expect(ModelExprSort::Bool, "EXCEPT value"));
                tasks.push(Task::Sort(value));
                tasks.push(Task::Expect(ModelExprSort::Int, "EXCEPT index"));
                tasks.push(Task::Sort(index));
            }
            E::Comprehension(index, low, high, body) => {
                let index = index.as_ref();
                validate_temporal_identifier(index, "comprehension index")
                    .map_err(model_setup_error)?;
                if globals.contains(index) || bound.iter().any(|binder| *binder == index) {
                    return Err(model_setup_error(format!(
                        "comprehension index `{index}` shadows another model identifier"
                    )));
                }
                // The domain-shape decision is knowable now, but the original
                // recursion reports it only AFTER both bound sorts checked out —
                // schedule the matching outcome in that exact position.
                if let (E::Int(1), E::ConstRef(range)) = (&**low, &**high) {
                    tasks.push(Task::Emit(ModelExprSort::Function(range.as_ref())));
                    tasks.push(Task::Expect(ModelExprSort::Bool, "function comprehension body"));
                    tasks.push(Task::PopBinder);
                    tasks.push(Task::Sort(body));
                    tasks.push(Task::PushBinder(index));
                } else {
                    tasks.push(Task::FailComprehensionDomain);
                }
                tasks.push(Task::Expect(ModelExprSort::Int, "comprehension upper bound"));
                tasks.push(Task::Sort(high));
                tasks.push(Task::Expect(ModelExprSort::Int, "comprehension lower bound"));
                tasks.push(Task::Sort(low));
            }
        }
    }
    Ok(sorts.pop().expect("iterative sort checking produced exactly one root sort"))
}

/// Validate the public legacy [`Model`] carrier before it is rendered, checked,
/// replay-bound, or projected into Clean's finite manifest.
///
/// `Model` is intentionally constructible for compatibility, so macro parsing
/// is not an admission boundary. This shared preflight rejects ambiguous TLA+
/// namespaces, dangling references, ill-sorted expressions, malformed finite
/// function domains, and duplicate/unknown action targets before any backend
/// can assign them divergent meanings.
pub(crate) fn validate_model_for_certification<'m, S: AsRef<str>>(
    model: &'m Model<S>,
) -> Result<(), TyCertifyError> {
    validate_temporal_identifier(model.name.as_ref(), "model").map_err(model_setup_error)?;
    if model.vars.is_empty() && model.fn_vars.is_empty() {
        return Err(model_setup_error(
            "a certifiable model needs at least one scalar or function-valued state variable",
        ));
    }
    if model.actions.is_empty() {
        return Err(model_setup_error("a certifiable model needs at least one action"));
    }
    if model.invariants.is_empty() {
        return Err(model_setup_error("a certifiable model needs at least one invariant"));
    }

    let mut globals: BTreeSet<&'m str> = BTreeSet::from(["Init", "Next", "Spec", "vars"]);
    let mut register = |name: &'m str, role: &str| -> Result<(), TyCertifyError> {
        validate_temporal_identifier(name, role).map_err(model_setup_error)?;
        if !globals.insert(name) {
            return Err(model_setup_error(format!("duplicate or reserved {role} name `{name}`")));
        }
        Ok(())
    };
    for (name, _) in &model.consts {
        register(name.as_ref(), "constant")?;
    }
    for variable in &model.vars {
        register(variable.name.as_ref(), "variable")?;
    }
    for variable in &model.fn_vars {
        register(variable.name.as_ref(), "function variable")?;
    }
    for action in &model.actions {
        register(action.name.as_ref(), "action")?;
    }
    for invariant in &model.invariants {
        register(invariant.name.as_ref(), "invariant")?;
    }
    drop(register);

    for variable in &model.fn_vars {
        let variable_name = variable.name.as_ref();
        let variable_range = variable.range.as_ref();
        let mut ranges = model
            .consts
            .iter()
            .filter_map(|(name, value)| (name.as_ref() == variable_range).then_some(*value));
        let range = ranges.next().ok_or_else(|| {
            model_setup_error(format!(
                "function variable `{variable_name}` names missing range constant \
                 `{variable_range}`"
            ))
        })?;
        if ranges.next().is_some() {
            return Err(model_setup_error(format!(
                "function variable `{variable_name}` range constant `{variable_range}` is not \
                 unique"
            )));
        }
        if range <= 0 {
            return Err(model_setup_error(format!(
                "function variable `{variable_name}` range constant `{variable_range}` must be \
                 positive, found {range}"
            )));
        }
    }

    for action in &model.actions {
        let action_name = action.name.as_ref();
        if let Some(guard) = &action.guard {
            expect_model_expr_sort(
                model_expr_sort(model, guard, &globals, &mut Vec::new())?,
                ModelExprSort::Bool,
                &format!("action `{action_name}` guard"),
            )?;
        }
        let mut updated = BTreeSet::new();
        for update in &action.updates {
            let update_var = update.var.as_ref();
            if !updated.insert(update_var) {
                return Err(model_setup_error(format!(
                    "action `{action_name}` updates `{update_var}` more than once"
                )));
            }
            let expected = if model.vars.iter().any(|variable| variable.name.as_ref() == update_var)
            {
                ModelExprSort::Int
            } else if let Some(variable) =
                model.fn_vars.iter().find(|variable| variable.name.as_ref() == update_var)
            {
                ModelExprSort::Function(variable.range.as_ref())
            } else {
                return Err(model_setup_error(format!(
                    "action `{action_name}` updates unknown variable `{update_var}`"
                )));
            };
            expect_model_expr_sort(
                model_expr_sort(model, &update.expr, &globals, &mut Vec::new())?,
                expected,
                &format!("action `{action_name}` update of `{update_var}`"),
            )?;
        }
    }
    for invariant in &model.invariants {
        expect_model_expr_sort(
            model_expr_sort(model, &invariant.expr, &globals, &mut Vec::new())?,
            ModelExprSort::Bool,
            &format!("invariant `{}`", invariant.name.as_ref()),
        )?;
    }
    Ok(())
}

/// Run `ty certify <spec> --config <cfg> --out <spec stem>.cert.json`, then
/// parse the emitted certificate and BIND it to the inputs: `ty.cert/v1`
/// schema, byte-exact `expected_spec_src`, and `expected_invariants` names.
/// Returns the bound certificate or the structured failure — never a silent
/// fallback to the text-parse lane. Grants NO proof credit by itself.
#[cfg(test)]
fn run_ty_certify(
    ty: &Path,
    spec: &Path,
    cfg: &Path,
    expected_spec_src: &str,
    expected_invariants: &[&str],
) -> Result<BoundTyCert, TyCertifyError> {
    let cert_path = spec.with_extension("cert.json");
    let out = Command::new(ty)
        .arg("certify")
        .arg(spec)
        .arg("--config")
        .arg(cfg)
        .arg("--out")
        .arg(&cert_path)
        .output()
        .map_err(|e| TyCertifyError::Spawn(e.to_string()))?;
    if !out.status.success() {
        return Err(TyCertifyError::Declined {
            code: out.status.code(),
            output: format!(
                "{}{}",
                String::from_utf8_lossy(&out.stdout),
                String::from_utf8_lossy(&out.stderr)
            )
            .trim()
            .to_string(),
        });
    }
    let raw_json = std::fs::read_to_string(&cert_path)
        .map_err(|e| TyCertifyError::MissingCertificate(format!("{}: {e}", cert_path.display())))?;
    parse_and_bind_ty_cert(&raw_json, expected_spec_src, expected_invariants)
}

/// The pure parse + input-binding half of [`run_ty_certify`] (separated so the
/// binding checks are unit-testable without any ty process). Checks run in
/// order — parse, schema tag, `spec_src` byte-match, invariant names — and the
/// FIRST failure is returned, naming its binding.
fn parse_and_bind_ty_cert(
    raw_json: &str,
    expected_spec_src: &str,
    expected_invariants: &[&str],
) -> Result<BoundTyCert, TyCertifyError> {
    let cert: TyCertV1 =
        serde_json::from_str(raw_json).map_err(|e| TyCertifyError::MalformedJson(e.to_string()))?;
    if cert.schema != TY_CERT_SCHEMA_V1 {
        return Err(TyCertifyError::SchemaMismatch { found: cert.schema });
    }
    if cert.spec_src != expected_spec_src {
        let first_divergence = cert
            .spec_src
            .bytes()
            .zip(expected_spec_src.bytes())
            .position(|(a, b)| a != b)
            .unwrap_or_else(|| cert.spec_src.len().min(expected_spec_src.len()));
        return Err(TyCertifyError::SpecSrcMismatch {
            expected_len: expected_spec_src.len(),
            found_len: cert.spec_src.len(),
            first_divergence,
        });
    }
    let mut expected: Vec<String> = expected_invariants.iter().map(|s| s.to_string()).collect();
    let mut found = cert.invariants.clone();
    expected.sort();
    found.sort();
    if expected != found {
        return Err(TyCertifyError::InvariantsMismatch { expected, found });
    }
    Ok(BoundTyCert {
        cert,
        raw_json: raw_json.to_string(),
        kernel_rechecked: false,
        recheck_detail: String::new(),
    })
}

/// Bind the certificate's semantic configuration, not merely its module text.
/// TLA+ constants live in the `.cfg`; omitting this check would let a
/// certificate for `Buggy = 1` masquerade as evidence for `Buggy = 0` (or vice
/// versa) while `spec_src` remained byte-identical.
fn bind_model_configuration<S: AsRef<str>>(
    bound: &BoundTyCert,
    model: &Model<S>,
) -> Result<(), TyCertifyError> {
    let expected_init = Some("Init".to_string());
    let expected_next = Some("Next".to_string());
    if bound.cert.init != expected_init || bound.cert.next != expected_next {
        return Err(TyCertifyError::ConfigurationMismatch {
            expected: "INIT Init; NEXT Next".into(),
            found: format!("INIT {:?}; NEXT {:?}", bound.cert.init, bound.cert.next),
        });
    }

    // The committed model constants are always integers. A certificate may
    // encode them either as ty's externally-tagged `Value("<int>")` (the
    // explicit-fixpoint lane) or as clean-tla's bare `Int(<int>)` (the finite
    // lane); both denote the same integer, so bind on the integer VALUE, not on
    // the wire representation. This preserves the `Buggy = 1` masquerade guard
    // in either encoding.
    let mut expected: Vec<(String, i64)> =
        model.consts.iter().map(|(name, value)| (name.as_ref().to_string(), *value)).collect();
    let mut found = bound.cert.constants.clone();
    expected.sort_by(|a, b| a.0.cmp(&b.0));
    found.sort_by(|a, b| a.0.cmp(&b.0));
    let bound_matches = expected.len() == found.len()
        && expected.iter().zip(found.iter()).all(
            |((expected_name, expected_int), (found_name, found_value))| {
                expected_name == found_name
                    && config_constant_denotes_int(found_value, *expected_int)
            },
        );
    if !bound_matches {
        return Err(TyCertifyError::ConfigurationMismatch {
            expected: format!("constants {expected:?}"),
            found: format!("constants {found:?}"),
        });
    }
    Ok(())
}

/// Whether the model needs the Clean finite-product reconstruction rather than
/// the legacy one-scalar explicit-fixpoint lane.
///
/// A function-valued variable is a product even when it is the only declared
/// variable: its `[1..N -> BOOLEAN]` domain flattens to one Bool slot per key.
/// Route that shape explicitly instead of keying only on declaration count.
fn model_uses_clean_finite_product<S>(model: &Model<S>) -> bool {
    !model.fn_vars.is_empty() || model.vars.len() + model.fn_vars.len() > 1
}

fn clean_function_sort_is_supported(sort: &str) -> bool {
    let Some(inner) = sort.trim().strip_prefix('[').and_then(|sort| sort.strip_suffix(']')) else {
        return false;
    };
    let Some((domain, range)) = inner.split_once("->") else {
        return false;
    };
    if domain.contains("->") || range.trim() != "BOOLEAN" {
        return false;
    }
    let Some((low, high)) = domain.trim().split_once("..") else {
        return false;
    };
    let supported_bound = |bound: &str| {
        let bound = bound.trim();
        bound.parse::<i64>().is_ok()
            || (valid_tla_identifier(bound)
                && !clean_model_lane::TLA_RESERVED_IDENTIFIER_TOKENS.contains(&bound))
    };
    !high.contains("..") && supported_bound(low) && supported_bound(high)
}

fn clean_recheck_needs_finite_product(
    cert: &clean_tla::ty_cert::TyCert,
) -> Result<bool, TyCertifyError> {
    if cert.var_sorts.is_empty() {
        return Err(TyCertifyError::KernelRecheckDeclined(
            "Clean state-sort manifest is empty".to_owned(),
        ));
    }
    let mut names = BTreeSet::new();
    let mut has_function = false;
    for (name, sort) in &cert.var_sorts {
        if !names.insert(name.as_str()) {
            return Err(TyCertifyError::KernelRecheckDeclined(format!(
                "Clean state-sort manifest repeats variable `{name}`"
            )));
        }
        match sort.trim() {
            "Int" | "Nat" => {}
            sort if clean_function_sort_is_supported(sort) => has_function = true,
            unsupported => {
                return Err(TyCertifyError::KernelRecheckDeclined(format!(
                    "unsupported Clean state sort `{unsupported}` for `{name}`; expected `Int`, \
                     `Nat`, or `[lo..hi -> BOOLEAN]`"
                )));
            }
        }
    }
    Ok(has_function || cert.var_sorts.len() > 1)
}

/// Project an already source/config-bound TY certificate into Clean's read-only
/// finite re-encoder carrier.
///
/// The producer JSON stays byte-for-byte untouched in [`BoundTyCert::raw_json`]
/// (including its digest, explicit-fixpoint proof, and tagged constants). This
/// separate in-memory projection adds only the state-sort manifest the S4
/// product needs and translates the *already bound* committed constants to
/// Clean's integer carrier. It is not producer evidence and grants no credit by
/// itself; [`recheck_model_bound_clean_kernel`] first verifies the original TY
/// object, then Clean reconstructs and kernel-closes the stronger theorem from
/// this exact cross-bound projection.
fn clean_finite_projection<S: AsRef<str>>(
    bound: &BoundTyCert,
    model: &Model<S>,
) -> clean_tla::ty_cert::TyCert {
    let mut var_sorts = model
        .vars
        .iter()
        .map(|var| (var.name.as_ref().to_owned(), "Int".to_owned()))
        .collect::<Vec<_>>();
    var_sorts.extend(model.fn_vars.iter().map(|var| {
        (var.name.as_ref().to_owned(), format!("[1..{} -> BOOLEAN]", var.range.as_ref()))
    }));

    let mut constants = model
        .consts
        .iter()
        .map(|(name, value)| (name.as_ref().to_owned(), *value))
        .collect::<Vec<_>>();
    constants.sort_by(|left, right| left.0.cmp(&right.0));

    clean_tla::ty_cert::TyCert {
        schema: bound.cert.schema.clone(),
        verdict: bound.cert.verdict.clone(),
        spec_src: bound.cert.spec_src.clone(),
        init: bound.cert.init.clone(),
        next: bound.cert.next.clone(),
        invariants: bound.cert.invariants.clone(),
        invariant_j_tla: bound.cert.invariant_j_tla.clone(),
        var_sorts,
        constants,
        ay_proof_obligations: Vec::new(),
    }
}

/// Whether a certificate's configured constant denotes the integer `expected`,
/// in either producer's encoding (clean-tla `Int`, ty externally-tagged
/// `Value("<int>")`). Any other shape (a symbolic `ModelValue`, a set, a
/// replacement, or a non-integer `Value`) does NOT bind an integer constant.
fn config_constant_denotes_int(found: &TyConfigConstant, expected: i64) -> bool {
    match found {
        TyConfigConstant::Int(value) => *value == expected,
        TyConfigConstant::Value(value) => *value == expected.to_string(),
        TyConfigConstant::ModelValue
        | TyConfigConstant::ModelValueSet(_)
        | TyConfigConstant::Replacement(_) => false,
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum CompletenessAuthority {
    Shortcut,
    General,
}

fn matched_completeness_authority(
    obligation: &str,
    shortcut_descriptor: bool,
    shortcut_term: bool,
    general_descriptor: bool,
    general_term: bool,
) -> Result<CompletenessAuthority, String> {
    let shortcut_present = shortcut_descriptor || shortcut_term;
    let general_present = general_descriptor || general_term;
    if shortcut_present && general_present {
        return Err(format!(
            "finite explicit-fixpoint certificate has mixed {obligation} completeness families \
             (shortcut descriptor={shortcut_descriptor}, shortcut term={shortcut_term}, general \
             descriptor={general_descriptor}, general term={general_term})"
        ));
    }
    if shortcut_present {
        return if shortcut_descriptor && shortcut_term {
            Ok(CompletenessAuthority::Shortcut)
        } else {
            Err(format!(
                "finite explicit-fixpoint certificate has an incomplete {obligation} shortcut \
                 completeness pair (descriptor={shortcut_descriptor}, term={shortcut_term})"
            ))
        };
    }
    if general_present {
        return if general_descriptor && general_term {
            Ok(CompletenessAuthority::General)
        } else {
            Err(format!(
                "finite explicit-fixpoint certificate has an incomplete {obligation} general \
                 completeness pair (descriptor={general_descriptor}, term={general_term})"
            ))
        };
    }
    Err(format!(
        "enumerator-assisted finite explicit-fixpoint certificate is missing the {obligation} \
         completeness descriptor/term pair"
    ))
}

/// Require the proof shape that may back Trust's Certified temporal tier.
///
/// `tla-check` intentionally accepts older/weaker explicit-fixpoint objects
/// whose `Init` or `Next` completeness legs are absent: their concrete
/// membership terms are kernel checked, but exhaustiveness still rests on the
/// state enumerator. Its aggregate `kernel_recheck` bit therefore cannot, by
/// itself, authorize a Certified Trust result. Both public evidence import and
/// the legacy `ModelVerdict::Proved` bridge call this one gate.
fn certified_explicit_fixpoint_authority(
    certificate: &tla_check::cert::SafetyCertificate,
) -> Result<String, String> {
    let fixpoint = certificate.explicit_fixpoint.as_ref().ok_or_else(|| {
        "Certified safety requires an explicit-fixpoint kernel certificate".to_owned()
    })?;

    if fixpoint.unbounded_invariant.is_some() {
        // The verifier subsequently checks mutual exclusion from every finite
        // field, re-binds the recognized shape to spec_src, and kernel-checks
        // initiation, consecution, and preservation at rebuilt types.
        return Ok(
            "unbounded invariant authority: initiation, consecution, and preservation must all \
             recheck in the Clean kernel"
                .to_owned(),
        );
    }

    let next = matched_completeness_authority(
        "Next",
        fixpoint.next_shape.is_some(),
        fixpoint.next_completeness.is_some(),
        fixpoint.next_pred.is_some(),
        fixpoint.next_general_completeness.is_some(),
    )?;
    let init = matched_completeness_authority(
        "Init",
        fixpoint.init_shape.is_some(),
        fixpoint.init_completeness.is_some(),
        fixpoint.init_pred.is_some(),
        fixpoint.init_general_completeness.is_some(),
    )?;

    // A general completeness proof is only as exhaustive as the product
    // domain over which it was reduced. Require every such axis to cover its
    // universe by construction or carry a kernel-proven bound; a Rust-derived
    // heuristic bound is not Certified authority. The scalar shortcut is an
    // explicit exception: its small affine/literal recognizer and bound rule
    // remain part of the pinned semantic-adapter TCB, and the kernel still
    // re-evaluates the exact recognized predicate over that whole domain.
    let coverage = tla_check::explicit_fixpoint_cert::domain_coverage_of_cert(fixpoint);
    if next == CompletenessAuthority::General && !coverage.next_rust_columns.is_empty() {
        return Err(format!(
            "general Next completeness still relies on Rust-derived domain bounds for columns {:?}",
            coverage.next_rust_columns
        ));
    }
    if init == CompletenessAuthority::General && !coverage.init_rust_columns.is_empty() {
        return Err(format!(
            "general Init completeness still relies on Rust-derived domain bounds for columns {:?}",
            coverage.init_rust_columns
        ));
    }

    let shortcut_tcb = if matches!(next, CompletenessAuthority::Shortcut)
        || matches!(init, CompletenessAuthority::Shortcut)
    {
        "; scalar affine/literal shortcut recognition remains in the pinned tla-check adapter TCB"
    } else {
        "; all general product-domain axes are universe-complete or kernel-proven"
    };
    Ok(format!(
        "complete finite authority: matched Init {init:?} and Next {next:?} completeness pairs\
         {shortcut_tcb}"
    ))
}

/// Independently reconstruct the certificate's temporal theorem with
/// `clean-tla`, then re-run `clean-kernel` on the stored proof term. This code
/// does not call ty and never interprets producer stdout as a proof verdict.
///
/// The Clean bridge has two disjoint, fail-closed shapes: the legacy one-scalar
/// closed `x >= 0` family, and the S4 finite product for cfg-bounded scalar /
/// finite-function machines. The scalar adapter's documented Int-to-Nat
/// approximation is rejected here; the finite product instead requires dual
/// Int/Nat agreement on every explored operation. Only a fidelity-exact
/// reconstruction can receive R5 credit.
fn recheck_bound_clean_kernel(bound: &mut BoundTyCert) -> Result<(), TyCertifyError> {
    // A recheck is a fresh authority decision. Never let a refusal retain an
    // earlier caller-visible success bit or diagnostic.
    bound.kernel_rechecked = false;
    bound.recheck_detail.clear();
    let _ty_transaction = in_process_ty_transaction_lock();
    if bound.cert.explicit_fixpoint.is_some() {
        // `clean-tla::ty_cert` is the scalar inductive-certificate adapter; it
        // predates ty's broader explicit-state proof.  Do not reject the newer
        // proof merely because that older adapter cannot decode it.  The
        // repository-pinned `tla-check` verifier independently re-parses the
        // embedded spec, re-derives its proof object, and re-runs the Clean
        // kernel on its stored terms. Trust additionally requires unbounded
        // invariant authority or complete Init/Next finite completeness pairs;
        // `Accepted + kernel_recheck` alone also describes the weaker,
        // enumerator-assisted tier and is not enough for Certified credit.
        let cert = tla_check::cert::SafetyCertificate::from_json(&bound.raw_json)
            .map_err(TyCertifyError::KernelRecheckDeclined)?;
        let authority = certified_explicit_fixpoint_authority(&cert)
            .map_err(TyCertifyError::KernelFragmentNotClosed)?;
        let report = tla_check::cert::verify_safety_certificate(&cert);
        if !matches!(report.verdict, tla_check::cert::CertVerdict::Accepted)
            || report.kernel_recheck != Some(true)
        {
            return Err(TyCertifyError::KernelRecheckDeclined(report.detail));
        }
        bound.kernel_rechecked = true;
        bound.recheck_detail = format!(
            "{authority}; tla-check re-derived the explicit fixpoint from spec_src and Clean-kernel \
             rechecked every authoritative leg: {}",
            report.detail,
        );
        return Ok(());
    }

    let cert = clean_tla::ty_cert::TyCert::from_json(&bound.raw_json)
        .map_err(TyCertifyError::KernelRecheckDeclined)?;

    // Dispatch by machine shape. A MULTI-VARIABLE machine (> 1 state variable),
    // or even one function-valued product variable, is outside the closed
    // scalar adapter's `sole_var : Int/Nat` fragment; route it to the landed S4
    // finite-fragment keystone (`clean_tla::finite`), which
    // reconstructs the whole cfg-bounded multi-variable machine from spec_src,
    // exhaustively explores it under dual Int/Nat semantics, and kernel-closes a
    // bare-conclusion theorem. The 1-variable scalar path below (the closed
    // `x >= 0`/Nat discharge) is unchanged — it is a strictly weaker discharge
    // and is NEVER substituted for a multi-variable finite certificate, so no
    // finite cert is silently downgraded to it.
    let needs_finite_product = clean_recheck_needs_finite_product(&cert)?;
    if needs_finite_product {
        return recheck_bound_clean_kernel_finite(bound, &cert);
    }

    let fidelity = cert.fidelity_notes();
    if !fidelity.is_empty() {
        return Err(TyCertifyError::SemanticFidelity(fidelity.join("; ")));
    }
    let encoded =
        clean_tla::ty_cert::encode_cert(&cert).map_err(TyCertifyError::KernelRecheckDeclined)?;
    let mut env = clean_kernel::env::Environment::with_prelude();
    const THEOREM: &str = "TrustTemporalBoundSafetyClosed";
    clean_tla::ty_cert::register_ty_cert_safety_closed(&mut env, THEOREM, &encoded)
        .map_err(TyCertifyError::KernelRecheckDeclined)?;

    let name = clean_kernel::name::Name::from_string(THEOREM);
    let declaration = env.get_const(&name).ok_or_else(|| {
        TyCertifyError::KernelRecheckDeclined("closed theorem was not registered".into())
    })?;
    let value = declaration.value.as_ref().ok_or_else(|| {
        TyCertifyError::KernelRecheckDeclined("closed theorem has no proof term".into())
    })?;
    let checker = clean_kernel::tc::TypeChecker::with_mode(&env, env.mode());
    checker
        .check_type(value, &declaration.type_)
        .map_err(|error| TyCertifyError::KernelRecheckDeclined(error.to_string()))?;
    let quality = env.proof_quality(&name).ok_or_else(|| {
        TyCertifyError::KernelRecheckDeclined("closed theorem proof quality was unavailable".into())
    })?;
    if quality != clean_kernel::env::ProofQuality::Constructive {
        return Err(TyCertifyError::KernelRecheckDeclined(format!(
            "closed theorem quality is {quality:?}, not Constructive"
        )));
    }
    let axioms = env.axiom_deps(&name).ok_or_else(|| {
        TyCertifyError::KernelRecheckDeclined("closed theorem axiom closure was unavailable".into())
    })?;
    if axioms.iter().any(|axiom| {
        let name = axiom.to_string();
        name.contains("sorry") || name.contains("Sorry") || name.contains("trusted")
    }) {
        return Err(TyCertifyError::KernelRecheckDeclined(format!(
            "closed theorem has forbidden axiom closure {axioms:?}"
        )));
    }

    bound.kernel_rechecked = true;
    bound.recheck_detail =
        "clean-tla reconstructed spec_src; clean-kernel accepted a Constructive closed theorem"
            .into();
    Ok(())
}

/// The finite product's registered theorem name. Distinct from the closed
/// path's `TrustTemporalBoundSafetyClosed` so a single environment could carry
/// both without a squat.
const FINITE_THEOREM: &str = "TrustTemporalBoundSafetyFinite";

/// Route a MULTI-VARIABLE bounded machine to the landed S4 finite-fragment
/// keystone ([`clean_tla::finite::register_ty_cert_safety_finite`]).
///
/// The keystone reconstructs the whole cfg-bounded multi-variable machine from
/// the certificate's OWN `spec_src` (source fidelity — not from any producer-
/// authored proof term), explores its reachable state space exhaustively under
/// dual Int/Nat semantics, and atomically registers a four-declaration,
/// kernel-checked product whose bare conclusion is `∀ b, Runs Init Next b →
/// Sat b (□ Safety)`.
///
/// FAIL-CLOSED: every keystone refusal — `NameCollision`,
/// `StateSpaceBoundExceeded`, `TruncationDivergence`, `Fragment`,
/// `VocabularySquatted`, `Falsified`, `MissingPrelude`, … — maps to a declined
/// recheck. The caller ([`certify_model`]) turns that into
/// [`ModelVerdict::Unknown`]; it is NEVER a certificate. The final promotion
/// is additionally guarded by the LOAD-BEARING anti-forgery gate in
/// [`finite_theorem_kernel_gate`].
fn recheck_bound_clean_kernel_finite(
    bound: &mut BoundTyCert,
    cert: &clean_tla::ty_cert::TyCert,
) -> Result<(), TyCertifyError> {
    bound.kernel_rechecked = false;
    bound.recheck_detail.clear();
    let mut env = clean_kernel::env::Environment::with_prelude();

    // Reconstruct + explore + kernel-close, all from the cert's spec_src. Any
    // keystone error is a fail-closed decline — no partial state escapes because
    // the keystone stages on an env clone and commits only on full success.
    let report = clean_tla::finite::register_ty_cert_safety_finite(&mut env, FINITE_THEOREM, cert)
        .map_err(|error| {
            TyCertifyError::KernelRecheckDeclined(format!(
                "clean-tla S4 finite keystone refused: {error}"
            ))
        })?;

    // LOAD-BEARING anti-forgery + kernel-acceptance gate. Recompute the expected
    // bare conclusion from the SAME certificate we registered from and α-compare
    // it to the type the kernel actually holds; then recheck the proof term,
    // require Constructive, and reject any sorry/trusted axiom closure. A
    // mismatch REFUSES — the registered declaration is never trusted by name.
    finite_theorem_kernel_gate(&env, FINITE_THEOREM, cert)?;

    bound.kernel_rechecked = true;
    bound.recheck_detail = format!(
        "clean-tla S4 finite keystone reconstructed a {}-slot multi-variable machine from \
         spec_src and exhaustively explored {} reachable state(s) ({} Bool leaves) under dual \
         Int/Nat semantics; clean-kernel accepted a Constructive bare-conclusion theorem whose \
         type α-matches the independently recomputed conclusion_ty; honest fidelity: {}",
        report.manifest.len(),
        report.reachable_states,
        report.check_leaf_count,
        if report.fidelity_notes.is_empty() {
            "(none)".to_string()
        } else {
            report.fidelity_notes.join(" | ")
        },
    );
    Ok(())
}

/// The finite lane's anti-forgery + kernel-acceptance gate. LOAD-BEARING.
///
/// It does NOT trust the keystone's returned declaration by name. Instead it:
///
/// 1. fetches the theorem registered under `thm_name`;
/// 2. INDEPENDENTLY recomputes the expected bare conclusion from
///    `expected_cert`'s own source (`from_cert → explore → encode_finite →
///    conclusion_ty`), reading nothing off the registered declaration;
/// 3. α-compares the fetched type to the recomputed conclusion. `clean-kernel`
///    `Expr` is de-Bruijn, so structural `==` IS α-equality. A mismatch REFUSES
///    — this rejects the `_assumed` product (extra leading Pi-hypotheses), a
///    name-squatted declaration of any other statement, and any wrong-statement
///    mint. `ProofQuality::Constructive` alone does NOT discriminate these; the
///    TYPE is the only sound discriminator;
/// 4. rechecks the stored proof term against its declared type in-kernel,
///    requires `ProofQuality::Constructive`, and rejects any `sorry`/`trusted`
///    axiom closure.
///
/// In production `expected_cert` is the certificate the theorem was registered
/// from, so an honest finite product passes step 3 by construction; the gate
/// catches a keystone that ever registered a different statement under the
/// product name.
fn finite_theorem_kernel_gate(
    env: &clean_kernel::env::Environment,
    thm_name: &str,
    expected_cert: &clean_tla::ty_cert::TyCert,
) -> Result<(), TyCertifyError> {
    let name = clean_kernel::name::Name::from_string(thm_name);
    let declaration = env.get_const(&name).ok_or_else(|| {
        TyCertifyError::KernelRecheckDeclined(
            "finite theorem was not registered under its product name".into(),
        )
    })?;

    // Independent recompute of the expected bare conclusion from source.
    let machine = clean_tla::finite::FiniteMachine::from_cert(expected_cert).map_err(|error| {
        TyCertifyError::KernelRecheckDeclined(format!(
            "anti-forgery recompute failed (from_cert): {error}"
        ))
    })?;
    let explored = machine.explore().map_err(|error| {
        TyCertifyError::KernelRecheckDeclined(format!(
            "anti-forgery recompute failed (explore): {error}"
        ))
    })?;
    let enc = clean_tla::finite::encode_finite(&machine, &explored, thm_name).map_err(|error| {
        TyCertifyError::KernelRecheckDeclined(format!(
            "anti-forgery recompute failed (encode): {error}"
        ))
    })?;
    let expected_conclusion = clean_tla::ty_cert::conclusion_ty(&enc.init, &enc.next, &enc.safety);

    // THE anti-forgery α-exact refusal.
    if declaration.type_ != expected_conclusion {
        return Err(TyCertifyError::KernelRecheckDeclined(
            "registered finite theorem type does NOT α-match the independently recomputed bare \
             conclusion (anti-forgery refusal): refusing to trust the registered declaration by \
             name"
                .into(),
        ));
    }

    // Kernel acceptance of the stored proof term against its declared type.
    let value = declaration.value.as_ref().ok_or_else(|| {
        TyCertifyError::KernelRecheckDeclined("finite theorem has no proof term".into())
    })?;
    let checker = clean_kernel::tc::TypeChecker::with_mode(env, env.mode());
    checker
        .check_type(value, &declaration.type_)
        .map_err(|error| TyCertifyError::KernelRecheckDeclined(error.to_string()))?;
    let quality = env.proof_quality(&name).ok_or_else(|| {
        TyCertifyError::KernelRecheckDeclined("finite theorem proof quality was unavailable".into())
    })?;
    if quality != clean_kernel::env::ProofQuality::Constructive {
        return Err(TyCertifyError::KernelRecheckDeclined(format!(
            "finite theorem quality is {quality:?}, not Constructive"
        )));
    }
    let axioms = env.axiom_deps(&name).ok_or_else(|| {
        TyCertifyError::KernelRecheckDeclined("finite theorem axiom closure was unavailable".into())
    })?;
    if axioms.iter().any(|axiom| {
        let axiom = axiom.to_string();
        axiom.contains("sorry") || axiom.contains("Sorry") || axiom.contains("trusted")
    }) {
        return Err(TyCertifyError::KernelRecheckDeclined(format!(
            "finite theorem has forbidden axiom closure {axioms:?}"
        )));
    }
    Ok(())
}

/// Recheck a real [`Model`]'s already-bound TY evidence with the authority
/// appropriate to its state shape.
///
/// Finite products retain TY's original, digest-sealed explicit-fixpoint object
/// as mandatory producer evidence. The pinned verifier must accept it and
/// recheck its stored kernel legs, even though its enumerator-assisted
/// completeness is not sufficient for Certified credit. Only then do we derive
/// the model-aware Clean projection and let S4 supply the stronger exhaustive,
/// kernel-closed authority. A malformed/tampered producer object never falls
/// through to Clean.
pub(crate) fn recheck_model_bound_clean_kernel<S: AsRef<str>>(
    bound: &mut BoundTyCert,
    model: &Model<S>,
) -> Result<(), TyCertifyError> {
    // This public-carrier seam is independently fail-closed even when the
    // caller reuses a previously accepted `BoundTyCert` allocation.
    bound.kernel_rechecked = false;
    bound.recheck_detail.clear();
    validate_model_for_certification(model)?;
    if !model_uses_clean_finite_product(model) {
        return recheck_bound_clean_kernel(bound);
    }

    let _ty_transaction = in_process_ty_transaction_lock();
    let expected_invariants =
        model.invariants.iter().map(|invariant| invariant.name.as_ref()).collect::<Vec<_>>();
    let rebound = parse_and_bind_ty_cert(&bound.raw_json, &model.to_tla(), &expected_invariants)?;
    bind_model_configuration(&rebound, model)?;
    if rebound.cert != bound.cert {
        return Err(TyCertifyError::KernelRecheckDeclined(
            "finite Model evidence no longer matches the previously bound TY transport".to_owned(),
        ));
    }

    let producer = tla_check::cert::SafetyCertificate::from_json(&bound.raw_json)
        .map_err(TyCertifyError::KernelRecheckDeclined)?;
    if producer.explicit_fixpoint.is_none() {
        return Err(TyCertifyError::KernelFragmentNotClosed(
            "finite Model projection requires the digest-sealed TY explicit-fixpoint producer object"
                .to_owned(),
        ));
    }
    let producer_report = tla_check::cert::verify_safety_certificate(&producer);
    if !matches!(producer_report.verdict, tla_check::cert::CertVerdict::Accepted)
        || !producer_report.digest_ok
        || producer_report.kernel_recheck != Some(true)
    {
        return Err(TyCertifyError::KernelRecheckDeclined(format!(
            "TY producer evidence failed before Clean finite projection: {}",
            producer_report.detail
        )));
    }

    let producer_authority = match certified_explicit_fixpoint_authority(&producer) {
        Ok(authority) => format!(
            "the TY producer independently also met Trust's Certified authority gate \
             ({authority})"
        ),
        Err(reason) => format!(
            "the TY producer did not independently supply Certified completeness authority \
             ({reason})"
        ),
    };

    let projection = clean_finite_projection(bound, model);
    recheck_bound_clean_kernel_finite(bound, &projection)?;
    let finite_detail = std::mem::take(&mut bound.recheck_detail);
    bound.recheck_detail = format!(
        "TY producer object retained byte-exact and independently accepted (digest_ok={}, \
         kernel_recheck=true); {producer_authority}; the exactly source/config/manifest-bound \
         Clean projection supplied finite-product Certified authority: {finite_detail}; producer \
         detail: {}",
        producer_report.digest_ok, producer_report.detail,
    );
    Ok(())
}

/// Outcome of the proof-bearing certify lane for one model.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CertifyOutcome {
    /// [`ModelVerdict::Proved`] means all certificate/kernel/non-vacuity gates
    /// passed. Every unsupported or incomplete case is non-Proved.
    pub verdict: ModelVerdict,
    /// The exactly-bound, kernel-rechecked certificate, or the structured gate
    /// failure. A successful value always has `kernel_rechecked == true`.
    pub bound: Result<BoundTyCert, TyCertifyError>,
    /// Result of the `Buggy = 1` falsification run, when certificate recheck got
    /// far enough to run it. `Some(Proved)` is the required mutation break;
    /// `None` means an earlier gate failed.
    pub non_vacuity: Option<ModelVerdict>,
}

/// Certify `m` through the honest R5 chain.
///
/// Promotion requires exact source/config binding, a fidelity-exact theorem
/// independently reconstructed by clean-tla and accepted in-process by
/// clean-kernel, exactly one committed `Buggy = 0` baseline, and a
/// counterexample under the preserved `Buggy = 1` mutant. Missing, duplicate,
/// or nonzero committed dials and unsupported Clean fragments fail closed,
/// never `Proved`.
pub fn certify_model<S: AsRef<str>>(m: &Model<S>) -> CertifyOutcome {
    let _ty_transaction = in_process_ty_transaction_lock();
    let (bound, non_vacuity) = match certify_model_candidate(m) {
        Ok((bound, non_vacuity)) => (Ok(bound), Some(non_vacuity)),
        Err(error) => (Err(error), None),
    };
    let verdict = match &non_vacuity {
        Some(ModelVerdict::Proved) => ModelVerdict::Proved,
        Some(ModelVerdict::Failed(invariant)) => ModelVerdict::Failed(invariant.clone()),
        Some(ModelVerdict::Vacuous) => ModelVerdict::Vacuous,
        Some(ModelVerdict::ProvedNoDial) => ModelVerdict::Unknown(
            "kernel certificate rechecked, but Certified temporal credit requires a Buggy non-vacuity dial"
                .into(),
        ),
        Some(ModelVerdict::Unknown(reason)) => ModelVerdict::Unknown(format!(
            "kernel certificate rechecked, but non-vacuity was inconclusive: {reason}"
        )),
        None => ModelVerdict::Unknown(format!(
            "ty certify lane: {}",
            bound.as_ref().unwrap_err()
        )),
    };
    CertifyOutcome { verdict, bound, non_vacuity }
}

pub(crate) fn validate_committed_buggy_values(
    values: impl IntoIterator<Item = i64>,
) -> Result<(), TyCertifyError> {
    let mut found = None;
    for value in values {
        if found.replace(value).is_some() {
            return Err(TyCertifyError::Setup(
                "committed `Buggy` constant must equal 0 and occur exactly once before certification or replay; found duplicates"
                    .to_owned(),
            ));
        }
    }
    match found {
        Some(0) => Ok(()),
        None => Err(TyCertifyError::Setup(
            "committed `Buggy` constant must equal 0 and occur exactly once before certification or replay; found none"
                .to_owned(),
        )),
        Some(value) => Err(TyCertifyError::Setup(format!(
            "committed `Buggy` constant must equal 0 and occur exactly once before certification or replay; found value {value}"
        ))),
    }
}

pub(crate) fn validate_committed_buggy_baseline<S: AsRef<str>>(
    m: &Model<S>,
) -> Result<(), TyCertifyError> {
    validate_committed_buggy_values(
        m.consts.iter().filter_map(|(name, value)| (name.as_ref() == "Buggy").then_some(*value)),
    )
}

fn certify_model_candidate<S: AsRef<str>>(
    m: &Model<S>,
) -> Result<(BoundTyCert, ModelVerdict), TyCertifyError> {
    let _ty_transaction = in_process_ty_transaction_lock();
    validate_committed_buggy_baseline(m)?;
    validate_model_for_certification(m)?;
    let tla_text = m.to_tla();
    let mut config = tla_check::Config::parse(&m.to_cfg())
        .map_err(|error| TyCertifyError::Setup(format!("generated cfg is invalid: {error:?}")))?;
    // `Model` always generates these two named operators.  Resolve the
    // SPECIFICATION form here before passing the config to certificate APIs,
    // exactly as the CLI does, while retaining the configured invariants and
    // constants as semantic inputs.
    config.init = Some("Init".to_owned());
    config.next = Some("Next".to_owned());

    // TY remains the mandatory producer for every Model shape. Preserve its
    // digest-sealed explicit-fixpoint object unchanged; the model-aware recheck
    // below either applies the established one-scalar authority gate or, for a
    // finite product, first verifies this producer object and then cross-binds
    // it into Clean's stronger S4 reconstruction.
    let fixpoint =
        tla_check::explicit_fixpoint_cert::certify_explicit_state_spec(&tla_text, &config)
            .ok_or_else(|| TyCertifyError::Declined {
                code: None,
                output: "the explicit-fixpoint certificate lane declined".to_owned(),
            })?;
    if !tla_check::explicit_fixpoint_cert::verify_explicit_state_cert(&fixpoint) {
        return Err(TyCertifyError::KernelRecheckDeclined(
            "fresh explicit-state certificate failed its mandatory kernel self-check".to_owned(),
        ));
    }
    let certificate =
        tla_check::cert::build_explicit_fixpoint_certificate(&tla_text, &config, fixpoint);
    let raw_json = certificate.to_json();
    let expected_invariants: Vec<&str> = m.invariants.iter().map(|i| i.name.as_ref()).collect();
    let mut bound = parse_and_bind_ty_cert(&raw_json, &tla_text, &expected_invariants)?;
    bind_model_configuration(&bound, m)?;
    recheck_model_bound_clean_kernel(&mut bound, m)?;
    let non_vacuity = recheck_buggy_counterexample(m)?;
    Ok((bound, non_vacuity))
}

/// Preserve the historical `Buggy = 1` mutation ratchet with proof-carrying
/// negative evidence.  The model checker finds a trace, but acceptance rests on
/// `ty.verdict/v1` replay: the verifier re-parses the exact embedded spec/config,
/// checks Init and every Next step, and confirms that the named invariant is
/// false at the final state.
fn recheck_buggy_counterexample<S: AsRef<str>>(
    m: &Model<S>,
) -> Result<ModelVerdict, TyCertifyError> {
    if !m.consts.iter().any(|(name, _)| name.as_ref() == "Buggy") {
        return Ok(ModelVerdict::ProvedNoDial);
    }
    let _ty_transaction = in_process_ty_transaction_lock();
    let spec_src = m.to_tla();
    let config_src = m.to_replay_cfg_with(&[("Buggy", 1)]);
    let config = tla_check::Config::parse(&config_src).map_err(|error| {
        TyCertifyError::Setup(format!("generated Buggy=1 cfg is invalid: {error:?}"))
    })?;
    let tree = tla_core::parse_to_syntax_tree(&spec_src);
    let module = tla_core::lower(tla_core::FileId(0), &tree).module.ok_or_else(|| {
        TyCertifyError::Setup("generated temporal module failed to lower".to_owned())
    })?;
    let result = tla_check::check_module(&module, &config);
    let envelope = tla_check::verdict::build_violation_envelope(
        &spec_src,
        Some(&config_src),
        &config,
        &result,
        tla_check::verdict::Completeness::Exhaustive,
        tla_check::verdict::ProducerIdentity::current(),
    )
    .ok_or_else(|| {
        TyCertifyError::KernelRecheckDeclined(format!(
            "Buggy=1 did not produce a replayable invariant violation: {result:?}"
        ))
    })?;
    let report = tla_check::verdict::verify_violation_envelope(&envelope);
    if !matches!(report.verdict, tla_check::verdict::VerdictVerdict::Verified) {
        return Err(TyCertifyError::KernelRecheckDeclined(format!(
            "Buggy=1 counterexample replay declined: {}",
            report.detail
        )));
    }
    if !matches!(envelope.kind, tla_check::verdict::ViolationKind::Invariant)
        || !envelope.violated.as_deref().is_some_and(|name| {
            m.invariants.iter().any(|invariant| invariant.name.as_ref() == name)
        })
    {
        return Err(TyCertifyError::KernelRecheckDeclined(
            "Buggy=1 replay did not witness one of the committed invariants".to_owned(),
        ));
    }
    Ok(ModelVerdict::Proved)
}

/// Certify `m` through the pinned, in-process proof-producing lane.
///
/// Positive credit requires an exact source/config-bound safety certificate,
/// independent kernel recheck, and a replay-verified `Buggy = 1`
/// counterexample.  No subprocess text or caller-selected checker path can
/// promote this result.
pub fn check_model<S: AsRef<str>>(m: &Model<S>) -> ModelVerdict {
    certify_model(m).verdict
}

#[cfg(test)]
const UNBOUND_TEMPORAL_INPUT: &str = "legacy exploratory subprocess result has no proof credit";

#[cfg(test)]
fn demote_unbound_temporal_result(verdict: ModelVerdict) -> ModelVerdict {
    match verdict {
        ModelVerdict::Proved => {
            ModelVerdict::Unknown(format!("{UNBOUND_TEMPORAL_INPUT} (exploratory result: Proved)"))
        }
        ModelVerdict::ProvedNoDial => ModelVerdict::Unknown(format!(
            "{UNBOUND_TEMPORAL_INPUT} (exploratory result: ProvedNoDial)"
        )),
        other => other,
    }
}

fn valid_tla_identifier(name: &str) -> bool {
    let mut bytes = name.bytes();
    bytes.next().is_some_and(|byte| byte.is_ascii_alphabetic())
        && bytes.all(|byte| byte.is_ascii_alphanumeric() || byte == b'_')
}

pub(crate) fn validate_temporal_identifier(name: &str, role: &str) -> Result<(), String> {
    if name.len() > clean_model_lane::MAX_NAME_BYTES || !valid_tla_identifier(name) {
        return Err(format!(
            "{role} `{name}` is not a supported TLA+ identifier (max {} bytes)",
            clean_model_lane::MAX_NAME_BYTES
        ));
    }
    if clean_model_lane::TLA_RESERVED_IDENTIFIER_TOKENS.contains(&name) {
        return Err(format!("{role} `{name}` is a reserved TLA+ lexer token"));
    }
    Ok(())
}

/// Certify every model and exit nonzero unless every proof and non-vacuity gate
/// closes.
pub fn check_models_or_exit(models: &[Model]) -> ! {
    check_models_or_exit_with_protocol(models, None)
}

/// Explore every model and replay-bind diagnostic records to a one-use
/// capability supplied by the supervising process.
///
/// The capability prevents transcript replay by a supervising process.  Proof
/// credit itself comes only from [`check_model`]'s in-process certificate and
/// counterexample recheck, not from the transcript.
pub fn check_models_with_capability_or_exit(models: &[Model], capability: &str) -> ! {
    if !valid_temporal_capability(capability) {
        eprintln!("temporal: invalid supervising-session capability; refusing to emit evidence");
        std::process::exit(2);
    }
    check_models_or_exit_with_protocol(models, Some(capability))
}

fn check_models_or_exit_with_protocol(models: &[Model], capability: Option<&str>) -> ! {
    const LEGACY_PROTOCOL: &str = "TRUST_TEMPORAL_V1";
    const CAPABILITY_PROTOCOL: &str = "TRUST_TEMPORAL_V2";
    let emit = |record: &str| match capability {
        Some(capability) => {
            eprintln!("{CAPABILITY_PROTOCOL}\t{capability}\t{record}");
        }
        None => {
            eprintln!("{LEGACY_PROTOCOL}\t{record}");
        }
    };
    emit(&format!("INVENTORY\t{}", models.len()));
    eprintln!(
        "temporal: model-checking {} model(s) with the embedded ty checker (first-party/ty)...",
        models.len()
    );
    let mut proved = 0usize;
    let mut verdicts = Vec::with_capacity(models.len());
    for m in models {
        let verdict = check_model(m);
        let ok = verdict.is_proved();
        proved += usize::from(ok);
        let verdict_tag = match &verdict {
            ModelVerdict::Proved => "proved",
            ModelVerdict::ProvedNoDial => "proved_no_dial",
            ModelVerdict::Failed(_) => "failed",
            ModelVerdict::Vacuous => "vacuous",
            ModelVerdict::Unknown(_) => "unknown",
        };
        let encoded_name =
            m.name.as_bytes().iter().map(|byte| format!("{byte:02x}")).collect::<String>();
        emit(&format!("MODEL\t{encoded_name}\t{verdict_tag}"));
        let tag = if ok { "ok  " } else { "FAIL" };
        eprintln!("  {tag} {:<24} {verdict:?}", m.name);
        verdicts.push(verdict);
    }
    emit(&format!(
        "SUMMARY\t{}\t{}\t{}",
        models.len(),
        proved,
        models.len().saturating_sub(proved)
    ));
    std::process::exit(temporal_diagnostic_exit_code(&verdicts));
}

fn temporal_diagnostic_exit_code(verdicts: &[ModelVerdict]) -> i32 {
    if !verdicts.is_empty() && verdicts.iter().all(ModelVerdict::is_proved) {
        0
    } else if verdicts
        .iter()
        .any(|verdict| matches!(verdict, ModelVerdict::Failed(_) | ModelVerdict::Vacuous))
    {
        1
    } else {
        // Empty, unbound, missing-tool, and otherwise inconclusive evidence are
        // setup/evidence failures rather than property counterexamples.
        2
    }
}

fn valid_temporal_capability(capability: &str) -> bool {
    capability.len() == 64
        && capability.bytes().all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
}

// The former "deprecated M3 compatibility registry" (link-time model
// inventory: `pub use inventory`, `RegisteredModel`, `registered_models*`, and
// the `check_registered_models*_or_exit` helpers) was deleted as extraneous
// (owner ruling 2026-07-20, "no deprecation limbo"): the live Targo
// temporal/build gates never trusted the process-owned registry as program
// evidence and unconditionally reject the automatic route with
// unbound-evidence exit 2. Callers own their explicit model list and use
// `check_models_or_exit` / `check_models_with_capability_or_exit` /
// `certify_clean_scalar_model_with_ty` directly.

#[cfg(test)]
#[allow(deprecated)]
mod trust_fabric_tests {
    use super::*;

    fn grouping_sensitive_model() -> Model {
        trust_model! {
            GroupingSensitive {
                const Buggy = 0;
                var x = 9;
                action Step {
                    x = if Buggy == 0 { 10 - (x + 1) } else { 0 };
                }
                invariant Positive: x > 0;
            }
        }
    }

    fn edge_gate_model() -> Model {
        trust_model! {
            EdgeGate {
                const Buggy = 0;
                var granted = 0;
                var decision = 0;
                action Grant when (granted <= 0) {
                    granted = 1;
                    decision = if 1 + Buggy > 0 { 1 } else { 0 };
                }
                action Revoke when (granted > 0) {
                    granted = 0;
                    decision = if 0 + Buggy > 0 { 1 } else { 0 };
                }
                invariant FailClosed: decision <= granted;
            }
        }
    }

    // The generated TLA+ is the documented module shape (emitter stability).
    #[test]
    fn edge_gate_generates_expected_tla() {
        let tla = edge_gate_model().to_tla();
        assert!(tla.contains("FailClosed == decision =< granted"), "tla:\n{tla}");
        assert!(tla.contains("CONSTANT Buggy"), "tla:\n{tla}");
    }

    #[test]
    fn renderer_preserves_grouping_shared_with_interpreter() {
        let model = grouping_sensitive_model();
        let tla = model.to_tla();
        assert!(tla.contains("x' = (IF Buggy = 0 THEN (10 - (x + 1)) ELSE 0)"), "tla:\n{tla}");

        let mut state = model.init_state();
        assert!(model.fire("Step", &mut state));
        assert_eq!(state.get("x"), Some(&0));
    }

    #[test]
    fn forall_rendering_cannot_capture_a_following_conjunct() {
        let expression = and_(forall("n", int(1), int(0), eq(var("n"), int(0))), bool_lit(false));
        assert_eq!(expression.to_tla(), "(\\A n \\in 1..0 : n = 0) /\\ FALSE");
        assert_eq!(expression.eval(&BTreeMap::new()), Value::Bool(false));
    }

    #[test]
    fn interpreter_fails_stop_outside_its_exact_i64_domain() {
        for expression in [add(int(i64::MAX), int(1)), sub(int(i64::MIN), int(1))] {
            assert!(
                std::panic::catch_unwind(|| expression.eval(&BTreeMap::new())).is_err(),
                "the compatibility interpreter must not wrap a TLA+ integer operation"
            );
        }
    }

    #[test]
    fn temporal_capabilities_are_canonical_unambiguous_tokens() {
        assert!(valid_temporal_capability(&"a".repeat(64)));
        assert!(valid_temporal_capability(
            "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef"
        ));
        assert!(!valid_temporal_capability(&"a".repeat(63)));
        assert!(!valid_temporal_capability(&"A".repeat(64)));
        assert!(!valid_temporal_capability(&format!("{}\n", "a".repeat(64))));
    }

    #[test]
    fn diagnostic_exit_distinguishes_proofs_violations_and_unknowns() {
        assert_eq!(temporal_diagnostic_exit_code(&[ModelVerdict::Proved]), 0);
        assert_eq!(
            temporal_diagnostic_exit_code(&[ModelVerdict::Unknown(
                UNBOUND_TEMPORAL_INPUT.to_string(),
            )]),
            2
        );
        assert_eq!(temporal_diagnostic_exit_code(&[]), 2);
        assert_eq!(temporal_diagnostic_exit_code(&[ModelVerdict::Failed("Invariant".into())]), 1);
        assert_eq!(temporal_diagnostic_exit_code(&[ModelVerdict::Vacuous]), 1);
    }

    #[test]
    fn forged_or_ambient_exploratory_success_is_never_proof_credit() {
        for exploratory in [ModelVerdict::Proved, ModelVerdict::ProvedNoDial] {
            let public = demote_unbound_temporal_result(exploratory);
            assert!(
                matches!(public, ModelVerdict::Unknown(ref detail) if detail.contains("legacy exploratory subprocess")),
                "apparent checker success was not demoted: {public:?}"
            );
            assert!(!public.is_proved());
        }
    }

    #[test]
    fn public_check_is_the_certificate_lane_not_exploratory_stdout() {
        let model = edge_gate_model();
        assert_eq!(check_model(&model), certify_model(&model).verdict);
    }

    #[test]
    fn aggregate_success_requires_nonempty_all_proved() {
        assert_eq!(temporal_diagnostic_exit_code(&[]), 2);
        assert_eq!(temporal_diagnostic_exit_code(&[ModelVerdict::Proved, ModelVerdict::Proved]), 0);
        assert_eq!(
            temporal_diagnostic_exit_code(&[
                ModelVerdict::Proved,
                ModelVerdict::Unknown("declined".to_owned())
            ]),
            2
        );
    }
}

#[cfg(test)]
#[allow(deprecated)]
mod ty_certify_lane_tests {
    use super::*;

    const COMPLETE_FINITE_SPEC: &str = "---- MODULE TrustCompleteFinite ----\n\
EXTENDS Integers\n\
VARIABLE x\n\
Init == x = 0\n\
Next == x' = x + 1 /\\ x < 3\n\
Safety == x >= 0\n\
====\n";

    const COMPLETE_FINITE_CONFIG: &str =
        "INIT Init\nNEXT Next\nINVARIANT Safety\nCHECK_DEADLOCK FALSE\n";

    fn explicit_certificate_with(
        spec_src: &str,
        config_src: &str,
        mutate: impl FnOnce(&mut tla_check::explicit_fixpoint_cert::ExplicitFixpointCert),
    ) -> tla_check::cert::SafetyCertificate {
        // Test helpers are not exempt from the embedded TY transaction
        // contract. The harness invokes these producers in parallel with the
        // public model/liveness lanes, so guard their complete semantic input
        // lifetime just like production callers do.
        let _ty_transaction = in_process_ty_transaction_lock();
        let config = tla_check::Config::parse(config_src).expect("test config parses");
        let mut fixpoint =
            tla_check::explicit_fixpoint_cert::certify_explicit_state_spec(spec_src, &config)
                .expect("test spec has an explicit-fixpoint certificate");
        mutate(&mut fixpoint);
        tla_check::cert::build_explicit_fixpoint_certificate(spec_src, &config, fixpoint)
    }

    fn bound_explicit_certificate(certificate: &tla_check::cert::SafetyCertificate) -> BoundTyCert {
        let raw = certificate.to_json();
        let expected = certificate.invariants.iter().map(String::as_str).collect::<Vec<_>>();
        parse_and_bind_ty_cert(&raw, &certificate.spec_src, &expected)
            .expect("fresh explicit certificate binds")
    }

    fn assert_both_certified_safety_apis_decline(
        certificate: &tla_check::cert::SafetyCertificate,
        expected_detail: &str,
    ) {
        let mut bound = bound_explicit_certificate(certificate);
        let internal = recheck_bound_clean_kernel(&mut bound).unwrap_err();
        assert!(
            matches!(internal, TyCertifyError::KernelFragmentNotClosed(ref detail)
                if detail.contains(expected_detail)),
            "unexpected internal result: {internal:?}"
        );
        assert!(!bound.kernel_rechecked);

        let public = recheck_certified_temporal_evidence(
            &certificate.to_json(),
            &certificate.spec_src,
            COMPLETE_FINITE_CONFIG,
            &["Safety"],
            None,
        )
        .unwrap_err();
        assert!(
            matches!(public, CertifiedTemporalError::Declined(ref detail)
                if detail.contains(expected_detail)),
            "unexpected public result: {public:?}"
        );
    }

    /// A minimal, well-formed `ty.cert/v1` JSON for `spec_src`/`invariants`
    /// (the extra fields mirror what the real emitter writes; unknown fields
    /// like the proof legs are irrelevant to the transport parse).
    fn cert_json(spec_src: &str, invariants: &[&str]) -> String {
        serde_json::json!({
            "schema": "ty.cert/v1",
            "verdict": "explicit-state-fixpoint-safe",
            "spec_src": spec_src,
            "init": "Init",
            "next": "Next",
            "invariants": invariants,
            "invariant_j_tla": "",
            "var_sorts": [],
            "ay_proof_obligations": [],
            "digest": "0".repeat(64),
        })
        .to_string()
    }

    // ---- pure binding checks (no process at all) ---------------------------

    #[test]
    fn binding_happy_path_returns_bound_cert() {
        let spec = ring_model().to_tla();
        let raw = cert_json(&spec, &["LenBounded"]);
        let bound = parse_and_bind_ty_cert(&raw, &spec, &["LenBounded"]).expect("must bind");
        assert_eq!(bound.cert.schema, TY_CERT_SCHEMA_V1);
        assert_eq!(bound.cert.spec_src, spec);
        assert_eq!(bound.cert.invariants, vec!["LenBounded".to_string()]);
        assert_eq!(bound.cert.init.as_deref(), Some("Init"));
        assert_eq!(bound.cert.next.as_deref(), Some("Next"));
        assert_eq!(bound.raw_json, raw);
    }

    #[test]
    fn binding_rejects_spec_src_mismatch() {
        let spec = ring_model().to_tla();
        let tampered = spec.replace("LenBounded == ((seq - lo) + 1) =< Cap", "LenBounded == TRUE");
        assert_ne!(tampered, spec, "test fixture must actually alter the module");
        let raw = cert_json(&tampered, &["LenBounded"]);
        let err = parse_and_bind_ty_cert(&raw, &spec, &["LenBounded"]).unwrap_err();
        assert!(
            matches!(err, TyCertifyError::SpecSrcMismatch { .. }),
            "expected SpecSrcMismatch, got {err:?}"
        );
        assert!(err.to_string().contains("spec_src"), "error must name the binding: {err}");
    }

    #[test]
    fn binding_rejects_malformed_json() {
        let spec = ring_model().to_tla();
        let err = parse_and_bind_ty_cert("{ not json", &spec, &["LenBounded"]).unwrap_err();
        assert!(
            matches!(err, TyCertifyError::MalformedJson(_)),
            "expected MalformedJson, got {err:?}"
        );
    }

    #[test]
    fn binding_rejects_missing_schema_tag() {
        let spec = ring_model().to_tla();
        let mut v: serde_json::Value =
            serde_json::from_str(&cert_json(&spec, &["LenBounded"])).expect("fixture JSON parses");
        v.as_object_mut().unwrap().remove("schema");
        let err = parse_and_bind_ty_cert(&v.to_string(), &spec, &["LenBounded"]).unwrap_err();
        assert_eq!(err, TyCertifyError::SchemaMismatch { found: String::new() });
        assert!(err.to_string().contains("(absent)"), "error must say the tag is absent: {err}");
    }

    #[test]
    fn binding_rejects_wrong_schema_tag() {
        let spec = ring_model().to_tla();
        let raw = cert_json(&spec, &["LenBounded"]).replace("ty.cert/v1", "ty.cert/v2");
        let err = parse_and_bind_ty_cert(&raw, &spec, &["LenBounded"]).unwrap_err();
        assert_eq!(err, TyCertifyError::SchemaMismatch { found: "ty.cert/v2".into() });
    }

    #[test]
    fn binding_rejects_invariant_name_mismatch() {
        let spec = ring_model().to_tla();
        let raw = cert_json(&spec, &["SomethingElse"]);
        let err = parse_and_bind_ty_cert(&raw, &spec, &["LenBounded"]).unwrap_err();
        assert!(
            matches!(err, TyCertifyError::InvariantsMismatch { .. }),
            "expected InvariantsMismatch, got {err:?}"
        );
        assert!(err.to_string().contains("invariants"), "error must name the binding: {err}");
    }

    #[test]
    fn binding_invariant_names_are_order_insensitive() {
        let spec = "---- MODULE M ----\n====\n";
        let raw = cert_json(spec, &["B", "A"]);
        parse_and_bind_ty_cert(&raw, spec, &["A", "B"]).expect("order must not matter");
    }

    #[test]
    fn exploratory_check_transport_is_still_demoted() {
        let demoted = demote_unbound_temporal_result(ModelVerdict::Proved);
        assert!(
            matches!(demoted, ModelVerdict::Unknown(ref d) if d.contains("legacy exploratory subprocess")),
            "stdout-based check success must stay demoted: {demoted:?}"
        );
    }

    fn bound_for_model(model: &Model) -> BoundTyCert {
        let raw = cert_json(
            &model.to_tla(),
            &model.invariants.iter().map(|i| i.name).collect::<Vec<_>>(),
        );
        let mut json: serde_json::Value = serde_json::from_str(&raw).unwrap();
        json["constants"] = serde_json::Value::Array(
            model
                .consts
                .iter()
                .map(|(name, value)| serde_json::json!([name, { "Value": value.to_string() }]))
                .collect(),
        );
        parse_and_bind_ty_cert(
            &json.to_string(),
            &model.to_tla(),
            &model.invariants.iter().map(|i| i.name).collect::<Vec<_>>(),
        )
        .unwrap()
    }

    #[test]
    fn configuration_binding_includes_init_next_and_constants() {
        let model = kernel_model();
        let bound = bound_for_model(&model);
        bind_model_configuration(&bound, &model).expect("committed config must bind");
    }

    #[test]
    fn finite_projection_preserves_bound_producer_and_exact_scalar_manifest() {
        let model = kernel_model();
        let bound = bound_for_model(&model);
        let producer_raw = bound.raw_json.clone();
        let clean = clean_finite_projection(&bound, &model);

        assert_eq!(bound.raw_json, producer_raw, "projection must not rewrite producer evidence");
        assert_eq!(clean.spec_src, bound.cert.spec_src);
        assert_eq!(clean.init, bound.cert.init);
        assert_eq!(clean.next, bound.cert.next);
        assert_eq!(clean.invariants, bound.cert.invariants);
        assert_eq!(clean.constants.iter().find(|(name, _)| name == "Buggy").unwrap().1, 0);
        assert_eq!(
            clean.var_sorts,
            vec![("seq".into(), "Int".into()), ("count".into(), "Int".into())]
        );
    }

    #[test]
    fn finite_projection_manifest_preserves_function_product_shape() {
        let model = evict_full_model();
        assert!(model_uses_clean_finite_product(&model));
        let bound = bound_for_model(&model);
        let clean = clean_finite_projection(&bound, &model);
        assert_eq!(
            clean.var_sorts,
            vec![
                ("seq".into(), "Int".into()),
                ("lo".into(), "Int".into()),
                ("live".into(), "[1..MaxSeq -> BOOLEAN]".into()),
            ]
        );

        let mut sole_scalar = kernel_model();
        sole_scalar.vars.truncate(1);
        assert!(!model_uses_clean_finite_product(&sole_scalar));

        let mut sole_function = evict_full_model();
        sole_function.vars.clear();
        assert!(
            model_uses_clean_finite_product(&sole_function),
            "one finite function variable is still a product and must not route to sole_var"
        );
    }

    #[test]
    fn configuration_binding_rejects_buggy_value_swap() {
        let model = kernel_model();
        let mut bound = bound_for_model(&model);
        let buggy = bound
            .cert
            .constants
            .iter_mut()
            .find(|(name, _)| name == "Buggy")
            .expect("fixture has Buggy");
        buggy.1 = TyConfigConstant::Value("1".into());
        let error = bind_model_configuration(&bound, &model).unwrap_err();
        assert!(matches!(error, TyCertifyError::ConfigurationMismatch { .. }));
        assert!(error.to_string().contains("configuration"));
    }

    #[test]
    fn configuration_binding_rejects_non_value_constant_tags() {
        for forged in [
            TyConfigConstant::ModelValue,
            TyConfigConstant::ModelValueSet(vec!["0".into()]),
            TyConfigConstant::Replacement("Other".into()),
        ] {
            let model = kernel_model();
            let mut bound = bound_for_model(&model);
            bound
                .cert
                .constants
                .iter_mut()
                .find(|(name, _)| name == "Buggy")
                .expect("fixture has Buggy")
                .1 = forged;
            let error = bind_model_configuration(&bound, &model).unwrap_err();
            assert!(
                matches!(error, TyCertifyError::ConfigurationMismatch { .. }),
                "tagged constants must not alias an exact integer binding: {error:?}"
            );
        }
    }

    fn assert_committed_buggy_baseline_rejected(model: &Model, expected: &str) {
        let outcome = certify_model(model);
        assert!(matches!(
            &outcome.bound,
            Err(TyCertifyError::Setup(detail))
                if detail.contains("`Buggy` constant must equal 0") && detail.contains(expected)
        ));
        assert!(matches!(
            &outcome.verdict,
            ModelVerdict::Unknown(detail)
                if detail.contains("`Buggy` constant must equal 0") && detail.contains(expected)
        ));
        assert_eq!(outcome.non_vacuity, None);
    }

    #[test]
    fn certification_rejects_missing_nonzero_and_duplicate_buggy_baselines_before_ty() {
        let mut missing = kernel_model();
        missing.consts.retain(|(name, _)| *name != "Buggy");
        assert_committed_buggy_baseline_rejected(&missing, "found none");

        let mut nonzero = kernel_model();
        nonzero
            .consts
            .iter_mut()
            .find(|(name, _)| *name == "Buggy")
            .expect("fixture has Buggy")
            .1 = 2;
        assert_committed_buggy_baseline_rejected(&nonzero, "found value 2");

        let mut duplicate = kernel_model();
        duplicate.consts.push(("Buggy", 0));
        assert_committed_buggy_baseline_rejected(&duplicate, "found duplicates");
    }

    fn assert_model_preflight_rejected(model: &Model, expected: &str) {
        let error = validate_model_for_certification(model).unwrap_err();
        assert!(
            matches!(error, TyCertifyError::Setup(ref detail) if detail.contains(expected)),
            "model preflight did not name `{expected}`: {error:?}"
        );
    }

    #[test]
    fn legacy_model_preflight_rejects_empty_inventories_and_bad_names() {
        let mut no_variables = kernel_model();
        no_variables.vars.clear();
        assert_model_preflight_rejected(&no_variables, "at least one scalar or function-valued");

        let mut no_actions = kernel_model();
        no_actions.actions.clear();
        assert_model_preflight_rejected(&no_actions, "at least one action");

        let mut no_invariants = kernel_model();
        no_invariants.invariants.clear();
        assert_model_preflight_rejected(&no_invariants, "at least one invariant");

        let mut duplicate = kernel_model();
        duplicate.vars[0].name = "MaxSeq";
        assert_model_preflight_rejected(&duplicate, "duplicate or reserved variable name `MaxSeq`");

        let mut duplicate_constant = kernel_model();
        duplicate_constant.consts.push(("MaxSeq", 7));
        assert_model_preflight_rejected(
            &duplicate_constant,
            "duplicate or reserved constant name `MaxSeq`",
        );

        let mut generated = kernel_model();
        generated.actions[0].name = "Next";
        assert_model_preflight_rejected(&generated, "duplicate or reserved action name `Next`");

        let mut lexer_keyword = kernel_model();
        lexer_keyword.vars[0].name = "TRUE";
        assert_model_preflight_rejected(&lexer_keyword, "reserved TLA+ lexer token");

        let mut invalid_model_name = kernel_model();
        invalid_model_name.name = "_Kernel";
        assert_model_preflight_rejected(&invalid_model_name, "not a supported TLA+ identifier");
    }

    #[test]
    fn legacy_model_preflight_checks_targets_references_binders_and_sorts() {
        let mut unknown_target = kernel_model();
        unknown_target.actions[0].updates[0].var = "missing";
        assert_model_preflight_rejected(&unknown_target, "updates unknown variable `missing`");

        let mut duplicate_target = kernel_model();
        duplicate_target.actions[0].updates.push(Update { var: "seq", expr: var("seq") });
        assert_model_preflight_rejected(&duplicate_target, "updates `seq` more than once");

        let mut unknown_reference = kernel_model();
        unknown_reference.actions[0].guard = Some(le(var("missing"), int(1)));
        assert_model_preflight_rejected(&unknown_reference, "unknown state/bound variable");

        let mut unknown_constant = kernel_model();
        unknown_constant.invariants[0].expr = le(var("seq"), cst("Missing"));
        assert_model_preflight_rejected(&unknown_constant, "unknown constant `Missing`");

        let mut shadowing_binder = kernel_model();
        shadowing_binder.invariants[0].expr =
            forall("seq", int(1), cst("MaxSeq"), le(var("seq"), cst("MaxSeq")));
        assert_model_preflight_rejected(&shadowing_binder, "shadows another model identifier");

        let mut wrong_guard_sort = kernel_model();
        wrong_guard_sort.actions[0].guard = Some(int(1));
        assert_model_preflight_rejected(&wrong_guard_sort, "action `Emit` guard has sort Int");
        let outcome = certify_model(&wrong_guard_sort);
        assert!(matches!(
            outcome.bound,
            Err(TyCertifyError::Setup(ref detail))
                if detail.contains("action `Emit` guard has sort Int")
        ));
        assert_eq!(outcome.non_vacuity, None);

        let mut wrong_update_sort = kernel_model();
        wrong_update_sort.actions[0].updates[0].expr = bool_lit(true);
        assert_model_preflight_rejected(
            &wrong_update_sort,
            "action `Emit` update of `count` has sort Bool",
        );
    }

    #[test]
    fn legacy_model_preflight_checks_finite_function_domains() {
        let valid = evict_full_model();
        validate_model_for_certification(&valid)
            .expect("the committed finite-function model must pass shared preflight");

        let mut missing_range = valid.clone();
        missing_range.fn_vars[0].range = "Missing";
        assert_model_preflight_rejected(&missing_range, "missing range constant `Missing`");

        let mut zero_range = valid.clone();
        zero_range.consts.push(("Zero", 0));
        zero_range.fn_vars[0].range = "Zero";
        assert_model_preflight_rejected(&zero_range, "must be positive, found 0");

        let mut wrong_domain = valid;
        let update = wrong_domain.actions[0]
            .updates
            .iter_mut()
            .find(|update| update.var == "live")
            .expect("fixture updates live");
        update.expr = comprehension("n", int(1), cst("Cap"), bool_lit(false));
        assert_model_preflight_rejected(&wrong_domain, "expected Function(\"MaxSeq\")");
    }

    #[test]
    fn configuration_binding_rejects_wrong_transition_operators() {
        let model = kernel_model();
        let mut bound = bound_for_model(&model);
        bound.cert.next = Some("OtherNext".into());
        assert!(matches!(
            bind_model_configuration(&bound, &model),
            Err(TyCertifyError::ConfigurationMismatch { .. })
        ));
    }

    #[test]
    fn malformed_explicit_fixpoint_is_not_accepted_by_presence_alone() {
        let model = kernel_model();
        let mut bound = bound_for_model(&model);
        bound.cert.explicit_fixpoint = Some(serde_json::json!({ "reachable": [[0, 0]] }));
        let mut raw: serde_json::Value = serde_json::from_str(&bound.raw_json).unwrap();
        raw["explicit_fixpoint"] = bound.cert.explicit_fixpoint.clone().unwrap();
        bound.raw_json = raw.to_string();
        assert!(matches!(
            recheck_bound_clean_kernel(&mut bound),
            Err(TyCertifyError::KernelRecheckDeclined(_))
        ));
        assert!(!bound.kernel_rechecked);
    }

    #[test]
    fn complete_finite_pairs_authorize_both_certified_safety_apis() {
        let certificate =
            explicit_certificate_with(COMPLETE_FINITE_SPEC, COMPLETE_FINITE_CONFIG, |_| {});
        let fixpoint = certificate.explicit_fixpoint.as_ref().unwrap();
        assert!(fixpoint.init_shape.is_some() && fixpoint.init_completeness.is_some());
        assert!(fixpoint.next_shape.is_some() && fixpoint.next_completeness.is_some());

        let mut bound = bound_explicit_certificate(&certificate);
        recheck_bound_clean_kernel(&mut bound).expect("complete finite authority must recheck");
        assert!(bound.kernel_rechecked);
        assert!(bound.recheck_detail.contains("complete finite authority"));

        let evidence = recheck_certified_temporal_evidence(
            &certificate.to_json(),
            COMPLETE_FINITE_SPEC,
            COMPLETE_FINITE_CONFIG,
            &["Safety"],
            None,
        )
        .expect("the public evidence API must apply the same authority gate");
        assert!(evidence.recheck_detail.contains("complete finite authority"));
    }

    #[test]
    fn unbounded_invariant_authorizes_both_certified_safety_apis() {
        const SPEC: &str = "---- MODULE TrustUnbounded ----\n\
EXTENDS Integers\n\
VARIABLE x\n\
Init == x = 0\n\
Next == x' = x + 1\n\
Safety == x >= 0\n\
====\n";
        let certificate = explicit_certificate_with(SPEC, COMPLETE_FINITE_CONFIG, |_| {});
        assert!(certificate.explicit_fixpoint.as_ref().unwrap().unbounded_invariant.is_some());

        let mut bound = bound_explicit_certificate(&certificate);
        recheck_bound_clean_kernel(&mut bound).expect("unbounded invariant legs must recheck");
        assert!(bound.kernel_rechecked);
        assert!(bound.recheck_detail.contains("unbounded invariant authority"));

        let evidence = recheck_certified_temporal_evidence(
            &certificate.to_json(),
            SPEC,
            COMPLETE_FINITE_CONFIG,
            &["Safety"],
            None,
        )
        .expect("the public evidence API must accept the same unbounded authority");
        assert!(evidence.recheck_detail.contains("unbounded invariant authority"));
    }

    #[test]
    fn enumerator_assisted_missing_pairs_decline_in_both_certified_safety_apis() {
        let certificate =
            explicit_certificate_with(COMPLETE_FINITE_SPEC, COMPLETE_FINITE_CONFIG, |fixpoint| {
                fixpoint.next_shape = None;
                fixpoint.next_completeness = None;
                fixpoint.next_pred = None;
                fixpoint.next_general_completeness = None;
                fixpoint.init_shape = None;
                fixpoint.init_completeness = None;
                fixpoint.init_pred = None;
                fixpoint.init_general_completeness = None;
            });
        let upstream = {
            let _ty_transaction = in_process_ty_transaction_lock();
            tla_check::cert::verify_safety_certificate(&certificate)
        };
        assert!(
            matches!(upstream.verdict, tla_check::cert::CertVerdict::Accepted)
                && upstream.kernel_recheck == Some(true),
            "regression must exercise the weaker upstream acceptance: {upstream:?}"
        );
        assert_both_certified_safety_apis_decline(&certificate, "enumerator-assisted");
    }

    #[test]
    fn incomplete_completeness_pair_declines_in_both_certified_safety_apis() {
        let certificate =
            explicit_certificate_with(COMPLETE_FINITE_SPEC, COMPLETE_FINITE_CONFIG, |fixpoint| {
                fixpoint.next_completeness = None
            });
        assert_both_certified_safety_apis_decline(&certificate, "incomplete Next shortcut");
    }

    #[test]
    fn mixed_completeness_families_decline_in_both_certified_safety_apis() {
        const GENERAL_SPEC: &str = "---- MODULE TrustGeneralFinite ----\n\
EXTENDS Integers\n\
VARIABLE x\n\
Init == x = 0\n\
Next == x' = (x + 2) % 5 /\\ x' < 9\n\
Safety == x >= 0\n\
====\n";
        let general = explicit_certificate_with(GENERAL_SPEC, COMPLETE_FINITE_CONFIG, |_| {});
        let general = general.explicit_fixpoint.as_ref().unwrap();
        assert!(general.next_pred.is_some() && general.next_general_completeness.is_some());
        let certificate =
            explicit_certificate_with(COMPLETE_FINITE_SPEC, COMPLETE_FINITE_CONFIG, |fixpoint| {
                fixpoint.next_pred = general.next_pred.clone();
                fixpoint.next_general_completeness = general.next_general_completeness.clone();
            });
        assert_both_certified_safety_apis_decline(&certificate, "mixed Next completeness families");
    }

    const CLEAN_ACC_CERT: &str = include_str!(
        "../../../first-party/clean/crates/clean-tla/tests/fixtures/accumulator.ty.cert.json"
    );

    fn clean_acc_bound(raw_json: &str) -> BoundTyCert {
        let parsed: serde_json::Value = serde_json::from_str(raw_json).unwrap();
        let spec = parsed["spec_src"].as_str().unwrap();
        parse_and_bind_ty_cert(raw_json, spec, &["Safety"]).unwrap()
    }

    #[test]
    fn int_to_nat_clean_reconstruction_is_not_promoted() {
        let mut bound = clean_acc_bound(CLEAN_ACC_CERT);
        let error = recheck_bound_clean_kernel(&mut bound).unwrap_err();
        assert!(matches!(error, TyCertifyError::SemanticFidelity(_)));
        assert!(error.to_string().contains("Int") && error.to_string().contains("Nat"));
        assert!(!bound.kernel_rechecked);
    }

    #[test]
    fn exact_nat_clean_fragment_is_kernel_rechecked_in_process() {
        let mut json: serde_json::Value = serde_json::from_str(CLEAN_ACC_CERT).unwrap();
        json["var_sorts"] = serde_json::json!([["x", "Nat"]]);
        let raw = json.to_string();
        let mut bound = clean_acc_bound(&raw);
        recheck_bound_clean_kernel(&mut bound)
            .expect("the fidelity-exact Nat fragment must close in clean-kernel");
        assert!(bound.kernel_rechecked);
        assert!(bound.recheck_detail.contains("clean-kernel"));
    }

    // ═══════════════════════════════════════════════════════════════════════
    // S4 finite-fragment routing: MULTI-VARIABLE bounded machines certify
    // through the landed clean-tla keystone at the recheck_bound_clean_kernel
    // seam. The 1-variable closed path above is unchanged.
    // ═══════════════════════════════════════════════════════════════════════

    /// The real 2-variable EdgeGate fail-closed safety machine (`granted`,
    /// `decision`) — the smallest multi-variable model in the finite corpus.
    const EDGEGATE_JSON: &str = include_str!(
        "../../../first-party/clean/crates/clean-tla/tests/fixtures/edgegate.ty.cert.json"
    );

    /// Ring (2-var: `seq`, `lo`); MaxSeq drives the reachable-set size, so a
    /// large bound overruns the finite keystone's enumeration cap.
    const RING_SPEC: &str = "---- MODULE Ring ----\n\
         EXTENDS Naturals\n\
         CONSTANTS MaxSeq, Cap\n\
         VARIABLES seq, lo\n\
         Init == seq = 0 /\\ lo = 1\n\
         Push ==\n\
           /\\ seq <= MaxSeq - 1\n\
           /\\ seq' = seq + 1\n\
           /\\ lo' = (IF (seq + 1) - lo + 1 > Cap THEN lo + 1 ELSE lo)\n\
         Next == Push\n\
         LenBounded == seq - lo + 1 <= Cap\n\
         ====\n";

    /// Cursor (2-var: `seq`, `cursor`) — a DIFFERENT valid machine, used to
    /// force an α-mismatch against a registered EdgeGate theorem.
    const CURSOR_SPEC: &str = "---- MODULE Cursor ----\n\
         EXTENDS Naturals\n\
         CONSTANT MaxSeq\n\
         VARIABLES seq, cursor\n\
         Grow == seq <= MaxSeq - 1 /\\ seq' = seq + 1 /\\ UNCHANGED cursor\n\
         Deliver == seq > cursor /\\ cursor' = seq /\\ UNCHANGED seq\n\
         Init == seq = 0 /\\ cursor = 0\n\
         Next == Grow \\/ Deliver\n\
         CursorBounded == cursor <= seq\n\
         ====\n";

    /// A one-declaration state whose declaration is itself a finite product.
    /// Dispatch must inspect the sort, not merely `var_sorts.len()`.
    const SOLE_FUNCTION_SPEC: &str = "---- MODULE SoleFunction ----\n\
         EXTENDS Naturals\n\
         CONSTANT MaxSeq\n\
         VARIABLE live\n\
         Init == live = [n \\in 1..MaxSeq |-> FALSE]\n\
         Stay == live' = live\n\
         Next == Stay\n\
         AllFalse == \\A n \\in 1..MaxSeq : live[n] <=> FALSE\n\
         ====\n";

    /// Assemble a bare clean-tla `ty.cert/v1` JSON blob (INTEGER constants — the
    /// shape a real multi-variable temporal model carries).
    fn clean_tla_cert_json(
        spec_src: &str,
        invariants: &[&str],
        var_sorts: &[(&str, &str)],
        constants: &[(&str, i64)],
    ) -> String {
        serde_json::json!({
            "schema": "ty.cert/v1",
            "verdict": "inductive-safety-safe",
            "spec_src": spec_src,
            "init": "Init",
            "next": "Next",
            "invariants": invariants,
            "invariant_j_tla": "TRUE",
            "var_sorts": var_sorts.iter().map(|(v, s)| [*v, *s]).collect::<Vec<_>>(),
            "constants": constants
                .iter()
                .map(|(n, v)| serde_json::json!([*n, *v]))
                .collect::<Vec<_>>(),
        })
        .to_string()
    }

    /// Build a [`BoundTyCert`] from a bare clean-tla certificate blob, faithfully
    /// mirroring its fields into the trust-side transport with
    /// `explicit_fixpoint = None` (so the seam takes the clean-tla else-branch).
    /// The seam re-parses `raw_json` independently; the transport's integer
    /// constants are recorded as `TyConfigConstant::Value` for audit but are not
    /// read by the finite recheck.
    fn bound_from_clean_tla_json(raw_json: &str) -> BoundTyCert {
        let ct = clean_tla::ty_cert::TyCert::from_json(raw_json)
            .expect("blob parses as a clean-tla ty.cert/v1");
        let cert = TyCertV1 {
            schema: ct.schema.clone(),
            verdict: ct.verdict.clone(),
            spec_src: ct.spec_src.clone(),
            init: ct.init.clone(),
            next: ct.next.clone(),
            invariants: ct.invariants.clone(),
            constants: ct
                .constants
                .iter()
                .map(|(n, v)| (n.clone(), TyConfigConstant::Value(v.to_string())))
                .collect(),
            invariant_j_tla: ct.invariant_j_tla.clone(),
            digest: String::new(),
            ay_proof_obligations: vec![],
            explicit_fixpoint: None,
        };
        BoundTyCert {
            cert,
            raw_json: raw_json.to_string(),
            kernel_rechecked: false,
            recheck_detail: String::new(),
        }
    }

    #[test]
    fn multi_variable_model_certifies_through_the_finite_keystone() {
        // The real 2-variable EdgeGate machine goes through the seam, is routed
        // by machine shape to the S4 finite keystone, reconstructed from
        // spec_src, exhaustively explored, kernel-closed, and its bare theorem
        // α-verified — end to end.
        let mut bound = bound_from_clean_tla_json(EDGEGATE_JSON);
        recheck_bound_clean_kernel(&mut bound)
            .expect("the 2-variable EdgeGate machine must certify through the finite keystone");
        assert!(bound.kernel_rechecked, "kernel_rechecked must be set");
        assert!(
            bound.recheck_detail.contains("finite keystone")
                && bound.recheck_detail.contains("multi-variable")
                && bound.recheck_detail.contains("α-match"),
            "detail must record the finite, α-verified discharge: {}",
            bound.recheck_detail
        );
    }

    #[test]
    fn falsifiable_multi_variable_model_surfaces_unknown_not_cert() {
        // EdgeGate under the buggy dial (Buggy = 1) reachably violates
        // FailClosed. The finite keystone FALSIFIES it; the seam fails closed to
        // a declined recheck (never a certificate).
        let mut json: serde_json::Value = serde_json::from_str(EDGEGATE_JSON).unwrap();
        json["constants"] = serde_json::json!([["Buggy", 1]]);
        let raw = json.to_string();
        let mut bound = bound_from_clean_tla_json(&raw);
        let error = recheck_bound_clean_kernel(&mut bound).unwrap_err();
        assert!(
            matches!(error, TyCertifyError::KernelRecheckDeclined(_)),
            "a falsified machine must decline, got {error:?}"
        );
        let text = error.to_string();
        assert!(
            text.contains("finite keystone refused") && text.contains("FALSIFIED"),
            "decline must name the keystone falsification: {text}"
        );
        assert!(!bound.kernel_rechecked, "no certificate on a falsified machine");
    }

    #[test]
    fn oversize_multi_variable_enumeration_surfaces_unknown_not_cert() {
        // A large cfg bound overruns the exhaustive-enumeration cap. The keystone
        // refuses (StateSpaceBoundExceeded); the seam fails closed.
        let raw = clean_tla_cert_json(
            RING_SPEC,
            &["LenBounded"],
            &[("seq", "Int"), ("lo", "Int")],
            &[("MaxSeq", 9999), ("Cap", 3)],
        );
        let mut bound = bound_from_clean_tla_json(&raw);
        let error = recheck_bound_clean_kernel(&mut bound).unwrap_err();
        assert!(
            matches!(error, TyCertifyError::KernelRecheckDeclined(_)),
            "an oversize enumeration must decline, got {error:?}"
        );
        assert!(
            error.to_string().contains("state-space bound exceeded"),
            "decline must name the bound guard: {error}"
        );
        assert!(!bound.kernel_rechecked, "no certificate on an oversize machine");
    }

    #[test]
    fn anti_forgery_gate_refuses_when_recomputed_conclusion_mismatches() {
        // Register the honest EdgeGate finite product.
        let edge = clean_tla::ty_cert::TyCert::from_json(EDGEGATE_JSON).expect("edgegate parses");
        let mut env = clean_kernel::env::Environment::with_prelude();
        clean_tla::finite::register_ty_cert_safety_finite(&mut env, FINITE_THEOREM, &edge)
            .expect("EdgeGate finite product registers");

        // POSITIVE control: recomputing the expected conclusion from the SAME
        // certificate α-matches the registered theorem — the gate passes.
        finite_theorem_kernel_gate(&env, FINITE_THEOREM, &edge)
            .expect("honest finite product passes the anti-forgery gate");

        // SYNTHETIC MISMATCH: recompute the expected conclusion from a DIFFERENT
        // machine (Cursor). The kernel holds EdgeGate's statement under the
        // product name, so the α-exact comparison MUST refuse — the registered
        // declaration is never trusted by name.
        let cursor = clean_tla::ty_cert::TyCert::from_json(&clean_tla_cert_json(
            CURSOR_SPEC,
            &["CursorBounded"],
            &[("seq", "Int"), ("cursor", "Int")],
            &[("MaxSeq", 4)],
        ))
        .expect("cursor parses");
        let error = finite_theorem_kernel_gate(&env, FINITE_THEOREM, &cursor).unwrap_err();
        assert!(
            matches!(error, TyCertifyError::KernelRecheckDeclined(ref detail)
                if detail.contains("anti-forgery")),
            "a conclusion mismatch must refuse via the anti-forgery gate, got {error:?}"
        );
    }

    #[test]
    fn one_variable_cert_stays_on_the_closed_scalar_path() {
        // Dispatch correctness: a 1-variable Nat cert must NOT be hijacked to the
        // finite keystone; it stays on the closed scalar discharge (regression).
        let mut json: serde_json::Value = serde_json::from_str(CLEAN_ACC_CERT).unwrap();
        json["var_sorts"] = serde_json::json!([["x", "Nat"]]);
        let raw = json.to_string();
        let mut bound = clean_acc_bound(&raw);
        recheck_bound_clean_kernel(&mut bound)
            .expect("1-variable Nat cert must close on the closed scalar path");
        assert!(bound.kernel_rechecked);
        assert!(
            bound.recheck_detail.contains("closed theorem"),
            "1-variable cert must stay on the closed path: {}",
            bound.recheck_detail
        );
        assert!(
            !bound.recheck_detail.contains("finite keystone"),
            "1-variable cert must NOT route to the finite keystone: {}",
            bound.recheck_detail
        );
    }

    #[test]
    fn sole_function_variable_routes_to_the_finite_keystone() {
        let raw = clean_tla_cert_json(
            SOLE_FUNCTION_SPEC,
            &["AllFalse"],
            &[("live", "[1..MaxSeq -> BOOLEAN]")],
            &[("MaxSeq", 3)],
        );
        let mut bound = bound_from_clean_tla_json(&raw);
        recheck_bound_clean_kernel(&mut bound)
            .expect("one function declaration is a finite product and must close through S4");
        assert!(bound.kernel_rechecked);
        assert!(
            bound.recheck_detail.contains("finite keystone")
                && !bound.recheck_detail.contains("closed theorem"),
            "sole function dispatch took the wrong lane: {}",
            bound.recheck_detail
        );
    }

    #[test]
    fn malformed_clean_manifests_fail_closed_and_clear_stale_evidence() {
        let cases = [
            (Vec::<(&str, &str)>::new(), "manifest is empty"),
            (vec![("x", "BOOLEAN")], "unsupported Clean state sort"),
            (vec![("x", "Int"), ("x", "Nat")], "repeats variable `x`"),
        ];
        for (var_sorts, expected) in cases {
            let raw = clean_tla_cert_json(COMPLETE_FINITE_SPEC, &["Safety"], &var_sorts, &[]);
            let mut bound = bound_from_clean_tla_json(&raw);
            bound.kernel_rechecked = true;
            bound.recheck_detail = "stale accepted evidence".to_owned();
            let error = recheck_bound_clean_kernel(&mut bound).unwrap_err();
            assert!(
                error.to_string().contains(expected),
                "manifest refusal did not name `{expected}`: {error}"
            );
            assert!(!bound.kernel_rechecked);
            assert!(bound.recheck_detail.is_empty());
        }
    }

    // ---- full invocation lane against a FAKE ty binary ---------------------

    /// Write an executable fake-ty shell script. Every fake asserts the exact
    /// CLI contract this lane speaks — `certify <spec> --config <cfg> --out
    /// <cert>` — and exits 3 on any drift, so a happy-path test doubles as an
    /// invocation-shape test.
    #[cfg(unix)]
    fn fake_ty(dir: &Path, then: &str) -> PathBuf {
        use std::os::unix::fs::PermissionsExt;
        let script = format!(
            "#!/bin/sh\n\
             [ \"$1\" = \"certify\" ] || exit 3\n\
             [ -f \"$2\" ] || exit 3\n\
             [ \"$3\" = \"--config\" ] || exit 3\n\
             [ -f \"$4\" ] || exit 3\n\
             [ \"$5\" = \"--out\" ] || exit 3\n\
             {then}\n"
        );
        let path = dir.join("fake-ty");
        std::fs::write(&path, script).unwrap();
        let mut perms = std::fs::metadata(&path).unwrap().permissions();
        perms.set_mode(0o755);
        std::fs::set_permissions(&path, perms).unwrap();
        path
    }

    /// Temp dir + generated ring spec/cfg on disk (the real lane's inputs).
    #[cfg(unix)]
    fn ring_fixture() -> (tempfile::TempDir, PathBuf, PathBuf, String) {
        let dir = tempfile::Builder::new().prefix("trust-certify-test-").tempdir().unwrap();
        let m = ring_model();
        let tla = m.to_tla();
        let spec = dir.path().join("Ring.tla");
        let cfg = dir.path().join("Ring.cfg");
        std::fs::write(&spec, &tla).unwrap();
        std::fs::write(&cfg, m.to_cfg()).unwrap();
        (dir, spec, cfg, tla)
    }

    #[cfg(unix)]
    #[test]
    fn run_ty_certify_happy_path_with_fake_binary() {
        let (dir, spec, cfg, tla) = ring_fixture();
        let payload = dir.path().join("payload.json");
        std::fs::write(&payload, cert_json(&tla, &["LenBounded"])).unwrap();
        let ty = fake_ty(dir.path(), &format!("cp \"{}\" \"$6\"\nexit 0", payload.display()));
        let bound = run_ty_certify(&ty, &spec, &cfg, &tla, &["LenBounded"]).expect("must bind");
        assert_eq!(bound.cert.spec_src, tla);
        assert_eq!(bound.cert.invariants, vec!["LenBounded".to_string()]);
    }

    #[cfg(unix)]
    #[test]
    fn run_ty_certify_rejects_spec_src_mismatch_from_binary() {
        let (dir, spec, cfg, tla) = ring_fixture();
        let payload = dir.path().join("payload.json");
        std::fs::write(&payload, cert_json("---- MODULE Other ----\n====\n", &["LenBounded"]))
            .unwrap();
        let ty = fake_ty(dir.path(), &format!("cp \"{}\" \"$6\"\nexit 0", payload.display()));
        let err = run_ty_certify(&ty, &spec, &cfg, &tla, &["LenBounded"]).unwrap_err();
        assert!(matches!(err, TyCertifyError::SpecSrcMismatch { .. }), "got {err:?}");
    }

    #[cfg(unix)]
    #[test]
    fn run_ty_certify_rejects_malformed_json_from_binary() {
        let (dir, spec, cfg, tla) = ring_fixture();
        let ty = fake_ty(dir.path(), "printf '{ not json' > \"$6\"\nexit 0");
        let err = run_ty_certify(&ty, &spec, &cfg, &tla, &["LenBounded"]).unwrap_err();
        assert!(matches!(err, TyCertifyError::MalformedJson(_)), "got {err:?}");
    }

    #[cfg(unix)]
    #[test]
    fn run_ty_certify_rejects_missing_schema_tag_from_binary() {
        let (dir, spec, cfg, tla) = ring_fixture();
        let mut v: serde_json::Value =
            serde_json::from_str(&cert_json(&tla, &["LenBounded"])).unwrap();
        v.as_object_mut().unwrap().remove("schema");
        let payload = dir.path().join("payload.json");
        std::fs::write(&payload, v.to_string()).unwrap();
        let ty = fake_ty(dir.path(), &format!("cp \"{}\" \"$6\"\nexit 0", payload.display()));
        let err = run_ty_certify(&ty, &spec, &cfg, &tla, &["LenBounded"]).unwrap_err();
        assert_eq!(err, TyCertifyError::SchemaMismatch { found: String::new() });
    }

    #[cfg(unix)]
    #[test]
    fn run_ty_certify_decline_is_structured() {
        let (dir, spec, cfg, tla) = ring_fixture();
        let ty = fake_ty(
            dir.path(),
            "echo 'NOT CERTIFIED: this spec is not in the inductive-safety provable class' >&2\nexit 2",
        );
        let err = run_ty_certify(&ty, &spec, &cfg, &tla, &["LenBounded"]).unwrap_err();
        match err {
            TyCertifyError::Declined { code, ref output } => {
                assert_eq!(code, Some(2));
                assert!(output.contains("NOT CERTIFIED"), "output: {output}");
            }
            other => panic!("expected Declined, got {other:?}"),
        }
    }

    #[cfg(unix)]
    #[test]
    fn run_ty_certify_missing_out_file_is_structured() {
        let (dir, spec, cfg, tla) = ring_fixture();
        let ty = fake_ty(dir.path(), "exit 0");
        let err = run_ty_certify(&ty, &spec, &cfg, &tla, &["LenBounded"]).unwrap_err();
        assert!(matches!(err, TyCertifyError::MissingCertificate(_)), "got {err:?}");
    }

    // ---- R5 producer wiring: multi-variable safety Models reach the landed ----
    // ---- S4 finite-fragment keystone through `certify_model` IN PRODUCTION ----

    /// The historical multi-variable model now reaches the S4 finite product in
    /// production: exact transport binding, Clean reconstruction/exploration,
    /// kernel closure, and Buggy=1 replay all have to close.
    #[test]
    fn real_model_promotes_through_clean_finite_product() {
        // This test inspects the pinned-TY producer directly after exercising
        // the public lane. Retain one transaction across both operations so a
        // sibling producer cannot reuse run-scoped state between them.
        let _ty_transaction = in_process_ty_transaction_lock();
        let model = kernel_model();
        let outcome = certify_model(&model);
        assert_eq!(outcome.verdict, ModelVerdict::Proved);
        assert_eq!(outcome.non_vacuity, Some(ModelVerdict::Proved));
        let bound = outcome.bound.expect("finite product must return bound evidence");
        assert!(bound.kernel_rechecked);
        let producer = tla_check::cert::SafetyCertificate::from_json(&bound.raw_json)
            .expect("returned raw evidence must remain a real TY certificate");
        assert!(producer.explicit_fixpoint.is_some());
        assert!(producer.var_sorts.is_empty(), "projection must not rewrite TY's raw manifest");
        assert_eq!(producer.compute_digest(), producer.digest);
        let producer_report = tla_check::cert::verify_safety_certificate(&producer);
        assert!(matches!(producer_report.verdict, tla_check::cert::CertVerdict::Accepted));
        assert_eq!(producer_report.kernel_recheck, Some(true));
        let expected_authority_detail = if certified_explicit_fixpoint_authority(&producer).is_ok()
        {
            "independently also met Trust's Certified authority gate"
        } else {
            "did not independently supply Certified completeness authority"
        };
        assert!(
            bound.recheck_detail.contains("finite keystone")
                && bound.recheck_detail.contains("multi-variable")
                && bound.recheck_detail.contains("α-match")
                && bound.recheck_detail.contains("producer object retained byte-exact")
                && bound.recheck_detail.contains(expected_authority_detail),
            "unexpected finite evidence detail: {}",
            bound.recheck_detail
        );

        // A parseable producer object with a broken digest must be rejected
        // before the Clean projection is even constructed. Keep the local
        // bound mirror in sync so this specifically exercises producer
        // verification, not the earlier raw-vs-bound consistency check.
        let mut tampered = bound.clone();
        let mut tampered_producer = producer;
        tampered_producer.digest = "0".repeat(64);
        tampered.raw_json = tampered_producer.to_json();
        tampered.cert.digest = tampered_producer.digest;
        tampered.kernel_rechecked = true;
        tampered.recheck_detail = "stale accepted evidence".to_owned();
        let error = recheck_model_bound_clean_kernel(&mut tampered, &model).unwrap_err();
        assert!(
            matches!(error, TyCertifyError::KernelRecheckDeclined(ref detail)
                if detail.contains("producer evidence failed before Clean finite projection")),
            "digest tamper must stop before projection, got {error:?}"
        );
        assert!(!tampered.kernel_rechecked);
        assert!(tampered.recheck_detail.is_empty());
    }

    /// Constants transport round-trip: the one `TyConfigConstant` transport
    /// decodes BOTH producers' disjoint encodings — clean-tla's bare integers and
    /// ty's externally-tagged variants — byte-identically, and refuses unknown
    /// shapes fail-closed.
    #[test]
    fn ty_config_constant_deserializes_every_producer_encoding() {
        // clean-tla finite lane: BARE integers (the shape that used to hard-fail).
        let ints: Vec<(String, TyConfigConstant)> =
            serde_json::from_str(r#"[["Buggy", 0], ["MaxSeq", 6], ["Neg", -3]]"#)
                .expect("bare-integer constants must deserialize");
        assert_eq!(
            ints,
            vec![
                ("Buggy".to_string(), TyConfigConstant::Int(0)),
                ("MaxSeq".to_string(), TyConfigConstant::Int(6)),
                ("Neg".to_string(), TyConfigConstant::Int(-3)),
            ]
        );

        // ty explicit-fixpoint lane: EXTERNALLY-TAGGED variants, decoded identically.
        let tagged: Vec<(String, TyConfigConstant)> = serde_json::from_str(
            r#"[["a", {"Value": "3"}], ["b", "ModelValue"], ["c", {"ModelValueSet": ["m1", "m2"]}], ["d", {"Replacement": "R"}]]"#,
        )
        .expect("externally-tagged ty encodings must still deserialize");
        assert_eq!(
            tagged,
            vec![
                ("a".to_string(), TyConfigConstant::Value("3".to_string())),
                ("b".to_string(), TyConfigConstant::ModelValue),
                (
                    "c".to_string(),
                    TyConfigConstant::ModelValueSet(vec!["m1".to_string(), "m2".to_string()])
                ),
                ("d".to_string(), TyConfigConstant::Replacement("R".to_string())),
            ]
        );

        // Fail-closed on unknown unit tag / unknown object tag / multi-key object.
        assert!(serde_json::from_str::<TyConfigConstant>(r#""Nope""#).is_err());
        assert!(serde_json::from_str::<TyConfigConstant>(r#"{"Unknown": 1}"#).is_err());
        assert!(serde_json::from_str::<TyConfigConstant>(r#"{"Value": "1", "Extra": 2}"#).is_err());
        assert!(serde_json::from_str::<TyConfigConstant>(r#"{"Value": 5}"#).is_err());

        // The integer denotation binds in either encoding, and only for integers.
        assert!(config_constant_denotes_int(&TyConfigConstant::Int(0), 0));
        assert!(config_constant_denotes_int(&TyConfigConstant::Value("0".to_string()), 0));
        assert!(!config_constant_denotes_int(&TyConfigConstant::Int(1), 0));
        assert!(!config_constant_denotes_int(&TyConfigConstant::ModelValue, 0));
    }
}

#[cfg(test)]
mod clean_temporal_surface_tests {
    use clean_elab::{
        FileContext, elaborate_decl_and_register_with_context, preprocess_decl_with_context,
    };
    use clean_kernel::env::{Environment, ProofQuality};
    use clean_kernel::name::Name;
    use clean_parser::parse_file;

    const TEMPORAL_PRELUDE: &str = include_str!("../clean/Trust/Temporal.lean");

    fn elaborate_temporal_prelude() -> Environment {
        let declarations = parse_file(TEMPORAL_PRELUDE)
            .unwrap_or_else(|error| panic!("temporal prelude must parse: {error:?}"));
        let mut environment = Environment::with_prelude();
        let mut context = FileContext::new();
        for declaration in &declarations {
            let processed = preprocess_decl_with_context(declaration, &mut context);
            elaborate_decl_and_register_with_context(&mut environment, &processed, &mut context)
                .unwrap_or_else(|error| panic!("temporal prelude must elaborate: {error}"));
        }
        environment
    }

    #[test]
    fn clean_temporal_prelude_is_real_kernel_checked_surface() {
        assert!(TEMPORAL_PRELUDE.contains("□"));
        assert!(TEMPORAL_PRELUDE.contains("◇"));
        assert!(TEMPORAL_PRELUDE.contains(" ~> "));
        assert!(
            !TEMPORAL_PRELUDE.contains("MODULE") && !TEMPORAL_PRELUDE.contains("EXTENDS"),
            "TLA+ is an engine format, not the Clean surface"
        );

        let environment = elaborate_temporal_prelude();
        for theorem in [
            "Trust.Temporal.box_unfolds",
            "Trust.Temporal.diamond_unfolds",
            "Trust.Temporal.leadsto_unfolds",
            "Trust.Temporal.box_implies_diamond",
            "Trust.Temporal.leadsto_refl",
        ] {
            let name = Name::from_string(theorem);
            assert!(
                environment.get_const(&name).is_some(),
                "missing {theorem}; temporal constants: {:?}",
                environment
                    .constants()
                    .map(|info| info.name.to_string())
                    .filter(|name| name.contains("Trust.Temporal"))
                    .collect::<Vec<_>>()
            );
            assert_eq!(
                environment.proof_quality(&name),
                Some(ProofQuality::Constructive),
                "{theorem} must be a constructive kernel theorem"
            );
            let axioms = environment.axiom_deps(&name).expect("theorem must be registered");
            assert!(
                axioms.iter().all(|axiom| {
                    let axiom = axiom.to_string();
                    !axiom.contains("sorry")
                        && !axiom.contains("Sorry")
                        && !axiom.contains("trusted")
                }),
                "{theorem} has forbidden axiom closure {axioms:?}"
            );
        }
    }
}
