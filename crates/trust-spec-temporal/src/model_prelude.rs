// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

//! Kernel-check API for the Beyond-TLA executable presentation (lane B1a).
//!
//! The presentation is the Clean source `trust-model-prelude` serves: its
//! [`MODULES`](trust_model_prelude::MODULES), in the B1A-D50 order, starting with this
//! crate's own `Temporal.lean` and `FiniteModel.lean` (one copy: that crate
//! `include_str!`s these files). This module elaborates them, in that order, into a
//! fresh copy of Clean's kernel prelude and kernel-checks theorems stated over them.
//! It grants no proof authority of its own: acceptance is
//! [`clean_surface::checked_theorem`](crate::clean_surface) itself (B1A-D53).
//!
//! * **Closure-based, on the kernel-worker pool.** Every call runs its closure on the
//!   persistent [`kernel_worker`](crate::kernel_worker) pool (B1A-D64) and hands it an
//!   owned clone of that worker's cached prelude. The closure is what keeps every
//!   reduction on a pool thread: kernel reduction recurses deeply and needs the
//!   worker's 64 MiB stack, the prelude cache is per worker, and Clean's declaration
//!   budget is thread-local, armed on the thread that does the work (B1A-D53). (Clean's
//!   `FileContext` is `Send + Sync` at trust's Clean pin `08084daa09`,
//!   `clean-elab/src/file_context.rs:191-199`; that is not what the closure is for.)
//!   [`ModelPrelude`] is therefore not `Send`, so it cannot leave its worker, and
//!   [`elaborate_model_suffix`] and [`check_model_theorem`] refuse
//!   ([`ModelPreludeError::OutsideModelPreludeJob`]) on any thread that is not running
//!   one of this module's closures, so an `Environment` cloned out of a closure is
//!   never checked off the pool. Nothing a closure does reaches the cache or another
//!   call.
//! * **Budgeted.** Every elaboration and every theorem check runs with Clean's ambient
//!   declaration budget armed at [`MODEL_DECL_BUDGET`] ticks. The scope is one call:
//!   one prelude module, one authored suffix, or one theorem check. Exhaustion is the
//!   distinct [`ModelPreludeError::BudgetExhausted`], never a pass and never a
//!   refutation (B1A-D37, B1A-D54). A budget somebody else armed is left in charge,
//!   never refilled.
//! * **Fail-closed elaboration.** A module that does not parse, a declaration that
//!   does not elaborate (a `Failed` leaf included), or an authored parser or
//!   elaborator extension refuses the whole prelude or suffix, with the same rules as
//!   the temporal surface (`elaborate_unit`, `elaborate_suffix_with_parser_prelude`).
//! * **Patched and prefix preludes** (`with_model_prelude_patched`,
//!   `with_model_prelude_prefix`, feature `test-support`) exist only for the lane's
//!   controls and measurements: variant preludes and negative controls (B1A-D36,
//!   B1A-D53), and the Clean capability matrix, which runs on the trust-owned base
//!   modules only (B1A-02a). They are never cached.

use std::cell::{Cell, OnceCell};
use std::fmt;
use std::marker::PhantomData;
use std::sync::OnceLock;

use clean_elab::FileContext;
use clean_kernel::env::Environment;
use clean_kernel::name::Name;

use crate::clean_surface::{
    CleanTemporalCertificateError, checked_theorem, elaborate_suffix_with_parser_prelude,
    elaborate_unit,
};

/// Clean's ambient declaration budget, in kernel ticks, armed for every elaboration
/// and theorem check of this module (B1A-D37), spent per call (one module, suffix or
/// theorem check). Frozen by B1A-02b's calibration (`model_prelude_kernel::budget_calibration`,
/// at clean `08084daa09`; re-frozen from 2^26 by its repair round 1) at 2^24 instead of
/// the initial 2e9 (Clean's CLI per-declaration default, `cli/mod.rs:107`). A
/// D07-shaped fuel loop costs 8 elaboration and 4 check ticks per step, linearly, to
/// 200 000 steps (1.6M ticks; nothing stopped), and RSS grew by about 0.37 KiB per tick
/// (elaboration plus check) at worst. One theorem is two calls, an elaboration and a
/// check, each allowed this budget; charging all of a step's growth to its 4 check
/// ticks bounds the growth by 3 x the worst rate per budget tick. 2^24 is the largest
/// power of two whose projected peak, the process baseline (about 0.16 GiB) plus that
/// growth (about 18 GiB), stays under the lane's 24 GiB RSS ceiling (B1A-D37; 2^25
/// would project to about 36 GiB), so the budget stops a runaway before the ceiling
/// does; the calibration asserts this projection. It leaves 10x the largest calibrated
/// call and over 300x the largest served module (about 51k ticks). Exhaustion is
/// reported, never a pass or a refutation. `0` would disable the budget, so it is not
/// allowed.
pub const MODEL_DECL_BUDGET: u64 = 1 << 24;

const _: () = assert!(MODEL_DECL_BUDGET != 0, "a zero declaration budget disables the budget");

/// Why the model prelude, an authored suffix, or a theorem check was refused.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ModelPreludeError {
    /// The kernel-worker pool could not run the job (no worker could be started, or
    /// the job panicked and its worker was retired).
    Worker(String),
    /// Clean refused: a parse, elaboration or registration failure, a forbidden
    /// authored parser extension, or a theorem the acceptance path refused
    /// (`checked_theorem`: kernel type check, constructive quality, empty axiom
    /// closure, strict certification audit).
    Clean(CleanTemporalCertificateError),
    /// The declaration budget ran out during `unit`. The work did not finish: this is
    /// neither a pass nor a refutation (B1A-D54).
    BudgetExhausted {
        /// The module, suffix or theorem being processed.
        unit: String,
        /// The budget limit that was spent.
        limit: u64,
    },
    /// A module name that is not in `trust_model_prelude::MODULES`.
    UnknownModule(String),
    /// An elaboration or theorem check was called on a thread that is not running one
    /// of this module's closures (`with_model_prelude` and its test-support siblings):
    /// it would reduce off the kernel-worker pool, without the worker's stack, and
    /// under that thread's budget state (B1A-D53, B1A-D64). Nothing was checked.
    OutsideModelPreludeJob(String),
    /// A test-support patch did not match exactly once in its module's source.
    PatchMismatch {
        /// The patched module.
        module: String,
        /// The text the patch looked for.
        find: String,
        /// How many times `find` occurs in the module source.
        occurrences: usize,
    },
}

impl fmt::Display for ModelPreludeError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Worker(detail) => write!(formatter, "model-prelude kernel worker: {detail}"),
            Self::Clean(error) => write!(formatter, "model prelude: {error}"),
            Self::BudgetExhausted { unit, limit } => write!(
                formatter,
                "model prelude: the declaration budget ({limit} ticks) ran out in {unit}; \
                 the work did not finish"
            ),
            Self::UnknownModule(module) => {
                write!(formatter, "model prelude: `{module}` is not a served module")
            }
            Self::OutsideModelPreludeJob(unit) => write!(
                formatter,
                "model prelude: {unit} was not run inside a model-prelude closure on the \
                 kernel-worker pool; nothing was checked"
            ),
            Self::PatchMismatch { module, find, occurrences } => write!(
                formatter,
                "model prelude patch for `{module}` must match exactly once, \
                 matched {occurrences} times: {find:?}"
            ),
        }
    }
}

impl std::error::Error for ModelPreludeError {}

impl From<CleanTemporalCertificateError> for ModelPreludeError {
    fn from(error: CleanTemporalCertificateError) -> Self {
        Self::Clean(error)
    }
}

/// An elaborated model prelude: the kernel environment, the parser/elaborator
/// context that gives its notation meaning, and the source text a later authored
/// suffix is parsed after.
///
/// It is not `Send`: it exists only inside the closure of [`with_model_prelude`] (or a
/// test-support sibling), on the kernel worker that built it, and cannot be returned
/// from that closure.
#[derive(Clone)]
pub struct ModelPrelude {
    environment: Environment,
    context: FileContext,
    /// Every elaborated module's source, joined by `\n`, as
    /// `elaborate_suffix_with_parser_prelude` re-parses it before a suffix.
    parser_prelude: String,
    /// `(module, declaration-budget ticks its elaboration spent)`, in elaboration order.
    modules: Vec<(&'static str, u64)>,
    /// Keeps the prelude on the worker thread that built it (not `Send`).
    _on_its_worker: PhantomData<*const ()>,
}

impl ModelPrelude {
    /// The kernel environment: Clean's kernel prelude plus every elaborated module and
    /// suffix.
    #[must_use]
    pub fn environment(&self) -> &Environment {
        &self.environment
    }

    /// The modules elaborated into this prelude, in order.
    #[must_use]
    pub fn module_names(&self) -> Vec<&'static str> {
        self.modules.iter().map(|(module, _)| *module).collect()
    }

    /// The declaration-budget ticks each module's elaboration spent, in order: the
    /// measurement a budget calibration reads (B1A-D37). A module elaborated under a
    /// budget armed by someone else reports `0`.
    #[must_use]
    pub fn module_budget_used(&self) -> &[(&'static str, u64)] {
        &self.modules
    }

    /// Trust (Clean R80 item 2; `docs/DECISION_QUEUE.md` R80-CONSUMERS-1): a copy
    /// in a NEW elaboration run (`FileContext::fork_run`), to which the prelude's
    /// declarations are imported, so an authored suffix's `attribute
    /// [implemented_by]` / `[extern]` command cannot bind one (Lean refuses it as
    /// imported). A plain clone keeps the run that built the prelude.
    fn in_a_new_run(&self) -> Self {
        Self {
            environment: self.environment.clone(),
            context: self.context.fork_run(),
            parser_prelude: self.parser_prelude.clone(),
            modules: self.modules.clone(),
            _on_its_worker: PhantomData,
        }
    }

    /// Elaborate an authored Clean suffix after the prelude.
    ///
    /// # Errors
    /// See [`elaborate_model_suffix`].
    pub fn elaborate_suffix(
        &mut self,
        source: &str,
        unit: &'static str,
    ) -> Result<(), ModelPreludeError> {
        let Self { environment, context, parser_prelude, .. } = self;
        in_model_prelude_job(unit)?;
        budgeted(unit, || {
            elaborate_suffix_with_parser_prelude(environment, context, parser_prelude, source, unit)
        })
        .map(|((), _)| ())
    }
}

/// Elaborate an authored Clean suffix into `prelude`, with the authored-suffix rules of
/// the temporal surface: the suffix is parsed after the prelude's own source (so its
/// notation applies), only the suffix is elaborated, an authored `syntax`, `macro`,
/// `notation`, `elab` or `open scoped` declaration is refused, and so is any declaration
/// that fails to elaborate. The declaration budget is armed for the call.
///
/// # Errors
/// [`ModelPreludeError::Clean`] when Clean refuses the suffix,
/// [`ModelPreludeError::BudgetExhausted`] when the budget ran out, and
/// [`ModelPreludeError::OutsideModelPreludeJob`] when called outside a model-prelude
/// closure.
pub fn elaborate_model_suffix(
    prelude: &mut ModelPrelude,
    source: &str,
    unit: &'static str,
) -> Result<(), ModelPreludeError> {
    prelude.elaborate_suffix(source, unit)
}

/// Kernel-check theorem `theorem` of `environment` through the temporal surface's
/// acceptance path, `checked_theorem` (B1A-D53): the kernel re-checks the proof against
/// the statement, the proof must be classified constructive with an empty axiom
/// closure, and Clean's strict reachable-provenance audit (`audit_certification`)
/// must certify it. The declaration budget is armed for the check.
///
/// It must be called inside a model-prelude closure (on the kernel-worker pool,
/// B1A-D64); anywhere else it refuses without checking anything.
///
/// # Errors
/// [`ModelPreludeError::Clean`] when any of those checks refuses,
/// [`ModelPreludeError::BudgetExhausted`] when the budget ran out, and
/// [`ModelPreludeError::OutsideModelPreludeJob`] off the pool.
pub fn check_model_theorem(
    environment: &Environment,
    theorem: &str,
) -> Result<(), ModelPreludeError> {
    in_model_prelude_job(theorem)?;
    budgeted(theorem, || checked_theorem(environment, theorem).map(|_| ())).map(|((), _)| ())
}

/// The shape of a refused door statement at Clean's elaborator: the `rfl` proof of
/// `<door> = true` does not have that type (B1A-D54, frozen by B1A-02b at trust's Clean
/// pin `08084daa09`). The in-process elaborator reports it as
/// ``declaration `<name>` failed: TypeMismatch { expected: "<door> = true", actual: "<door> = <door>" }``,
/// with no reduct: a door that reduces to `false` and a door whose reduction is stuck
/// (a free variable, a rigid head) give the same text. (The `clean` CLI prints the
/// reduct, "const mismatch: Bool.false vs Bool.true", FiniteModelCheck.lean:58-60; this
/// path does not.) So the shape is necessary for [`Rejection::Definite`] and not
/// sufficient: [`classify_rejection`] decides Definite only by kernel-checking the
/// complementary door `<door> = false`.
pub const DEFINITE_MISMATCH: &str = "failed: TypeMismatch { expected: \"";

/// The shape of the kernel's top-level lazy-delta give-up (B1A-D54, frozen by B1A-02b):
/// the elaborator accepted `rfl`, then the kernel check that registers the declaration
/// ran its definitional-equality loop into the 10 000-unfolding cap (clean
/// `tc/def_eq/delta.rs:65`, FiniteModelCheck.lean:72-77) and answered "not equal":
/// ``declaration `<name>` failed: KernelCheckFailed { .. detail: "Type mismatch: expected <door> = true, got <door> = <door> (heads: Eq vs Eq)..." }``.
/// Nothing was decided. A statement written as a door never reaches the loop.
pub const STUCK: &str = "failed: KernelCheckFailed {";

/// The text of Clean's per-type-checker heartbeat stop
/// (`TypeError::HeartbeatExceeded`, `DEFAULT_HEARTBEAT_LIMIT`, clean `tc/mod.rs:233`):
/// a resource stop, not a verdict.
pub const HEARTBEAT_EXCEEDED: &str = "heartbeat limit exceeded";

/// The same heartbeat stop in its Debug form (`HeartbeatExceeded { limit: .., profile: .. }`),
/// matched defensively. The temporal surface reports a declaration that fails to elaborate
/// as the Debug form of the elaborator's error (`clean_surface.rs`, `failed: {error:?}`),
/// so a refusal that carried Clean's `TypeError::HeartbeatExceeded` value itself would
/// show this text and not [`HEARTBEAT_EXCEEDED`]'s Display text. No refusal measured at
/// trust's Clean pin `08084daa09` does: the one real heartbeat refusal (`door_heartbeat`
/// in `model_prelude_kernel::clean_capabilities_doors`) carries the Display text inside
/// `KernelCheckFailed { .. detail: "(deterministic) heartbeat limit exceeded, .." }`, and
/// this Debug form was seen only from a `TypeChecker` that test built itself (B1A-09,
/// correcting B1A-02b's repair round, which called it measured).
pub const HEARTBEAT_EXCEEDED_VARIANT: &str = "HeartbeatExceeded {";

/// The text of Clean's ambient declaration-budget stop
/// (`TypeError::DeclarationBudgetExhausted`). [`ModelPreludeError::BudgetExhausted`] is
/// what this module reports for it (the latch is read first); the text is matched too,
/// in case a refusal carries it.
pub const DECLARATION_BUDGET_EXHAUSTED: &str = "declaration budget exhausted";

/// The declaration-budget stop in its Debug form (`DeclarationBudgetExhausted { limit: .. }`),
/// matched defensively, as [`HEARTBEAT_EXCEEDED_VARIANT`] is for the heartbeat stop: no
/// refusal measured at trust's Clean pin carries it (a budget stop is reported as
/// [`ModelPreludeError::BudgetExhausted`], read from the latch first).
pub const DECLARATION_BUDGET_EXHAUSTED_VARIANT: &str = "DeclarationBudgetExhausted {";

/// What a refused door statement means (B1A-D54). Only [`Rejection::Definite`] is a
/// refutation; every other class is "nothing was decided" or "not a door verdict".
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Rejection {
    /// A closed door (no binders) reduces to `false`: the complementary door
    /// `<door> = false` is a kernel-checked theorem (`check_model_theorem`, audit
    /// included).
    Definite,
    /// A door-shaped refusal ([`DEFINITE_MISMATCH`] or [`STUCK`]) that is not a
    /// refutation: its complement is not provable either (the reduction stopped at a
    /// free variable, a rigid head or the lazy-delta cap before an answer), or the door
    /// has binders, whose types may be empty, so even a provable complement refutes
    /// nothing.
    Stuck,
    /// A resource ran out: the declaration budget ([`ModelPreludeError::BudgetExhausted`],
    /// [`DECLARATION_BUDGET_EXHAUSTED`], [`DECLARATION_BUDGET_EXHAUSTED_VARIANT`]) or a
    /// type checker's heartbeats ([`HEARTBEAT_EXCEEDED`], [`HEARTBEAT_EXCEEDED_VARIANT`]).
    /// The work did not finish.
    Budget,
    /// Not a door verdict at all: a parse error, an unknown name, an ill-typed
    /// statement, an audit refusal, a worker failure. A control that is refused for
    /// one of these reasons tests nothing.
    Other,
}

/// A Bool door statement `∀ <binders>, <door> = true`, stated in namespace
/// `namespace` (dot-separated, empty for the root), as a fixture or control states it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DoorStatement<'a> {
    /// The namespace the statement is elaborated in, such as `Trust.Model`.
    pub namespace: &'a str,
    /// Binders before the colon, such as `(n : Nat)`; empty for a closed door.
    pub binders: &'a str,
    /// The Bool-valued door expression.
    pub door: &'a str,
}

impl DoorStatement<'_> {
    /// The Clean source declaring `theorem <name> <binders> : (<door>) = <value> := rfl`
    /// inside the statement's namespace, in a section with `set_option autoImplicit false`.
    ///
    /// Clean's `autoImplicit` is on by default at trust's pin (clean-elab
    /// `options_registry.rs:274`): an unbound identifier in a statement's signature becomes
    /// a hidden implicit binder `∀ {x}`. A door statement's binders are exactly
    /// `binders`, so the option is turned off for it: an unbound name is an elaboration
    /// error (class [`Rejection::Other`]), never a hidden binder whose type may be empty and
    /// which would make a "closed" door's complement refute nothing (B1A-D54(a); B1A-09,
    /// control `door_auto_bound_empty`).
    #[must_use]
    pub fn source(&self, name: &str, value: bool) -> String {
        let mut source = String::new();
        let segments: Vec<&str> =
            self.namespace.split('.').filter(|segment| !segment.is_empty()).collect();
        for segment in &segments {
            source.push_str(&format!("namespace {segment}\n"));
        }
        // A section scopes the option to this one theorem, the scoping Clean's own tests
        // use (clean-elab `wave0_tests.rs`, `test_set_option_auto_implicit_scoped_in_section`).
        // The `set_option .. in` form is not used: at trust's Clean pin a refusal under it
        // names the enclosing namespace instead of the theorem (`door_heartbeat`'s refusal
        // names `Trust.Model`; B1A-09).
        source.push_str(&format!(
            "section\nset_option autoImplicit false\ntheorem {name} {} : ({}) = {value} := rfl\nend\n",
            self.binders, self.door
        ));
        for segment in segments.iter().rev() {
            source.push_str(&format!("end {segment}\n"));
        }
        source
    }

    /// The fully qualified name of theorem `name` declared by [`Self::source`].
    #[must_use]
    pub fn qualified(&self, name: &str) -> String {
        if self.namespace.is_empty() {
            name.to_owned()
        } else {
            format!("{}.{name}", self.namespace)
        }
    }
}

/// Whether a refusal's detail is the door's own mismatch: the statement `<door> = true`
/// elaborated, and its `rfl` proof was refused for that very equation (at the
/// elaborator, [`DEFINITE_MISMATCH`] with `expected: "… = true"`; at the kernel,
/// [`STUCK`] or a re-check refusal with `expected … = true, got`). A mismatch inside
/// the statement (an argument of the wrong type) is not one.
fn is_door_mismatch(detail: &str) -> bool {
    let elaborator = detail.contains(DEFINITE_MISMATCH) && detail.contains("= true\", actual: \"");
    // STUCK's detail, or `checked_theorem`'s kernel re-check (`KernelRejected`).
    let kernel = detail.contains("Type mismatch: expected ") && detail.contains(" = true, got ");
    elaborator || kernel
}

/// The name of the complementary door theorem [`classify_rejection`] elaborates.
const COMPLEMENT_THEOREM: &str = "b1a_door_complement";

/// Classify the refusal `error` of door statement `statement` (B1A-D54).
///
/// Resource stops are [`Rejection::Budget`]. A refusal of the door's own shape
/// ([`DEFINITE_MISMATCH`] or [`STUCK`]) of a closed door (empty `binders`) is
/// [`Rejection::Definite`] exactly when the complementary door `<door> = false := rfl`
/// elaborates after `prelude` and is accepted by [`check_model_theorem`] (kernel
/// re-check, constructive, axiom-free, audited) and its elaborated statement is a closed
/// `<door> = false` with no leading binder: that theorem is the refutation, so Definite
/// never rests on message text. The statements are elaborated with `autoImplicit` off
/// ([`DoorStatement::source`]), so an unbound name cannot become a hidden binder. If the
/// complement runs out of budget the class is Budget, and otherwise Stuck. A door with
/// binders is never Definite: `∀ b,
/// <door> = false` refutes `∀ b, <door> = true` only when the binder types are
/// inhabited (under `(h : False)` both hold vacuously), so its door-shaped refusal is
/// Stuck. Everything else is [`Rejection::Other`].
///
/// It elaborates, so it must be called inside a model-prelude closure; `prelude` is
/// cloned, never changed.
#[must_use]
pub fn classify_rejection(
    prelude: &ModelPrelude,
    statement: &DoorStatement<'_>,
    error: &ModelPreludeError,
) -> Rejection {
    let detail = match error {
        ModelPreludeError::BudgetExhausted { .. } => return Rejection::Budget,
        ModelPreludeError::Clean(
            CleanTemporalCertificateError::Elaborate { detail, .. }
            | CleanTemporalCertificateError::KernelRejected(detail),
        ) => detail.as_str(),
        _ => return Rejection::Other,
    };
    if [
        HEARTBEAT_EXCEEDED,
        HEARTBEAT_EXCEEDED_VARIANT,
        DECLARATION_BUDGET_EXHAUSTED,
        DECLARATION_BUDGET_EXHAUSTED_VARIANT,
    ]
    .iter()
    .any(|shape| detail.contains(shape))
    {
        return Rejection::Budget;
    }
    if !is_door_mismatch(detail) {
        return Rejection::Other;
    }
    // `∀ binders, <door> = false` refutes `∀ binders, <door> = true` only when the
    // binder types are inhabited: under `(h : False)` both are vacuously true and the
    // complement proves nothing. Only a closed door can be Definite.
    if !statement.binders.trim().is_empty() {
        return Rejection::Stuck;
    }
    let mut complement = prelude.clone();
    let name = statement.qualified(COMPLEMENT_THEOREM);
    let refuted = complement
        .elaborate_suffix(&statement.source(COMPLEMENT_THEOREM, false), "door complement")
        .and_then(|()| {
            // Defence in depth for the closed-door rule: whatever the source said, the
            // complement Definite rests on must be elaborated as a closed `<door> = false`
            // with no leading binder (an auto-bound implicit would be one).
            if is_closed_false_equation(complement.environment(), &name) {
                check_model_theorem(complement.environment(), &name).map(|()| true)
            } else {
                Ok(false)
            }
        });
    match refuted {
        Ok(true) => Rejection::Definite,
        Ok(false) => Rejection::Stuck,
        Err(ModelPreludeError::BudgetExhausted { .. }) => Rejection::Budget,
        Err(_) => Rejection::Stuck,
    }
}

/// Whether theorem `name` of `environment` states a closed `@Eq Bool <door> false`: no
/// leading binder, the head `Eq` applied to three arguments, the first `Bool` and the last
/// `false` (the source literal elaborates to the root constant `false` at trust's Clean
/// pin; `Bool.false` is accepted too), and no free or loose bound variable.
fn is_closed_false_equation(environment: &Environment, name: &str) -> bool {
    use clean_kernel::expr::ExprKind;

    let Some(constant) = environment.get_const(&Name::from_string(name)) else {
        return false;
    };
    let statement = &constant.type_;
    let is_const = |expr: &clean_kernel::expr::Expr, expected: &str| matches!(expr.kind(), ExprKind::Const(head, _) if *head == Name::from_string(expected));
    let arguments = statement.get_app_args();
    !statement.is_pi()
        && is_const(statement.get_app_fn(), "Eq")
        && arguments.len() == 3
        && is_const(arguments[0], "Bool")
        && (is_const(arguments[2], "false") || is_const(arguments[2], "Bool.false"))
        && !statement.has_fvar_quick()
        && !statement.has_loose_bvars()
}

/// Run `f` on a kernel worker with an owned clone of the model prelude.
///
/// The prelude is built once per worker thread (with external import search
/// disabled) and cached there; the closure receives a clone, so it may elaborate
/// suffixes and check theorems freely. The clone is a new elaboration run
/// (`hand_out`).
///
/// # Errors
/// The prelude's own build error (cached per worker: a prelude that does not
/// elaborate refuses every call), or [`ModelPreludeError::Worker`] when the pool
/// could not run the job.
pub fn with_model_prelude<T, F>(f: F) -> Result<T, ModelPreludeError>
where
    T: Send + 'static,
    F: FnOnce(ModelPrelude) -> T + Send + 'static,
{
    on_kernel_worker(move || {
        thread_local! {
            static MODEL_PRELUDE: OnceCell<Result<ModelPrelude, ModelPreludeError>> =
                const { OnceCell::new() };
        }
        let prelude = MODEL_PRELUDE.with(|cache| {
            hand_out(cache.get_or_init(|| {
                let sources: Vec<(&'static str, String)> = trust_model_prelude::MODULES
                    .iter()
                    .map(|(module, _, source)| (*module, (*source).to_owned()))
                    .collect();
                build_model_prelude(&sources)
            }))
        })?;
        Ok(f(prelude))
    })
}

/// One test-support edit of a served module: replace the single occurrence of
/// `find` in `module`'s source with `replace`.
#[cfg(feature = "test-support")]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ModulePatch {
    /// A module of `trust_model_prelude::MODULES`.
    pub module: String,
    /// Text that must occur exactly once in that module's source.
    pub find: String,
    /// Its replacement.
    pub replace: String,
}

/// Like [`with_model_prelude`], over a prelude whose module sources are first edited
/// by `patches` (feature `test-support`, B1A-D53). Each patch must match exactly once
/// in its module's source, patches apply in order, and the patched prelude is built
/// for this call only, never cached.
///
/// # Errors
/// [`ModelPreludeError::UnknownModule`] or [`ModelPreludeError::PatchMismatch`] for a
/// bad patch, otherwise as [`with_model_prelude`].
#[cfg(feature = "test-support")]
pub fn with_model_prelude_patched<T, F>(
    patches: Vec<ModulePatch>,
    f: F,
) -> Result<T, ModelPreludeError>
where
    T: Send + 'static,
    F: FnOnce(ModelPrelude) -> T + Send + 'static,
{
    let mut sources: Vec<(&'static str, String)> = trust_model_prelude::MODULES
        .iter()
        .map(|(module, _, source)| (*module, (*source).to_owned()))
        .collect();
    for patch in &patches {
        let Some((_, source)) = sources.iter_mut().find(|(module, _)| *module == patch.module)
        else {
            return Err(ModelPreludeError::UnknownModule(patch.module.clone()));
        };
        let occurrences =
            if patch.find.is_empty() { 0 } else { source.matches(&patch.find).count() };
        if occurrences != 1 {
            return Err(ModelPreludeError::PatchMismatch {
                module: patch.module.clone(),
                find: patch.find.clone(),
                occurrences,
            });
        }
        *source = source.replacen(&patch.find, &patch.replace, 1);
    }
    on_kernel_worker(move || Ok(f(hand_out(&build_model_prelude(&sources))?)))
}

/// Like [`with_model_prelude`], over a prelude of only the served modules up to and
/// including `through`, in MODULES order (feature `test-support`). B1A-02a's Clean
/// capability matrix runs on `Trust.FiniteModel`'s prefix, the trust-owned base every
/// `Trust.Model` module is elaborated after, so its feature files may declare the
/// encoding's own names without colliding with the modules later rows add. The prefix
/// prelude is built for this call only, never cached.
///
/// # Errors
/// [`ModelPreludeError::UnknownModule`] when `through` is not served, otherwise as
/// [`with_model_prelude`].
#[cfg(feature = "test-support")]
pub fn with_model_prelude_prefix<T, F>(through: &str, f: F) -> Result<T, ModelPreludeError>
where
    T: Send + 'static,
    F: FnOnce(ModelPrelude) -> T + Send + 'static,
{
    let Some(end) =
        trust_model_prelude::MODULES.iter().position(|(module, _, _)| *module == through)
    else {
        return Err(ModelPreludeError::UnknownModule(through.to_owned()));
    };
    let sources: Vec<(&'static str, String)> = trust_model_prelude::MODULES[..=end]
        .iter()
        .map(|(module, _, source)| (*module, (*source).to_owned()))
        .collect();
    on_kernel_worker(move || Ok(f(hand_out(&build_model_prelude(&sources))?)))
}

/// The names the model prelude adds to Clean's kernel prelude
/// (`Environment::with_prelude()`), from its constant, inductive, constructor and
/// recursor tables, sorted and without duplicates. For an environment built by this
/// module after authored suffixes, those suffixes' names are included too.
#[must_use]
pub fn prelude_added_constants(environment: &Environment) -> Vec<Name> {
    let base = kernel_prelude();
    let mut added: Vec<Name> = environment
        .constants()
        .map(|constant| &constant.name)
        .chain(environment.inductives().map(|inductive| &inductive.name))
        .chain(environment.constructors().map(|constructor| &constructor.name))
        .chain(environment.recursors().map(|recursor| &recursor.name))
        .filter(|name| !in_environment(base, name))
        .cloned()
        .collect();
    added.sort_by_cached_key(ToString::to_string);
    added.dedup();
    added
}

fn in_environment(environment: &Environment, name: &Name) -> bool {
    environment.get_const(name).is_some()
        || environment.get_inductive(name).is_some()
        || environment.get_constructor(name).is_some()
        || environment.get_recursor(name).is_some()
}

/// Clean's kernel prelude, built once per process. Callers clone it.
fn kernel_prelude() -> &'static Environment {
    static KERNEL_PRELUDE: OnceLock<Environment> = OnceLock::new();
    KERNEL_PRELUDE.get_or_init(Environment::with_prelude)
}

/// Elaborate `modules` in order into a fresh kernel prelude. The first module is
/// elaborated as a whole unit, as the temporal surface elaborates `Temporal.lean`;
/// each later one as a suffix parsed after everything before it, so earlier modules'
/// notation applies and a module may not add parser or elaborator extensions. Each
/// module is one budgeted call.
fn build_model_prelude(
    modules: &[(&'static str, String)],
) -> Result<ModelPrelude, ModelPreludeError> {
    let mut environment = kernel_prelude().clone();
    let mut context = FileContext::new();
    context.disable_external_import_search();
    let mut parser_prelude = String::new();
    let mut elaborated = Vec::with_capacity(modules.len());
    for (index, (module, source)) in modules.iter().enumerate() {
        let module: &'static str = module;
        let ((), used) = if index == 0 {
            budgeted(module, || {
                elaborate_unit(&mut environment, &mut context, source, module, None)
            })?
        } else {
            budgeted(module, || {
                elaborate_suffix_with_parser_prelude(
                    &mut environment,
                    &mut context,
                    &parser_prelude,
                    source,
                    module,
                )
            })?
        };
        if index > 0 {
            parser_prelude.push('\n');
        }
        parser_prelude.push_str(source);
        elaborated.push((module, used));
    }
    Ok(ModelPrelude {
        environment,
        context,
        parser_prelude,
        modules: elaborated,
        _on_its_worker: PhantomData,
    })
}

/// Trust (Clean R80 item 2; `docs/DECISION_QUEUE.md` R80-CONSUMERS-1): the copy of
/// a built prelude every closure of this module receives, in a new elaboration run
/// ([`ModelPrelude::in_a_new_run`]); the cached prelude, and a per-call one, stay in
/// the run that built them and are never handed out themselves.
fn hand_out(
    built: &Result<ModelPrelude, ModelPreludeError>,
) -> Result<ModelPrelude, ModelPreludeError> {
    built.as_ref().map(ModelPrelude::in_a_new_run).map_err(Clone::clone)
}

/// Run `operation` with the declaration budget armed at [`MODEL_DECL_BUDGET`] and
/// return its value with the ticks it spent.
///
/// The budget is thread-local. If it is disabled here (the state of every thread until
/// someone arms it), it is armed for the call and disabled again afterwards, unwinding
/// included, so a pooled worker never carries it into another lane's job. If somebody
/// else already armed it, it is left alone: Clean can set a limit but cannot restore a
/// partly spent one, so re-arming would refill the outer owner's fuel (the rule
/// clean-verify's spec budget follows). Either way the exhaustion latch is read after
/// the call, and it wins over the call's own result.
fn budgeted<T>(
    unit: &str,
    operation: impl FnOnce() -> Result<T, CleanTemporalCertificateError>,
) -> Result<(T, u64), ModelPreludeError> {
    let scope = ArmedBudget::arm(MODEL_DECL_BUDGET);
    let outcome = operation();
    let used = if scope.armed_here { clean_kernel::tc::declaration_budget_used() } else { 0 };
    if clean_kernel::tc::declaration_budget_exhausted() {
        return Err(ModelPreludeError::BudgetExhausted {
            unit: unit.to_owned(),
            limit: clean_kernel::tc::declaration_budget_limit(),
        });
    }
    drop(scope);
    Ok((outcome?, used))
}

/// Arms the ambient budget when it is disabled, and disables it again on drop.
struct ArmedBudget {
    armed_here: bool,
}

impl ArmedBudget {
    fn arm(limit: u64) -> Self {
        if clean_kernel::tc::declaration_budget_limit() != 0 {
            return Self { armed_here: false };
        }
        clean_kernel::tc::set_declaration_budget(limit);
        Self { armed_here: true }
    }
}

impl Drop for ArmedBudget {
    fn drop(&mut self) {
        if self.armed_here {
            clean_kernel::tc::clear_declaration_budget();
        }
    }
}

thread_local! {
    /// How many of this module's closures are running on this thread (nested calls
    /// run on other workers, so this is 0 or 1 in practice).
    static MODEL_PRELUDE_JOBS: Cell<usize> = const { Cell::new(0) };
}

/// Marks the current thread as running a model-prelude closure for its lifetime,
/// unwinding included.
struct ModelPreludeJob;

impl ModelPreludeJob {
    fn enter() -> Self {
        MODEL_PRELUDE_JOBS.with(|jobs| jobs.set(jobs.get() + 1));
        Self
    }
}

impl Drop for ModelPreludeJob {
    fn drop(&mut self) {
        MODEL_PRELUDE_JOBS.with(|jobs| jobs.set(jobs.get() - 1));
    }
}

/// Refuse `unit` unless this thread is running a model-prelude closure (B1A-D53).
fn in_model_prelude_job(unit: &str) -> Result<(), ModelPreludeError> {
    if MODEL_PRELUDE_JOBS.with(Cell::get) == 0 {
        return Err(ModelPreludeError::OutsideModelPreludeJob(unit.to_owned()));
    }
    Ok(())
}

fn on_kernel_worker<T: Send + 'static>(
    operation: impl FnOnce() -> Result<T, ModelPreludeError> + Send + 'static,
) -> Result<T, ModelPreludeError> {
    let job = move || {
        let _job = ModelPreludeJob::enter();
        operation()
    };
    crate::kernel_worker::run_on_kernel_worker(job).map_err(|error| match error {
        crate::kernel_worker::KernelWorkerError::Spawn(error) => {
            ModelPreludeError::Worker(format!("could not start a kernel worker: {error}"))
        }
        crate::kernel_worker::KernelWorkerError::Panicked => {
            ModelPreludeError::Worker("the model-prelude job panicked".to_owned())
        }
    })?
}

// `ModelPrelude` must not be `Send` (it may not leave its worker): this fails to
// compile, as an ambiguous impl, if it ever becomes `Send`.
const _: fn() = || {
    trait AmbiguousIfSend<A> {
        fn assert_not_send() {}
    }
    impl<T: ?Sized> AmbiguousIfSend<()> for T {}
    impl<T: ?Sized + Send> AmbiguousIfSend<u8> for T {}
    let _ = <ModelPrelude as AmbiguousIfSend<_>>::assert_not_send;
};

#[cfg(test)]
mod tests {
    use super::*;

    /// The acceptance path refuses to run off a model-prelude job: on the caller's
    /// thread and on a pool worker that is not running one, it checks nothing; inside
    /// a job it runs (here: a missing theorem). Cheap: nothing is elaborated.
    #[test]
    fn checks_refuse_outside_a_model_prelude_job() {
        let outside = check_model_theorem(kernel_prelude(), "noSuchTheorem");
        assert_eq!(
            outside,
            Err(ModelPreludeError::OutsideModelPreludeJob("noSuchTheorem".to_owned()))
        );
        let inside =
            on_kernel_worker(|| Ok(check_model_theorem(kernel_prelude(), "noSuchTheorem")))
                .expect("job runs");
        assert_eq!(
            inside,
            Err(ModelPreludeError::Clean(CleanTemporalCertificateError::MissingTheorem(
                "noSuchTheorem".to_owned()
            )))
        );
        let bare_worker = crate::kernel_worker::run_on_kernel_worker(|| {
            check_model_theorem(kernel_prelude(), "noSuchTheorem")
        })
        .expect("job runs");
        assert_eq!(
            bare_worker,
            Err(ModelPreludeError::OutsideModelPreludeJob("noSuchTheorem".to_owned()))
        );
    }

    /// The budget scope arms a disabled budget, leaves an armed one alone, and always
    /// leaves the thread as it found it. Cheap: nothing is elaborated.
    #[test]
    fn the_budget_scope_never_leaks_or_refills() {
        let observed = crate::kernel_worker::run_on_kernel_worker(|| {
            clean_kernel::tc::clear_declaration_budget();
            let inside = budgeted("scope", || Ok(clean_kernel::tc::declaration_budget_limit()))
                .expect("an empty operation finishes");
            let after = clean_kernel::tc::declaration_budget_limit();

            clean_kernel::tc::set_declaration_budget(7);
            let outer = budgeted("nested", || Ok(clean_kernel::tc::declaration_budget_limit()))
                .expect("an empty operation finishes");
            let outer_after = clean_kernel::tc::declaration_budget_limit();
            clean_kernel::tc::clear_declaration_budget();
            (inside.0, after, outer.0, outer_after)
        })
        .expect("job runs");
        assert_eq!(observed, (MODEL_DECL_BUDGET, 0, 7, 7));
    }

    /// Trust (Clean R80 item 2; `docs/DECISION_QUEUE.md` R80-CONSUMERS-1): every
    /// closure of this module receives its prelude through `hand_out`, a new
    /// elaboration run, so a suffix's command form of `[implemented_by]` on a
    /// served declaration is refused with Lean's text, and on one of the suffix's
    /// own declarations it binds. `with_model_prelude`'s cached prelude, which no
    /// debug test builds (B1A-D42), goes out through the same `hand_out`, so this
    /// is that path's mutation control. Cheap: the prelude is `Trust.Temporal`
    /// alone.
    #[test]
    fn a_handed_out_prelude_is_a_new_run() {
        const REBIND: &str = "def myDrop {State : Type} (b : Trust.Temporal.Behavior State) \
                              (n : Nat) : Trust.Temporal.Behavior State := b\n\
                              attribute [implemented_by myDrop] Trust.Temporal.drop\n";
        const OWN: &str = "def mySlow (n : Nat) : Nat := n + 2\n\
                           def myFast (n : Nat) : Nat := n + 1\n\
                           attribute [implemented_by myFast] mySlow\n";
        let (refused, bound) = on_kernel_worker(|| {
            let built = build_model_prelude(&[(
                "Trust.Temporal",
                trust_model_prelude::TEMPORAL.to_owned(),
            )]);
            let mut rebinding = hand_out(&built)?;
            let mut own = hand_out(&built)?;
            let refused = rebinding.elaborate_suffix(REBIND, "authored suffix");
            let bound = own.elaborate_suffix(OWN, "authored suffix").map(|()| {
                own.environment().get_implemented_by(&Name::from_string("mySlow")).cloned()
            });
            Ok((refused, bound))
        })
        .expect("the Trust.Temporal prelude elaborates");
        assert_eq!(
            refused,
            Err(ModelPreludeError::Clean(CleanTemporalCertificateError::Elaborate {
                unit: "authored suffix",
                detail: "Cannot add attribute `[implemented_by]` to declaration \
                         `Trust.Temporal.drop` because it is in an imported module"
                    .to_owned(),
            }))
        );
        assert_eq!(bound, Ok(Some(Name::from_string("myFast"))));
    }
}
