// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! A finite model an island DECLARES is model-checked by the compiler on its
//! own (temporal P2 "detection by type", aterm
//! `docs/DESIGN-trust-temporal-models-2026-09-29.md` §5).
//!
//! OPT-IN PER SESSION ([`CleanIslandSession::enable_model_checks`]). The
//! compiler builds many sessions over the same islands — the resolver's mint,
//! one per Clean-origin body, one per importing crate — and only the one that
//! REPORTS island results (the verify-pass session) turns this on, so a model
//! is searched once per build. Every other session, and the `.lean` front
//! door, elaborates the island's own declarations and nothing more.
//!
//! Detection is by kernel TYPE over kernel NAMES, never text: every constant
//! the island batch added (the environment's delta) that the island lists as
//! registered and whose type reduces to `Trust.Temporal.FiniteModel.ScalarModel`
//! is a model. For each one the session serves `Trust.FiniteModelCheck` and
//! asks the kernel for the weak-head normal form of `safetyVerdict M budget` —
//! ONE evaluation of the bounded search.
//!
//! - `ok`: the kernel is handed the theorem `trust_checked_safe.M :
//!   ScalarModel.safetyClaim M := proveSafe M budget (Eq.refl ok)` as kernel
//!   terms and checks it ([`CleanIslandModelVerdict::Safe`]). The name is in
//!   the compiler's reserved `trust_checked_*` namespace, which no island can
//!   declare into, so nothing an author writes can stand in for it.
//! - `invariantFails`: the island is REJECTED at the model's definition, with
//!   the state and the invariant named ([`CleanIslandModelVerdict::Unsafe`]).
//!   Declaring an invariant is the claim. This is the kernel's evaluation of
//!   the untrusted search, not a theorem.
//! - an undecided finite model is an ERROR unless it explicitly declares
//!   `def M.bounded : String := "reason for the incomplete check"`. That
//!   declaration permits only an incomplete check, never a false invariant;
//!   the compiler still reports `Undecided` and grants no proof authority.
//!   The same rule covers an undecided or searched-but-unproved finite
//!   progress claim; bounded claims still reject a kernel-confirmed livelock.
//!
//! The budget is a STATE budget, [`DEFAULT_STATE_BUDGET`] unless the batch
//! declares `def M.stateBudget : Nat := …`. A model that is unsafe on purpose
//! takes a parameter (`def M (buggy : Nat) : ScalarModel`): its type is a
//! function, so it is not a model constant and is not checked until applied.
//!
//! Nothing here is trusted: the only positive result is a theorem the kernel
//! checked, stated by construction as `ScalarModel.safetyClaim (Const M)`.

use std::collections::{HashMap, HashSet};

use clean_kernel::name::NameInner;
use clean_kernel::tc::TypeChecker;
use clean_kernel::{ConstantKind, Declaration, Environment, Expr, ExprKind, Level, Literal, Name};

use super::model_progress::{self, CertificateRow, ProgressSearch};
use super::model_trace::{
    CleanIslandModelStep, CleanIslandModelTruncation, Effort, Presearch, list_of, nat_list,
    presearch_and_first_truncation, render_lasso, render_run, shortest_run,
};
use super::{CleanIslandDiagnostic, CleanIslandOutcome, CleanIslandSession};

/// How many reachable states the kernel is asked to prove safe by default
/// (`def M.stateBudget : Nat := …`, or the session's
/// [`CleanIslandSession::set_model_state_budget`], overrides it).
///
/// Measured in process (release) on a real program's 270 models: every model
/// of at most 256 states is proved, median 0.2 s and at most 2.1 s. From 257
/// to 1,024 states 25 of 26 are proved, median 4.9 s and at most 16.6 s. Past
/// that the kernel's evaluation limit decides: 3 of 19 up to 4,096 states and
/// none above, and an attempt that reaches the limit costs tens of seconds
/// before it is reported. So the default proves what is cheap, and a model's
/// author opts in to more with `stateBudget`.
pub const DEFAULT_STATE_BUDGET: u64 = 256;

/// The search size (expression nodes evaluated, [`CleanIslandModelCheck::work`])
/// past which the kernel is not asked to prove a model or claim BY DEFAULT:
/// under 10 s of kernel time. A model or claim that declares its own
/// `stateBudget` opts in up to [`OPT_IN_SECONDS`]. Measured on the same 270
/// models under Clean's fixed default limit, before the check sized it
/// ([`HEARTBEATS_PER_WORK`]): every model under 300,000 was proved (time grows
/// with work, about 2 s per 100,000), 4 of 32 above 400,000, and none above
/// 634,000, where that limit stopped them.
pub const KERNEL_WORK_LIMIT: u64 = 650_000;

/// The estimated kernel time ([`Effort::seconds`]) past which the kernel is
/// not asked even when the model or claim declares its own `stateBudget` (the
/// author's opt-in to a longer build): ten minutes per proof.
pub const OPT_IN_SECONDS: f64 = 600.0;

/// The kernel's evaluation budget for a proof, per unit of search size: the
/// heartbeats `add_decl` may spend checking a safety or progress theorem are
/// this times the search's work, and never fewer than the kernel's default
/// (which is what stopped every proof past about 650,000).
pub const HEARTBEATS_PER_WORK: u64 = 40;

/// The heartbeats per estimated second of kernel time, a floor under
/// [`HEARTBEATS_PER_WORK`] for a model whose cost is its successor rows rather
/// than its expressions. The proof that spent the most time per unit of work
/// (374 s, 1.1M work, when the kernel still searched) passed with 44M
/// heartbeats, so about 118,000 a second.
pub const HEARTBEATS_PER_SECOND: u64 = 600_000;

/// A progress certificate costs about this many times a safety proof of the
/// same state space (measured: 2.3x, 2.0x and 3.1x on three claims).
const PROGRESS_FACTOR: f64 = 2.5;

/// The estimated kernel seconds of a safety proof ([`Effort::seconds`], one
/// machine: an order of magnitude, not a promise).
fn safety_seconds(effort: &Effort) -> f64 {
    effort.seconds()
}

/// The same for a progress claim.
fn progress_seconds(effort: &Effort) -> f64 {
    PROGRESS_FACTOR * effort.seconds()
}

fn seconds_text(seconds: f64) -> String {
    if seconds < 1.0 {
        "under a second".to_owned()
    } else {
        let seconds = seconds.round() as u64;
        format!("roughly {seconds} s")
    }
}

/// Whether the kernel is asked to prove a model or claim the search found no
/// counterexample to, by the search's size and whose budget covers it.
enum KernelAsk {
    Prove,
    /// Not asked; what would have it asked.
    Hint(String),
    /// Not asked: past what the kernel is ever asked.
    TooLarge(String),
}

const MODEL_MODULE: &str = "Trust.FiniteModel";
const CHECK_MODULE: &str = "Trust.FiniteModelCheck";
/// The type of a binding between a model and the code, and its constructor
/// (`Trust.Protocol`).
/// The served module that defines `Binding` (and nothing else).
const BINDING_MODULE: &str = "Trust.Binding";
const BINDING_TYPE: &str = "Trust.Protocol.Binding";
const BINDING_CONSTRUCTOR: &str = "Trust.Protocol.Binding.mk";
/// The type of a seal on a type of the crate, and its constructor (the same
/// served module).
const SEAL_TYPE: &str = "Trust.Protocol.Seal";
const SEAL_CONSTRUCTOR: &str = "Trust.Protocol.Seal.mk";
pub(super) const NAMESPACE: &str = "Trust.Temporal.FiniteModel";
/// The root of the automatic theorems' names: inside
/// [`super::SEEDED_MODEL_PREFIX`], which the strict island policy reserves.
const THEOREM_ROOT: &str = "trust_checked_safe";
/// The same, for the theorems that prove progress claims.
const LIVE_THEOREM_ROOT: &str = "trust_checked_live";

/// One binding an island declared between a model and the code beside it (a
/// constant whose kernel type is `Trust.Protocol.Binding`), read out of the
/// kernel term. It is data with no proof: the compiler checks it against the
/// crate's code (every write of the field must come from one of `arms`, or
/// from a `carried_by` fn) and fails the build at `start..end` otherwise.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct CleanIslandBinding {
    /// The binding constant's kernel name, as the kernel prints it.
    pub name: String,
    /// The Rust field path (`config.harness`).
    pub path: String,
    /// The message variants whose arms may write the field.
    pub arms: Vec<String>,
    /// The fns whose writes are declared carry-overs.
    pub carried_by: Vec<String>,
    /// Island-relative byte offsets of the definition's first line.
    pub start: usize,
    pub end: usize,
}

/// One seal an island declared on a type of the crate (a constant whose
/// kernel type is `Trust.Protocol.Seal`), read out of the kernel term. Data
/// with no proof, like a binding: the compiler checks the crate's code
/// against it and fails the build at `start..end` otherwise.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct CleanIslandSeal {
    /// The seal constant's kernel name, as the kernel prints it.
    pub name: String,
    /// The sealed type (`Generational`, `order::Generational`).
    pub type_name: String,
    /// The fns that may change a field of a value of it.
    pub writers: Vec<String>,
    /// The fns that may build a value of it.
    pub makers: Vec<String>,
    /// The fns that may call a maker.
    pub made_by: Vec<String>,
    /// The fns of other crates that may be handed a value holding one.
    pub trusts: Vec<String>,
    /// Island-relative byte offsets of the definition's first line.
    pub start: usize,
    pub end: usize,
}

/// One finite model an island declared, and what the automatic check found.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct CleanIslandModelCheck {
    /// The model constant's kernel name, as the kernel prints it (for a
    /// progress claim, the claim's).
    pub model: String,
    /// Whether this is a progress claim (`ScalarProgress`), not a model.
    pub progress: bool,
    /// The state budget the check ran with: `256`, or the value and name of
    /// the batch's own (``2 (`M.stateBudget`)``).
    pub budget: String,
    /// Explicit permission for an incomplete finite-model or progress check, with the
    /// author's nonempty reason (`def M.bounded : String := "…"`). No proof.
    #[serde(default)]
    pub bounded: Option<String>,
    pub verdict: CleanIslandModelVerdict,
    /// For a model the search exhausted: the size of that search in expression
    /// nodes evaluated, which is what the kernel repeats to prove it.
    pub work: Option<u64>,
    /// A subtraction that stops at zero on a state the check explored: the
    /// verdict is about the model as written, over the naturals, and this is
    /// where an integer reading of it differs. See [`Self::truncation_report`].
    pub truncation: Option<CleanIslandModelTruncation>,
    /// Where the model is defined: BYTE OFFSETS into the island text (the
    /// first line of its `def`; the whole island when the parse does not show
    /// it).
    pub start: usize,
    pub end: usize,
}

/// See the module docs.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum CleanIslandModelVerdict {
    /// The kernel checked `theorem`, which states `ScalarModel.safetyClaim
    /// <model>` by construction.
    Safe { theorem: String },
    /// A reachable state breaks an invariant. `state` is `(variable, value)`
    /// in the model's declaration order. `run` is a shortest run from the
    /// initial state to it (`model_trace`: an untrusted explanation held to the
    /// kernel's answer), empty when none could be reconstructed.
    Unsafe { state: Vec<(String, u64)>, invariant: String, run: Vec<CleanIslandModelStep> },
    /// The check decided nothing; `reason` says why and what to do.
    Undecided { reason: String },
    /// A PROGRESS CLAIM (`ScalarProgress`: the goal holds again and again on
    /// every fair run) fails: a fair run of `model` leaves the goal for good.
    /// `stem` runs from the initial state; `cycle` is the loop it then repeats
    /// forever, empty when it stutters at the stem's last state. The kernel
    /// confirmed it (`model_progress`).
    Livelock { model: String, stem: Vec<CleanIslandModelStep>, cycle: Vec<CleanIslandModelStep> },
    /// A PROGRESS CLAIM the kernel proved: `theorem` states
    /// `ScalarProgress.claim <claim>` by construction, from the certificate
    /// of the `states` reachable states of `model`.
    Live { model: String, theorem: String, states: usize },
    /// A progress claim an untrusted search found no counterexample to, over
    /// all `states` reachable states of `model`, and the kernel did NOT prove
    /// (`unproved` says why: no certificate was found, it is over its
    /// budget, it is too large for the kernel). An error unless the claim
    /// explicitly declares itself bounded, in which case it is a warning.
    Searched { model: String, states: usize, unproved: String },
}

impl CleanIslandModelCheck {
    /// The one wording every compiler seam reports a model check in. An
    /// `Unsafe` model is already an error on its island (the same text).
    #[must_use]
    pub fn report(&self) -> String {
        let Self { model, budget, .. } = self;
        match &self.verdict {
            CleanIslandModelVerdict::Safe { theorem } => format!(
                "finite model `{model}` proved safe by the kernel: every reachable state \
                 satisfies every invariant (`{theorem} : ScalarModel.safetyClaim {model}`, state \
                 budget {budget})"
            ),
            CleanIslandModelVerdict::Unsafe { state, invariant, run } => {
                let state = state
                    .iter()
                    .map(|(name, value)| {
                        if *value == u64::MAX {
                            format!("{name} = ?")
                        } else {
                            format!("{name} = {value}")
                        }
                    })
                    .collect::<Vec<_>>()
                    .join(", ");
                format!(
                    "finite model `{model}` is unsafe: the reachable state {{ {state} }} breaks \
                     invariant `{invariant}`. Trust checks every `ScalarModel` an island \
                     declares; the kernel evaluates the invariant false in that state{}. Fix the \
                     model or the system it describes. A model that is unsafe on purpose takes a \
                     parameter (`def M (buggy : Nat) : ScalarModel`): a function is not checked \
                     until applied.",
                    if run.is_empty() { "" } else { " and replayed the run to it (below)" }
                )
            }
            CleanIslandModelVerdict::Livelock { model: machine, stem, cycle } => {
                let last = stem.last().map_or_else(String::new, |step| {
                    step.state
                        .iter()
                        .map(|(name, value)| format!("{name} = {value}"))
                        .collect::<Vec<_>>()
                        .join(", ")
                });
                let then = if cycle.is_empty() {
                    "stutters there forever (no fair action can change that state)".to_owned()
                } else {
                    format!("repeats a loop of {} step(s) forever", cycle.len())
                };
                format!(
                    "progress claim `{model}` fails: a fair run of `{machine}` leaves the goal \
                     for good. It reaches {{ {last} }} and {then}, and the goal never holds \
                     again. Trust checks every `ScalarProgress` an island declares; the kernel \
                     replayed the run and evaluates the goal false and the fairness conditions \
                     met on the loop (below). Fix the model, the fairness it assumes, or the \
                     system it describes."
                )
            }
            CleanIslandModelVerdict::Live { model: machine, theorem, states } => format!(
                "progress claim `{model}` proved by the kernel: on every fair run of `{machine}` \
                 the goal holds again and again (`{theorem} : ScalarProgress.claim {model}`, from \
                 a certificate of its {states} reachable states)"
            ),
            CleanIslandModelVerdict::Searched { model: machine, states, unproved } => format!(
                "progress claim `{model}` is NOT proved: {unproved}. An untrusted search of all \
                 {states} reachable states of `{machine}` found no fair run that leaves the goal \
                 for good. {}",
                self.incomplete_disposition()
            ),
            CleanIslandModelVerdict::Undecided { reason } if self.progress => format!(
                "progress claim `{model}` was NOT checked: {reason}. {}. Nothing is claimed about \
                 it, and the kernel proves no progress claim yet",
                self.incomplete_disposition()
            ),
            CleanIslandModelVerdict::Undecided { reason } => format!(
                "finite model `{model}` was NOT checked: {reason}. {}. Nothing is claimed about \
                 it; an authored theorem of `ScalarModel.safetyClaim {model}` is checked as usual",
                self.incomplete_disposition()
            ),
        }
    }

    fn incomplete_disposition(&self) -> String {
        match &self.bounded {
            Some(why) => format!("explicitly declared bounded: {why}"),
            None => format!(
                "an incomplete check must be decided or explicitly declare \
                 `def {}.bounded : String := \"reason for the incomplete check\"`",
                self.model
            ),
        }
    }
}

impl CleanIslandModelCheck {
    /// For an unsafe model: the shortest run to the state, as the lines of a
    /// note for the compiler to print under the error.
    #[must_use]
    pub fn run_report(&self) -> Option<String> {
        match &self.verdict {
            CleanIslandModelVerdict::Unsafe { run, invariant, .. } if !run.is_empty() => {
                Some(render_run(&self.model, invariant, run))
            }
            CleanIslandModelVerdict::Livelock { model, stem, cycle } => {
                Some(render_lasso(&self.model, model, stem, cycle))
            }
            _ => None,
        }
    }
}

impl CleanIslandModelCheck {
    /// For a model whose subtraction stops at zero on a reachable state: the
    /// warning the compiler prints at the model, whatever the verdict.
    #[must_use]
    pub fn truncation_report(&self) -> Option<String> {
        let CleanIslandModelTruncation { place, left, right, state } = self.truncation.as_ref()?;
        let state = state
            .iter()
            .map(|(name, value)| format!("{name} = {value}"))
            .collect::<Vec<_>>()
            .join(", ");
        Some(format!(
            "finite model `{}`: a subtraction evaluates `{left} - {right}` in {place}, in the \
             reachable state {{ {state} }}. The model language is over the natural numbers, so \
             that is 0, not {}; a guard written `a <= b - 1` for `a < b` is TRUE at `a = b = 0`. \
             Move the subtrahend across the comparison (`a + 1 <= b`, or `gt b a`)",
            self.model,
            i128::from(*left) - i128::from(*right)
        ))
    }
}

/// The environment's constant names before an island batch was elaborated —
/// what [`CleanIslandSession::check_declared_models`] subtracts to find the
/// batch's own constants. `None` when there can be no model (the checks are
/// off, or `Trust.FiniteModel` was never served).
#[derive(Clone)]
pub(super) struct ModelWatch(HashSet<Name>);

impl ModelWatch {
    /// The names, sorted: the stored form of a prepared batch's baseline (TG6).
    pub(super) fn names(&self) -> Vec<Name> {
        let mut names: Vec<Name> = self.0.iter().cloned().collect();
        names.sort();
        names
    }

    pub(super) fn from_names(names: Vec<Name>) -> Self {
        Self(names.into_iter().collect())
    }
}

/// What kind of model-typed constant a batch added.
enum Declared {
    Model,
    /// A `ScalarProgress`: a progress claim over a model.
    Progress,
    /// A model- or claim-typed constant the automatic check cannot read: the
    /// reason, and whether it is a progress claim.
    Unreadable(String, bool),
    /// A `Trust.Protocol.Binding`: data for the compiler, with no proof.
    Binding,
    /// A binding the kernel cannot read: the reason. An error, since a
    /// binding that is not checked must not look like one that holds.
    UnreadableBinding(String),
    /// A `Trust.Protocol.Seal`: data for the compiler, like a binding.
    Seal,
    /// A seal the kernel cannot read: the reason. An error, as for a binding.
    UnreadableSeal(String),
}

impl Declared {
    /// Data the compiler reads and checks against the code, with no model
    /// behind it: a binding or a seal, readable or not.
    fn is_data(&self) -> bool {
        matches!(
            self,
            Declared::Binding
                | Declared::UnreadableBinding(_)
                | Declared::Seal
                | Declared::UnreadableSeal(_)
        )
    }
}

/// What the kernel's verdict decodes to, owned (no borrow of the environment).
enum Decoded {
    Ok,
    Unsafe { state: Vec<(String, u64)>, invariant: String, run: Vec<CleanIslandModelStep> },
    Undecided(String),
}

impl CleanIslandSession {
    /// Check the finite models this session's islands declare (module docs).
    /// Off by default: the session that reports island results turns it on.
    pub fn enable_model_checks(&mut self) {
        self.model_checks = true;
    }

    /// Whether this session both checks the finite models its islands declare
    /// ([`Self::enable_model_checks`]) and hands back their bindings and seals
    /// ([`Self::enable_binding_reads`]): only then do an outcome's
    /// `model_checks`, `bindings` and `seals` list everything the islands
    /// declare (`clean_island_rows::CrateIslandFacts::models_and_bindings_read`).
    /// Either alone is not enough: model checks alone read no binding of an
    /// island that imports `Trust.Binding` without `Trust.FiniteModel`, and
    /// binding reads alone check no model.
    #[must_use]
    pub fn models_and_bindings_read(&self) -> bool {
        self.model_checks && self.binding_reads
    }

    /// Hand back the bindings this session's islands declare
    /// ([`CleanIslandBinding`]) without checking any model: for a session
    /// that needs the bindings early (the resolver's, which must know before
    /// analysis whether the crate's code will be checked against one) and
    /// reports no island result itself.
    pub fn enable_binding_reads(&mut self) {
        self.binding_reads = true;
    }

    /// The state budget for models that declare none of their own (default
    /// [`DEFAULT_STATE_BUDGET`]): how many reachable states the kernel is
    /// asked to prove safe.
    pub fn set_model_state_budget(&mut self, states: u64) {
        self.model_state_budget = states;
    }

    /// The kernel's limits for the model checks: `work_limit`, the search size
    /// past which it is not asked to prove a model or a claim by default
    /// (default [`KERNEL_WORK_LIMIT`]; [`OPT_IN_SECONDS`] bounds every attempt), and `heartbeats_per_work`, its evaluation budget
    /// per unit of search size (default [`HEARTBEATS_PER_WORK`]; 0 leaves it
    /// unbounded).
    pub fn set_model_kernel_limits(&mut self, work_limit: u64, heartbeats_per_work: u64) {
        self.model_work_limit = work_limit;
        self.model_heartbeats_per_work = heartbeats_per_work;
    }

    /// Whether to ask the kernel: `reachable` states against `budget`, which
    /// the model or claim declared itself when `named`; `subject` is "model"
    /// or "claim" and `cost` the estimate for its kind.
    fn kernel_ask(
        &self,
        reachable: u64,
        budget: u64,
        named: bool,
        effort: Effort,
        subject: &str,
        cost: fn(&Effort) -> f64,
    ) -> KernelAsk {
        let work = effort.work;
        let seconds = cost(&effort);
        if seconds > OPT_IN_SECONDS {
            KernelAsk::TooLarge(format!(
                "too large for the kernel to prove today ({}, past the {OPT_IN_SECONDS} s it is \
                 asked at most)",
                seconds_text(seconds)
            ))
        } else if reachable > budget {
            KernelAsk::Hint(format!(
                "`def <{subject}>.stateBudget : Nat := {reachable}` beside the {subject} has the \
                 kernel prove it ({} per build)",
                seconds_text(seconds)
            ))
        } else if !named && work > self.model_work_limit {
            KernelAsk::Hint(format!(
                "a search of {work} evaluations is past the {} the kernel is asked by default; \
                 `def <{subject}>.stateBudget : Nat := {reachable}` beside the {subject} asks it \
                 anyway ({} per build)",
                self.model_work_limit,
                seconds_text(seconds)
            ))
        } else {
            KernelAsk::Prove
        }
    }

    /// The heartbeats a proof of `effort` may spend (0: unbounded): the larger
    /// of its work and its estimated time, scaled, and never under the
    /// kernel's default.
    fn kernel_heartbeats(&self, effort: &Effort) -> u64 {
        match self.model_heartbeats_per_work {
            0 => 0,
            per => {
                let by_time =
                    (PROGRESS_FACTOR * effort.seconds() * HEARTBEATS_PER_SECOND as f64) as u64;
                per.saturating_mul(effort.work)
                    .max(by_time)
                    .max(u64::from(clean_kernel::tc::DEFAULT_HEARTBEAT_LIMIT))
            }
        }
    }

    /// Call after serving a batch's imports and BEFORE elaborating it.
    pub(super) fn model_watch(&self) -> Option<ModelWatch> {
        self.model_watch_enabled().then(|| self.capture_model_watch())
    }

    pub(super) fn model_watch_enabled(&self) -> bool {
        let models = self.model_checks && self.keyed.served().contains(&MODEL_MODULE);
        let bindings = self.binding_reads && self.keyed.served().contains(&BINDING_MODULE);
        models || bindings
    }

    /// Capture the original declaration delta even when the reporting owner
    /// enables its policy only after elaboration has finished.
    pub(super) fn deferred_model_watch(&self) -> Option<ModelWatch> {
        self.keyed
            .served()
            .iter()
            .any(|module| *module == MODEL_MODULE || *module == BINDING_MODULE)
            .then(|| self.capture_model_watch())
    }

    fn capture_model_watch(&self) -> ModelWatch {
        ModelWatch(self.env().constants().map(|info| info.name.clone()).collect())
    }

    /// Check every model the batch added. `sources`, `parser_preludes` and
    /// `outcomes` are parallel, one per island. A rejected batch reports no
    /// green, so it is left alone.
    pub(super) fn check_declared_models(
        &mut self,
        watch: Option<ModelWatch>,
        sources: &[&str],
        parser_preludes: &[String],
        outcomes: &mut [CleanIslandOutcome],
    ) {
        let Some(ModelWatch(before)) = watch else { return };
        if outcomes.iter().any(CleanIslandOutcome::is_rejected) {
            return;
        }
        // (island, position in its `registered`, name, rendered name, kind), in authored order.
        let mut declared: Vec<(usize, usize, Name, String, Declared)> = Vec::new();
        {
            let env = self.env();
            let tc = TypeChecker::with_mode(env, env.mode());
            for info in env.constants() {
                if before.contains(&info.name) {
                    continue;
                }
                let Some(kind) = model_typed(&tc, info) else { continue };
                // Only a declaration the author wrote: an auxiliary constant
                // the elaborator generated is in no island's `registered`.
                let rendered = info.name.to_string();
                let Some(place) = outcomes.iter().enumerate().find_map(|(island, outcome)| {
                    let position = outcome.registered.iter().position(|name| *name == rendered)?;
                    Some((island, position))
                }) else {
                    continue;
                };
                declared.push((place.0, place.1, info.name.clone(), rendered, kind));
            }
        }
        // A session that only reads bindings and seals checks no model.
        let is_binding = Declared::is_data;
        if !self.model_checks {
            declared.retain(|(_, _, _, _, kind)| is_binding(kind));
        }
        if declared.is_empty() {
            return;
        }
        declared.sort_unstable_by(|a, b| (a.0, a.1, a.3.as_str()).cmp(&(b.0, b.1, b.3.as_str())));

        // The checker module, for the models; a binding needs none.
        let served = if declared.iter().all(|(_, _, _, _, kind)| is_binding(kind)) {
            Ok(())
        } else {
            self.serve_trust_module(CHECK_MODULE)
        };
        let mut spans: HashMap<usize, Vec<(String, usize, usize)>> = HashMap::new();
        for (island, _, name, model, kind) in declared {
            let source = sources.get(island).copied().unwrap_or("");
            let prelude = parser_preludes.get(island).map_or("", String::as_str);
            let definitions =
                spans.entry(island).or_insert_with(|| definition_spans(prelude, source));
            let (start, end) = definitions
                .iter()
                .find(|(defined, _, _)| *defined == model)
                .map_or((0, source.len()), |&(_, start, end)| (start, end));
            let outcome = &mut outcomes[island];
            // A seal needs no checker module either: it is read and handed
            // back.
            if matches!(kind, Declared::Seal | Declared::UnreadableSeal(_)) {
                let read = match &kind {
                    Declared::Seal => {
                        let env = self.env();
                        read_seal(&TypeChecker::with_mode(env, env.mode()), &name)
                    }
                    Declared::UnreadableSeal(reason) => Err(reason.clone()),
                    _ => unreachable!("matched above"),
                };
                match read {
                    Ok([writers, makers, made_by, trusts, type_name]) => {
                        outcome.seals.push(CleanIslandSeal {
                            name: model,
                            type_name: type_name.into_iter().next().unwrap_or_default(),
                            writers,
                            makers,
                            made_by,
                            trusts,
                            start,
                            end,
                        })
                    }
                    Err(why) => outcome.errors.push(CleanIslandDiagnostic {
                        start,
                        end,
                        message: format!(
                            "seal `{model}` cannot be read, so it cannot be checked against \
                             the code: {why}"
                        ),
                    }),
                }
                continue;
            }
            // A binding needs no checker module: it is read and handed back.
            if matches!(kind, Declared::Binding | Declared::UnreadableBinding(_)) {
                let read = match &kind {
                    Declared::Binding => {
                        let env = self.env();
                        read_binding(&TypeChecker::with_mode(env, env.mode()), &name)
                    }
                    Declared::UnreadableBinding(reason) => Err(reason.clone()),
                    _ => unreachable!("matched above"),
                };
                match read {
                    Ok((path, arms, carried_by)) => outcome.bindings.push(CleanIslandBinding {
                        name: model,
                        path,
                        arms,
                        carried_by,
                        start,
                        end,
                    }),
                    Err(why) => outcome.errors.push(CleanIslandDiagnostic {
                        start,
                        end,
                        message: format!(
                            "binding `{model}` cannot be read, so it cannot be checked against \
                             the code: {why}"
                        ),
                    }),
                }
                continue;
            }
            if let Err(why) = &served {
                // Serving taints the session, so the island must be rejected
                // with it: taint without a reported rejection is invisible.
                outcome.errors.push(CleanIslandDiagnostic {
                    start,
                    end,
                    message: format!(
                        "finite model `{model}` could not be checked: Trust's checker module \
                         `{CHECK_MODULE}` did not check in this session ({why}). An island must \
                         not declare names in `{NAMESPACE}`"
                    ),
                });
                continue;
            }
            let progress = matches!(kind, Declared::Progress | Declared::Unreadable(_, true));
            let (budget, verdict, truncation, work) = match kind {
                Declared::Model => self.check_model(&name),
                Declared::Progress => (String::new(), self.check_progress(&name), None, None),
                Declared::Unreadable(reason, _) => (
                    DEFAULT_STATE_BUDGET.to_string(),
                    CleanIslandModelVerdict::Undecided { reason },
                    None,
                    None,
                ),
                Declared::Binding
                | Declared::UnreadableBinding(_)
                | Declared::Seal
                | Declared::UnreadableSeal(_) => {
                    unreachable!("a binding or a seal is handled before the checker is consulted")
                }
            };
            let bounded = match self.model_bounded_reason(&name, progress) {
                Ok(reason) => reason,
                Err(message) => {
                    outcome.errors.push(CleanIslandDiagnostic { start, end, message });
                    None
                }
            };
            let check = CleanIslandModelCheck {
                model,
                progress,
                budget,
                bounded,
                verdict,
                work,
                truncation,
                start,
                end,
            };
            // An added verdict must explicitly choose its acceptance policy;
            // it cannot inherit success by falling through a refusal list.
            let refused = match check.verdict {
                CleanIslandModelVerdict::Safe { .. } | CleanIslandModelVerdict::Live { .. } => {
                    false
                }
                CleanIslandModelVerdict::Unsafe { .. }
                | CleanIslandModelVerdict::Livelock { .. } => true,
                CleanIslandModelVerdict::Undecided { .. }
                | CleanIslandModelVerdict::Searched { .. } => check.bounded.is_none(),
            };
            if refused {
                outcome.errors.push(CleanIslandDiagnostic { start, end, message: check.report() });
            }
            outcome.model_checks.push(check);
        }
        for outcome in outcomes {
            if outcome.is_rejected() {
                // The invariant on `standin_imports`: a rejected island reports none.
                outcome.standin_imports.clear();
            }
        }
    }

    /// A bounded declaration is typed kernel data, never a spelling found in
    /// source text. A stateBudget requests work; it is not this declaration.
    fn model_bounded_reason(
        &mut self,
        name: &Name,
        progress: bool,
    ) -> Result<Option<String>, String> {
        let marker = name.clone().str("bounded");
        self.model_metadata_reads.push(marker.clone());
        let env = self.env();
        let Some(info) = env.get_const(&marker) else { return Ok(None) };
        let tc = TypeChecker::with_mode(env, env.mode());
        let value = Expr::const_(marker.clone(), vec![]);
        if info.kind == ConstantKind::Definition
            && info.level_params.is_empty()
            && tc.check_type(&value, &Expr::const_str("String")).is_ok()
        {
            if let Some(reason) = string(&tc, &value).filter(|reason| !reason.trim().is_empty()) {
                return Ok(Some(reason));
            }
        }
        let subject = if progress { "progress claim" } else { "finite model" };
        Err(format!(
            "{subject} `{name}` has an invalid bounded declaration: \
             `{marker}` must be a definition of type `String` with a nonempty reason"
        ))
    }

    /// The fast untrusted search first, the kernel for every claim:
    ///
    /// 1. a state that breaks an invariant, which the kernel confirms by
    ///    replaying the run and evaluating the invariant: `Unsafe`, with no
    ///    kernel search, at any size the untrusted search covers;
    /// 2. more reachable states than the budget, or a search past
    ///    [`KERNEL_WORK_LIMIT`]: `Undecided`, with the count and what would
    ///    prove it, again with no kernel search;
    /// 3. within the budget: the kernel checks the search's rows
    ///    (`scalarSafetyOfCheck`, no search of its own: about twice as fast as
    ///    `proveSafe`, which searches and then checks);
    /// 4. anything else (the model is not readable here, or step 3 failed):
    ///    the kernel's own verdict, as before.
    ///
    /// Returns the budget as written, the verdict and any truncation.
    fn check_model(
        &mut self,
        name: &Name,
    ) -> (String, CleanIslandModelVerdict, Option<CleanIslandModelTruncation>, Option<u64>) {
        let model = Expr::const_(name.clone(), Vec::<Level>::new());
        let budget_name = name.clone().str("stateBudget");
        self.model_metadata_reads.push(budget_name.clone());
        let named = is_nat_definition(self.env(), &budget_name);
        let default = self.model_state_budget;
        let (mut budget, budget_expr) = if named {
            (budget_name.to_string(), Expr::const_(budget_name, Vec::<Level>::new()))
        } else {
            (default.to_string(), Expr::nat_lit(default))
        };
        let mut states = default;
        let (found, truncation) = {
            let env = self.env();
            let tc = TypeChecker::with_mode(env, env.mode());
            if let (true, Some(value)) = (named, nat(&tc, &budget_expr)) {
                budget = format!("{value} (`{budget}`)");
                states = value;
            }
            let limit = usize::try_from(states).unwrap_or(usize::MAX).min(1 << 16);
            presearch_and_first_truncation(&tc, &model, limit)
        };
        let work = match found {
            Presearch::Exhausted { effort, .. } => Some(effort.work),
            _ => None,
        };
        let verdict = match found {
            Presearch::Violation { invariant, run } => CleanIslandModelVerdict::Unsafe {
                state: run.last().map(|step| step.state.clone()).unwrap_or_default(),
                invariant,
                run,
            },
            Presearch::Exhausted { states: reachable, effort, rows } => {
                let reachable_states = u64::try_from(reachable).unwrap_or(u64::MAX);
                let ask = self.kernel_ask(
                    reachable_states,
                    states,
                    named,
                    effort,
                    "model",
                    safety_seconds,
                );
                if !matches!(ask, KernelAsk::Prove) {
                    let searched = "An untrusted search of all of them found no state that breaks \
                                    an invariant";
                    let reason = match (reachable_states > states, ask) {
                        (true, KernelAsk::Hint(hint)) => format!(
                            "it has {reachable} reachable states, more than its state budget of \
                             {budget}. {searched}; {hint}"
                        ),
                        (true, KernelAsk::TooLarge(why)) => format!(
                            "it has {reachable} reachable states, more than its state budget of \
                             {budget}. {searched}; the model is {why}"
                        ),
                        (false, KernelAsk::Hint(hint)) => format!(
                            "it has {reachable} reachable states, within its state budget of \
                             {budget}, but {hint}. {searched}"
                        ),
                        (false, KernelAsk::TooLarge(why)) => format!(
                            "it has {reachable} reachable states, within its state budget of \
                             {budget}, but the model is {why}. {searched}"
                        ),
                        (_, KernelAsk::Prove) => unreachable!("the guard excludes it"),
                    };
                    CleanIslandModelVerdict::Undecided { reason }
                } else {
                    match self.rows_safety_theorem(name, &rows, effort) {
                        Ok(theorem) => CleanIslandModelVerdict::Safe { theorem },
                        // The search says safe and the kernel did not accept the
                        // theorem: almost always its evaluation limit. A SHORT
                        // second look still catches a kernel that disagrees with
                        // the search, without paying for the whole search again.
                        Err(_) => match self.kernel_verdict(name, &budget, &budget_expr, 200_000) {
                            CleanIslandModelVerdict::Undecided { .. } => {
                                CleanIslandModelVerdict::Undecided {
                                    reason: format!(
                                        "it has {reachable} reachable states, within its state \
                                         budget of {budget}, but the kernel reached its \
                                         evaluation limit before it finished proving them: the \
                                         model is too large for the kernel today. A budget below \
                                         {reachable} (`def <model>.stateBudget : Nat := 0`) skips \
                                         the attempt"
                                    ),
                                }
                            }
                            decided => decided,
                        },
                    }
                }
            }
            Presearch::Unread => self.kernel_verdict(name, &budget, &budget_expr, 0),
        };
        (budget, verdict, truncation, work)
    }

    /// A progress claim: the untrusted search for a fair run that leaves the
    /// goal for good, confirmed by the kernel (`model_progress`).
    fn check_progress(&mut self, name: &Name) -> CleanIslandModelVerdict {
        let claim = Expr::const_(name.clone(), Vec::<Level>::new());
        let (model, states, certificate, effort) = match model_progress::search(self.env(), &claim)
        {
            ProgressSearch::Livelock { model, stem, cycle } => {
                return CleanIslandModelVerdict::Livelock { model, stem, cycle };
            }
            ProgressSearch::Unread(reason) => return CleanIslandModelVerdict::Undecided { reason },
            ProgressSearch::NoCounterexample { model, states, certificate, effort } => {
                (model, states, certificate, effort)
            }
        };
        // The budget, as for a model: the claim's own `C.stateBudget`, or the
        // session's.
        let budget_name = name.clone().str("stateBudget");
        self.model_metadata_reads.push(budget_name.clone());
        let named = is_nat_definition(self.env(), &budget_name);
        let budget = if named {
            let env = self.env();
            let tc = TypeChecker::with_mode(env, env.mode());
            nat(&tc, &Expr::const_(budget_name, Vec::<Level>::new()))
                .unwrap_or(self.model_state_budget)
        } else {
            self.model_state_budget
        };
        let searched = |unproved: String| CleanIslandModelVerdict::Searched {
            model: model.clone(),
            states,
            unproved,
        };
        let certificate = match certificate {
            Ok(certificate) => certificate,
            Err(why) => return searched(why),
        };
        let reachable = u64::try_from(states).unwrap_or(u64::MAX);
        match self.kernel_ask(reachable, budget, named, effort, "claim", progress_seconds) {
            KernelAsk::Prove => {}
            KernelAsk::Hint(hint) if reachable > budget => {
                return searched(format!(
                    "it has {states} reachable states, more than its state budget of {budget}; \
                     {hint}"
                ));
            }
            KernelAsk::Hint(hint) => {
                return searched(format!(
                    "it has {states} reachable states, within its state budget of {budget}, but \
                     {hint}"
                ));
            }
            KernelAsk::TooLarge(why) => {
                return searched(format!("its certificate is {why}"));
            }
        }
        match self.progress_theorem(name, &certificate, effort) {
            Ok(theorem) => CleanIslandModelVerdict::Live { model, theorem, states },
            Err(error) => searched(format!(
                "the kernel did not accept its certificate ({error}); a certificate the \
                 search found and the kernel refuses is a defect in Trust to report"
            )),
        }
    }

    /// Hand the kernel `trust_checked_live.C : ScalarProgress.claim C :=
    /// progressOfCheck C cert (Eq.refl true)`: it checks the proof against
    /// `progressCheck C cert = true` by evaluating the check.
    fn progress_theorem(
        &mut self,
        name: &Name,
        certificate: &[CertificateRow],
        effort: Effort,
    ) -> Result<String, String> {
        let claim = Expr::const_(name.clone(), Vec::<Level>::new());
        let theorem = reserved_name_under(LIVE_THEOREM_ROOT, name);
        let level_mk = constant("ProgressLevel.mk");
        let level_ty = constant("ProgressLevel");
        let row_mk = constant("ProgressRow.mk");
        let rows = certificate.iter().map(|(row, levels)| {
            let levels = levels.iter().map(|&(rank, helper)| {
                Expr::app(Expr::app(level_mk.clone(), Expr::nat_lit(rank)), Expr::nat_lit(helper))
            });
            Expr::app(
                Expr::app(row_mk.clone(), nat_list(row.iter().copied())),
                list_of(level_ty.clone(), levels.collect()),
            )
        });
        let refl = Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq.refl"), vec![Level::succ(Level::zero())]),
                Expr::const_str("Bool"),
            ),
            Expr::const_str("Bool.true"),
        );
        let declaration = Declaration::Theorem {
            name: theorem.clone(),
            level_params: vec![],
            type_: Expr::app(constant("ScalarProgress.claim"), claim.clone()),
            value: Expr::app(
                Expr::app(
                    Expr::app(constant("progressOfCheck"), claim),
                    list_of(constant("ProgressRow"), rows.collect()),
                ),
                refl,
            ),
        };
        let heartbeats = self.kernel_heartbeats(&effort);
        add_with_heartbeats(self.keyed.env_mut(), declaration, heartbeats)
            .map(|()| theorem.to_string())
    }

    /// Hand the kernel `trust_checked_safe.M : ScalarModel.safetyClaim M :=
    /// proveSafe M budget (Eq.refl ok)`: it checks the proof against
    /// `safetyVerdict M budget = CheckVerdict.ok` by evaluating the search.
    fn state_safety_theorem(
        &mut self,
        name: &Name,
        budget: &Expr,
        effort: Effort,
    ) -> Result<String, String> {
        let model = Expr::const_(name.clone(), Vec::<Level>::new());
        let theorem = reserved_theorem_name(name);
        let refl = Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq.refl"), vec![Level::succ(Level::zero())]),
                constant("CheckVerdict"),
            ),
            constant("CheckVerdict.ok"),
        );
        let declaration = Declaration::Theorem {
            name: theorem.clone(),
            level_params: vec![],
            type_: Expr::app(constant("ScalarModel.safetyClaim"), model.clone()),
            value: Expr::app(
                Expr::app(Expr::app(constant("proveSafe"), model), budget.clone()),
                refl,
            ),
        };
        let heartbeats = self.kernel_heartbeats(&effort);
        add_with_heartbeats(self.keyed.env_mut(), declaration, heartbeats)
            .map(|()| theorem.to_string())
    }

    /// Hand the kernel `trust_checked_safe.M : ScalarModel.safetyClaim M :=
    /// scalarSafetyOfCheck M rows (Eq.refl true)`: it checks the search's rows
    /// (the initial row among them, every row's successors among them, every
    /// invariant on each) without searching itself.
    fn rows_safety_theorem(
        &mut self,
        name: &Name,
        rows: &[Vec<u64>],
        effort: Effort,
    ) -> Result<String, String> {
        let model = Expr::const_(name.clone(), Vec::<Level>::new());
        let theorem = reserved_theorem_name(name);
        let row_type = Expr::app(
            Expr::const_(Name::from_string("List"), vec![Level::zero()]),
            Expr::const_str("Nat"),
        );
        let rows =
            list_of(row_type, rows.iter().map(|row| nat_list(row.iter().copied())).collect());
        let refl = Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq.refl"), vec![Level::succ(Level::zero())]),
                Expr::const_str("Bool"),
            ),
            Expr::const_str("Bool.true"),
        );
        let declaration = Declaration::Theorem {
            name: theorem.clone(),
            level_params: vec![],
            type_: Expr::app(constant("ScalarModel.safetyClaim"), model.clone()),
            value: Expr::app(
                Expr::app(Expr::app(constant("scalarSafetyOfCheck"), model), rows),
                refl,
            ),
        };
        let heartbeats = self.kernel_heartbeats(&effort);
        add_with_heartbeats(self.keyed.env_mut(), declaration, heartbeats)
            .map(|()| theorem.to_string())
    }

    /// The kernel's own search: the weak-head normal form of `safetyVerdict M
    /// budget`, and on `ok` the theorem. `heartbeats` bounds the evaluation
    /// (0: the checker's default limit).
    fn kernel_verdict(
        &mut self,
        name: &Name,
        budget: &str,
        budget_expr: &Expr,
        heartbeats: u32,
    ) -> CleanIslandModelVerdict {
        let model = Expr::const_(name.clone(), Vec::<Level>::new());
        let decoded = {
            let env = self.env();
            let mut tc = TypeChecker::with_mode(env, env.mode());
            if heartbeats != 0 {
                tc.set_heartbeat_limit(heartbeats);
            }
            let verdict = tc.whnf(&Expr::app(
                Expr::app(constant("safetyVerdict"), model.clone()),
                budget_expr.clone(),
            ));
            decode_verdict(env, &tc, &model, budget, &verdict)
        };
        match decoded {
            Decoded::Unsafe { state, invariant, run } => {
                CleanIslandModelVerdict::Unsafe { state, invariant, run }
            }
            Decoded::Undecided(reason) => CleanIslandModelVerdict::Undecided { reason },
            Decoded::Ok => match self.state_safety_theorem(name, budget_expr, Effort::default()) {
                Ok(theorem) => CleanIslandModelVerdict::Safe { theorem },
                Err(error) => CleanIslandModelVerdict::Undecided {
                    reason: format!(
                        "the check answers `ok`, but the kernel did not accept the safety \
                         theorem ({error})"
                    ),
                },
            },
        }
    }
}

/// Add `declaration` with the kernel's evaluation bounded by `heartbeats` (0:
/// unbounded), the environment's own `maxHeartbeats` restored after.
fn add_with_heartbeats(
    env: &mut Environment,
    declaration: Declaration,
    heartbeats: u64,
) -> Result<(), String> {
    const OPTION: &str = "maxHeartbeats";
    let saved = env.get_option(OPTION).cloned();
    let limit = u32::try_from(heartbeats).unwrap_or(u32::MAX);
    env.set_option(OPTION.to_owned(), Some(limit.to_string()));
    let added = env.add_decl(declaration).map_err(|error| error.to_string());
    match saved {
        Some(value) => env.set_option(OPTION.to_owned(), value),
        None => env.remove_option(OPTION),
    }
    added
}

fn constant(name: &str) -> Expr {
    Expr::const_str(&format!("{NAMESPACE}.{name}"))
}

/// `trust_checked_safe` followed by every component of `model`: injective, and
/// inside the namespace the strict island policy reserves for the compiler.
fn reserved_theorem_name(model: &Name) -> Name {
    reserved_name_under(THEOREM_ROOT, model)
}

fn reserved_name_under(root: &str, model: &Name) -> Name {
    match model.inner() {
        NameInner::Anon => Name::from_string(root),
        NameInner::Str(parent, component) => reserved_name_under(root, parent).str(&**component),
        NameInner::Num(parent, component) => reserved_name_under(root, parent).num(*component),
    }
}

/// Whether `info` is a model-typed constant: its type reduces to the constant
/// `ScalarModel` (so an alias of the type is seen through), or names the
/// function-valued `Model`.
fn model_typed(tc: &TypeChecker<'_>, info: &clean_kernel::ConstantInfo) -> Option<Declared> {
    if !matches!(info.kind, ConstantKind::Definition | ConstantKind::Opaque) {
        return None;
    }
    // A function, a sort or a literal type is never a model; only a constant
    // or an application can reduce to one.
    let type_ = match info.type_.kind() {
        ExprKind::Const(..) | ExprKind::App(..) => tc.whnf(&info.type_),
        _ => return None,
    };
    // A list of bindings, a pair, an option: binding data the compiler does
    // not read. It must not sit there unchecked and unremarked.
    fn names(expr: &Expr, wanted: &str) -> bool {
        match expr.kind() {
            ExprKind::Const(name, _) => name.to_string() == wanted,
            ExprKind::App(function, argument) => names(function, wanted) || names(argument, wanted),
            _ => false,
        }
    }
    if matches!(type_.kind(), ExprKind::App(..)) && names(&type_, BINDING_TYPE) {
        return Some(Declared::UnreadableBinding(
            "its type holds a `Binding` and is not one (a list, a pair): the compiler reads \
             only a constant of type `Trust.Protocol.Binding`, so declare each binding as a \
             constant of its own"
                .to_owned(),
        ));
    }
    if matches!(type_.kind(), ExprKind::App(..)) && names(&type_, SEAL_TYPE) {
        return Some(Declared::UnreadableSeal(
            "its type holds a `Seal` and is not one (a list, a pair): the compiler reads only \
             a constant of type `Trust.Protocol.Seal`, so declare each seal as a constant of \
             its own"
                .to_owned(),
        ));
    }
    let ExprKind::Const(type_name, _) = type_.kind() else { return None };
    let type_name = type_name.to_string();
    if type_name == SEAL_TYPE {
        return Some(if !info.level_params.is_empty() {
            Declared::UnreadableSeal("it is universe-polymorphic".to_owned())
        } else if info.kind != ConstantKind::Definition || info.value.is_none() {
            Declared::UnreadableSeal(
                "it is `opaque`, so the kernel cannot read its body".to_owned(),
            )
        } else {
            Declared::Seal
        });
    }
    if type_name == BINDING_TYPE {
        return Some(if !info.level_params.is_empty() {
            Declared::UnreadableBinding("it is universe-polymorphic".to_owned())
        } else if info.kind != ConstantKind::Definition || info.value.is_none() {
            Declared::UnreadableBinding(
                "it is `opaque`, so the kernel cannot read its body".to_owned(),
            )
        } else {
            Declared::Binding
        });
    }
    if type_name == format!("{NAMESPACE}.Model") {
        return Some(Declared::Unreadable(
            "the automatic check reads `ScalarModel`; a function-valued `Model` is outside it"
                .to_owned(),
            false,
        ));
    }
    let declared = if type_name == format!("{NAMESPACE}.ScalarModel") {
        Declared::Model
    } else if type_name == format!("{NAMESPACE}.ScalarProgress") {
        Declared::Progress
    } else {
        return None;
    };
    let progress = matches!(declared, Declared::Progress);
    Some(if !info.level_params.is_empty() {
        Declared::Unreadable("it is universe-polymorphic".to_owned(), progress)
    } else if info.kind != ConstantKind::Definition || info.value.is_none() {
        Declared::Unreadable(
            "it is `opaque`, so the kernel cannot read its body".to_owned(),
            progress,
        )
    } else {
        declared
    })
}

/// The path, the arms and the carried-by fns of the binding constant `name`:
/// its value reduced to `Trust.Protocol.Binding.mk`, with a string literal and
/// two lists of string literals.
fn read_binding(
    tc: &TypeChecker<'_>,
    name: &Name,
) -> Result<(String, Vec<String>, Vec<String>), String> {
    let value = tc.whnf(&Expr::const_(name.clone(), Vec::<Level>::new()));
    let (head, fields) = head_and_args(&value);
    let [path, arms, carried_by] = fields.as_slice() else {
        return Err(format!("it does not reduce to `{BINDING_CONSTRUCTOR} path arms carriedBy`"));
    };
    if head != BINDING_CONSTRUCTOR {
        return Err(format!("it does not reduce to `{BINDING_CONSTRUCTOR} path arms carriedBy`"));
    }
    let path = string(tc, path).ok_or("its path is not a string")?;
    if path.trim().is_empty() {
        return Err("its path is empty".to_owned());
    }
    let names = |expression: &Expr, what: &str| -> Result<Vec<String>, String> {
        list(tc, expression)
            .ok_or_else(|| format!("its {what} are not a list"))?
            .iter()
            .map(|item| {
                string(tc, item).ok_or_else(|| format!("one of its {what} is not a string"))
            })
            .collect()
    };
    Ok((path, names(arms, "arms")?, names(carried_by, "carried-by fns")?))
}

/// The seal constant `name`, as its four lists and its type (last, as a
/// one-element list): its value reduced to `Trust.Protocol.Seal.mk`, with a
/// string literal and four lists of string literals.
fn read_seal(tc: &TypeChecker<'_>, name: &Name) -> Result<[Vec<String>; 5], String> {
    let shape =
        format!("it does not reduce to `{SEAL_CONSTRUCTOR} type writers makers madeBy trusts`");
    let value = tc.whnf(&Expr::const_(name.clone(), Vec::<Level>::new()));
    let (head, fields) = head_and_args(&value);
    let [type_name, writers, makers, made_by, trusts] = fields.as_slice() else {
        return Err(shape);
    };
    if head != SEAL_CONSTRUCTOR {
        return Err(shape);
    }
    let type_name = string(tc, type_name).ok_or("its type is not a string")?;
    if type_name.trim().is_empty() {
        return Err("its type is empty".to_owned());
    }
    let names = |expression: &Expr, what: &str| -> Result<Vec<String>, String> {
        list(tc, expression)
            .ok_or_else(|| format!("its {what} are not a list"))?
            .iter()
            .map(|item| {
                string(tc, item).ok_or_else(|| format!("one of its {what} is not a string"))
            })
            .collect()
    };
    Ok([
        names(writers, "writers")?,
        names(makers, "makers")?,
        names(made_by, "made-by fns")?,
        names(trusts, "trusted fns")?,
        vec![type_name],
    ])
}

fn is_nat_definition(env: &Environment, name: &Name) -> bool {
    env.get_const(name).is_some_and(|info| {
        info.kind == ConstantKind::Definition
            && info.value.is_some()
            && info.level_params.is_empty()
            && matches!(info.type_.kind(), ExprKind::Const(ty, _) if ty.to_string() == "Nat")
    })
}

fn decode_verdict(
    env: &Environment,
    tc: &TypeChecker<'_>,
    model: &Expr,
    budget: &str,
    verdict: &Expr,
) -> Decoded {
    let (head, args) = head_and_args(verdict);
    let constructor = head.strip_prefix(&format!("{NAMESPACE}.CheckVerdict.")).unwrap_or("");
    match (constructor, args.as_slice()) {
        ("ok", []) => Decoded::Ok,
        ("invariantFails", [row, index]) => {
            let (variables, invariants) = model_names(tc, model);
            // The search keeps one slot per declared variable, so a repeated
            // name makes its rows meaningless (and such a model has no initial
            // state at all when the two initial values differ).
            if let Some(repeated) =
                variables.iter().enumerate().find(|(at, name)| variables[..*at].contains(name))
            {
                return Decoded::Undecided(format!(
                    "it declares the variable `{}` more than once, which the automatic check \
                     does not read",
                    repeated.1
                ));
            }
            let values = list(tc, row)
                .map(|cells| cells.iter().map(|cell| nat(tc, cell)).collect::<Vec<_>>())
                .unwrap_or_default();
            let state = values
                .iter()
                .enumerate()
                .map(|(position, value)| {
                    let name =
                        variables.get(position).cloned().unwrap_or_else(|| format!("#{position}"));
                    (name, value.unwrap_or(u64::MAX))
                })
                .collect();
            let index = nat(tc, index);
            let invariant = index
                .and_then(|index| invariants.get(usize::try_from(index).ok()?).cloned())
                .unwrap_or_else(|| index.map_or_else(|| "?".to_owned(), |i| format!("#{i}")));
            let run = values
                .iter()
                .copied()
                .collect::<Option<Vec<u64>>>()
                .zip(index.and_then(|index| usize::try_from(index).ok()))
                .and_then(|(target, index)| {
                    // Its own checker: the search above may have used most of
                    // this one's evaluation limit.
                    let fresh = TypeChecker::with_mode(env, env.mode());
                    shortest_run(&fresh, model, &target, index)
                })
                .unwrap_or_default();
            Decoded::Unsafe { state, invariant, run }
        }
        ("budgetExhausted", []) => Decoded::Undecided(format!(
            "it has more reachable states than its state budget of {budget}; a `def \
             <model>.stateBudget : Nat` beside the model sets the budget"
        )),
        ("unsupported", []) => Decoded::Undecided(
            "it uses a construct outside the checker's grammar (function-valued state, a \
             repeated update, or same-named constants that disagree)"
                .to_owned(),
        ),
        _ => Decoded::Undecided(format!(
            "the kernel did not reach a verdict within its evaluation limit (it stopped at `{}`); \
             the model is too large for the automatic check",
            if head.is_empty() { "a non-constant term" } else { head.as_str() }
        )),
    }
}

pub(super) fn head_and_args(expression: &Expr) -> (String, Vec<Expr>) {
    let head = match expression.get_app_fn().kind() {
        ExprKind::Const(name, _) => name.to_string(),
        _ => String::new(),
    };
    (head, expression.get_app_args().iter().map(|argument| (*argument).clone()).collect())
}

/// A `Nat` value: a literal, or `Nat.succ` over one (the checker's rows are
/// values, printed either way).
pub(super) fn nat(tc: &TypeChecker<'_>, expression: &Expr) -> Option<u64> {
    let mut current = tc.whnf(expression);
    let mut successors = 0u64;
    loop {
        if let ExprKind::Lit(Literal::Nat(value)) = current.kind() {
            return value.to_string().parse::<u64>().ok()?.checked_add(successors);
        }
        let (head, args) = head_and_args(&current);
        match (head.as_str(), args.as_slice()) {
            ("Nat.zero", []) => return Some(successors),
            ("Nat.succ", [previous]) => {
                successors = successors.checked_add(1)?;
                current = tc.whnf(previous);
            }
            _ => return None,
        }
    }
}

pub(super) fn list(tc: &TypeChecker<'_>, expression: &Expr) -> Option<Vec<Expr>> {
    let mut current = tc.whnf(expression);
    let mut items = Vec::new();
    loop {
        let (head, args) = head_and_args(&current);
        match (head.as_str(), args.as_slice()) {
            ("List.nil", [_]) => return Some(items),
            ("List.cons", [_, item, rest]) => {
                items.push(item.clone());
                current = tc.whnf(rest);
            }
            _ => return None,
        }
    }
}

pub(super) fn string(tc: &TypeChecker<'_>, expression: &Expr) -> Option<String> {
    match tc.whnf(expression).kind() {
        ExprKind::Lit(Literal::String(value)) => Some(value.to_string()),
        _ => None,
    }
}

/// The model's variable names and invariant names, in declaration order —
/// to make a rejection readable; an undecodable name reads `?`.
fn model_names(tc: &TypeChecker<'_>, model: &Expr) -> (Vec<String>, Vec<String>) {
    let (head, fields) = head_and_args(&tc.whnf(model));
    let [_, _, variables, _, invariants] = fields.as_slice() else {
        return (Vec::new(), Vec::new());
    };
    if head != format!("{NAMESPACE}.ScalarModel.mk") {
        return (Vec::new(), Vec::new());
    }
    let names = |entries: &Expr| {
        list(tc, entries)
            .unwrap_or_default()
            .iter()
            .map(|entry| {
                let (_, entry_fields) = head_and_args(&tc.whnf(entry));
                entry_fields
                    .first()
                    .and_then(|name| string(tc, name))
                    .unwrap_or_else(|| "?".to_owned())
            })
            .collect()
    };
    (names(variables), names(invariants))
}

/// Every `def` of an island as `(qualified name, start, end)`, the span being
/// the definition's first line, island-relative. Read off the REAL parse (the
/// island behind its parser prelude, exactly as it was checked), walking
/// namespaces; only a location for diagnostics — what is checked is decided
/// from the kernel environment.
fn definition_spans(parser_prelude: &str, source: &str) -> Vec<(String, usize, usize)> {
    fn walk(
        decls: &[clean_parser::SurfaceDecl],
        namespace: &str,
        base: usize,
        source: &str,
        out: &mut Vec<(String, usize, usize)>,
    ) {
        use clean_parser::SurfaceDecl;
        for decl in decls {
            match decl {
                SurfaceDecl::Def { span, name, .. } if span.start >= base => {
                    // The parser's span for a `def` is its keyword; the
                    // diagnostic takes the rest of that line.
                    let start = (span.start - base).min(source.len());
                    let end = source[start..].find('\n').map_or(source.len(), |line| start + line);
                    let name = name.to_string();
                    let qualified =
                        if namespace.is_empty() { name } else { format!("{namespace}.{name}") };
                    out.push((qualified, start, end));
                }
                SurfaceDecl::Namespace { name, decls, .. } => {
                    let name = name.to_string();
                    let inner =
                        if namespace.is_empty() { name } else { format!("{namespace}.{name}") };
                    walk(decls, &inner, base, source, out);
                }
                SurfaceDecl::Section { decls, .. } | SurfaceDecl::Mutual { decls, .. } => {
                    walk(decls, namespace, base, source, out);
                }
                SurfaceDecl::Open { body: Some(body), .. }
                | SurfaceDecl::SetOption { body: Some(body), .. } => {
                    walk(std::slice::from_ref(body.as_ref()), namespace, base, source, out);
                }
                _ => {}
            }
        }
    }
    let (combined, base) = if parser_prelude.is_empty() {
        (std::borrow::Cow::Borrowed(source), 0)
    } else {
        (std::borrow::Cow::Owned(format!("{parser_prelude}\n{source}")), parser_prelude.len() + 1)
    };
    let patterns = clean_elab::tactic::builtins::builtin_tactic_patterns();
    let mut out = Vec::new();
    if let Ok(decls) = clean_parser::parse_file_with_tactics_located(&combined, &patterns) {
        walk(&decls, "", base, source, &mut out);
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    const LOCKSTEP: &str =
        include_str!("../../../trust-spec-temporal/examples/clean_scalar_lockstep.lean");
    const SAFE_THEOREM: &str = "trust_checked_safe.Example.Lockstep";

    fn island(model: &str) -> String {
        format!("import Trust.FiniteModel\n{model}")
    }

    fn buggy() -> String {
        let buggy = island(&LOCKSTEP.replace("\"Buggy\" 0", "\"Buggy\" 1"));
        assert!(buggy.contains("\"Buggy\" 1"));
        buggy
    }

    fn checking_session() -> CleanIslandSession {
        let mut session = CleanIslandSession::new();
        session.enable_model_checks();
        session
    }

    fn states_safety_of(env: &Environment, theorem: &str, model: &str) -> bool {
        env.get_const(&Name::from_string(theorem)).is_some_and(|info| {
            let (head, args) = head_and_args(&info.type_);
            info.kind == ConstantKind::Theorem
                && head == format!("{NAMESPACE}.ScalarModel.safetyClaim")
                && matches!(args.as_slice(), [argument]
                    if matches!(argument.kind(), ExprKind::Const(name, _) if name.to_string() == model))
        })
    }

    /// The compiler proves a declared model safe WITHOUT the author writing the
    /// proof line: the island only declares `Example.Lockstep`, and the session
    /// detects it by type, serves the checker and has the kernel check the
    /// reserved theorem. The scalar expressions beside it are not models. The
    /// author's declarations are reported unchanged.
    #[test]
    fn a_declared_model_is_proved_safe_without_an_authored_proof() {
        let mut session = checking_session();
        let source = island(LOCKSTEP);
        let outcome = session.check(&source);
        assert!(!outcome.is_rejected(), "{:?}", outcome.errors);
        let [check] = outcome.model_checks.as_slice() else { panic!("{:?}", outcome.model_checks) };
        assert_eq!(check.model, "Example.Lockstep");
        assert_eq!(check.budget, DEFAULT_STATE_BUDGET.to_string());
        assert_eq!(
            check.verdict,
            CleanIslandModelVerdict::Safe { theorem: SAFE_THEOREM.to_owned() }
        );
        assert_eq!(
            &source[check.start..check.end],
            "def Lockstep : Trust.Temporal.FiniteModel.ScalarModel :="
        );
        assert!(check.report().contains("proved safe by the kernel"), "{}", check.report());
        assert!(states_safety_of(session.env(), SAFE_THEOREM, "Example.Lockstep"));
        assert!(!outcome.registered.iter().any(|name| name.starts_with(THEOREM_ROOT)));
        assert_eq!(
            session.served_trust_modules(),
            ["Trust.Temporal", "Trust.FiniteModel", "Trust.FiniteModelCheck"]
        );
        assert!(!session.is_tainted());
    }

    /// OFF BY DEFAULT: a session that does not report island results (the
    /// resolver's, one per Clean-origin body, the `.lean` front door) neither
    /// serves the checker nor searches, even for an unsafe model.
    #[test]
    fn a_session_that_did_not_opt_in_checks_no_model() {
        let mut session = CleanIslandSession::new();
        let outcome = session.check(&buggy());
        assert!(!outcome.is_rejected(), "{:?}", outcome.errors);
        assert!(outcome.model_checks.is_empty());
        assert_eq!(session.served_trust_modules(), ["Trust.Temporal", "Trust.FiniteModel"]);
    }

    /// NEGATIVE CONTROL: the same island with `Buggy = 1`, whose `x = y`
    /// invariant breaks one step in, is REJECTED — nobody claimed anything
    /// beyond declaring the model — and the diagnostic names the state and the
    /// invariant at the model's definition.
    #[test]
    fn a_declared_unsafe_model_fails_the_build_with_the_state_and_the_invariant() {
        let buggy = buggy();
        let mut session = checking_session();
        let outcome = session.check(&buggy);
        assert!(outcome.is_rejected());
        let [check] = outcome.model_checks.as_slice() else { panic!("{:?}", outcome.model_checks) };
        let state = |x, y| vec![("x".to_owned(), x), ("y".to_owned(), y)];
        assert_eq!(
            check.verdict,
            CleanIslandModelVerdict::Unsafe {
                state: state(1, 0),
                invariant: "Lockstep".to_owned(),
                run: vec![
                    CleanIslandModelStep { action: "(initial)".to_owned(), state: state(0, 0) },
                    CleanIslandModelStep { action: "Step".to_owned(), state: state(1, 0) },
                ],
            }
        );
        let run = check.run_report().expect("an unsafe model explains itself");
        assert!(run.contains("to the state that breaks `Lockstep` (1 step)"), "{run}");
        assert!(run.contains("the kernel replayed each step"), "{run}");
        assert!(run.contains("  0: (initial)  x = 0, y = 0"), "{run}");
        assert!(run.contains("  1: Step       x = 1"), "{run}");
        let [error] = outcome.errors.as_slice() else { panic!("{:?}", outcome.errors) };
        assert!(buggy[error.start..error.end].starts_with("def Lockstep :"), "{error:?}");
        assert!(error.message.contains("{ x = 1, y = 0 }"), "{}", error.message);
        assert!(error.message.contains("breaks invariant `Lockstep`"), "{}", error.message);
        assert!(session.env().get_const(&Name::from_string(SAFE_THEOREM)).is_none());
        assert!(session.is_tainted());
    }

    /// Nothing an author declares stands in for the check. The reserved name
    /// cannot be declared by an island at all, and a declaration that merely
    /// LOOKS like a safety theorem (`Example.Lockstep.checkedSafe`, any type)
    /// changes nothing: the unsafe model beside it is still rejected.
    #[test]
    fn no_authored_declaration_switches_the_check_off() {
        let decoy = format!("{}\ndef Example.Lockstep.checkedSafe : Nat := 0\n", buggy());
        let outcome = checking_session().check(&decoy);
        assert!(outcome.is_rejected(), "a decoy must not silence the check");
        assert!(matches!(
            outcome.model_checks.as_slice(),
            [CleanIslandModelCheck { verdict: CleanIslandModelVerdict::Unsafe { .. }, .. }]
        ));

        let squatter =
            format!("{}\ntheorem {SAFE_THEOREM} : True := True.intro\n", island(LOCKSTEP));
        let outcome = checking_session().check(&squatter);
        assert!(outcome.is_rejected(), "the reserved namespace is the compiler's");
        assert!(format!("{:?}", outcome.errors).contains("trust_checked_"), "{:?}", outcome.errors);
    }

    #[test]
    fn bounded_requires_typed_nonempty_data_and_never_permits_unsafe() {
        for marker in [
            "def Example.Lockstep.bounded : Bool := true",
            "def Example.Lockstep.bounded : String := \"\"",
            "def Example.Lockstep.bounded : String := \"   \"",
        ] {
            let source = format!("{}\n{marker}\n", island(LOCKSTEP));
            let outcome = checking_session().check(&source);
            assert!(outcome.is_rejected(), "invalid marker: {marker}");
            assert!(
                outcome.errors.iter().any(|error| error.message.contains("invalid bounded")),
                "{:?}",
                outcome.errors
            );
        }
        let source = format!(
            "{}\ndef Example.Lockstep.bounded : String := \"A deliberately small exploration sample\"\n",
            buggy()
        );
        let outcome = checking_session().check(&source);
        assert!(outcome.is_rejected());
        assert!(matches!(outcome.model_checks[0].verdict, CleanIslandModelVerdict::Unsafe { .. }));
    }

    /// The header-first batch path the compiler uses runs the same check: a
    /// safe model in one island, an unsafe one in another, and the unsafe
    /// one's island carries the error.
    #[test]
    fn the_batch_path_checks_each_islands_models() {
        let safe = island(LOCKSTEP);
        let unsafe_model =
            island(&LOCKSTEP.replace("\"Buggy\" 0", "\"Buggy\" 1").replace("Example", "Mutant"));
        let mut session = checking_session();
        let batch = session.check_all(&[&safe, &unsafe_model]);
        assert!(batch.cycles.is_empty());
        assert!(!batch.outcomes[0].is_rejected(), "{:?}", batch.outcomes[0].errors);
        assert!(matches!(
            batch.outcomes[0].model_checks.as_slice(),
            [CleanIslandModelCheck { verdict: CleanIslandModelVerdict::Safe { .. }, .. }]
        ));
        assert!(batch.outcomes[1].is_rejected());
        assert!(matches!(
            batch.outcomes[1].model_checks.as_slice(),
            [CleanIslandModelCheck { model, verdict: CleanIslandModelVerdict::Unsafe { .. }, .. }]
                if model == "Mutant.Lockstep"
        ));
        assert!(session.is_tainted());
    }

    /// TG9: only an explicitly bounded model may remain undecided. A budget
    /// declaration alone does not permit an incomplete check. A model behind a
    /// type alias is still a model; one that takes a parameter is a function,
    /// not a model constant, and is not checked at all.
    #[test]
    fn an_undecided_model_is_reported_and_a_parameterised_one_is_not_a_model() {
        let budgeted =
            format!("{}\ndef Example.Lockstep.stateBudget : Nat := 2\n", island(LOCKSTEP));
        let mut unbounded = checking_session();
        let refused = unbounded.check(&budgeted);
        assert!(refused.is_rejected(), "a budget alone cannot permit Undecided");
        assert!(unbounded.is_tainted());
        assert!(refused.errors.iter().any(|error| error.message.contains("explicitly declare")));
        let budgeted = format!(
            "{budgeted}\ndef Example.Lockstep.bounded : String := \"A two-state exploration sample; exhaustive safety remains open\"\n"
        );
        let mut session = checking_session();
        let outcome = session.check(&budgeted);
        assert!(!outcome.is_rejected(), "{:?}", outcome.errors);
        let [check] = outcome.model_checks.as_slice() else { panic!("{:?}", outcome.model_checks) };
        assert_eq!(check.budget, "2 (`Example.Lockstep.stateBudget`)");
        assert!(
            matches!(&check.verdict, CleanIslandModelVerdict::Undecided { reason }
                if reason.contains("it has 3 reachable states, more than its state budget of 2")
                    && reason.contains("stateBudget : Nat := 3")),
            "{:?}",
            check.verdict
        );
        assert!(check.report().contains("was NOT checked"), "{}", check.report());
        assert!(check.report().contains("explicitly declared bounded:"));
        assert!(check.bounded.as_ref().is_some_and(|reason| reason.contains("remains open")));
        assert!(session.env().get_const(&Name::from_string(SAFE_THEOREM)).is_none());
        assert!(!session.is_tainted());

        // A declaration belongs to one exact model, not every model in the
        // island or every definitionally equal alias of it.
        let with_alias = format!(
            "{budgeted}\ndef UnboundedAlias : Trust.Temporal.FiniteModel.ScalarModel := Example.Lockstep\n\
             def UnboundedAlias.stateBudget : Nat := 2\n"
        );
        let outcome = checking_session().check(&with_alias);
        assert!(outcome.is_rejected());
        assert!(
            outcome.errors.iter().any(|error| {
                error.message.contains("finite model `UnboundedAlias` was NOT checked")
            }),
            "{:?}",
            outcome.errors
        );

        let aliased = format!(
            "{}\ndef Kind : Type := Trust.Temporal.FiniteModel.ScalarModel\n\
             def Aliased : Kind := Example.Lockstep\n\
             def Dial (buggy : Nat) : Trust.Temporal.FiniteModel.ScalarModel :=\n  \
             Trust.Temporal.FiniteModel.ScalarModel.mk \"Dial\"\n    \
             [Trust.Temporal.FiniteModel.Constant.mk \"Buggy\" buggy] [] [] []\n",
            island(LOCKSTEP)
        );
        let outcome = checking_session().check(&aliased);
        assert!(!outcome.is_rejected(), "{:?}", outcome.errors);
        assert_eq!(
            outcome.model_checks.iter().map(|check| check.model.as_str()).collect::<Vec<_>>(),
            ["Example.Lockstep", "Aliased"]
        );
        assert!(
            outcome
                .model_checks
                .iter()
                .all(|check| matches!(check.verdict, CleanIslandModelVerdict::Safe { .. }))
        );
    }

    const HARNESS: &str =
        include_str!("../../../trust-spec-temporal/examples/harness_policy_one_writer.lean");

    /// A MODEL FROM A REAL PROGRAM: aterm's harness-policy protocol, whose
    /// one-writer design fixed a race five review rounds had not. Declared as
    /// an island, the compiler proves it (85 reachable states, the count ty
    /// reports for the same model). The mutant twin — a second writer and a
    /// Commit that raises no forget — is rejected with a run that shows the
    /// bug: the window commits without asking the watcher to forget, the
    /// deduped poll then posts nothing, and the window runs a policy the file
    /// does not write.
    #[test]
    fn a_real_protocol_is_proved_and_its_mutant_is_rejected_with_a_run() {
        let source = format!(
            "import Trust.Protocol\n{HARNESS}\ndef HarnessPolicy.Mutant : \
             Trust.Temporal.FiniteModel.ScalarModel :=\n  HarnessPolicy.Protocol 1\n"
        );
        let mut session = checking_session();
        let outcome = session.check(&source);
        let verdicts: Vec<(&str, &CleanIslandModelVerdict)> = outcome
            .model_checks
            .iter()
            .map(|check| (check.model.as_str(), &check.verdict))
            .collect();
        let [("HarnessPolicy.OneWriter", safe), ("HarnessPolicy.Mutant", mutant)] =
            verdicts.as_slice()
        else {
            panic!("{verdicts:?} {:?}", outcome.errors)
        };
        assert!(matches!(safe, CleanIslandModelVerdict::Safe { .. }), "{safe:?}");
        let CleanIslandModelVerdict::Unsafe { invariant, run, .. } = mutant else {
            panic!("{mutant:?}")
        };
        assert_eq!(invariant, "Agrees");
        let actions: Vec<&str> = run.iter().map(|step| step.action.as_str()).collect();
        assert_eq!(actions.first(), Some(&"(initial)"));
        assert!(
            actions.iter().any(
                |action| action.starts_with("SecondWriter") || *action == "CommitWithoutForget"
            ),
            "a mutant action is on the run: {actions:?}"
        );
        assert!(outcome.is_rejected());
        assert!(
            source[outcome.errors[0].start..outcome.errors[0].end]
                .starts_with("def HarnessPolicy.Mutant"),
            "{:?}",
            outcome.errors[0]
        );

        // The explanation is held to the kernel: this module's reading of the
        // model reaches exactly the states the kernel checker's search does.
        let env = session.env();
        let tc = TypeChecker::with_mode(env, env.mode());
        let design = Expr::const_str("HarnessPolicy.OneWriter");
        let kernel_rows = list(
            &tc,
            &Expr::app(Expr::app(constant("reachRows"), design.clone()), Expr::nat_lit(256)),
        )
        .expect("the kernel search returns rows");
        assert_eq!(kernel_rows.len(), 85);
        assert_eq!(super::super::model_trace::reachable_states(&tc, &design), Some(85));
    }

    /// THE NATURAL-NUMBER TRAP, found by running a real program's models
    /// through the checker: `handled <= received - 1`, the usual spelling of
    /// `handled < received`, is TRUE at `0 <= 0 - 1` over the naturals. The
    /// kernel then (correctly, for the model as written) finds a state the
    /// intended model never reaches. The check says so: it names the
    /// subtraction, the place and the state. The transposed guard
    /// (`handled + 1 <= received`) is the intended model, and is proved.
    #[test]
    fn a_subtraction_that_stops_at_zero_is_reported_with_its_place_and_state() {
        let queue = |guard: &str| {
            island(&format!(
                "namespace Queue\n\
                 def r : Trust.Temporal.FiniteModel.ScalarExpr := \
                 Trust.Temporal.FiniteModel.ScalarExpr.var \"received\"\n\
                 def h : Trust.Temporal.FiniteModel.ScalarExpr := \
                 Trust.Temporal.FiniteModel.ScalarExpr.var \"handled\"\n\
                 def one : Trust.Temporal.FiniteModel.ScalarExpr := \
                 Trust.Temporal.FiniteModel.ScalarExpr.int 1\n\
                 def M : Trust.Temporal.FiniteModel.ScalarModel :=\n  \
                 Trust.Temporal.FiniteModel.ScalarModel.mk \"Queue\" []\n    \
                 [Trust.Temporal.FiniteModel.StateVar.mk \"received\" 0,\n     \
                 Trust.Temporal.FiniteModel.StateVar.mk \"handled\" 0]\n    \
                 [Trust.Temporal.FiniteModel.Action.mk \"Receive\"\n       \
                 (Trust.Temporal.FiniteModel.Guard.when \
                 (Trust.Temporal.FiniteModel.ScalarExpr.le r one))\n       \
                 [Trust.Temporal.FiniteModel.Update.mk \"received\" \
                 (Trust.Temporal.FiniteModel.ScalarExpr.add r one)],\n     \
                 Trust.Temporal.FiniteModel.Action.mk \"Handle\"\n       \
                 (Trust.Temporal.FiniteModel.Guard.when ({guard}))\n       \
                 [Trust.Temporal.FiniteModel.Update.mk \"handled\" \
                 (Trust.Temporal.FiniteModel.ScalarExpr.add h one)]]\n    \
                 [Trust.Temporal.FiniteModel.Invariant.mk \"NeverAhead\" \
                 (Trust.Temporal.FiniteModel.ScalarExpr.le h r)]\n\
                 end Queue\n"
            ))
        };
        let trap = queue(
            "Trust.Temporal.FiniteModel.ScalarExpr.le h (Trust.Temporal.FiniteModel.ScalarExpr.sub r one)",
        );
        let outcome = checking_session().check(&trap);
        let [check] = outcome.model_checks.as_slice() else { panic!("{:?}", outcome.model_checks) };
        assert!(
            matches!(check.verdict, CleanIslandModelVerdict::Unsafe { .. }),
            "{:?}",
            check.verdict
        );
        assert_eq!(
            check.truncation,
            Some(CleanIslandModelTruncation {
                place: "the guard of `Handle`".to_owned(),
                left: 0,
                right: 1,
                state: vec![("received".to_owned(), 0), ("handled".to_owned(), 0)],
            })
        );
        let report = check.truncation_report().expect("a truncation is reported");
        assert!(report.contains("evaluates `0 - 1` in the guard of `Handle`"), "{report}");
        assert!(report.contains("that is 0, not -1"), "{report}");

        let intended = queue(
            "Trust.Temporal.FiniteModel.ScalarExpr.le (Trust.Temporal.FiniteModel.ScalarExpr.add h one) r",
        );
        let outcome = checking_session().check(&intended);
        let [check] = outcome.model_checks.as_slice() else { panic!("{:?}", outcome.model_checks) };
        assert!(
            matches!(check.verdict, CleanIslandModelVerdict::Safe { .. }),
            "{:?}",
            check.verdict
        );
        assert_eq!(check.truncation, None);
    }

    /// PROGRESS, ON THE REAL PROTOCOL. "The window catches up with the file":
    /// once committed, the policy in force keeps coming back to the one on
    /// disk, under weak fairness of the watcher's poll, the window's delivery
    /// and the forget. For the design the untrusted search finds no
    /// counterexample over all 85 states, and SAYS that is not a proof. For
    /// the mutant a fair run leaves the goal for good, and the kernel confirms
    /// it: the build fails with the run.
    #[test]
    fn a_progress_claim_is_searched_and_a_livelock_is_confirmed_by_the_kernel() {
        let claim = |name: &str, model: &str| {
            format!(
                "def HarnessPolicy.{name} : Trust.Temporal.FiniteModel.ScalarProgress :=\n  \
                 progress ({model})\n    \
                 (v \"committed\" ≐ n 0 ⋎ v \"in_force\" ≐ v \"disk\")\n    \
                 [\"Poll\", \"Deliver\", \"Forget\"] []\n"
            )
        };
        let source = format!(
            "import Trust.Protocol\n{HARNESS}\nopen Trust.Protocol\n{}{}\n\
             def HarnessPolicy.MutantCatchesUp.bounded : String := \"Bounded exploration cannot excuse a livelock\"\n",
            claim("CatchesUp", "HarnessPolicy.OneWriter"),
            claim("MutantCatchesUp", "HarnessPolicy.Protocol 1")
        );
        let outcome = checking_session().check(&source);
        let verdict = |name: &str| {
            let check = outcome
                .model_checks
                .iter()
                .find(|check| check.model == format!("HarnessPolicy.{name}"))
                .unwrap_or_else(|| panic!("{name}: {:?}", outcome.model_checks));
            assert!(check.progress, "{name}");
            check
        };
        assert_eq!(
            verdict("CatchesUp").verdict,
            CleanIslandModelVerdict::Live {
                model: "HarnessPolicy.OneWriter".to_owned(),
                theorem: "trust_checked_live.HarnessPolicy.CatchesUp".to_owned(),
                states: 85
            }
        );
        assert!(verdict("CatchesUp").report().contains("proved by the kernel"));
        let mutant = verdict("MutantCatchesUp");
        let CleanIslandModelVerdict::Livelock { stem, cycle, .. } = &mutant.verdict else {
            panic!("{:?}", mutant.verdict)
        };
        assert_eq!(stem.first().map(|step| step.action.as_str()), Some("(initial)"));
        let report = mutant.run_report().expect("a livelock explains itself");
        assert!(report.contains("leaves the goal of `HarnessPolicy.MutantCatchesUp` for good"));
        assert!(cycle.is_empty() == report.contains("stutters there forever"), "{report}");
        assert!(outcome.is_rejected());
        assert!(
            source[outcome.errors[0].start..outcome.errors[0].end]
                .starts_with("def HarnessPolicy.MutantCatchesUp"),
            "{:?}",
            outcome.errors[0]
        );
        assert!(outcome.errors[0].message.contains("progress claim"), "{:?}", outcome.errors[0]);
    }

    #[test]
    fn a_searched_but_unproved_progress_claim_requires_bounded_permission() {
        let source = format!(
            "import Trust.Protocol\n{HARNESS}\nopen Trust.Protocol\n\
             def HarnessPolicy.CatchesUp : Trust.Temporal.FiniteModel.ScalarProgress :=\n  \
             progress HarnessPolicy.OneWriter\n    \
             (v \"committed\" ≐ n 0 ⋎ v \"in_force\" ≐ v \"disk\")\n    \
             [\"Poll\", \"Deliver\", \"Forget\"] []\n\
             def HarnessPolicy.CatchesUp.stateBudget : Nat := 0\n"
        );
        let refused = checking_session().check(&source);
        let claim = refused.model_checks.iter().find(|check| check.progress).expect("claim");
        assert!(
            matches!(claim.verdict, CleanIslandModelVerdict::Searched { .. }),
            "{:?}",
            claim.verdict
        );
        assert!(refused.is_rejected());
        assert!(refused.errors.iter().any(|error| error.message.contains("is NOT proved")));

        let bounded = format!(
            "{source}\ndef HarnessPolicy.CatchesUp.bounded : String := \"Search only; progress certification deliberately deferred\"\n"
        );
        let mut session = checking_session();
        let accepted = session.check(&bounded);
        assert!(!accepted.is_rejected(), "{:?}", accepted.errors);
        let claim = accepted.model_checks.iter().find(|check| check.progress).expect("claim");
        assert!(matches!(claim.verdict, CleanIslandModelVerdict::Searched { .. }));
        assert!(claim.report().contains("explicitly declared bounded:"));
        assert!(
            session
                .env()
                .get_const(&Name::from_string("trust_checked_live.HarnessPolicy.CatchesUp"))
                .is_none(),
            "a bounded declaration must mint no progress theorem"
        );
    }

    /// WEAK VERSUS STRONG FAIRNESS, with a real loop. `Up` and `Down` toggle
    /// forever; `Finish` is enabled only after `Up`. Weakly fair, `Finish` is
    /// not CONTINUOUSLY enabled, so the toggle loop is a fair run that never
    /// finishes: a livelock, with the loop. Strongly fair, `Finish` is enabled
    /// again and again and must be taken: no counterexample.
    #[test]
    fn weak_fairness_admits_the_loop_that_strong_fairness_forbids() {
        let toggle = |weak: &str, strong: &str| {
            format!(
                "import Trust.FiniteModelCheck\nnamespace Toggle\n\
                 def x : Trust.Temporal.FiniteModel.ScalarExpr := \
                 Trust.Temporal.FiniteModel.ScalarExpr.var \"x\"\n\
                 def d : Trust.Temporal.FiniteModel.ScalarExpr := \
                 Trust.Temporal.FiniteModel.ScalarExpr.var \"done\"\n\
                 def k (value : Nat) : Trust.Temporal.FiniteModel.ScalarExpr := \
                 Trust.Temporal.FiniteModel.ScalarExpr.int value\n\
                 def guardAt (value : Nat) : Trust.Temporal.FiniteModel.Guard := \
                 Trust.Temporal.FiniteModel.Guard.when (Trust.Temporal.FiniteModel.ScalarExpr.and \
                 (Trust.Temporal.FiniteModel.ScalarExpr.eq x (k value)) \
                 (Trust.Temporal.FiniteModel.ScalarExpr.eq d (k 0)))\n\
                 def M : Trust.Temporal.FiniteModel.ScalarModel :=\n  \
                 Trust.Temporal.FiniteModel.ScalarModel.mk \"Toggle\" []\n    \
                 [Trust.Temporal.FiniteModel.StateVar.mk \"x\" 0,\n     \
                 Trust.Temporal.FiniteModel.StateVar.mk \"done\" 0]\n    \
                 [Trust.Temporal.FiniteModel.Action.mk \"Up\" (guardAt 0)\n       \
                 [Trust.Temporal.FiniteModel.Update.mk \"x\" (k 1)],\n     \
                 Trust.Temporal.FiniteModel.Action.mk \"Down\" (guardAt 1)\n       \
                 [Trust.Temporal.FiniteModel.Update.mk \"x\" (k 0)],\n     \
                 Trust.Temporal.FiniteModel.Action.mk \"Finish\" (guardAt 1)\n       \
                 [Trust.Temporal.FiniteModel.Update.mk \"done\" (k 1)]]\n    []\n\
                 def Finishes : Trust.Temporal.FiniteModel.ScalarProgress :=\n  \
                 Trust.Temporal.FiniteModel.ScalarProgress.mk M \
                 (Trust.Temporal.FiniteModel.ScalarExpr.eq d (k 1)) {weak} {strong}\n\
                 end Toggle\n"
            )
        };
        let progress = |source: &str| {
            let outcome = checking_session().check(source);
            outcome
                .model_checks
                .iter()
                .find(|check| check.progress)
                .unwrap_or_else(|| panic!("{:?} {:?}", outcome.model_checks, outcome.errors))
                .clone()
        };
        let weak = progress(&toggle("[\"Up\", \"Down\", \"Finish\"]", "[]"));
        let CleanIslandModelVerdict::Livelock { stem, cycle, .. } = &weak.verdict else {
            panic!("{:?}", weak.verdict)
        };
        assert_eq!(stem.len(), 1, "the loop starts at the initial state: {stem:?}");
        assert_eq!(
            cycle.iter().map(|step| step.action.as_str()).collect::<Vec<_>>(),
            ["Up", "Down"]
        );
        let report = weak.run_report().expect("the loop is printed");
        assert!(report.contains("then it repeats these 2 step(s) forever"), "{report}");

        // Strongly fair, no counterexample, and PROVED: `Finish` cannot move
        // the state with x = 0, so that state is ranked one level deeper with
        // `Up` as its helper, and strong fairness takes the run out of the loop.
        let strong = progress(&toggle("[\"Up\", \"Down\"]", "[\"Finish\"]"));
        assert!(
            matches!(&strong.verdict, CleanIslandModelVerdict::Live { model, states: 3, .. }
                if model == "Toggle.M"),
            "{:?}",
            strong.verdict
        );
    }

    /// STRONG FAIRNESS NESTED TWO DEEP. Unfair moves wander among x = 0, 1,
    /// 2; `A` (strongly fair) finishes from x = 2, `B` from x = 1, and `W`
    /// from x = 0. A run that stays unfinished must eventually avoid x = 2 (or
    /// `A` takes it), then x = 1 (or `B` does), and then sits at x = 0, where
    /// `W` is enabled for good. The certificate says exactly that: x = 2 has
    /// one level, x = 1 two and x = 0 three, and the kernel proves the claim.
    /// With `B` only weakly fair the 0-1 loop is a fair run: a livelock.
    #[test]
    fn strong_fairness_nested_two_deep_is_proved() {
        let island = |weak: &str, strong: &str| {
            format!(
                "import Trust.FiniteModelCheck\nnamespace Nest\n\
                 def x : Trust.Temporal.FiniteModel.ScalarExpr := \
                 Trust.Temporal.FiniteModel.ScalarExpr.var \"x\"\n\
                 def d : Trust.Temporal.FiniteModel.ScalarExpr := \
                 Trust.Temporal.FiniteModel.ScalarExpr.var \"done\"\n\
                 def k (value : Nat) : Trust.Temporal.FiniteModel.ScalarExpr := \
                 Trust.Temporal.FiniteModel.ScalarExpr.int value\n\
                 def guardAt (value : Nat) : Trust.Temporal.FiniteModel.Guard := \
                 Trust.Temporal.FiniteModel.Guard.when (Trust.Temporal.FiniteModel.ScalarExpr.and \
                 (Trust.Temporal.FiniteModel.ScalarExpr.eq x (k value)) \
                 (Trust.Temporal.FiniteModel.ScalarExpr.eq d (k 0)))\n\
                 def go (name : String) (start target : Nat) : Trust.Temporal.FiniteModel.Action := \
                 Trust.Temporal.FiniteModel.Action.mk name (guardAt start) \
                 [Trust.Temporal.FiniteModel.Update.mk \"x\" (k target)]\n\
                 def finish (name : String) (start : Nat) : Trust.Temporal.FiniteModel.Action := \
                 Trust.Temporal.FiniteModel.Action.mk name (guardAt start) \
                 [Trust.Temporal.FiniteModel.Update.mk \"done\" (k 1)]\n\
                 def M : Trust.Temporal.FiniteModel.ScalarModel :=\n  \
                 Trust.Temporal.FiniteModel.ScalarModel.mk \"Nest\" []\n    \
                 [Trust.Temporal.FiniteModel.StateVar.mk \"x\" 0,\n     \
                 Trust.Temporal.FiniteModel.StateVar.mk \"done\" 0]\n    \
                 [go \"U01\" 0 1, go \"U10\" 1 0, go \"U12\" 1 2, go \"U21\" 2 1,\n     \
                 finish \"A\" 2, finish \"B\" 1, finish \"W\" 0]\n    []\n\
                 def Finishes : Trust.Temporal.FiniteModel.ScalarProgress :=\n  \
                 Trust.Temporal.FiniteModel.ScalarProgress.mk M \
                 (Trust.Temporal.FiniteModel.ScalarExpr.eq d (k 1)) {weak} {strong}\n\
                 end Nest\n"
            )
        };
        let progress = |source: &str| {
            let outcome = checking_session().check(source);
            outcome
                .model_checks
                .iter()
                .find(|check| check.progress)
                .unwrap_or_else(|| panic!("{:?} {:?}", outcome.model_checks, outcome.errors))
                .clone()
        };
        let nested = progress(&island("[\"W\"]", "[\"A\", \"B\"]"));
        assert!(
            matches!(&nested.verdict, CleanIslandModelVerdict::Live { model, states: 6, .. }
                if model == "Nest.M"),
            "{:?}",
            nested.verdict
        );
        let weak_b = progress(&island("[\"W\", \"B\"]", "[\"A\"]"));
        assert!(
            matches!(&weak_b.verdict, CleanIslandModelVerdict::Livelock { .. }),
            "{:?}",
            weak_b.verdict
        );
    }

    /// AN AMBIGUOUS FAIRNESS NAME DECIDES NOTHING. Two actions are named `T`:
    /// the first is dead, the second is enabled at the initial state and
    /// reaches the goal. Read as "the first `T`", stuttering at the initial
    /// state would be a fair run that never reaches the goal — but the other
    /// `T` stays enabled and is never taken, so that run is not fair to it and
    /// the claim in fact holds. Neither the search nor the kernel picks one:
    /// the claim is reported undecided, and an unbounded build is refused.
    #[test]
    fn a_fair_name_two_actions_share_is_not_decided() {
        let source = "import Trust.FiniteModelCheck\nnamespace Twice\n\
             def x : Trust.Temporal.FiniteModel.ScalarExpr := \
             Trust.Temporal.FiniteModel.ScalarExpr.var \"x\"\n\
             def k (value : Nat) : Trust.Temporal.FiniteModel.ScalarExpr := \
             Trust.Temporal.FiniteModel.ScalarExpr.int value\n\
             def step (start : Nat) : Trust.Temporal.FiniteModel.Action := \
             Trust.Temporal.FiniteModel.Action.mk \"T\" (Trust.Temporal.FiniteModel.Guard.when \
             (Trust.Temporal.FiniteModel.ScalarExpr.eq x (k start))) \
             [Trust.Temporal.FiniteModel.Update.mk \"x\" (k 1)]\n\
             def M : Trust.Temporal.FiniteModel.ScalarModel :=\n  \
             Trust.Temporal.FiniteModel.ScalarModel.mk \"Twice\" []\n    \
             [Trust.Temporal.FiniteModel.StateVar.mk \"x\" 0] [step 9, step 0] []\n\
             def Reaches : Trust.Temporal.FiniteModel.ScalarProgress :=\n  \
             Trust.Temporal.FiniteModel.ScalarProgress.mk M \
             (Trust.Temporal.FiniteModel.ScalarExpr.eq x (k 1)) [\"T\"] []\n\
             end Twice\n";
        let outcome = checking_session().check(source);
        assert!(outcome.is_rejected(), "an undecided progress claim must fail");
        let bounded = format!(
            "{source}\ndef Twice.Reaches.bounded : String := \"Fairness action identities remain ambiguous\"\n"
        );
        let bounded = checking_session().check(&bounded);
        assert!(!bounded.is_rejected(), "{:?}", bounded.errors);
        let claim = outcome
            .model_checks
            .iter()
            .find(|check| check.progress)
            .unwrap_or_else(|| panic!("{:?}", outcome.model_checks));
        assert!(
            matches!(&claim.verdict, CleanIslandModelVerdict::Undecided { reason }
                if reason.contains("declares more than once")),
            "{:?}",
            claim.verdict
        );
        assert!(claim.report().starts_with("progress claim `Twice.Reaches` was NOT checked"));
    }

    /// A counter that steps to `top`, with the invariant `x <= bound`.
    fn counter(top: u64, bound: u64) -> String {
        island(&format!(
            "namespace Deep\n\
             def x : Trust.Temporal.FiniteModel.ScalarExpr := \
             Trust.Temporal.FiniteModel.ScalarExpr.var \"x\"\n\
             def Counter : Trust.Temporal.FiniteModel.ScalarModel :=\n  \
             Trust.Temporal.FiniteModel.ScalarModel.mk \"Counter\" []\n    \
             [Trust.Temporal.FiniteModel.StateVar.mk \"x\" 0]\n    \
             [Trust.Temporal.FiniteModel.Action.mk \"Step\"\n       \
             (Trust.Temporal.FiniteModel.Guard.when (Trust.Temporal.FiniteModel.ScalarExpr.le \
             (Trust.Temporal.FiniteModel.ScalarExpr.add x \
             (Trust.Temporal.FiniteModel.ScalarExpr.int 1)) \
             (Trust.Temporal.FiniteModel.ScalarExpr.int {top})))\n       \
             [Trust.Temporal.FiniteModel.Update.mk \"x\" \
             (Trust.Temporal.FiniteModel.ScalarExpr.add x \
             (Trust.Temporal.FiniteModel.ScalarExpr.int 1))]]\n    \
             [Trust.Temporal.FiniteModel.Invariant.mk \"Bounded\" \
             (Trust.Temporal.FiniteModel.ScalarExpr.le x \
             (Trust.Temporal.FiniteModel.ScalarExpr.int {bound}))]\n\
             end Deep\n"
        ))
    }

    /// A BUG PAST THE BUDGET IS STILL CAUGHT. The violation is 600 steps deep
    /// in a 1,001-state model, far beyond the 256 states the kernel's own
    /// search explores. The untrusted search finds it; the kernel replays the
    /// 600 steps and evaluates the invariant false at the end, and never
    /// searches. The build fails with the run.
    #[test]
    fn a_violation_beyond_the_state_budget_is_found_and_confirmed_by_replay() {
        let outcome = checking_session().check(&counter(1000, 599));
        let [check] = outcome.model_checks.as_slice() else { panic!("{:?}", outcome.model_checks) };
        let CleanIslandModelVerdict::Unsafe { state, invariant, run } = &check.verdict else {
            panic!("{:?}", check.verdict)
        };
        assert_eq!(
            (state.as_slice(), invariant.as_str()),
            (&[("x".to_owned(), 600)][..], "Bounded")
        );
        assert_eq!(run.len(), 601);
        assert!(outcome.is_rejected());
        let report = check.run_report().expect("the run is printed");
        assert!(report.contains("(600 steps); the kernel replayed each step"), "{report}");
        assert!(report.contains("steps not shown"), "{report}");
    }

    /// A SAFE MODEL OVER THE BUDGET is not handed to the kernel's search: the
    /// warning says how many states it has and the budget that proves it.
    /// With that budget declared, the kernel proves it.
    #[test]
    fn a_safe_model_over_the_budget_reports_the_budget_that_proves_it() {
        let over = counter(300, 300);
        let outcome = checking_session().check(&over);
        assert!(outcome.is_rejected(), "an undeclared incomplete check must fail");
        let [check] = outcome.model_checks.as_slice() else { panic!("{:?}", outcome.model_checks) };
        assert!(
            matches!(&check.verdict, CleanIslandModelVerdict::Undecided { reason }
                if reason.contains("it has 301 reachable states, more than its state budget of 256")
                    && reason.contains("stateBudget : Nat := 301")),
            "{:?}",
            check.verdict
        );

        let budgeted = format!("{over}\ndef Deep.Counter.stateBudget : Nat := 301\n");
        let outcome = checking_session().check(&budgeted);
        let [check] = outcome.model_checks.as_slice() else { panic!("{:?}", outcome.model_checks) };
        assert!(
            matches!(check.verdict, CleanIslandModelVerdict::Safe { .. }),
            "{:?}",
            check.verdict
        );
    }

    /// `TRUST_MODEL_WORK_LIMIT` and `TRUST_MODEL_HEARTBEATS_PER_WORK` MEASURE
    /// other kernel limits (`set_model_kernel_limits`).
    fn set_kernel_limits_from_env(session: &mut CleanIslandSession) {
        let read = |key: &str, default: u64| {
            std::env::var(key).ok().map_or(default, |value| value.parse().expect("a number"))
        };
        session.set_model_kernel_limits(
            read("TRUST_MODEL_WORK_LIMIT", KERNEL_WORK_LIMIT),
            read("TRUST_MODEL_HEARTBEATS_PER_WORK", HEARTBEATS_PER_WORK),
        );
    }

    /// Incompleteness is accepted only for this exact explicitly bounded
    /// subject, and must never leave a safety or progress theorem behind.
    fn assert_incomplete_scope(
        session: &CleanIslandSession,
        outcome: &CleanIslandOutcome,
        check: &CleanIslandModelCheck,
    ) {
        let refused =
            outcome.errors.iter().any(|error| error.start == check.start && error.end == check.end);
        assert_eq!(refused, check.bounded.is_none(), "{}", check.report());
        if let Some(reason) = &check.bounded {
            assert!(!reason.trim().is_empty());
        }
        let name = Name::from_string(&check.model);
        let theorem = if check.progress {
            reserved_name_under(LIVE_THEOREM_ROOT, &name)
        } else {
            reserved_theorem_name(&name)
        };
        assert!(session.env().get_const(&theorem).is_none(), "{}", check.report());
    }

    /// THE CORPUS LANE: a real program's models through the compiler's check.
    ///
    /// `TRUST_MODEL_CORPUS` names a directory written by aterm's emitter
    /// (`targo --unverified run -p aterm-spec --example emit_clean_models --
    /// <dir>`): `manifest.tsv` and `islands/NNN_Name.lean`, each island
    /// declaring `AtermN.design` and one `AtermN.mutantK` per `Buggy = K`
    /// dial the model declares (each a race it was written to catch). The
    /// manifest carries what aterm's own integer interpreter found: the design
    /// is safe with `states` reachable states, and each listed mutant breaks
    /// an invariant.
    ///
    /// Held here, per model: the design is PROVED when it fits the budget and
    /// otherwise explicitly bounded or refused with exactly aterm's state
    /// count, without a theorem; every mutant is
    /// REJECTED, at any size, with a run the kernel replayed; and no model's
    /// subtraction stops at zero (the emitter transposes comparisons).
    ///
    /// ```text
    /// TRUST_MODEL_CORPUS=<dir> targo --unverified test --release --locked \
    ///   -p trust-certify --lib -- --ignored corpus --nocapture
    /// ```
    #[test]
    #[ignore = "set TRUST_MODEL_CORPUS to a directory written by aterm's emit_clean_models"]
    fn a_corpus_of_real_models_agrees_with_its_manifest() {
        let dir = std::env::var("TRUST_MODEL_CORPUS").expect("TRUST_MODEL_CORPUS is set");
        let manifest = std::fs::read_to_string(format!("{dir}/manifest.tsv")).expect("manifest");
        let mut session = checking_session();
        // `TRUST_MODEL_BUDGET=<states>` MEASURES a larger budget instead:
        // which designs the kernel then proves and how long each island takes
        // (one `timing` line per model). Designs are not held to a verdict in
        // that mode; mutants still are.
        let budget = std::env::var("TRUST_MODEL_BUDGET")
            .ok()
            .map_or(DEFAULT_STATE_BUDGET, |budget| budget.parse().expect("a state count"));
        let measuring = budget != DEFAULT_STATE_BUDGET;
        session.set_model_state_budget(budget);
        set_kernel_limits_from_env(&mut session);
        let (mut proved, mut over_budget, mut caught) = (0, 0, 0);
        let mut wrong = Vec::new();
        for row in manifest.lines().skip(1) {
            let fields: Vec<&str> = row.split('\t').collect();
            let [index, name, states, mutants, "emitted", ..] = fields.as_slice() else { continue };
            let dials: Vec<u64> = match *mutants {
                "-" => Vec::new(),
                listed => listed.split(',').map(|dial| dial.parse().expect("a dial")).collect(),
            };
            let index: usize = index.parse().expect("an index");
            let states: u64 = states.parse().expect("a state count");
            let source = std::fs::read_to_string(format!("{dir}/islands/{index:03}_{name}.lean"))
                .expect("the island");
            let started = std::time::Instant::now();
            let outcome = session.check(&source);
            let seconds = started.elapsed().as_secs_f64();
            let verdict_of = |model: &str| {
                outcome
                    .model_checks
                    .iter()
                    .find(|check| check.model == format!("Aterm{index}.{model}"))
            };
            if measuring {
                let design = match verdict_of("design").map(|check| &check.verdict) {
                    Some(CleanIslandModelVerdict::Safe { .. }) => "proved",
                    Some(CleanIslandModelVerdict::Undecided { .. }) => "undecided",
                    _ => "other",
                };
                let work = verdict_of("design").and_then(|check| check.work).unwrap_or(0);
                println!("timing\t{name}\t{states}\t{design}\t{seconds:.2}\t{work}");
            }
            match verdict_of("design") {
                Some(check) if check.truncation.is_some() => {
                    wrong.push(format!("{name}: design truncates: {:?}", check.truncation));
                }
                Some(CleanIslandModelCheck {
                    verdict: CleanIslandModelVerdict::Safe { .. },
                    ..
                }) if measuring || states <= DEFAULT_STATE_BUDGET => {
                    proved += 1;
                }
                Some(
                    check @ CleanIslandModelCheck {
                        verdict: CleanIslandModelVerdict::Undecided { reason },
                        ..
                    },
                ) if measuring
                    || (states > DEFAULT_STATE_BUDGET
                        && reason.contains(&format!("it has {states} reachable states"))) =>
                {
                    over_budget += 1;
                    assert_incomplete_scope(&session, &outcome, check);
                }
                other => wrong.push(format!(
                    "{name}: design ({states} states): {:?}; errors {:?}",
                    other.map(|check| &check.verdict),
                    outcome.errors.first().map(|error| &error.message)
                )),
            }
            for dial in dials {
                match verdict_of(&format!("mutant{dial}")) {
                    Some(CleanIslandModelCheck {
                        verdict: CleanIslandModelVerdict::Unsafe { run, .. },
                        ..
                    }) if !run.is_empty() => caught += 1,
                    other => wrong.push(format!(
                        "{name}: mutant{dial}: {:?}",
                        other.map(|check| &check.verdict)
                    )),
                }
            }
        }
        println!(
            "corpus: {proved} designs proved, {over_budget} explicitly bounded or refused undecided designs with aterm's \
             exact state count, {caught} mutants rejected with a replayed run, {} wrong",
            wrong.len()
        );
        assert!(wrong.is_empty(), "{}", wrong.join("\n"));
        assert!(proved + over_budget > 0, "the corpus is empty");
    }

    /// THE CORPUS LANE, PROGRESS HALF. `<dir>/progress.tsv` and
    /// `progress/NNN_Name.lean`, written by the same emitter: every liveness
    /// obligation of the program as `ScalarProgress` claims named for what the
    /// program's own audit found. `holds`: no fair run leaves the goal for
    /// good, over exactly the manifest's state count. `fails_without_<A>`: the
    /// obligation with one fairness assumption dropped. `fails_mutant_<A>`: the
    /// obligation over the model with one mutant added. Every `fails_*` must be
    /// a livelock the KERNEL confirmed.
    #[test]
    #[ignore = "set TRUST_MODEL_CORPUS to a directory written by aterm's emit_clean_models"]
    fn a_corpus_of_real_progress_claims_agrees_with_its_manifest() {
        let dir = std::env::var("TRUST_MODEL_CORPUS").expect("TRUST_MODEL_CORPUS is set");
        let manifest = std::fs::read_to_string(format!("{dir}/progress.tsv")).expect("manifest");
        let mut session = checking_session();
        // The same measuring knobs as the safety half.
        if let Ok(budget) = std::env::var("TRUST_MODEL_BUDGET") {
            session.set_model_state_budget(budget.parse().expect("a state count"));
        }
        set_kernel_limits_from_env(&mut session);
        let (mut proved, mut held, mut livelocks) = (0, 0, 0);
        let mut unproved_reasons: Vec<String> = Vec::new();
        let mut wrong = Vec::new();
        for row in manifest.lines().skip(1) {
            let fields: Vec<&str> = row.split('\t').collect();
            let [index, _, name, states, "emitted"] = fields.as_slice() else { continue };
            let index: usize = index.parse().expect("an index");
            let states: usize = states.parse().expect("a state count");
            let source = std::fs::read_to_string(format!("{dir}/progress/{index:03}_{name}.lean"))
                .expect("the island");
            let started = std::time::Instant::now();
            let outcome = session.check(&source);
            let seconds = started.elapsed().as_secs_f64();
            let claims: Vec<_> =
                outcome.model_checks.iter().filter(|check| check.progress).collect();
            if std::env::var("TRUST_MODEL_BUDGET").is_ok() {
                println!("timing\t{name}\t{states}\t{seconds:.2}");
            }
            if claims.is_empty() {
                wrong.push(format!("{name}: no claim was checked: {:?}", outcome.errors.first()));
            }
            for check in claims {
                let claim = check.model.rsplit('.').next().unwrap_or_default();
                match &check.verdict {
                    CleanIslandModelVerdict::Live { states: reached, .. }
                        if claim == "holds" && *reached == states =>
                    {
                        proved += 1;
                    }
                    CleanIslandModelVerdict::Searched { states: reached, unproved, .. }
                        if claim == "holds" && *reached == states =>
                    {
                        held += 1;
                        assert_incomplete_scope(&session, &outcome, check);
                        unproved_reasons.push(format!("{name} ({states} states): {unproved}"));
                    }
                    CleanIslandModelVerdict::Livelock { .. } if claim.starts_with("fails_") => {
                        livelocks += 1;
                    }
                    other => wrong.push(format!("{name}: {claim}: {other:?}")),
                }
            }
        }
        println!(
            "progress corpus: {proved} obligations PROVED by the kernel, {held} searched with \
             no counterexample but not proved, each over the program's exact state count; \
             {livelocks} livelocks confirmed by the kernel; {} wrong",
            wrong.len()
        );
        for reason in &unproved_reasons {
            println!("  not proved: {reason}");
        }
        assert!(wrong.is_empty(), "{}", wrong.join("\n"));
        assert!(proved + held > 0, "the corpus is empty");
    }

    /// A MODEL PAST THE DEFAULT CEILING IS NOT ATTEMPTED UNLESS ITS AUTHOR
    /// OPTS IN. The session's budget covers it, but its search is past what
    /// the kernel is asked by default: the warning says so at once, with the
    /// `stateBudget` that asks anyway and roughly what that costs, where an
    /// attempt would take tens of seconds.
    #[test]
    fn a_model_past_the_default_ceiling_is_reported_without_an_attempt() {
        let source = counter(80000, 80000);
        let started = std::time::Instant::now();
        let mut session = checking_session();
        session.set_model_state_budget(100_000);
        let outcome = session.check(&source);
        let [check] = outcome.model_checks.as_slice() else { panic!("{:?}", outcome.model_checks) };
        assert!(check.work.is_some_and(|work| work > KERNEL_WORK_LIMIT), "{:?}", check.work);
        assert!(
            matches!(&check.verdict, CleanIslandModelVerdict::Undecided { reason }
                if reason.contains("it has 80001 reachable states, within its state budget")
                    && reason.contains("the kernel is asked by default")
                    && reason.contains("stateBudget : Nat := 80001")),
            "{:?}",
            check.verdict
        );
        assert!(outcome.is_rejected(), "even a session budget does not permit Undecided");
        // Serving the modules dominates; a kernel attempt would add minutes here.
        assert!(started.elapsed() < std::time::Duration::from_secs(600));
    }

    /// The search hands the kernel its rows sorted by the checker's own
    /// `rowHash`, the order it indexes in one balanced pass; any other order
    /// is still checked, row by row and slower. So the Rust hash is the kernel's.
    #[test]
    fn the_rows_are_sorted_by_the_checkers_own_hash() {
        let mut session = checking_session();
        let outcome = session.check("import Trust.FiniteModelCheck\n");
        assert!(outcome.errors.is_empty(), "{:?}", outcome.errors);
        let env = session.env();
        let tc = TypeChecker::with_mode(env, env.mode());
        for row in [vec![], vec![0], vec![1, 2, 3], vec![4_294_967_291, 7, 1_000_003]] {
            let hashed = Expr::app(constant("rowHash"), nat_list(row.iter().copied()));
            assert_eq!(
                nat(&tc, &hashed),
                Some(super::super::model_trace::row_hash(&row)),
                "{row:?}"
            );
        }
    }

    #[test]
    fn the_reserved_theorem_name_keeps_every_component() {
        let name = Name::from_string("A").str("B.C").num(7).str("m");
        let reserved = reserved_theorem_name(&name);
        assert_eq!(reserved, Name::from_string(THEOREM_ROOT).str("A").str("B.C").num(7).str("m"));
        assert!(reserved.to_string().starts_with(super::super::SEEDED_MODEL_PREFIX));
        assert_ne!(reserved, reserved_theorem_name(&Name::from_string("A.B.C").num(7).str("m")));
    }

    /// A BINDING IS DATA, FOUND BY TYPE. An island that declares a constant of
    /// type `Trust.Protocol.Binding` gets it back, read out of the kernel term
    /// (helper definitions unfold on the way), with the span of its
    /// definition. It is no model: nothing is searched and no theorem is
    /// minted for it.
    #[test]
    fn a_declared_binding_is_read_out_with_its_span() {
        let source = "import Trust.Protocol\nnamespace HarnessPolicy\nopen Trust.Protocol\n\
                      def arm : String := \"HarnessPolicyObserved\"\n\
                      def policy : Trust.Protocol.Binding :=\n  \
                      binds \"config.harness\" [arm, \"Wake::Reset\"] [\"App::carry\"]\n\
                      end HarnessPolicy\n";
        let mut session = checking_session();
        let outcome = session.check(source);
        assert!(!outcome.is_rejected(), "{:?}", outcome.errors);
        assert!(outcome.model_checks.is_empty(), "{:?}", outcome.model_checks);
        let [binding] = outcome.bindings.as_slice() else { panic!("{:?}", outcome.bindings) };
        assert_eq!(binding.name, "HarnessPolicy.policy");
        assert_eq!(binding.path, "config.harness");
        assert_eq!(binding.arms, ["HarnessPolicyObserved", "Wake::Reset"]);
        assert_eq!(binding.carried_by, ["App::carry"]);
        assert_eq!(&source[binding.start..binding.end], "def policy : Trust.Protocol.Binding :=");
        assert!(!session.is_tainted());
    }

    /// A SEAL IS DATA TOO, FOUND BY TYPE: a constant of type
    /// `Trust.Protocol.Seal` comes back with its type and its four lists,
    /// beside any binding, from the module that defines both and nothing
    /// else.
    #[test]
    fn a_declared_seal_is_read_out_with_its_span() {
        let source = "import Trust.Binding\nnamespace HarnessPolicy\nopen Trust.Protocol\n\
                      def cell : Trust.Protocol.Seal :=\n  \
                      seals \"order::Generational\" [\"offer\"] [\"new\"] [\"App::new\"] []\n\
                      def policy : Trust.Protocol.Binding := binds \"n\" [\"Tick\"] []\n\
                      end HarnessPolicy\n";
        let mut session = CleanIslandSession::new();
        session.enable_binding_reads();
        let outcome = session.check(source);
        assert!(!outcome.is_rejected(), "{:?}", outcome.errors);
        let [seal] = outcome.seals.as_slice() else { panic!("{:?}", outcome.seals) };
        assert_eq!(seal.name, "HarnessPolicy.cell");
        assert_eq!(seal.type_name, "order::Generational");
        assert_eq!(seal.writers, ["offer"]);
        assert_eq!(seal.makers, ["new"]);
        assert_eq!(seal.made_by, ["App::new"]);
        assert!(seal.trusts.is_empty());
        assert_eq!(&source[seal.start..seal.end], "def cell : Trust.Protocol.Seal :=");
        assert_eq!(outcome.bindings.len(), 1, "{:?}", outcome.bindings);
        assert_eq!(session.served_trust_modules(), ["Trust.Binding"]);
        assert!(!session.is_tainted());
    }

    /// A seal the compiler cannot read is an error at the island, never a
    /// seal that looks checked: an empty type, and a list of seals.
    #[test]
    fn a_seal_that_cannot_be_read_rejects_the_island() {
        for source in [
            "import Trust.Binding\nopen Trust.Protocol\n\
             def cell : Trust.Protocol.Seal := seals \"\" [] [] [] []\n",
            "import Trust.Binding\nopen Trust.Protocol\n\
             def both : List Trust.Protocol.Seal := [seals \"A\" [] [] [] []]\n",
        ] {
            let mut session = CleanIslandSession::new();
            session.enable_binding_reads();
            let outcome = session.check(source);
            assert!(outcome.is_rejected(), "{source}");
            assert!(outcome.seals.is_empty(), "{:?}", outcome.seals);
            assert!(
                outcome.errors.iter().any(|error| error.message.contains("cannot be read")),
                "{:?}",
                outcome.errors
            );
        }
    }

    /// OFF BY DEFAULT, like the model check: a session that does not report
    /// island results hands back no binding, so only one session's bindings
    /// are ever checked against the code.
    #[test]
    fn a_session_that_did_not_opt_in_reads_no_binding() {
        let source = "import Trust.Protocol\nopen Trust.Protocol\n\
                      def policy : Trust.Protocol.Binding := binds \"n\" [\"Tick\"] []\n";
        let mut session = CleanIslandSession::new();
        let outcome = session.check(source);
        assert!(!outcome.is_rejected(), "{:?}", outcome.errors);
        assert!(outcome.bindings.is_empty());
    }

    /// A session that only READS bindings (the resolver's, which needs them
    /// before analysis) gets them and checks no model: the unsafe model beside
    /// the binding is neither searched nor rejected here.
    #[test]
    fn a_session_that_reads_bindings_checks_no_model() {
        let source = format!(
            "{}\nimport Trust.Protocol\ndef policy : Trust.Protocol.Binding :=\n  \
             Trust.Protocol.binds \"n\" [\"Tick\"] []\n",
            buggy()
        );
        let mut session = CleanIslandSession::new();
        session.enable_binding_reads();
        let outcome = session.check(&source);
        assert!(!outcome.is_rejected(), "{:?}", outcome.errors);
        assert!(outcome.model_checks.is_empty(), "{:?}", outcome.model_checks);
        let [binding] = outcome.bindings.as_slice() else { panic!("{:?}", outcome.bindings) };
        assert_eq!((binding.name.as_str(), binding.path.as_str()), ("policy", "n"));
        assert_eq!(binding.arms, ["Tick"]);
    }

    /// FAIL CLOSED: a binding the kernel cannot read (an empty path) rejects
    /// the island at its definition. A binding that is not checked must never
    /// look like one that holds. (An `opaque` binding never gets this far: a
    /// strict island refuses a valueless opaque.)
    #[test]
    fn a_binding_that_cannot_be_read_rejects_the_island() {
        let source = "import Trust.Protocol\nopen Trust.Protocol\n\
                      def policy : Trust.Protocol.Binding := binds \"\" [\"Tick\"] []\n";
        let mut session = checking_session();
        let outcome = session.check(source);
        assert!(outcome.bindings.is_empty(), "{:?}", outcome.bindings);
        let [error] = outcome.errors.as_slice() else { panic!("{:?}", outcome.errors) };
        assert!(error.message.contains("cannot be read"), "{}", error.message);
        assert!(error.message.contains("its path is empty"), "{}", error.message);
        assert!(source[error.start..error.end].starts_with("def policy"), "{error:?}");
    }

    /// A binding needs only `Trust.Binding`, which imports nothing: an island
    /// that declares one serves no model library, in a session that reads
    /// bindings and in one that also checks models.
    #[test]
    fn a_binding_needs_only_its_own_module() {
        let source = "import Trust.Binding\nopen Trust.Protocol\n\
                      def policy : Trust.Protocol.Binding := binds \"level\" [\"Tick\"] []\n";
        for checks_models in [false, true] {
            let mut session = CleanIslandSession::new();
            session.enable_binding_reads();
            if checks_models {
                session.enable_model_checks();
            }
            let outcome = session.check(source);
            assert!(!outcome.is_rejected(), "{:?}", outcome.errors);
            let [binding] = outcome.bindings.as_slice() else { panic!("{:?}", outcome.bindings) };
            assert_eq!(
                (binding.path.as_str(), binding.arms.as_slice()),
                ("level", &["Tick".to_owned()][..])
            );
            assert_eq!(session.served_trust_modules(), ["Trust.Binding"]);
        }
    }

    /// FAIL CLOSED: binding data that is not itself a constant of type
    /// `Binding` (a list of them) is not read, and must not sit in an island
    /// unchecked and unremarked.
    #[test]
    fn binding_data_that_is_not_a_binding_rejects_the_island() {
        let source = "import Trust.Binding\nopen Trust.Protocol\n\
                      def both : List Trust.Protocol.Binding :=\n  \
                      [binds \"a\" [\"Tick\"] [], binds \"b\" [\"Tick\"] []]\n";
        let mut session = CleanIslandSession::new();
        session.enable_binding_reads();
        let outcome = session.check(source);
        assert!(outcome.bindings.is_empty(), "{:?}", outcome.bindings);
        let [error] = outcome.errors.as_slice() else { panic!("{:?}", outcome.errors) };
        assert!(error.message.contains("holds a `Binding` and is not one"), "{}", error.message);
    }
}
