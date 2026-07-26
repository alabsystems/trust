// trust-types/formula/pred_vocab: closed vocabulary of safety predicates
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0
//
//! Closed, reviewed vocabulary for `Formula::Pred` (SAFE_API.md §3.2).
//!
//! `Formula::Pred` names are restricted to this table so the uninterpreted-
//! predicate surface cannot sprawl: each entry maps a per-category safety
//! predicate to the sorts of its arguments. A `Pred` whose `(name, arity)` is
//! not present here is rejected (at spec-parse time and by [`is_valid_pred`]).
//!
//! This closure is what keeps an opaque `Pred` sound: a predicate has no axioms
//! and no definition, so it can only become true at a use site via an in-scope
//! hypothesis — and the only sanctioned source of such a hypothesis is a proved
//! constructor's definitional binding (see SAFE_API.md §1.3). A spec author
//! cannot invent a predicate, and the solver cannot discharge one for free.

use super::Sort;

/// One reviewed predicate: its SMT symbol name and the sorts of its arguments.
/// The result sort of a `Pred` application is always `Bool`.
pub const PRED_VOCAB: &[(&str, &[Sort])] = &[
    // --- RawPathApi capability (M-SAFE-1) ---
    // DirHandle ghost identity (the open directory fd).
    ("dir_open", &[Sort::Int]),
    // Component: the path component count is exactly one (no separators/`..`).
    ("single_component", &[Sort::Int]),
    // --- Reserved for the expansion path (SAFE_API.md §7); one per category ---
    ("path_validated", &[Sort::Int]),
    ("byte_exact", &[Sort::Int]), // Utf8Reject / ByteLoss
    ("error_propagated", &[Sort::Int]), // ErrorDiscard
    ("perms_creation_safe", &[Sort::Int]), // PermissionCreate / PermissionWindow
    ("priv_dropped", &[]), // TrustDomain
    ("domain_entered_before_lookup", &[]), // TrustDomainOrder
];

/// Closed vocabulary of CHECKER-CORE structural / inductive spec predicates over
/// the kernel-expression carrier (Gap-A: recursive-spec predicates a
/// `#[ensures]` can state about a literal clean-kernel function's result).
///
/// These are a DISTINCT category from the safety-capability [`PRED_VOCAB`]: they
/// name a recursive/inductive property of a kernel `Expr` (e.g. `is_whnf` —
/// weak-head-normal-form). The carrier argument is modeled as an OPAQUE `Sort::Int`
/// GHOST HANDLE identifying the `Expr` value, exactly as the capability predicates
/// (`dir_open(Int)`) model a directory by its opaque fd identity. The Int handle
/// is never interpreted arithmetically.
///
/// SOUNDNESS (fail-closed, same envelope as [`PRED_VOCAB`], SAFE_API.md §3): a
/// checker-core `Pred` is UNINTERPRETED — it has no SMT axioms and no definition,
/// so a first-order solver can NEVER prove it. A postcondition `is_whnf(result)`
/// therefore lowers to a negated-postcondition VC that stays satisfiable under
/// SMT and is reported NOT-PROVED (never a false PROVE). Its recursive SEMANTICS
/// is realized ONLY by a kernel-checked discharge against the clean-verify KExpr
/// definition it is bound to (see [`checker_core_semantics`]); until that lane
/// runs, the obligation is honestly not-discharged, not silently satisfied.
pub const CHECKER_CORE_PRED_VOCAB: &[(&str, &[Sort])] = &[
    // is_whnf(e): the kernel expression `e` is in weak-head normal form. Bound to
    // clean-verify's inductive `is_whnf : KExpr -> Prop` (ctors is_whnf.sort /
    // is_whnf.lam / is_whnf.pi), which has the DerivedProved lemma `value_is_whnf`.
    ("is_whnf", &[Sort::Int]),
];

/// The declared argument sorts for predicate `name`, drawn from the UNION of the
/// safety-capability vocabulary [`PRED_VOCAB`] and the checker-core vocabulary
/// [`CHECKER_CORE_PRED_VOCAB`]. `None` for any out-of-vocabulary name (both the
/// spec parser's `Pred` routing gate and the router's `declare-fun` lowering rely
/// on this returning the true arg sorts for every legal `Formula::Pred`).
#[must_use]
pub fn pred_arg_sorts(name: &str) -> Option<&'static [Sort]> {
    PRED_VOCAB
        .iter()
        .chain(CHECKER_CORE_PRED_VOCAB.iter())
        .find(|(n, _)| *n == name)
        .map(|(_, sorts)| *sorts)
}

/// True iff `name` is a reviewed predicate (safety or checker-core) whose declared
/// arity matches `arity`. Used to reject out-of-vocabulary or mis-arity `Pred`
/// terms at construction.
#[must_use]
pub fn is_valid_pred(name: &str, arity: usize) -> bool {
    pred_arg_sorts(name).is_some_and(|sorts| sorts.len() == arity)
}

/// True iff `name` is a CHECKER-CORE structural/inductive predicate (as opposed to
/// a safety-capability predicate). Distinguishes the two `Pred` categories that
/// share the opaque, fail-closed lowering but differ in their sanctioned discharge
/// path (a kernel-checked KExpr proof term, not an in-scope capability hypothesis).
#[must_use]
pub fn is_checker_core_pred(name: &str) -> bool {
    CHECKER_CORE_PRED_VOCAB.iter().any(|(n, _)| *n == name)
}

/// The recursive SEMANTICS binding of a checker-core predicate: the clean-verify
/// KExpr definition it denotes, plus a `DerivedProved` backing lemma that
/// witnesses the definition is inhabited in the kernel. This is the CODE artifact
/// that gives a checker-core `Pred` its meaning (a discharge lane binds the opaque
/// predicate to this definition and kernel-checks the term); a predicate with no
/// registry entry has NO sanctioned discharge and stays not-proved (fail-closed).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CheckerCoreSemantics {
    /// The predicate's spec name (`is_whnf`).
    pub pred: &'static str,
    /// The clean-verify KExpr inductive/definitional name this predicate denotes.
    pub clean_verify_def: &'static str,
    /// A clean-verify `DerivedProved` lemma over that definition (the discharge
    /// lane's proof-term source / soundness anchor).
    pub backing_lemma: &'static str,
    /// Human-readable meaning of the predicate over the KExpr carrier.
    pub meaning: &'static str,
}

/// The sound semantics of every checker-core predicate. Fail-closed: a predicate
/// absent here cannot be discharged (no proof-term binding), so it stays
/// not-proved. Keep in lock-step with [`CHECKER_CORE_PRED_VOCAB`].
pub const CHECKER_CORE_SEMANTICS: &[CheckerCoreSemantics] = &[CheckerCoreSemantics {
    pred: "is_whnf",
    clean_verify_def: "is_whnf",
    backing_lemma: "value_is_whnf",
    meaning: "the kernel expression is in weak-head normal form (clean-verify \
              inductive `is_whnf : KExpr -> Prop`; ctors is_whnf.sort/lam/pi)",
}];

/// The recursive semantics binding for checker-core predicate `name`, or `None`
/// (fail-closed) if `name` is not a registered checker-core predicate.
#[must_use]
pub fn checker_core_semantics(name: &str) -> Option<CheckerCoreSemantics> {
    CHECKER_CORE_SEMANTICS.iter().find(|s| s.pred == name).copied()
}
