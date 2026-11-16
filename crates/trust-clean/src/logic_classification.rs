// trust-clean/logic_classification.rs: SMT logic classification for certification scoping
//
// Classifies formulas into SMT-LIB logic fragments to determine whether
// the clean certification pipeline can certify them. Currently, only
// QF_LIA (quantifier-free linear integer arithmetic) and QF_UF
// (quantifier-free uninterpreted functions) are certifiable. Other logics
// degrade gracefully to uncertified or partial certification.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::logic_lattice::Theories;
use trust_types::{Formula, Sort};

// ---------------------------------------------------------------------------
// SMT logic classification
// ---------------------------------------------------------------------------

/// SMT-LIB logic fragment that a formula belongs to.
///
/// Used to determine whether the clean Alethe proof replay pipeline can
/// certify a given proof. The classification is conservative: if any
/// subformula uses a feature outside a simpler logic, the formula is
/// classified into the more expressive logic.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum SmtLogic {
    /// Quantifier-free linear integer arithmetic.
    /// Variables are Int-sorted, operations are +, -, comparisons, and
    /// multiplication by constants only.
    QfLia,
    /// Quantifier-free uninterpreted functions (equality + Boolean).
    /// Pure equality reasoning over uninterpreted sorts.
    QfUf,
    /// Quantifier-free linear integer arithmetic combined with uninterpreted
    /// functions / equality logic. Formulas that use both integer arithmetic
    /// (Add, Sub, comparisons over Int-sorted variables) and Boolean equality
    /// reasoning over uninterpreted sorts.
    QfLiaUf,
    /// Quantifier-free linear integer/real arithmetic.
    /// Like QF_LIA but also includes real-sorted variables.
    QfLira,
    /// Quantifier-free bitvector arithmetic.
    QfBv,
    /// Quantifier-free arrays + uninterpreted functions + linear integer arithmetic.
    QfAuflia,
    /// Full first-order logic (quantifiers present).
    Full,
    /// Cannot classify — formula uses features outside known fragments.
    Unknown,
}

impl SmtLogic {
    /// Human-readable name matching SMT-LIB convention.
    #[must_use]
    pub fn name(&self) -> &'static str {
        match self {
            SmtLogic::QfLia => "QF_LIA",
            SmtLogic::QfUf => "QF_UF",
            SmtLogic::QfLiaUf => "QF_LIA+UF",
            SmtLogic::QfLira => "QF_LIRA",
            SmtLogic::QfBv => "QF_BV",
            SmtLogic::QfAuflia => "QF_AUFLIA",
            SmtLogic::Full => "ALL",
            SmtLogic::Unknown => "UNKNOWN",
        }
    }
}

// ---------------------------------------------------------------------------
// Certification strategy
// ---------------------------------------------------------------------------

/// Strategy for certifying a proof based on the logic fragment.
///
/// The clean Alethe proof replay pipeline currently supports QF_LIA and
/// QF_UF. For other logics, we degrade gracefully rather than failing.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum CertificationStrategy {
    /// Full clean kernel certification is available.
    FullCertification,
    /// Partial certification: some proof steps can be certified, but the
    /// formula uses features outside the certifiable fragment.
    PartialCertification {
        /// Why full certification is not possible.
        uncertified_reason: String,
    },
    /// No certification possible for this logic fragment.
    NoCertification {
        /// Why certification is not available.
        reason: String,
    },
}

impl CertificationStrategy {
    /// Returns `true` if full certification is available.
    #[must_use]
    pub fn is_full(&self) -> bool {
        matches!(self, CertificationStrategy::FullCertification)
    }

    /// Returns `true` if no certification is available at all.
    #[must_use]
    pub fn is_none(&self) -> bool {
        matches!(self, CertificationStrategy::NoCertification { .. })
    }
}

// ---------------------------------------------------------------------------
// Certification scope — outcome of theory-aware certification
// ---------------------------------------------------------------------------

/// Outcome of an Alethe-to-clean certification attempt, scoped
/// by the formula's SMT logic.
///
/// For supported theories (QF_LIA, QF_UF, QF_LIA+UF), full Alethe-to-clean
/// certificates are produced. For other theories, the pipeline degrades
/// gracefully by producing an `Uncertified` marker with a reason instead of
/// failing the build.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum CertificationScope {
    /// Full Alethe-to-clean certification was produced.
    /// The proof obligation is within QF_LIA, QF_UF, or QF_LIA+UF.
    FullyCertified,
    /// Partial certification: some proof steps are certified, but the formula
    /// extends beyond the fully certifiable fragment.
    PartiallyCertified {
        /// The logic fragment of the formula.
        logic: SmtLogic,
        /// What parts could not be certified and why.
        reason: String,
    },
    /// No certification was possible. The proof obligation remains
    /// SmtBacked (trusted via `axiom ay_trusted` in clean) rather than
    /// fully reconstructed.
    Uncertified {
        /// Why certification was not possible.
        reason: String,
    },
}

impl CertificationScope {
    /// Returns `true` if full Alethe-to-clean certification was produced.
    #[must_use]
    pub fn is_fully_certified(&self) -> bool {
        matches!(self, CertificationScope::FullyCertified)
    }

    /// Returns `true` if partial certification was produced.
    #[must_use]
    pub fn is_partially_certified(&self) -> bool {
        matches!(self, CertificationScope::PartiallyCertified { .. })
    }

    /// Returns `true` if no certification was possible.
    #[must_use]
    pub fn is_uncertified(&self) -> bool {
        matches!(self, CertificationScope::Uncertified { .. })
    }

    /// Human-readable summary of the scope.
    #[must_use]
    pub fn summary(&self) -> String {
        match self {
            CertificationScope::FullyCertified => {
                "fully certified via Alethe-to-clean pipeline".to_string()
            }
            CertificationScope::PartiallyCertified { logic, reason } => {
                format!("partially certified (logic: {}): {}", logic.name(), reason)
            }
            CertificationScope::Uncertified { reason } => {
                format!("uncertified: {reason}")
            }
        }
    }
}

// ---------------------------------------------------------------------------
// TheoryClassifier — inspects Formula nodes to determine theory
// ---------------------------------------------------------------------------

/// Classifies proof obligations by SMT theory and determines
/// the certification scope.
///
/// `TheoryClassifier` wraps the formula classification logic and maps it
/// to a `CertificationScope` that tells callers whether full, partial,
/// or no Alethe-to-clean certification is available.
///
/// # Usage
///
/// ```text
/// let classifier = TheoryClassifier::new();
/// let scope = classifier.classify(&vc.formula);
/// match scope {
///     CertificationScope::FullyCertified => { /* produce clean cert */ }
///     CertificationScope::PartiallyCertified { .. } => { /* partial cert */ }
///     CertificationScope::Uncertified { reason } => { /* SmtBacked fallback */ }
/// }
/// ```
pub struct TheoryClassifier {
    _priv: (),
}

impl TheoryClassifier {
    /// Create a new theory classifier.
    #[must_use]
    pub fn new() -> Self {
        TheoryClassifier { _priv: () }
    }

    /// Classify a formula's SMT logic and return the resulting theory.
    #[must_use]
    pub fn classify_logic(&self, formula: &Formula) -> SmtLogic {
        classify_formula(formula)
    }

    /// Determine the certification scope for a formula.
    ///
    /// This is the main entry point: it classifies the formula, then maps
    /// the logic to a `CertificationScope` using the degradation strategy.
    #[must_use]
    pub fn classify(&self, formula: &Formula) -> CertificationScope {
        let logic = classify_formula(formula);
        scope_from_logic(&logic)
    }

    /// Classify a formula and return both the logic and the scope.
    #[must_use]
    pub fn classify_with_logic(&self, formula: &Formula) -> (SmtLogic, CertificationScope) {
        let logic = classify_formula(formula);
        let scope = scope_from_logic(&logic);
        (logic, scope)
    }
}

impl Default for TheoryClassifier {
    fn default() -> Self {
        Self::new()
    }
}

/// Map an `SmtLogic` to a `CertificationScope`.
///
/// - Fully certifiable logics (QF_LIA, QF_UF, QF_LIA+UF) -> `FullyCertified`
/// - Partially certifiable logics (QF_LIRA, QF_BV, QF_AUFLIA) -> `PartiallyCertified`
/// - Non-certifiable logics (Full, Unknown) -> `Uncertified`
#[must_use]
pub fn scope_from_logic(logic: &SmtLogic) -> CertificationScope {
    let strategy = degradation_strategy(logic);
    match strategy {
        CertificationStrategy::FullCertification => CertificationScope::FullyCertified,
        CertificationStrategy::PartialCertification { uncertified_reason } => {
            CertificationScope::PartiallyCertified {
                logic: logic.clone(),
                reason: uncertified_reason,
            }
        }
        CertificationStrategy::NoCertification { reason } => {
            CertificationScope::Uncertified { reason }
        }
    }
}

// ---------------------------------------------------------------------------
// Public API
// ---------------------------------------------------------------------------

/// Classify a formula into its SMT logic fragment.
///
/// # ONE FEATURE RECORD, SHARED WITH EVERY OTHER SMT LANE
///
/// The theory dimensions come from
/// [`trust_types::logic_lattice::formula_theories`] — the same record the
/// `(set-logic …)` selectors in `trust_types::smt_logic` and trust-router's
/// `smt2_export` read, walked over the same sort-position inventory the
/// declaration emitters use. This function used to own a THIRD private
/// `FormulaFeatures` struct and a THIRD early-return cascade, and it carried the
/// defect that shape produces, in its most dangerous form:
///
/// * `collect_features` ended in `_ => {}`, so EVERY floating-point node, every
///   `Rat` (real) literal, every datatype `Ctor`/`Sel`/`IsCtor`, every
///   `Pred`/`FnApp` application and every interned `SymVar` contributed NOTHING.
/// * The cascade's fall-through was `QF_UF` — a CERTIFIABLE fragment.
///
/// So a floating-point obligation, a real-arithmetic obligation and a datatype
/// obligation all classified as `QF_UF` and were handed
/// `CertificationStrategy::FullCertification`: the pipeline claimed full clean
/// kernel certification for three theories the Alethe replay engine does not
/// reconstruct at all. (Compare the M1 defect in the logic-line selectors,
/// which was the same blindness pointing the other way — a logic line too
/// NARROW for the transcript. Here the blindness pointed at the trust root.)
///
/// The record below is total over `Formula`, so the fall-through is gone.
/// Anything the certifiable fragment does not cover now reaches
/// [`SmtLogic::Unknown`] or a partial-certification fragment, never `QF_UF` by
/// omission.
///
/// # LINEARITY now comes from the shared record too
///
/// This crate used to detect nonlinearity itself, because the shared record had
/// no linearity dimension — a gap `trust_types::logic_lattice` pinned as a
/// failing-by-documentation test. That dimension now exists
/// (`Theories::NONLINEAR`, set by the same `node_theories` every SMT lane
/// reads), so the private detector is gone and this cascade reads the shared
/// bit.
///
/// THE SWITCH IS STRICTLY MORE CONSERVATIVE HERE, which is the only direction
/// a certification SCOPE may move on its own. The private detector asked
/// "does each operand CONTAIN a variable", which UNDER-approximates:
/// `Mul(x, FnApp(f, [Int(1)]))` is `(* x (f 1))` — genuinely nonlinear, with no
/// `Var` in the second operand — and was classified as certifiable. The shared
/// bit asks "is each operand a numeric LITERAL", which over-approximates, and
/// every formula the old rule called nonlinear the new one does too (a term
/// containing a variable is not a literal). So the set of obligations reaching
/// `SmtLogic::Unknown` can only GROW: fewer full-certification claims, never
/// more.
///
/// # The one dimension this crate still keeps of its own
///
/// * **BOOLEAN VARIABLES.** A free `Bool` variable needs no theory — every
///   SMT-LIB logic admits it, so the shared record deliberately ignores it —
///   but propositional structure is what distinguishes this crate's
///   `QF_LIA+UF` scope from plain `QF_LIA`. Unlike the old walker, `SymVar` is
///   counted too.
#[must_use]
pub fn classify_formula(formula: &Formula) -> SmtLogic {
    let theories = trust_types::logic_lattice::formula_theories(formula);
    let extras = CleanExtras::of(formula);

    // Theories the clean Alethe replay engine has no reconstruction for AND
    // that no `SmtLogic` variant names. `Unknown` degrades to
    // `NoCertification`, which is the only honest answer: the previous code
    // reached `QF_UF` here and claimed FULL certification.
    if theories.contains(Theories::FLOATS) || theories.contains(Theories::DATATYPES) {
        return SmtLogic::Unknown;
    }

    // Quantifiers → full first-order logic. Checked first because no
    // quantifier-free fragment name is truthful once a binder is present.
    if theories.contains(Theories::QUANTIFIERS) {
        return SmtLogic::Full;
    }

    // Bitvectors → QF_BV (even combined with other features: the name is used
    // here to select a DEGRADATION STRATEGY, and the bit-blast one is the
    // binding constraint whatever else is present).
    if theories.contains(Theories::BITVECTORS) {
        return SmtLogic::QfBv;
    }

    // An array sort outside `(Array Int Int)` / `(Array (_ BitVec i) (_ BitVec
    // j))` (`Theories::WIDE_ARRAY`) is not QF_AUFLIA — that declaration admits
    // only `(Array Int Int)` — and this enum has no scope for the wider logics.
    if theories.contains(Theories::WIDE_ARRAY) {
        return SmtLogic::Unknown;
    }

    // Arrays → QF_AUFLIA.
    if theories.contains(Theories::ARRAYS) {
        return SmtLogic::QfAuflia;
    }

    // Non-linear arithmetic → Unknown: the replay engine certifies linear
    // steps. The SMT-LIB name for such a query is now a real one (`QF_NIA` and
    // its family — see `trust_types::logic_lattice`), but that is a LOGIC LINE;
    // this enum picks a CERTIFICATION SCOPE, and nothing here reconstructs a
    // nonlinear step, so `Unknown` stays the honest answer.
    //
    // Read from the SHARED record rather than from a private walker. The
    // cascade position is unchanged (after the BV and ARRAYS short-circuits),
    // so the only formulas whose verdict moves are the ones the old
    // under-approximating rule missed, and they move TOWARD `Unknown`.
    //
    // DIVISION AND REMAINDER BY A LITERAL ARE IN THIS ARM TOO, since the shared
    // bit was re-read off `QF_LIA`'s [S1] declaration: `div`/`mod` are excluded
    // from the linear name by NAME, numeral divisor or not, so `x div 2` heads
    // `QF_NIA` and reaches `Unknown` here. That is a NARROWING of this crate's
    // certification scope (it used to answer `QfLia`, i.e. full certification,
    // for that shape), and it is deliberately NOT undone by a private check.
    // MEASURED 2026-09-23 by the live harness `live_ay_replay_tests` (the pinned
    // ay solving under `:produce-proofs`, its Alethe replayed through this
    // crate's own path): for `x div 2` the pinned ay exports NO proof at all
    // (its strict self-check rejects its own proof and it answers Unknown), and
    // for `x mod 2` the strict-verified proof carries the mod lemma as an Alethe
    // `hole` and this crate's replay does not certify it. The plain QF_LIA
    // control does not certify through that replay either (the clean kernel
    // rejects the reconstructed term), so nothing here supports widening the
    // scope. If that harness ever shows a by-numeral div/mod proof certifying,
    // the decision to give that shape `QfLia` SCOPE belongs here, by a private
    // predicate — the logic LINE must still say `QF_NIA`.
    if theories.contains(Theories::NONLINEAR) {
        return SmtLogic::Unknown;
    }

    // Real arithmetic → QF_LIRA (with or without integers beside it). The old
    // cascade could not reach this variant at all: `Rat` literals and
    // `Real`-sorted variables were invisible to it, so a real obligation fell
    // through to `QF_UF` and was declared fully certifiable.
    if theories.contains(Theories::REALS) {
        return SmtLogic::QfLira;
    }

    let has_lia = theories.contains(Theories::INTS);
    // `Theories::UF` is an APPLIED uninterpreted symbol of arity >= 1, the same
    // rule the transcript lane charges the UF dimension by; a `Bool` variable
    // is the propositional half of the same scope for this crate.
    let has_uf = extras.bool_vars || theories.contains(Theories::UF);
    match (has_lia, has_uf) {
        (true, true) => SmtLogic::QfLiaUf,
        (true, false) => SmtLogic::QfLia,
        // Pure Boolean/equality, and the ground Boolean formula with no
        // variables at all, are both genuinely `QF_UF`.
        (false, _) => SmtLogic::QfUf,
    }
}

/// Returns `true` if the given logic can be fully certified by the clean
/// Alethe proof replay pipeline.
///
/// Currently QF_LIA, QF_UF, and QF_LIA+UF (the combination) are certifiable.
#[must_use]
pub fn is_certifiable(logic: &SmtLogic) -> bool {
    matches!(logic, SmtLogic::QfLia | SmtLogic::QfUf | SmtLogic::QfLiaUf)
}

/// Determine the certification strategy for a given logic fragment.
///
/// - QF_LIA and QF_UF: full certification via clean Alethe replay.
/// - QF_LIRA, QF_BV, QF_AUFLIA: partial — some steps certifiable,
///   but the fragment extends beyond what the replay engine handles.
/// - Full, Unknown: no certification available.
#[must_use]
pub fn degradation_strategy(logic: &SmtLogic) -> CertificationStrategy {
    match logic {
        SmtLogic::QfLia | SmtLogic::QfUf | SmtLogic::QfLiaUf => {
            CertificationStrategy::FullCertification
        }

        SmtLogic::QfLira => CertificationStrategy::PartialCertification {
            uncertified_reason: "QF_LIRA contains real arithmetic steps that the clean Alethe \
                 replay engine cannot yet certify; integer-only steps are certified"
                .to_string(),
        },

        SmtLogic::QfBv => CertificationStrategy::PartialCertification {
            uncertified_reason: "QF_BV bitvector reasoning is not yet supported by the clean \
                 Alethe proof replay; bit-blast steps remain uncertified"
                .to_string(),
        },

        SmtLogic::QfAuflia => CertificationStrategy::PartialCertification {
            uncertified_reason: "QF_AUFLIA array axiom steps (select/store) are not yet \
                 reconstructed in the clean Alethe replay engine"
                .to_string(),
        },

        SmtLogic::Full => CertificationStrategy::NoCertification {
            reason: "full first-order logic with quantifiers cannot be certified \
                 by the clean Alethe replay engine; quantifier instantiation \
                 steps are not yet supported"
                .to_string(),
        },

        SmtLogic::Unknown => CertificationStrategy::NoCertification {
            reason: "formula uses features outside any recognized SMT logic \
                 fragment; cannot determine a certification strategy"
                .to_string(),
        },
    }
}

// ---------------------------------------------------------------------------
// Feature collection (internal)
// ---------------------------------------------------------------------------

/// The ONE dimension [`classify_formula`] needs that the shared theory record
/// does not carry: the presence of Boolean VARIABLES.
///
/// Everything else — LINEARITY included, since `Theories::NONLINEAR` landed —
/// is read from `trust_types::logic_lattice::formula_theories`, so this crate
/// no longer maintains a parallel list of `Formula` arms that can fall out of
/// step with the declaration emitters or with the logic-line selectors.
#[derive(Debug, Default, Clone, Copy)]
struct CleanExtras {
    /// A free or bound `Bool`-sorted `Var`/`SymVar`.
    bool_vars: bool,
}

impl CleanExtras {
    /// Walk `formula` once.
    ///
    /// Uses `Formula::visit`, which reaches every node including quantifier
    /// BODIES, rather than a hand-written recursion with a `_ => {}` arm — the
    /// arm that made the old walker blind to floats, reals, datatypes,
    /// applications and interned variables.
    fn of(formula: &Formula) -> Self {
        Self {
            bool_vars: trust_types::any_formula_node(formula, &mut |node| {
                matches!(node, Formula::Var(_, Sort::Bool) | Formula::SymVar(_, Sort::Bool))
            }),
        }
    }
}

// ---------------------------------------------------------------------------
#[cfg(test)]
mod tests {
    use trust_types::Symbol;

    use super::*;

    // Helpers
    fn int_var(name: &str) -> Formula {
        Formula::Var(name.into(), Sort::Int)
    }

    fn bool_var(name: &str) -> Formula {
        Formula::Var(name.into(), Sort::Bool)
    }

    fn bv_var(name: &str, w: u32) -> Formula {
        Formula::Var(name.into(), Sort::BitVec(w))
    }

    fn arr_var(name: &str) -> Formula {
        Formula::Var(name.into(), Sort::Array(Box::new(Sort::Int), Box::new(Sort::Int)))
    }

    // -----------------------------------------------------------------------
    // SmtLogic::name
    // -----------------------------------------------------------------------

    #[test]
    fn test_smt_logic_names() {
        assert_eq!(SmtLogic::QfLia.name(), "QF_LIA");
        assert_eq!(SmtLogic::QfUf.name(), "QF_UF");
        assert_eq!(SmtLogic::QfLiaUf.name(), "QF_LIA+UF");
        assert_eq!(SmtLogic::QfLira.name(), "QF_LIRA");
        assert_eq!(SmtLogic::QfBv.name(), "QF_BV");
        assert_eq!(SmtLogic::QfAuflia.name(), "QF_AUFLIA");
        assert_eq!(SmtLogic::Full.name(), "ALL");
        assert_eq!(SmtLogic::Unknown.name(), "UNKNOWN");
    }

    // -----------------------------------------------------------------------
    // classify_formula: QF_UF
    // -----------------------------------------------------------------------

    #[test]
    fn test_classify_ground_bool_is_qf_uf() {
        let f = Formula::And(vec![Formula::Bool(true), Formula::Bool(false)]);
        assert_eq!(classify_formula(&f), SmtLogic::QfUf);
    }

    #[test]
    fn test_classify_bool_vars_is_qf_uf() {
        let f = Formula::Or(vec![bool_var("p"), Formula::Not(Box::new(bool_var("q")))]);
        assert_eq!(classify_formula(&f), SmtLogic::QfUf);
    }

    #[test]
    fn test_classify_pure_equality_is_qf_uf() {
        let f = Formula::Eq(Box::new(bool_var("a")), Box::new(bool_var("b")));
        assert_eq!(classify_formula(&f), SmtLogic::QfUf);
    }

    // -----------------------------------------------------------------------
    // classify_formula: QF_LIA
    // -----------------------------------------------------------------------

    #[test]
    fn test_classify_int_var_is_qf_lia() {
        let f = Formula::Eq(Box::new(int_var("x")), Box::new(Formula::Int(0)));
        assert_eq!(classify_formula(&f), SmtLogic::QfLia);
    }

    #[test]
    fn test_classify_linear_addition_is_qf_lia() {
        let f = Formula::Le(
            Box::new(Formula::Add(Box::new(int_var("x")), Box::new(int_var("y")))),
            Box::new(Formula::Int(100)),
        );
        assert_eq!(classify_formula(&f), SmtLogic::QfLia);
    }

    #[test]
    fn test_classify_int_literal_comparison_is_qf_lia() {
        let f = Formula::Lt(Box::new(Formula::Int(1)), Box::new(Formula::Int(2)));
        assert_eq!(classify_formula(&f), SmtLogic::QfLia);
    }

    #[test]
    fn test_classify_subtraction_is_qf_lia() {
        let f = Formula::Sub(Box::new(int_var("a")), Box::new(Formula::Int(1)));
        assert_eq!(classify_formula(&f), SmtLogic::QfLia);
    }

    #[test]
    fn test_classify_negation_is_qf_lia() {
        let f = Formula::Neg(Box::new(int_var("x")));
        assert_eq!(classify_formula(&f), SmtLogic::QfLia);
    }

    #[test]
    fn test_classify_mul_by_constant_is_qf_lia() {
        // Mul where one side is a constant (no variable) is linear
        let f = Formula::Mul(Box::new(Formula::Int(3)), Box::new(int_var("x")));
        assert_eq!(classify_formula(&f), SmtLogic::QfLia);
    }

    // -----------------------------------------------------------------------
    // classify_formula: QF_BV
    // -----------------------------------------------------------------------

    #[test]
    fn test_classify_bv_var_is_qf_bv() {
        let f = Formula::Eq(
            Box::new(bv_var("x", 32)),
            Box::new(Formula::BitVec { value: 0, width: 32 }),
        );
        assert_eq!(classify_formula(&f), SmtLogic::QfBv);
    }

    #[test]
    fn test_classify_bv_add_is_qf_bv() {
        let f = Formula::BvAdd(Box::new(bv_var("a", 8)), Box::new(bv_var("b", 8)), 8);
        assert_eq!(classify_formula(&f), SmtLogic::QfBv);
    }

    #[test]
    fn test_classify_bv_extract_is_qf_bv() {
        let f = Formula::BvExtract { inner: Box::new(bv_var("x", 32)), high: 15, low: 0 };
        assert_eq!(classify_formula(&f), SmtLogic::QfBv);
    }

    // -----------------------------------------------------------------------
    // classify_formula: QF_AUFLIA (arrays)
    // -----------------------------------------------------------------------

    #[test]
    fn test_classify_array_select_is_qf_auflia() {
        let f = Formula::Select(Box::new(arr_var("a")), Box::new(Formula::Int(0)));
        assert_eq!(classify_formula(&f), SmtLogic::QfAuflia);
    }

    #[test]
    fn test_classify_array_store_is_qf_auflia() {
        let f = Formula::Store(
            Box::new(arr_var("a")),
            Box::new(Formula::Int(0)),
            Box::new(Formula::Int(42)),
        );
        assert_eq!(classify_formula(&f), SmtLogic::QfAuflia);
    }

    #[test]
    fn test_classify_array_var_is_qf_auflia() {
        let f = Formula::Eq(Box::new(arr_var("a")), Box::new(arr_var("b")));
        assert_eq!(classify_formula(&f), SmtLogic::QfAuflia);
    }

    #[test]
    fn an_array_sort_qf_auflia_does_not_declare_is_no_certification_scope() {
        // QF_AUFLIA admits only `(Array Int Int)`; a `(Array Bool Bool)` or
        // `(Array Int Bool)` needs a wider logic this enum has no scope for.
        for (index, element) in [(Sort::Bool, Sort::Bool), (Sort::Int, Sort::Bool)] {
            let sort = Sort::Array(Box::new(index), Box::new(element));
            let a = Formula::Var("a".into(), sort.clone());
            let b = Formula::Var("b".into(), sort);
            let f = Formula::Eq(Box::new(a), Box::new(b));
            assert_eq!(classify_formula(&f), SmtLogic::Unknown, "{f:?}");
            assert!(!is_certifiable(&classify_formula(&f)));
        }
    }

    // -----------------------------------------------------------------------
    // classify_formula: Full (quantifiers)
    // -----------------------------------------------------------------------

    #[test]
    fn test_classify_forall_is_full() {
        let f = Formula::Forall(
            vec![("x".into(), Sort::Int)],
            Box::new(Formula::Ge(Box::new(int_var("x")), Box::new(Formula::Int(0)))),
        );
        assert_eq!(classify_formula(&f), SmtLogic::Full);
    }

    #[test]
    fn test_classify_exists_is_full() {
        let f = Formula::Exists(vec![("y".into(), Sort::Bool)], Box::new(bool_var("y")));
        assert_eq!(classify_formula(&f), SmtLogic::Full);
    }

    // -----------------------------------------------------------------------
    // classify_formula: Unknown (non-linear arithmetic)
    // -----------------------------------------------------------------------

    #[test]
    fn test_classify_nonlinear_mul_is_unknown() {
        // x * y where both are variables → non-linear
        let f = Formula::Mul(Box::new(int_var("x")), Box::new(int_var("y")));
        assert_eq!(classify_formula(&f), SmtLogic::Unknown);
    }

    #[test]
    fn test_classify_div_by_variable_is_unknown() {
        let f = Formula::Div(Box::new(int_var("x")), Box::new(int_var("y")));
        assert_eq!(classify_formula(&f), SmtLogic::Unknown);
    }

    #[test]
    fn test_classify_rem_by_variable_is_unknown() {
        let f = Formula::Rem(Box::new(int_var("x")), Box::new(int_var("y")));
        assert_eq!(classify_formula(&f), SmtLogic::Unknown);
    }

    // -----------------------------------------------------------------------
    // classify_formula: nested/mixed
    // -----------------------------------------------------------------------

    #[test]
    fn test_classify_nested_ite_with_ints_is_qf_lia() {
        let f = Formula::Ite(
            Box::new(Formula::Lt(Box::new(int_var("x")), Box::new(Formula::Int(0)))),
            Box::new(Formula::Neg(Box::new(int_var("x")))),
            Box::new(int_var("x")),
        );
        assert_eq!(classify_formula(&f), SmtLogic::QfLia);
    }

    #[test]
    fn test_classify_bv_in_ite_is_qf_bv() {
        // Even if the condition is pure bool, a BV in the branches makes it QF_BV
        let f = Formula::Ite(
            Box::new(Formula::Bool(true)),
            Box::new(bv_var("a", 32)),
            Box::new(bv_var("b", 32)),
        );
        assert_eq!(classify_formula(&f), SmtLogic::QfBv);
    }

    #[test]
    fn test_classify_div_by_constant_requires_a_broader_fragment() {
        // A constant divisor does not make the emitted `div` operator a term
        // of SMT-LIB's linear integer fragment: `QF_LIA`'s declaration excludes
        // `div`/`mod` by name. The shared record therefore carries NONLINEAR,
        // and this crate answers the scope it can honestly certify — none.
        for f in [
            Formula::Div(Box::new(int_var("x")), Box::new(Formula::Int(2))),
            Formula::Rem(Box::new(int_var("x")), Box::new(Formula::Int(2))),
        ] {
            let logic = classify_formula(&f);
            assert_eq!(logic, SmtLogic::Unknown, "{f:?}");
            assert!(!is_certifiable(&logic), "{f:?}");
            assert!(
                matches!(
                    degradation_strategy(&logic),
                    CertificationStrategy::NoCertification { .. }
                ),
                "{f:?}"
            );
        }
    }

    #[test]
    fn test_classify_implies_with_int_comparisons_is_qf_lia() {
        let f = Formula::Implies(
            Box::new(Formula::Ge(Box::new(int_var("n")), Box::new(Formula::Int(0)))),
            Box::new(Formula::Le(
                Box::new(Formula::Add(Box::new(int_var("n")), Box::new(Formula::Int(1)))),
                Box::new(Formula::Int(100)),
            )),
        );
        assert_eq!(classify_formula(&f), SmtLogic::QfLia);
    }

    #[test]
    fn test_classify_uint_literal_is_qf_lia() {
        let f = Formula::Eq(Box::new(Formula::UInt(42)), Box::new(int_var("x")));
        assert_eq!(classify_formula(&f), SmtLogic::QfLia);
    }

    // -----------------------------------------------------------------------
    // is_certifiable
    // -----------------------------------------------------------------------

    #[test]
    fn test_is_certifiable_qf_lia() {
        assert!(is_certifiable(&SmtLogic::QfLia));
    }

    #[test]
    fn test_is_certifiable_qf_uf() {
        assert!(is_certifiable(&SmtLogic::QfUf));
    }

    #[test]
    fn test_is_not_certifiable_qf_bv() {
        assert!(!is_certifiable(&SmtLogic::QfBv));
    }

    #[test]
    fn test_is_not_certifiable_qf_lira() {
        assert!(!is_certifiable(&SmtLogic::QfLira));
    }

    #[test]
    fn test_is_not_certifiable_qf_auflia() {
        assert!(!is_certifiable(&SmtLogic::QfAuflia));
    }

    #[test]
    fn test_is_not_certifiable_full() {
        assert!(!is_certifiable(&SmtLogic::Full));
    }

    #[test]
    fn test_is_not_certifiable_unknown() {
        assert!(!is_certifiable(&SmtLogic::Unknown));
    }

    // -----------------------------------------------------------------------
    // degradation_strategy
    // -----------------------------------------------------------------------

    #[test]
    fn test_strategy_qf_lia_is_full() {
        let s = degradation_strategy(&SmtLogic::QfLia);
        assert!(s.is_full());
        assert!(!s.is_none());
    }

    #[test]
    fn test_strategy_qf_uf_is_full() {
        let s = degradation_strategy(&SmtLogic::QfUf);
        assert!(s.is_full());
    }

    #[test]
    fn test_strategy_qf_lira_is_partial() {
        let s = degradation_strategy(&SmtLogic::QfLira);
        assert!(!s.is_full());
        assert!(!s.is_none());
        if let CertificationStrategy::PartialCertification { uncertified_reason } = &s {
            assert!(uncertified_reason.contains("real arithmetic"));
        } else {
            panic!("expected PartialCertification, got {s:?}");
        }
    }

    #[test]
    fn test_strategy_qf_bv_is_partial() {
        let s = degradation_strategy(&SmtLogic::QfBv);
        assert!(!s.is_full());
        assert!(!s.is_none());
        if let CertificationStrategy::PartialCertification { uncertified_reason } = &s {
            assert!(uncertified_reason.contains("bitvector"));
        } else {
            panic!("expected PartialCertification, got {s:?}");
        }
    }

    #[test]
    fn test_strategy_qf_auflia_is_partial() {
        let s = degradation_strategy(&SmtLogic::QfAuflia);
        if let CertificationStrategy::PartialCertification { uncertified_reason } = &s {
            assert!(uncertified_reason.contains("array"));
        } else {
            panic!("expected PartialCertification, got {s:?}");
        }
    }

    #[test]
    fn test_strategy_full_is_none() {
        let s = degradation_strategy(&SmtLogic::Full);
        assert!(s.is_none());
        if let CertificationStrategy::NoCertification { reason } = &s {
            assert!(reason.contains("quantifier"));
        } else {
            panic!("expected NoCertification, got {s:?}");
        }
    }

    #[test]
    fn test_strategy_unknown_is_none() {
        let s = degradation_strategy(&SmtLogic::Unknown);
        assert!(s.is_none());
        if let CertificationStrategy::NoCertification { reason } = &s {
            assert!(reason.contains("outside any recognized"));
        } else {
            panic!("expected NoCertification, got {s:?}");
        }
    }

    // -----------------------------------------------------------------------
    // End-to-end: classify then check certifiability
    // -----------------------------------------------------------------------

    #[test]
    fn test_e2e_division_by_zero_vc_is_certifiable() {
        // Typical division-by-zero VC: NOT(divisor = 0)
        let f = Formula::Not(Box::new(Formula::Eq(
            Box::new(int_var("divisor")),
            Box::new(Formula::Int(0)),
        )));
        let logic = classify_formula(&f);
        assert_eq!(logic, SmtLogic::QfLia);
        assert!(is_certifiable(&logic));
        assert!(degradation_strategy(&logic).is_full());
    }

    #[test]
    fn test_e2e_overflow_vc_with_bv_is_not_certifiable() {
        // Overflow check using bitvectors
        let f = Formula::BvULt(
            Box::new(Formula::BvAdd(Box::new(bv_var("a", 64)), Box::new(bv_var("b", 64)), 64)),
            Box::new(bv_var("a", 64)),
            64,
        );
        let logic = classify_formula(&f);
        assert_eq!(logic, SmtLogic::QfBv);
        assert!(!is_certifiable(&logic));
        assert!(!degradation_strategy(&logic).is_full());
        assert!(!degradation_strategy(&logic).is_none()); // partial, not none
    }

    #[test]
    fn test_e2e_quantified_property_not_certifiable() {
        let f = Formula::Forall(
            vec![("i".into(), Sort::Int)],
            Box::new(Formula::Implies(
                Box::new(Formula::Ge(Box::new(int_var("i")), Box::new(Formula::Int(0)))),
                Box::new(Formula::Lt(
                    Box::new(Formula::Select(Box::new(arr_var("arr")), Box::new(int_var("i")))),
                    Box::new(Formula::Int(100)),
                )),
            )),
        );
        let logic = classify_formula(&f);
        assert_eq!(logic, SmtLogic::Full);
        assert!(!is_certifiable(&logic));
        assert!(degradation_strategy(&logic).is_none());
    }

    // =======================================================================
    // QF_LIA+UF classification tests
    // =======================================================================

    // -----------------------------------------------------------------------
    // classify_formula: QF_LIA+UF (combined)
    // -----------------------------------------------------------------------

    #[test]
    fn test_classify_int_and_bool_vars_is_qf_lia_uf() {
        // Formula with both Int variable and Bool variable => QF_LIA+UF
        let f = Formula::And(vec![
            Formula::Lt(Box::new(int_var("x")), Box::new(Formula::Int(10))),
            bool_var("p"),
        ]);
        assert_eq!(classify_formula(&f), SmtLogic::QfLiaUf);
    }

    #[test]
    fn test_classify_int_arithmetic_and_equality_is_qf_lia_uf() {
        // a + b <= MAX AND p = q
        let f = Formula::And(vec![
            Formula::Le(
                Box::new(Formula::Add(Box::new(int_var("a")), Box::new(int_var("b")))),
                Box::new(Formula::Int(100)),
            ),
            Formula::Eq(Box::new(bool_var("p")), Box::new(bool_var("q"))),
        ]);
        assert_eq!(classify_formula(&f), SmtLogic::QfLiaUf);
    }

    #[test]
    fn test_classify_int_comparison_with_bool_implies_is_qf_lia_uf() {
        // p => x > 0
        let f = Formula::Implies(
            Box::new(bool_var("p")),
            Box::new(Formula::Gt(Box::new(int_var("x")), Box::new(Formula::Int(0)))),
        );
        assert_eq!(classify_formula(&f), SmtLogic::QfLiaUf);
    }

    #[test]
    fn test_classify_ite_int_bool_is_qf_lia_uf() {
        // if p then x else y (with Bool var and Int vars)
        let f = Formula::Ite(
            Box::new(bool_var("cond")),
            Box::new(int_var("x")),
            Box::new(int_var("y")),
        );
        assert_eq!(classify_formula(&f), SmtLogic::QfLiaUf);
    }

    // -----------------------------------------------------------------------
    // is_certifiable: QF_LIA+UF
    // -----------------------------------------------------------------------

    #[test]
    fn test_is_certifiable_qf_lia_uf() {
        assert!(is_certifiable(&SmtLogic::QfLiaUf));
    }

    // -----------------------------------------------------------------------
    // degradation_strategy: QF_LIA+UF
    // -----------------------------------------------------------------------

    #[test]
    fn test_strategy_qf_lia_uf_is_full() {
        let s = degradation_strategy(&SmtLogic::QfLiaUf);
        assert!(s.is_full());
        assert!(!s.is_none());
    }

    // =======================================================================
    // CertificationScope tests
    // =======================================================================

    // -----------------------------------------------------------------------
    // CertificationScope variant predicates
    // -----------------------------------------------------------------------

    #[test]
    fn test_scope_fully_certified_predicates() {
        let scope = CertificationScope::FullyCertified;
        assert!(scope.is_fully_certified());
        assert!(!scope.is_partially_certified());
        assert!(!scope.is_uncertified());
    }

    #[test]
    fn test_scope_partially_certified_predicates() {
        let scope = CertificationScope::PartiallyCertified {
            logic: SmtLogic::QfBv,
            reason: "bitvector not supported".to_string(),
        };
        assert!(!scope.is_fully_certified());
        assert!(scope.is_partially_certified());
        assert!(!scope.is_uncertified());
    }

    #[test]
    fn test_scope_uncertified_predicates() {
        let scope = CertificationScope::Uncertified { reason: "quantifiers present".to_string() };
        assert!(!scope.is_fully_certified());
        assert!(!scope.is_partially_certified());
        assert!(scope.is_uncertified());
    }

    // -----------------------------------------------------------------------
    // CertificationScope::summary
    // -----------------------------------------------------------------------

    #[test]
    fn test_scope_summary_fully_certified() {
        let scope = CertificationScope::FullyCertified;
        assert!(scope.summary().contains("fully certified"));
    }

    #[test]
    fn test_scope_summary_partially_certified() {
        let scope = CertificationScope::PartiallyCertified {
            logic: SmtLogic::QfBv,
            reason: "bitvector steps uncertified".to_string(),
        };
        let summary = scope.summary();
        assert!(summary.contains("partially certified"));
        assert!(summary.contains("QF_BV"));
        assert!(summary.contains("bitvector steps uncertified"));
    }

    #[test]
    fn test_scope_summary_uncertified() {
        let scope =
            CertificationScope::Uncertified { reason: "quantifiers not supported".to_string() };
        let summary = scope.summary();
        assert!(summary.contains("uncertified"));
        assert!(summary.contains("quantifiers not supported"));
    }

    // -----------------------------------------------------------------------
    // scope_from_logic
    // -----------------------------------------------------------------------

    #[test]
    fn test_scope_from_logic_qf_lia_is_fully_certified() {
        let scope = scope_from_logic(&SmtLogic::QfLia);
        assert!(scope.is_fully_certified());
    }

    #[test]
    fn test_scope_from_logic_qf_uf_is_fully_certified() {
        let scope = scope_from_logic(&SmtLogic::QfUf);
        assert!(scope.is_fully_certified());
    }

    #[test]
    fn test_scope_from_logic_qf_lia_uf_is_fully_certified() {
        let scope = scope_from_logic(&SmtLogic::QfLiaUf);
        assert!(scope.is_fully_certified());
    }

    #[test]
    fn test_scope_from_logic_qf_bv_is_partially_certified() {
        let scope = scope_from_logic(&SmtLogic::QfBv);
        assert!(scope.is_partially_certified());
        if let CertificationScope::PartiallyCertified { logic, reason } = &scope {
            assert_eq!(*logic, SmtLogic::QfBv);
            assert!(reason.contains("bitvector"));
        } else {
            panic!("expected PartiallyCertified, got {scope:?}");
        }
    }

    #[test]
    fn test_scope_from_logic_qf_lira_is_partially_certified() {
        let scope = scope_from_logic(&SmtLogic::QfLira);
        assert!(scope.is_partially_certified());
        if let CertificationScope::PartiallyCertified { logic, reason } = &scope {
            assert_eq!(*logic, SmtLogic::QfLira);
            assert!(reason.contains("real arithmetic"));
        } else {
            panic!("expected PartiallyCertified, got {scope:?}");
        }
    }

    #[test]
    fn test_scope_from_logic_qf_auflia_is_partially_certified() {
        let scope = scope_from_logic(&SmtLogic::QfAuflia);
        assert!(scope.is_partially_certified());
        if let CertificationScope::PartiallyCertified { logic, reason } = &scope {
            assert_eq!(*logic, SmtLogic::QfAuflia);
            assert!(reason.contains("array"));
        } else {
            panic!("expected PartiallyCertified, got {scope:?}");
        }
    }

    #[test]
    fn test_scope_from_logic_full_is_uncertified() {
        let scope = scope_from_logic(&SmtLogic::Full);
        assert!(scope.is_uncertified());
        if let CertificationScope::Uncertified { reason } = &scope {
            assert!(reason.contains("quantifier"));
        } else {
            panic!("expected Uncertified, got {scope:?}");
        }
    }

    #[test]
    fn test_scope_from_logic_unknown_is_uncertified() {
        let scope = scope_from_logic(&SmtLogic::Unknown);
        assert!(scope.is_uncertified());
        if let CertificationScope::Uncertified { reason } = &scope {
            assert!(reason.contains("outside any recognized"));
        } else {
            panic!("expected Uncertified, got {scope:?}");
        }
    }

    // =======================================================================
    // TheoryClassifier tests
    // =======================================================================

    #[test]
    fn test_theory_classifier_classify_logic_qf_lia() {
        let classifier = TheoryClassifier::new();
        let f = Formula::Add(Box::new(int_var("x")), Box::new(Formula::Int(1)));
        assert_eq!(classifier.classify_logic(&f), SmtLogic::QfLia);
    }

    #[test]
    fn test_theory_classifier_classify_logic_qf_uf() {
        let classifier = TheoryClassifier::new();
        let f = Formula::Eq(Box::new(bool_var("a")), Box::new(bool_var("b")));
        assert_eq!(classifier.classify_logic(&f), SmtLogic::QfUf);
    }

    #[test]
    fn test_theory_classifier_classify_logic_qf_lia_uf() {
        let classifier = TheoryClassifier::new();
        let f = Formula::And(vec![
            Formula::Lt(Box::new(int_var("x")), Box::new(Formula::Int(10))),
            bool_var("flag"),
        ]);
        assert_eq!(classifier.classify_logic(&f), SmtLogic::QfLiaUf);
    }

    #[test]
    fn test_theory_classifier_classify_returns_scope() {
        let classifier = TheoryClassifier::new();

        // QF_LIA -> FullyCertified
        let f_lia = Formula::Le(Box::new(int_var("x")), Box::new(Formula::Int(100)));
        assert!(classifier.classify(&f_lia).is_fully_certified());

        // QF_BV -> PartiallyCertified
        let f_bv = Formula::BvAdd(Box::new(bv_var("a", 32)), Box::new(bv_var("b", 32)), 32);
        assert!(classifier.classify(&f_bv).is_partially_certified());

        // Full -> Uncertified
        let f_full = Formula::Forall(vec![("x".into(), Sort::Int)], Box::new(int_var("x")));
        assert!(classifier.classify(&f_full).is_uncertified());
    }

    #[test]
    fn test_theory_classifier_classify_with_logic() {
        let classifier = TheoryClassifier::new();
        let f = Formula::And(vec![
            Formula::Gt(Box::new(int_var("n")), Box::new(Formula::Int(0))),
            bool_var("valid"),
        ]);
        let (logic, scope) = classifier.classify_with_logic(&f);
        assert_eq!(logic, SmtLogic::QfLiaUf);
        assert!(scope.is_fully_certified());
    }

    // -----------------------------------------------------------------------
    // E2E: QF_LIA+UF in realistic scenarios
    // -----------------------------------------------------------------------

    #[test]
    fn test_e2e_mixed_int_bool_guard_is_certifiable() {
        // Typical pattern: "n > 0 AND valid" — guard with both int and bool
        let f = Formula::And(vec![
            Formula::Gt(Box::new(int_var("n")), Box::new(Formula::Int(0))),
            bool_var("valid"),
        ]);
        let logic = classify_formula(&f);
        assert_eq!(logic, SmtLogic::QfLiaUf);
        assert!(is_certifiable(&logic));
        assert!(degradation_strategy(&logic).is_full());
        assert!(scope_from_logic(&logic).is_fully_certified());
    }

    #[test]
    fn test_e2e_nested_ite_with_int_and_bool_is_certifiable() {
        // if flag then x + 1 else y — combines Bool and Int
        let f = Formula::Ite(
            Box::new(bool_var("flag")),
            Box::new(Formula::Add(Box::new(int_var("x")), Box::new(Formula::Int(1)))),
            Box::new(int_var("y")),
        );
        let logic = classify_formula(&f);
        assert_eq!(logic, SmtLogic::QfLiaUf);
        assert!(is_certifiable(&logic));
    }

    // -----------------------------------------------------------------------
    // The blind-spot regressions: theories the old private walker could not
    // see, which therefore fell through its cascade to `QF_UF` — a CERTIFIABLE
    // fragment. Each of these must now reach a fragment that does NOT claim
    // full clean-kernel certification.
    // -----------------------------------------------------------------------

    /// A FLOATING-POINT obligation used to classify as `QF_UF` and be handed
    /// `FullCertification`: `collect_features` had no `Fp*` arm at all, and its
    /// `_ => {}` fall-through swallowed every one of them.
    #[test]
    fn floating_point_is_not_silently_certifiable() {
        let f =
            Formula::FpIsNaN(Box::new(Formula::Var("g".into(), Sort::Float { eb: 11, sb: 53 })));
        let logic = classify_formula(&f);
        assert_eq!(logic, SmtLogic::Unknown, "floating point has no certifiable fragment here");
        assert!(!is_certifiable(&logic));
        assert!(degradation_strategy(&logic).is_none());
    }

    /// A REAL-arithmetic obligation used to classify as `QF_UF` too: `Rat`
    /// literals and `Real`-sorted variables were invisible. It must reach
    /// `QF_LIRA`, whose strategy is PARTIAL certification — and which the old
    /// cascade could not return at all.
    #[test]
    fn real_arithmetic_reaches_qf_lira_not_qf_uf() {
        let f = Formula::Le(
            Box::new(Formula::Var("x".into(), Sort::Real)),
            Box::new(Formula::rat_from_int(1)),
        );
        let logic = classify_formula(&f);
        assert_eq!(logic, SmtLogic::QfLira);
        assert!(!is_certifiable(&logic));
        assert!(matches!(
            degradation_strategy(&logic),
            CertificationStrategy::PartialCertification { .. }
        ));
    }

    /// A DATATYPE obligation used to classify as `QF_UF` as well.
    #[test]
    fn datatypes_are_not_silently_certifiable() {
        let sort = Sort::Datatype { name: "Expr".to_string(), constructors: Vec::new() };
        let f = Formula::Eq(
            Box::new(Formula::Var("e".into(), sort.clone())),
            Box::new(Formula::Var("e2".into(), sort)),
        );
        let logic = classify_formula(&f);
        assert_eq!(logic, SmtLogic::Unknown);
        assert!(!is_certifiable(&logic));
    }

    /// An APPLIED uninterpreted function is a genuine UF requirement. The old
    /// walker never set `has_uninterpreted` — nothing assigned it — so a
    /// formula mixing integer arithmetic with an application classified as
    /// plain `QF_LIA`. Both remain certifiable, so this is a precision fix, not
    /// a soundness one, and it is pinned so the dimension cannot go quiet
    /// again.
    #[test]
    fn an_applied_uninterpreted_function_sets_the_uf_dimension() {
        let f = Formula::And(vec![
            Formula::Gt(Box::new(int_var("n")), Box::new(Formula::Int(0))),
            Formula::Pred("p".into(), vec![int_var("n")]),
        ]);
        assert_eq!(classify_formula(&f), SmtLogic::QfLiaUf);
    }

    /// An INTERNED (`SymVar`) variable was invisible to the old walker in every
    /// position. A `SymVar`-only product is nonlinear, and must classify as
    /// such rather than as the ground `QF_UF` the old cascade fell through to.
    #[test]
    fn interned_variables_are_visible_to_both_dimensions() {
        let x = Formula::SymVar(Symbol::intern("x"), Sort::Int);
        let y = Formula::SymVar(Symbol::intern("y"), Sort::Int);
        let nonlinear = Formula::Gt(
            Box::new(Formula::Mul(Box::new(x.clone()), Box::new(y))),
            Box::new(Formula::Int(0)),
        );
        assert_eq!(classify_formula(&nonlinear), SmtLogic::Unknown);

        let linear = Formula::Gt(Box::new(x), Box::new(Formula::Int(0)));
        assert_eq!(classify_formula(&linear), SmtLogic::QfLia);
    }

    /// The classifier and the workspace's `(set-logic …)` selector now read the
    /// SAME theory record, so they cannot disagree about which theories a
    /// formula uses. This checks the two agree on the M1 shape specifically:
    /// FP mixed with Int is neither `QF_FP` on the transcript side nor a
    /// certifiable fragment here.
    #[test]
    fn the_classifier_and_the_logic_selector_read_one_record() {
        let f = Formula::And(vec![
            Formula::Gt(Box::new(int_var("x")), Box::new(Formula::Int(0))),
            Formula::FpIsNaN(Box::new(Formula::Var("g".into(), Sort::Float { eb: 11, sb: 53 }))),
        ]);
        let theories = trust_types::logic_lattice::formula_theories(&f);
        assert!(theories.contains(Theories::FLOATS) && theories.contains(Theories::INTS));
        assert_eq!(trust_types::smt_logic::select_logic(&f), "ALL");
        assert_eq!(classify_formula(&f), SmtLogic::Unknown);
    }

    /// LINEARITY is read from the shared record now, and that closed an
    /// UNDER-approximation this crate used to carry.
    ///
    /// The old private detector asked whether each operand CONTAINS a variable.
    /// `(* x (f 1))` is a product of a variable and an uninterpreted
    /// application with a literal argument: genuinely nonlinear, but the second
    /// operand holds no `Var`, so it was called linear and handed a
    /// certification strategy. The shared bit asks whether each operand is a
    /// numeric LITERAL, which catches it.
    ///
    /// The two classifications must also AGREE, which is the point of reading
    /// one record: the logic line says `QF_UFNIA` and the scope says `Unknown`.
    #[test]
    fn a_product_with_an_application_operand_is_nonlinear_here_too() {
        let application =
            Formula::FnApp { func: "f".to_string(), args: vec![Formula::Int(1)], sort: Sort::Int };
        let f = Formula::Gt(
            Box::new(Formula::Mul(Box::new(int_var("x")), Box::new(application))),
            Box::new(Formula::Int(0)),
        );
        let theories = trust_types::logic_lattice::formula_theories(&f);
        assert!(theories.contains(Theories::NONLINEAR), "`(* x (f 1))` is nonlinear");
        assert_eq!(trust_types::smt_logic::select_logic(&f), "QF_UFNIA");
        assert_eq!(classify_formula(&f), SmtLogic::Unknown);
    }

    /// The other side of the split, so the switch to the shared bit cannot
    /// quietly send ordinary linear VCs to `Unknown`: multiplication of a free
    /// constant by a LITERAL stays certifiable. (Division and remainder by a
    /// literal do NOT — see `test_classify_div_by_constant_requires_a_broader_
    /// fragment` — because `QF_LIA`'s declaration excludes `div`/`mod` outright.)
    #[test]
    fn multiplication_by_a_literal_is_still_linear_here() {
        for f in [
            Formula::Mul(Box::new(Formula::Int(3)), Box::new(int_var("x"))),
            Formula::Mul(Box::new(int_var("x")), Box::new(Formula::Int(3))),
            Formula::Mul(Box::new(Formula::Int(-3)), Box::new(int_var("x"))),
        ] {
            let goal = Formula::Gt(Box::new(f), Box::new(Formula::Int(0)));
            assert!(
                !trust_types::logic_lattice::formula_theories(&goal).contains(Theories::NONLINEAR)
            );
            assert_eq!(classify_formula(&goal), SmtLogic::QfLia);
        }
    }
}
