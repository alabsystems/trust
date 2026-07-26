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
// Formula feature flags (internal)
// ---------------------------------------------------------------------------

/// Internal feature flags collected during formula traversal.
#[derive(Debug, Default)]
struct FormulaFeatures {
    has_quantifiers: bool,
    has_bitvectors: bool,
    has_arrays: bool,
    has_nonlinear_arith: bool,
    has_int_arithmetic: bool,
    has_int_vars: bool,
    has_bool_vars: bool,
    has_uninterpreted: bool,
}

// ---------------------------------------------------------------------------
// Public API
// ---------------------------------------------------------------------------

/// Classify a formula into its SMT logic fragment.
///
/// Traverses the formula tree, collecting feature flags, then maps the
/// combination of features to the most specific SMT logic.
#[must_use]
pub fn classify_formula(formula: &Formula) -> SmtLogic {
    let mut features = FormulaFeatures::default();
    collect_features(formula, &mut features);

    // Quantifiers → Full logic
    if features.has_quantifiers {
        return SmtLogic::Full;
    }

    // Bitvectors → QF_BV (even if combined with other features)
    if features.has_bitvectors {
        return SmtLogic::QfBv;
    }

    // Arrays → QF_AUFLIA
    if features.has_arrays {
        return SmtLogic::QfAuflia;
    }

    // Non-linear arithmetic → Unknown (no standard QF fragment covers it well)
    if features.has_nonlinear_arith {
        return SmtLogic::Unknown;
    }

    // Detect combined QF_LIA+UF — formulas that use both
    // integer arithmetic and Boolean/equality reasoning.
    let has_lia = features.has_int_arithmetic || features.has_int_vars;
    let has_uf = features.has_bool_vars || features.has_uninterpreted;
    if has_lia && has_uf {
        return SmtLogic::QfLiaUf;
    }

    // Integer arithmetic (linear) → QF_LIA
    if has_lia {
        return SmtLogic::QfLia;
    }

    // Pure Boolean/equality → QF_UF
    if has_uf {
        return SmtLogic::QfUf;
    }

    // Ground Boolean formula with no variables — trivially QF_UF
    SmtLogic::QfUf
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

/// Recursively collect feature flags from a formula.
fn collect_features(formula: &Formula, features: &mut FormulaFeatures) {
    match formula {
        // -- Leaves --
        Formula::Bool(_) => {}
        Formula::Int(_) | Formula::UInt(_) => {
            features.has_int_arithmetic = true;
        }
        Formula::BitVec { .. } => {
            features.has_bitvectors = true;
        }
        Formula::Var(_, sort) => match sort {
            Sort::Int => features.has_int_vars = true,
            Sort::Bool => features.has_bool_vars = true,
            Sort::BitVec(_) => features.has_bitvectors = true,
            Sort::Array(..) => features.has_arrays = true,
            _ => { /* unknown sort variant -- skip */ }
        },

        // -- Boolean connectives (recurse into children) --
        Formula::Not(a) => collect_features(a, features),
        Formula::And(terms) | Formula::Or(terms) => {
            for t in terms {
                collect_features(t, features);
            }
        }
        Formula::Implies(a, b) => {
            collect_features(a, features);
            collect_features(b, features);
        }

        // -- Comparisons --
        Formula::Eq(a, b)
        | Formula::Lt(a, b)
        | Formula::Le(a, b)
        | Formula::Gt(a, b)
        | Formula::Ge(a, b) => {
            collect_features(a, features);
            collect_features(b, features);
        }

        // -- Linear integer arithmetic --
        Formula::Add(a, b) | Formula::Sub(a, b) => {
            features.has_int_arithmetic = true;
            collect_features(a, features);
            collect_features(b, features);
        }
        Formula::Neg(a) => {
            features.has_int_arithmetic = true;
            collect_features(a, features);
        }

        // -- Potentially non-linear: Mul is non-linear if both operands
        //    contain variables. We conservatively flag it. --
        Formula::Mul(a, b) => {
            features.has_int_arithmetic = true;
            if has_variable(a) && has_variable(b) {
                features.has_nonlinear_arith = true;
            }
            collect_features(a, features);
            collect_features(b, features);
        }
        Formula::Div(a, b) | Formula::Rem(a, b) => {
            features.has_int_arithmetic = true;
            if has_variable(b) {
                features.has_nonlinear_arith = true;
            }
            collect_features(a, features);
            collect_features(b, features);
        }

        // -- Bitvector operations --
        Formula::BvAdd(a, b, _)
        | Formula::BvSub(a, b, _)
        | Formula::BvMul(a, b, _)
        | Formula::BvUDiv(a, b, _)
        | Formula::BvSDiv(a, b, _)
        | Formula::BvURem(a, b, _)
        | Formula::BvSRem(a, b, _)
        | Formula::BvAnd(a, b, _)
        | Formula::BvOr(a, b, _)
        | Formula::BvXor(a, b, _)
        | Formula::BvShl(a, b, _)
        | Formula::BvLShr(a, b, _)
        | Formula::BvAShr(a, b, _)
        | Formula::BvULt(a, b, _)
        | Formula::BvULe(a, b, _)
        | Formula::BvSLt(a, b, _)
        | Formula::BvSLe(a, b, _) => {
            features.has_bitvectors = true;
            collect_features(a, features);
            collect_features(b, features);
        }
        Formula::BvNot(a, _) => {
            features.has_bitvectors = true;
            collect_features(a, features);
        }
        Formula::BvToInt(a, _, _) | Formula::IntToBv(a, _) => {
            features.has_bitvectors = true;
            collect_features(a, features);
        }
        Formula::BvExtract { inner, .. } => {
            features.has_bitvectors = true;
            collect_features(inner, features);
        }
        Formula::BvConcat(a, b) => {
            features.has_bitvectors = true;
            collect_features(a, features);
            collect_features(b, features);
        }
        Formula::BvZeroExt(a, _) | Formula::BvSignExt(a, _) => {
            features.has_bitvectors = true;
            collect_features(a, features);
        }

        // -- Conditional --
        Formula::Ite(cond, then_br, else_br) => {
            collect_features(cond, features);
            collect_features(then_br, features);
            collect_features(else_br, features);
        }

        // -- Quantifiers --
        Formula::Forall(_, body) | Formula::Exists(_, body) => {
            features.has_quantifiers = true;
            collect_features(body, features);
        }

        // -- Arrays --
        Formula::Select(arr, idx) => {
            features.has_arrays = true;
            collect_features(arr, features);
            collect_features(idx, features);
        }
        Formula::Store(arr, idx, val) => {
            features.has_arrays = true;
            collect_features(arr, features);
            collect_features(idx, features);
            collect_features(val, features);
        }
        _ => {} // Unknown Formula variant — no features to collect
    }
}

/// Check if a formula contains any variable reference (used for
/// non-linearity detection in Mul/Div/Rem).
fn has_variable(formula: &Formula) -> bool {
    let mut found = false;
    formula.visit(&mut |f| {
        if !found && let Formula::Var(..) = f {
            found = true;
        }
    });
    found
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
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
    fn test_classify_div_by_constant_is_qf_lia() {
        // div by constant (no variable in denominator) stays linear
        let f = Formula::Div(Box::new(int_var("x")), Box::new(Formula::Int(2)));
        assert_eq!(classify_formula(&f), SmtLogic::QfLia);
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
    fn test_theory_classifier_new_and_default() {
        let c1 = TheoryClassifier::new();
        let c2 = TheoryClassifier::default();
        // Both should classify the same formula identically
        let f = Formula::Bool(true);
        assert_eq!(c1.classify_logic(&f), c2.classify_logic(&f));
    }

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
}
