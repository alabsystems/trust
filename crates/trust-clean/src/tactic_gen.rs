// trust-clean/tactic_gen.rs: Automated tactic generation for Clean proofs
//
// Analyzes verification condition structure to generate proof tactic
// sequences. Provides difficulty estimation and Clean syntax rendering.
// This module builds on the lower-level `tactics` module, adding
// heuristic-driven tactic selection and proof formatting.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::{Formula, Sort, VcKind, VerificationCondition};

use crate::tactics::{Tactic, TacticScript};

// ---------------------------------------------------------------------------
// TacticHint — high-level proof strategy hints
// ---------------------------------------------------------------------------

/// High-level hint about which proof strategy to attempt.
///
/// Each variant maps to one or more concrete `Tactic` sequences. The
/// tactic generator selects hints based on VC structure, then expands
/// them into concrete tactic scripts.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum TacticHint {
    /// Try simplification lemmas.
    Simplify,
    /// Rewrite using an equality hypothesis or lemma.
    Rewrite(String),
    /// Perform structural induction on a variable.
    Induction(String),
    /// Case split on an expression.
    CaseSplit(String),
    /// Use `omega` for natural number / integer linear arithmetic.
    OmegaNat,
    /// Use `ring` for polynomial arithmetic.
    Ring,
    /// Use `simp_all` to simplify all hypotheses and the goal.
    SimpAll,
    /// Use `decide` for decidable propositions.
    Decide,
}

impl TacticHint {
    /// Expand this hint into concrete Clean tactics.
    #[must_use]
    pub fn expand(&self) -> Vec<Tactic> {
        match self {
            TacticHint::Simplify => vec![Tactic::Simp(vec![])],
            TacticHint::Rewrite(rule) => vec![Tactic::Rewrite(rule.clone())],
            TacticHint::Induction(var) => {
                vec![Tactic::Induction { var: var.clone(), pattern: None }]
            }
            TacticHint::CaseSplit(expr) => vec![Tactic::Cases(expr.clone())],
            TacticHint::OmegaNat => vec![Tactic::Omega],
            TacticHint::Ring => vec![Tactic::Ring],
            TacticHint::SimpAll => {
                vec![Tactic::Simp(vec![]), Tactic::AllGoals(Box::new(Tactic::Simp(vec![])))]
            }
            TacticHint::Decide => vec![Tactic::Decide],
        }
    }

    /// Estimated cost of this hint (lower is cheaper).
    #[must_use]
    pub fn cost(&self) -> u32 {
        match self {
            TacticHint::Decide => 1,
            TacticHint::Simplify | TacticHint::SimpAll => 2,
            TacticHint::OmegaNat | TacticHint::Ring => 3,
            TacticHint::Rewrite(_) => 4,
            TacticHint::CaseSplit(_) => 5,
            TacticHint::Induction(_) => 6,
        }
    }
}

// ---------------------------------------------------------------------------
// TacticSequence — ordered list of hints with parameters
// ---------------------------------------------------------------------------

/// An ordered sequence of tactic hints with optional parameters.
///
/// This is the high-level representation produced by `generate_tactics()`.
/// Call `to_tactic_script()` to lower it into a concrete `TacticScript`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TacticSequence {
    /// Name for the generated theorem.
    pub theorem_name: String,
    /// Ordered tactic hints.
    pub hints: Vec<TacticHint>,
    /// Optional parameters for each hint (same length as `hints`).
    pub params: Vec<Option<String>>,
}

impl TacticSequence {
    /// Create a new empty tactic sequence.
    #[must_use]
    pub fn new(theorem_name: &str) -> Self {
        Self { theorem_name: theorem_name.to_string(), hints: Vec::new(), params: Vec::new() }
    }

    /// Add a hint with an optional parameter.
    pub fn push(&mut self, hint: TacticHint, param: Option<String>) {
        self.hints.push(hint);
        self.params.push(param);
    }

    /// Returns `true` if the sequence has no hints.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.hints.is_empty()
    }

    /// Returns the number of hints.
    #[must_use]
    pub fn len(&self) -> usize {
        self.hints.len()
    }

    /// Total estimated cost across all hints.
    #[must_use]
    pub fn total_cost(&self) -> u32 {
        self.hints.iter().map(TacticHint::cost).sum()
    }

    /// Lower this sequence into a concrete `TacticScript`.
    #[must_use]
    pub fn to_tactic_script(&self) -> TacticScript {
        let mut script = TacticScript::new(&self.theorem_name);
        for hint in &self.hints {
            for tactic in hint.expand() {
                script.push(tactic);
            }
        }
        script
    }
}

// ---------------------------------------------------------------------------
// Difficulty estimation
// ---------------------------------------------------------------------------

/// Estimated difficulty of proving a verification condition.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Difficulty {
    /// Trivially provable (ground terms, simple decidable).
    Easy,
    /// Requires some automation (linear arithmetic, simple induction).
    Medium,
    /// Requires significant proof effort (quantifiers, non-linear arithmetic).
    Hard,
    /// Cannot estimate difficulty.
    Unknown,
}

/// Estimate how hard a verification condition is to prove.
///
/// Uses structural analysis of the formula and VC kind to assign a
/// difficulty level. This is a heuristic — actual proof difficulty may
/// differ.
#[must_use]
pub fn estimate_difficulty(vc: &VerificationCondition) -> Difficulty {
    let formula = &vc.formula;

    // Ground formulas with no variables are Easy (decidable)
    if is_ground(formula) {
        return Difficulty::Easy;
    }

    // Count structural complexity
    let depth = formula_depth(formula);
    let has_quantifier = has_quantifiers(formula);
    let has_nonlinear = has_nonlinear_arithmetic(formula);

    if has_quantifier && has_nonlinear {
        return Difficulty::Hard;
    }

    if has_quantifier {
        // Quantifiers with simple bodies are Medium, complex are Hard
        if depth > 5 {
            return Difficulty::Hard;
        }
        return Difficulty::Medium;
    }

    if has_nonlinear {
        return Difficulty::Medium;
    }

    // Simple comparisons and arithmetic are Easy
    if depth <= 3 && is_linear_formula(formula) {
        return Difficulty::Easy;
    }

    // Moderate depth without quantifiers or non-linear is Medium
    if depth <= 6 {
        return Difficulty::Medium;
    }

    Difficulty::Hard
}

// ---------------------------------------------------------------------------
// Tactic generation
// ---------------------------------------------------------------------------

/// Generate a tactic sequence for a verification condition.
///
/// Analyzes the VC's kind and formula structure to select appropriate
/// tactic hints. The result is a high-level `TacticSequence` that can
/// be lowered to a `TacticScript` via `to_tactic_script()`.
#[must_use]
pub fn generate_tactics(vc: &VerificationCondition) -> TacticSequence {
    let theorem_name = format!("Trust.vc.{}", sanitize_name(vc.function.as_str()));
    let mut seq = TacticSequence::new(&theorem_name);

    // Phase 1: Intro tactics for top-level structure
    generate_intro_hints(&vc.formula, &mut seq);

    // Phase 2: Kind-specific tactics
    generate_kind_hints(&vc.kind, &mut seq);

    // Phase 3: Formula-structure-driven tactics
    generate_formula_hints(&vc.formula, &mut seq);

    // Phase 4: Closing tactic
    generate_closing_hint(&vc.formula, &mut seq);

    seq
}

/// Generate tactics specifically for arithmetic verification conditions.
///
/// Selects omega for linear arithmetic, ring for polynomial, and
/// combined strategies for mixed formulas.
#[must_use]
pub fn tactic_for_arithmetic(formula: &Formula) -> TacticSequence {
    let mut seq = TacticSequence::new("arith");

    // Always start with simplification
    seq.push(TacticHint::Simplify, None);

    if has_nonlinear_arithmetic(formula) {
        // Non-linear: try ring first, then omega as fallback
        seq.push(TacticHint::Ring, Some("polynomial arithmetic".to_string()));
        seq.push(TacticHint::OmegaNat, Some("linear fallback".to_string()));
    } else {
        // Linear arithmetic: omega is the primary tactic
        seq.push(TacticHint::OmegaNat, Some("linear arithmetic".to_string()));
    }

    seq
}

/// Generate tactics for inductive/recursive verification conditions.
///
/// Identifies a suitable induction variable and generates an induction
/// scheme with base case and step tactics.
#[must_use]
pub fn tactic_for_induction(formula: &Formula) -> TacticSequence {
    let mut seq = TacticSequence::new("induction");

    // Find a suitable induction variable
    if let Some(var) = find_induction_variable(formula) {
        seq.push(TacticHint::Induction(var), Some("structural induction".to_string()));
        // Base case: try simplification + omega
        seq.push(TacticHint::Simplify, Some("base case".to_string()));
        seq.push(TacticHint::OmegaNat, Some("base arithmetic".to_string()));
        // Step case: simp_all to use induction hypothesis
        seq.push(TacticHint::SimpAll, Some("inductive step".to_string()));
        seq.push(TacticHint::OmegaNat, Some("step arithmetic".to_string()));
    } else {
        // No obvious induction variable — fall back to simplification
        seq.push(TacticHint::SimpAll, None);
        seq.push(TacticHint::OmegaNat, None);
    }

    seq
}

/// Render a tactic sequence as a Clean proof string.
///
/// Produces a complete `theorem ... := by` block with one tactic per
/// line, indented by two spaces.
#[must_use]
pub fn format_clean_proof(seq: &TacticSequence) -> String {
    let script = seq.to_tactic_script();
    script.to_lean_code()
}

// ---------------------------------------------------------------------------
// Internal helpers
// ---------------------------------------------------------------------------

/// Generate intro hints for top-level quantifiers and implications.
fn generate_intro_hints(formula: &Formula, seq: &mut TacticSequence) {
    match formula {
        Formula::Forall(bindings, _body) => {
            for (name, _sort) in bindings {
                // Intros are handled directly via the tactic script, not hints.
                // We add a simplify hint after introducing each variable.
                let _ = name; // Variable is introduced by the tactic script
            }
        }
        Formula::Implies(_, _) => {
            // Implication: will need intro
            seq.push(TacticHint::Simplify, Some("after intro".to_string()));
        }
        _ => {}
    }
}

/// Generate hints based on VC kind.
fn generate_kind_hints(kind: &VcKind, seq: &mut TacticSequence) {
    match kind {
        VcKind::DivisionByZero | VcKind::RemainderByZero => {
            seq.push(TacticHint::Simplify, Some("division definition".to_string()));
            seq.push(TacticHint::OmegaNat, Some("divisor nonzero".to_string()));
        }
        VcKind::ArithmeticOverflow { .. } => {
            seq.push(TacticHint::Simplify, None);
            seq.push(TacticHint::OmegaNat, Some("bounds check".to_string()));
        }
        VcKind::IndexOutOfBounds | VcKind::SliceBoundsCheck => {
            seq.push(TacticHint::Simplify, Some("array size".to_string()));
            seq.push(TacticHint::OmegaNat, Some("index bounds".to_string()));
        }
        VcKind::Assertion { .. } | VcKind::Precondition { .. } | VcKind::Postcondition => {
            seq.push(TacticHint::Simplify, None);
        }
        VcKind::NonTermination { .. } => {
            seq.push(TacticHint::Simplify, None);
            seq.push(TacticHint::OmegaNat, Some("measure decrease".to_string()));
        }
        _ => {
            seq.push(TacticHint::Simplify, None);
        }
    }
}

/// Generate hints based on formula structure.
fn generate_formula_hints(formula: &Formula, seq: &mut TacticSequence) {
    match formula {
        Formula::And(children) if children.len() > 1 => {
            // Conjunction: try case split via constructor
            seq.push(TacticHint::SimpAll, Some("conjunction".to_string()));
        }
        Formula::Or(children) if !children.is_empty() => {
            seq.push(TacticHint::CaseSplit("h".to_string()), Some("disjunction".to_string()));
        }
        Formula::Eq(lhs, rhs) if is_arithmetic_term(lhs) && is_arithmetic_term(rhs) => {
            if has_nonlinear_arithmetic(formula) {
                seq.push(TacticHint::Ring, Some("ring equality".to_string()));
            } else {
                seq.push(TacticHint::OmegaNat, Some("arithmetic equality".to_string()));
            }
        }
        Formula::Le(_, _) | Formula::Lt(_, _) | Formula::Ge(_, _) | Formula::Gt(_, _) => {
            seq.push(TacticHint::OmegaNat, Some("inequality".to_string()));
        }
        Formula::Exists(_, _) => {
            // Existential: need a witness; try constructor + simplify
            seq.push(TacticHint::Simplify, Some("existential".to_string()));
        }
        _ => {}
    }
}

/// Generate a closing hint to finish the proof.
fn generate_closing_hint(formula: &Formula, seq: &mut TacticSequence) {
    if is_ground(formula) {
        seq.push(TacticHint::Decide, Some("ground decidable".to_string()));
    } else if is_linear_formula(formula) {
        seq.push(TacticHint::OmegaNat, Some("linear closing".to_string()));
    } else {
        seq.push(TacticHint::SimpAll, Some("fallback".to_string()));
    }
}

/// Check if a formula has no free variables (ground term).
fn is_ground(formula: &Formula) -> bool {
    match formula {
        Formula::Bool(_) | Formula::Int(_) | Formula::UInt(_) | Formula::BitVec { .. } => true,
        Formula::Var(_, _) => false,
        _ => formula.children().iter().all(|c| is_ground(c)),
    }
}

/// Compute the nesting depth of a formula.
fn formula_depth(formula: &Formula) -> usize {
    let children = formula.children();
    if children.is_empty() {
        0
    } else {
        1 + children.iter().map(|c| formula_depth(c)).max().unwrap_or(0)
    }
}

/// Check if a formula contains quantifiers (Forall or Exists).
fn has_quantifiers(formula: &Formula) -> bool {
    match formula {
        Formula::Forall(_, _) | Formula::Exists(_, _) => true,
        _ => formula.children().iter().any(|c| has_quantifiers(c)),
    }
}

/// Check if a formula contains non-linear arithmetic (variable * variable).
fn has_nonlinear_arithmetic(formula: &Formula) -> bool {
    match formula {
        Formula::Mul(a, b) => {
            let a_has_var = contains_variable(a);
            let b_has_var = contains_variable(b);
            if a_has_var && b_has_var {
                return true;
            }
            has_nonlinear_arithmetic(a) || has_nonlinear_arithmetic(b)
        }
        _ => formula.children().iter().any(|c| has_nonlinear_arithmetic(c)),
    }
}

/// Check if a formula is linear (no multiplication of variables).
fn is_linear_formula(formula: &Formula) -> bool {
    !has_nonlinear_arithmetic(formula) && !has_quantifiers(formula)
}

/// Check if a formula/term contains any variable.
fn contains_variable(formula: &Formula) -> bool {
    match formula {
        Formula::Var(_, _) => true,
        _ => formula.children().iter().any(|c| contains_variable(c)),
    }
}

/// Check if a term is purely arithmetic (integer operations).
fn is_arithmetic_term(formula: &Formula) -> bool {
    match formula {
        Formula::Int(_) | Formula::UInt(_) => true,
        Formula::Var(_, Sort::Int) => true,
        Formula::Add(a, b)
        | Formula::Sub(a, b)
        | Formula::Mul(a, b)
        | Formula::Div(a, b)
        | Formula::Rem(a, b) => is_arithmetic_term(a) && is_arithmetic_term(b),
        Formula::Neg(inner) => is_arithmetic_term(inner),
        _ => false,
    }
}

/// Find a suitable induction variable in a formula.
///
/// Looks for Forall-bound integer variables, or the first integer variable
/// appearing in a recursive-looking structure.
fn find_induction_variable(formula: &Formula) -> Option<String> {
    match formula {
        Formula::Forall(bindings, _) => {
            // Prefer the first integer-sorted binding
            bindings.iter().find(|(_, sort)| *sort == Sort::Int).map(|(name, _)| name.to_string())
        }
        _ => {
            // Collect variables and pick the first integer one
            let mut vars = Vec::new();
            collect_int_variables(formula, &mut vars);
            vars.into_iter().next()
        }
    }
}

/// Collect integer-sorted variable names from a formula.
fn collect_int_variables(formula: &Formula, vars: &mut Vec<String>) {
    if let Formula::Var(name, Sort::Int) = formula
        && !vars.contains(name)
    {
        vars.push(name.clone());
    }
    for child in formula.children() {
        collect_int_variables(child, vars);
    }
}

/// Sanitize a function name for use as a Clean identifier.
fn sanitize_name(name: &str) -> String {
    name.chars().map(|c| if c.is_alphanumeric() || c == '_' { c } else { '_' }).collect()
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use trust_types::*;

    use super::*;

    // --- Helper VCs ---

    fn make_linear_vc() -> VerificationCondition {
        VerificationCondition {
            kind: VcKind::ArithmeticOverflow {
                op: BinOp::Add,
                operand_tys: (Ty::usize(), Ty::usize()),
            },
            function: "add_safe".into(),
            location: SourceSpan::default(),
            formula: Formula::Le(
                Box::new(Formula::Add(
                    Box::new(Formula::Var("a".into(), Sort::Int)),
                    Box::new(Formula::Var("b".into(), Sort::Int)),
                )),
                Box::new(Formula::Int(u64::MAX as i128)),
            ),
            contract_metadata: None,
            obligation: None,
        }
    }

    fn make_ground_vc() -> VerificationCondition {
        VerificationCondition {
            kind: VcKind::Assertion { message: "1 + 1 = 2".to_string() },
            function: "trivial".into(),
            location: SourceSpan::default(),
            formula: Formula::Eq(
                Box::new(Formula::Int(2)),
                Box::new(Formula::Add(Box::new(Formula::Int(1)), Box::new(Formula::Int(1)))),
            ),
            contract_metadata: None,
            obligation: None,
        }
    }

    fn make_nonlinear_vc() -> VerificationCondition {
        VerificationCondition {
            kind: VcKind::Postcondition,
            function: "square_nonneg".into(),
            location: SourceSpan::default(),
            formula: Formula::Ge(
                Box::new(Formula::Mul(
                    Box::new(Formula::Var("x".into(), Sort::Int)),
                    Box::new(Formula::Var("x".into(), Sort::Int)),
                )),
                Box::new(Formula::Int(0)),
            ),
            contract_metadata: None,
            obligation: None,
        }
    }

    fn make_forall_vc() -> VerificationCondition {
        VerificationCondition {
            kind: VcKind::Postcondition,
            function: "forall_bound".into(),
            location: SourceSpan::default(),
            formula: Formula::Forall(
                vec![("n".into(), Sort::Int)],
                Box::new(Formula::Le(
                    Box::new(Formula::Var("n".into(), Sort::Int)),
                    Box::new(Formula::Add(
                        Box::new(Formula::Var("n".into(), Sort::Int)),
                        Box::new(Formula::Int(1)),
                    )),
                )),
            ),
            contract_metadata: None,
            obligation: None,
        }
    }

    fn make_disjunction_vc() -> VerificationCondition {
        VerificationCondition {
            kind: VcKind::Assertion { message: "or case".to_string() },
            function: "or_test".into(),
            location: SourceSpan::default(),
            formula: Formula::Or(vec![
                Formula::Gt(
                    Box::new(Formula::Var("x".into(), Sort::Int)),
                    Box::new(Formula::Int(0)),
                ),
                Formula::Le(
                    Box::new(Formula::Var("x".into(), Sort::Int)),
                    Box::new(Formula::Int(0)),
                ),
            ]),
            contract_metadata: None,
            obligation: None,
        }
    }

    // --- TacticHint tests ---

    #[test]
    fn test_tactic_hint_expand_simplify() {
        let tactics = TacticHint::Simplify.expand();
        assert_eq!(tactics.len(), 1);
        assert_eq!(tactics[0], Tactic::Simp(vec![]));
    }

    #[test]
    fn test_tactic_hint_expand_omega() {
        let tactics = TacticHint::OmegaNat.expand();
        assert_eq!(tactics.len(), 1);
        assert_eq!(tactics[0], Tactic::Omega);
    }

    #[test]
    fn test_tactic_hint_expand_induction() {
        let tactics = TacticHint::Induction("n".to_string()).expand();
        assert_eq!(tactics.len(), 1);
        assert_eq!(tactics[0], Tactic::Induction { var: "n".to_string(), pattern: None });
    }

    #[test]
    fn test_tactic_hint_cost_ordering() {
        assert!(TacticHint::Decide.cost() < TacticHint::Simplify.cost());
        assert!(TacticHint::Simplify.cost() < TacticHint::Ring.cost());
        assert!(TacticHint::Ring.cost() < TacticHint::CaseSplit("h".into()).cost());
        assert!(
            TacticHint::CaseSplit("h".into()).cost() < TacticHint::Induction("n".into()).cost()
        );
    }

    // --- TacticSequence tests ---

    #[test]
    fn test_tactic_sequence_new_is_empty() {
        let seq = TacticSequence::new("test_thm");
        assert!(seq.is_empty());
        assert_eq!(seq.len(), 0);
        assert_eq!(seq.total_cost(), 0);
    }

    #[test]
    fn test_tactic_sequence_push_and_len() {
        let mut seq = TacticSequence::new("test_thm");
        seq.push(TacticHint::Simplify, None);
        seq.push(TacticHint::OmegaNat, Some("linear".to_string()));
        assert!(!seq.is_empty());
        assert_eq!(seq.len(), 2);
        assert_eq!(seq.params[0], None);
        assert_eq!(seq.params[1], Some("linear".to_string()));
    }

    #[test]
    fn test_tactic_sequence_to_tactic_script() {
        let mut seq = TacticSequence::new("thm");
        seq.push(TacticHint::Simplify, None);
        seq.push(TacticHint::OmegaNat, None);
        let script = seq.to_tactic_script();
        assert_eq!(script.theorem_name, "thm");
        assert_eq!(script.len(), 2);
        let code = script.to_lean_code();
        assert!(code.contains("simp"));
        assert!(code.contains("omega"));
    }

    // --- estimate_difficulty tests ---

    #[test]
    fn test_estimate_difficulty_nonlinear_is_medium() {
        let vc = make_nonlinear_vc();
        let diff = estimate_difficulty(&vc);
        assert_eq!(diff, Difficulty::Medium, "nonlinear without quantifiers should be Medium");
    }

    #[test]
    fn test_estimate_difficulty_ground_is_easy() {
        let vc = make_ground_vc();
        assert_eq!(estimate_difficulty(&vc), Difficulty::Easy);
    }

    #[test]
    fn test_estimate_difficulty_linear_inequality() {
        let vc = make_linear_vc();
        let diff = estimate_difficulty(&vc);
        // Linear arithmetic with variables at depth 2: Easy
        assert!(
            diff == Difficulty::Easy || diff == Difficulty::Medium,
            "linear vc difficulty should be Easy or Medium, got {:?}",
            diff
        );
    }

    #[test]
    fn test_estimate_difficulty_quantified_is_at_least_medium() {
        let vc = make_forall_vc();
        let diff = estimate_difficulty(&vc);
        assert!(
            diff >= Difficulty::Medium,
            "quantified vc should be at least Medium, got {:?}",
            diff
        );
    }

    // --- generate_tactics tests ---

    #[test]
    fn test_generate_tactics_linear_vc() {
        let vc = make_linear_vc();
        let seq = generate_tactics(&vc);
        assert!(!seq.is_empty());
        assert_eq!(seq.theorem_name, "Trust.vc.add_safe");
        // Should contain omega for linear arithmetic
        let script = seq.to_tactic_script();
        let code = script.to_lean_code();
        assert!(code.contains("omega"), "linear vc should use omega, got:\n{code}");
    }

    #[test]
    fn test_generate_tactics_ground_vc() {
        let vc = make_ground_vc();
        let seq = generate_tactics(&vc);
        assert!(!seq.is_empty());
        let script = seq.to_tactic_script();
        let code = script.to_lean_code();
        assert!(code.contains("decide"), "ground vc should use decide, got:\n{code}");
    }

    #[test]
    fn test_generate_tactics_disjunction_vc() {
        let vc = make_disjunction_vc();
        let seq = generate_tactics(&vc);
        let script = seq.to_tactic_script();
        let code = script.to_lean_code();
        assert!(code.contains("cases"), "disjunction vc should use cases, got:\n{code}");
    }

    // --- tactic_for_arithmetic tests ---

    #[test]
    fn test_tactic_for_arithmetic_linear() {
        let formula = Formula::Le(
            Box::new(Formula::Add(
                Box::new(Formula::Var("x".into(), Sort::Int)),
                Box::new(Formula::Int(1)),
            )),
            Box::new(Formula::Int(10)),
        );
        let seq = tactic_for_arithmetic(&formula);
        assert!(!seq.is_empty());
        let code = seq.to_tactic_script().to_lean_code();
        assert!(code.contains("omega"), "linear formula should get omega, got:\n{code}");
        assert!(!code.contains("ring"), "linear formula should not get ring, got:\n{code}");
    }

    #[test]
    fn test_tactic_for_arithmetic_nonlinear() {
        let formula = Formula::Eq(
            Box::new(Formula::Mul(
                Box::new(Formula::Var("x".into(), Sort::Int)),
                Box::new(Formula::Var("y".into(), Sort::Int)),
            )),
            Box::new(Formula::Mul(
                Box::new(Formula::Var("y".into(), Sort::Int)),
                Box::new(Formula::Var("x".into(), Sort::Int)),
            )),
        );
        let seq = tactic_for_arithmetic(&formula);
        let code = seq.to_tactic_script().to_lean_code();
        assert!(code.contains("ring"), "nonlinear formula should get ring, got:\n{code}");
    }

    // --- tactic_for_induction tests ---

    #[test]
    fn test_tactic_for_induction_with_forall() {
        let formula = Formula::Forall(
            vec![("n".into(), Sort::Int)],
            Box::new(Formula::Le(
                Box::new(Formula::Var("n".into(), Sort::Int)),
                Box::new(Formula::Int(100)),
            )),
        );
        let seq = tactic_for_induction(&formula);
        assert!(!seq.is_empty());
        let code = seq.to_tactic_script().to_lean_code();
        assert!(code.contains("induction n"), "induction should target variable n, got:\n{code}");
    }

    #[test]
    fn test_tactic_for_induction_no_variable() {
        let formula = Formula::Bool(true);
        let seq = tactic_for_induction(&formula);
        // Should fall back to simp_all + omega
        assert!(!seq.is_empty());
        let code = seq.to_tactic_script().to_lean_code();
        assert!(
            code.contains("simp") || code.contains("omega"),
            "fallback should use simp or omega, got:\n{code}"
        );
    }

    // --- format_clean_proof tests ---

    #[test]
    fn test_format_clean_proof_basic() {
        let mut seq = TacticSequence::new("my_theorem");
        seq.push(TacticHint::Simplify, None);
        seq.push(TacticHint::OmegaNat, None);
        let proof = format_clean_proof(&seq);
        assert!(proof.starts_with("theorem my_theorem := by\n"));
        assert!(proof.contains("  simp\n"));
        assert!(proof.contains("  omega\n"));
    }

    #[test]
    fn test_format_clean_proof_with_induction() {
        let mut seq = TacticSequence::new("ind_thm");
        seq.push(TacticHint::Induction("n".to_string()), None);
        seq.push(TacticHint::Simplify, None);
        let proof = format_clean_proof(&seq);
        assert!(proof.contains("induction n"));
        assert!(proof.contains("simp"));
    }

    // --- Difficulty ordering test ---

    #[test]
    fn test_difficulty_ordering() {
        assert!(Difficulty::Easy < Difficulty::Medium);
        assert!(Difficulty::Medium < Difficulty::Hard);
        assert!(Difficulty::Hard < Difficulty::Unknown);
    }

    // --- Helper function tests ---

    #[test]
    fn test_is_ground_literals() {
        assert!(is_ground(&Formula::Bool(true)));
        assert!(is_ground(&Formula::Int(42)));
        assert!(!is_ground(&Formula::Var("x".into(), Sort::Int)));
    }

    #[test]
    fn test_formula_depth() {
        assert_eq!(formula_depth(&Formula::Int(1)), 0);
        assert_eq!(
            formula_depth(&Formula::Add(Box::new(Formula::Int(1)), Box::new(Formula::Int(2)),)),
            1
        );
        assert_eq!(
            formula_depth(&Formula::Add(
                Box::new(Formula::Add(Box::new(Formula::Int(1)), Box::new(Formula::Int(2)),)),
                Box::new(Formula::Int(3)),
            )),
            2
        );
    }

    #[test]
    fn test_has_quantifiers() {
        assert!(!has_quantifiers(&Formula::Int(1)));
        assert!(has_quantifiers(&Formula::Forall(
            vec![("x".into(), Sort::Int)],
            Box::new(Formula::Bool(true)),
        )));
        assert!(has_quantifiers(&Formula::Not(Box::new(Formula::Exists(
            vec![("x".into(), Sort::Int)],
            Box::new(Formula::Bool(true)),
        )))));
    }
}
