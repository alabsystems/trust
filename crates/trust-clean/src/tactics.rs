// trust-clean/tactics.rs: Clean tactic script generation
//
// Generates Clean tactic scripts from verification conditions. The tactic
// script is a sequence of Clean tactics that, when executed, produce a
// proof of the VC's formula. This is an alternative to proof reconstruction:
// instead of building a proof term directly, we emit a script that guides
// Clean's tactic engine to find the proof.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::fmt::Write;

use trust_types::{Formula, Sort, VcKind, VerificationCondition};

// ---------------------------------------------------------------------------
// Tactic enum
// ---------------------------------------------------------------------------

/// A single Clean tactic.
///
/// Each variant corresponds to a Clean tactic that can appear in a
/// `by` block. Tactics are rendered to Clean source code via
/// `Tactic::to_lean_code`.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum Tactic {
    /// `intro x` — introduce a hypothesis or variable.
    Intro(String),
    /// `apply <expr>` — apply a lemma or function to the goal.
    Apply(String),
    /// `exact <expr>` — provide the exact proof term.
    Exact(String),
    /// `rewrite [<rule>]` — rewrite the goal using an equality.
    Rewrite(String),
    /// `simp [<lemmas>]` — simplify using the simplifier.
    Simp(Vec<String>),
    /// `omega` — solve linear arithmetic goals.
    Omega,
    /// `decide` — decide a decidable proposition.
    Decide,
    /// `cases <expr>` — case split on a term.
    Cases(String),
    /// `induction <var> with <pattern>` — structural induction.
    Induction {
        /// Variable to induct on.
        var: String,
        /// Optional pattern for the inductive hypothesis.
        pattern: Option<String>,
    },
    /// `ring` — prove ring equalities.
    Ring,
    /// `linarith` — prove linear arithmetic inequalities.
    Linarith,
    // Trust: Specialized tactic variants for better proof automation
    /// `norm_num` — normalize numeric expressions.
    NormNum,
    /// `ring_nf` — normalize using ring laws without closing the goal.
    RingNf,
    /// `constructor` — apply the constructor of an inductive type.
    Constructor,
    /// `contradiction` — close the goal by finding contradictory hypotheses.
    Contradiction,
    /// `rcases <expr> with <pattern>` — recursive case split.
    Rcases {
        /// Expression to case-split on.
        expr: String,
        /// Pattern for destructuring.
        pattern: String,
    },
    /// `obtain <pattern> := <expr>` — destructure an existential or conjunction.
    Obtain {
        /// Pattern to bind.
        pattern: String,
        /// Expression providing the value.
        expr: String,
    },
    /// `have <name> : <type> := <proof>` — introduce a local hypothesis.
    Have {
        /// Name for the new hypothesis.
        name: String,
        /// Type (statement) of the hypothesis.
        ty: String,
        /// Proof term or tactic block (rendered inline).
        proof: String,
    },
    /// `suffices <name> : <type>` — reduce to proving a sufficient condition.
    Suffices {
        /// Name for the sufficiency hypothesis.
        name: String,
        /// The sufficient condition to prove.
        ty: String,
    },
    /// A focused tactic block: `· <inner_tactics>`.
    Focus(Vec<Tactic>),
    /// `all_goals <tactic>` — apply a tactic to all remaining goals.
    AllGoals(Box<Tactic>),
    /// `first | t1 | t2 | ...` — try tactics left-to-right until one succeeds.
    First(Vec<Tactic>),
    /// `repeat <tactic>` — apply a tactic repeatedly until it fails.
    Repeat(Box<Tactic>),
}

impl Tactic {
    /// Render this tactic as Clean source code.
    #[must_use]
    pub fn to_lean_code(&self) -> String {
        match self {
            Tactic::Intro(name) => format!("intro {name}"),
            Tactic::Apply(expr) => format!("apply {expr}"),
            Tactic::Exact(expr) => format!("exact {expr}"),
            Tactic::Rewrite(rule) => format!("rewrite [{rule}]"),
            Tactic::Simp(lemmas) => {
                if lemmas.is_empty() {
                    "simp".to_string()
                } else {
                    format!("simp [{}]", lemmas.join(", "))
                }
            }
            Tactic::Omega => "omega".to_string(),
            Tactic::Decide => "decide".to_string(),
            Tactic::Cases(expr) => format!("cases {expr}"),
            Tactic::Induction { var, pattern } => {
                if let Some(pat) = pattern {
                    format!("induction {var} with {pat}")
                } else {
                    format!("induction {var}")
                }
            }
            Tactic::Ring => "ring".to_string(),
            Tactic::Linarith => "linarith".to_string(),
            Tactic::NormNum => "norm_num".to_string(),
            Tactic::RingNf => "ring_nf".to_string(),
            Tactic::Constructor => "constructor".to_string(),
            Tactic::Contradiction => "contradiction".to_string(),
            Tactic::Rcases { expr, pattern } => format!("rcases {expr} with {pattern}"),
            Tactic::Obtain { pattern, expr } => format!("obtain {pattern} := {expr}"),
            Tactic::Have { name, ty, proof } => format!("have {name} : {ty} := {proof}"),
            Tactic::Suffices { name, ty } => format!("suffices {name} : {ty}"),
            Tactic::Focus(inner) => {
                let mut out = String::from("·");
                for t in inner {
                    let _ = write!(out, " {}", t.to_lean_code());
                }
                out
            }
            Tactic::AllGoals(inner) => format!("all_goals {}", inner.to_lean_code()),
            Tactic::First(alternatives) => {
                let parts: Vec<String> = alternatives.iter().map(|t| t.to_lean_code()).collect();
                format!("first | {}", parts.join(" | "))
            }
            Tactic::Repeat(inner) => format!("repeat {}", inner.to_lean_code()),
        }
    }

    /// Returns `true` if this tactic targets arithmetic goals.
    #[must_use]
    pub fn is_arithmetic(&self) -> bool {
        matches!(
            self,
            Tactic::Omega | Tactic::Linarith | Tactic::NormNum | Tactic::Ring | Tactic::RingNf
        )
    }

    /// Returns `true` if this tactic performs case analysis.
    #[must_use]
    pub fn is_case_analysis(&self) -> bool {
        matches!(self, Tactic::Cases(_) | Tactic::Rcases { .. } | Tactic::Obtain { .. })
    }

    /// Estimated cost of this tactic (for strategy selection).
    /// Lower is cheaper. Simple tactics score 1, compound higher.
    #[must_use]
    pub fn estimated_cost(&self) -> u32 {
        match self {
            Tactic::Exact(_) | Tactic::Decide | Tactic::Contradiction => 1,
            Tactic::Intro(_) | Tactic::Constructor => 2,
            Tactic::Omega | Tactic::Linarith | Tactic::NormNum | Tactic::Ring | Tactic::RingNf => 3,
            Tactic::Simp(_) | Tactic::Rewrite(_) | Tactic::Apply(_) => 4,
            Tactic::Cases(_) | Tactic::Rcases { .. } | Tactic::Obtain { .. } => 5,
            Tactic::Induction { .. } => 6,
            Tactic::Have { .. } | Tactic::Suffices { .. } => 5,
            Tactic::Focus(inner) => inner.iter().map(Tactic::estimated_cost).sum::<u32>() + 1,
            Tactic::AllGoals(inner) | Tactic::Repeat(inner) => inner.estimated_cost() + 2,
            Tactic::First(alts) => alts.iter().map(Tactic::estimated_cost).min().unwrap_or(1),
        }
    }
}

// ---------------------------------------------------------------------------
// Tactic script
// ---------------------------------------------------------------------------

/// A sequence of Clean tactics to prove a theorem.
///
/// The script is rendered as a Clean `by` block with one tactic per line.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TacticScript {
    /// The theorem name (for the generated Clean declaration).
    pub theorem_name: String,
    /// Ordered sequence of tactics.
    pub tactics: Vec<Tactic>,
}

impl TacticScript {
    /// Create a new empty tactic script.
    #[must_use]
    pub fn new(theorem_name: &str) -> Self {
        TacticScript { theorem_name: theorem_name.to_string(), tactics: Vec::new() }
    }

    /// Add a tactic to the script.
    pub fn push(&mut self, tactic: Tactic) {
        self.tactics.push(tactic);
    }

    /// Returns `true` if the script has no tactics.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.tactics.is_empty()
    }

    /// Returns the number of tactics in the script.
    #[must_use]
    pub fn len(&self) -> usize {
        self.tactics.len()
    }

    /// Render the tactic script as a complete Clean proof.
    ///
    /// Produces a `theorem` declaration with a `by` block containing
    /// one tactic per line, indented by two spaces.
    #[must_use]
    pub fn to_lean_code(&self) -> String {
        let mut output = format!("theorem {} := by\n", self.theorem_name);
        for tactic in &self.tactics {
            let _ = writeln!(output, "  {}", tactic.to_lean_code());
        }
        output
    }

    /// Total estimated cost of all tactics in this script.
    #[must_use]
    pub fn total_cost(&self) -> u32 {
        self.tactics.iter().map(Tactic::estimated_cost).sum()
    }

    /// Append all tactics from another script, discarding the other's theorem name.
    pub fn extend(&mut self, other: &TacticScript) {
        self.tactics.extend(other.tactics.iter().cloned());
    }
}

// ---------------------------------------------------------------------------
// Trust: Tactic composition — build strategies from multiple tactics
// ---------------------------------------------------------------------------

/// Compose multiple tactic scripts into a single strategy.
///
/// Merges the tactics from `scripts` into one script under `theorem_name`.
/// The tactics appear in order: all tactics from scripts[0], then scripts[1], etc.
#[must_use]
pub fn compose_tactics(theorem_name: &str, scripts: &[TacticScript]) -> TacticScript {
    let mut result = TacticScript::new(theorem_name);
    for script in scripts {
        result.extend(script);
    }
    result
}

/// Build an arithmetic strategy: `simp` then `norm_num` then `ring` then `omega`.
///
/// Targets linear and polynomial arithmetic goals. Tries simplification first,
/// then increasingly powerful arithmetic tactics.
#[must_use]
pub fn arithmetic_strategy(theorem_name: &str) -> TacticScript {
    let mut script = TacticScript::new(theorem_name);
    script.push(Tactic::Simp(vec![]));
    script.push(Tactic::First(vec![
        Tactic::NormNum,
        Tactic::Ring,
        Tactic::Linarith,
        Tactic::Omega,
    ]));
    script
}

/// Build an induction strategy for a variable with a measure function.
///
/// Introduces the variable, sets up the induction, then tries arithmetic
/// to close the base case and inductive step.
#[must_use]
pub fn induction_strategy(theorem_name: &str, var: &str, ih_pattern: Option<&str>) -> TacticScript {
    let mut script = TacticScript::new(theorem_name);
    script.push(Tactic::Intro(var.to_string()));
    script.push(Tactic::Induction {
        var: var.to_string(),
        pattern: ih_pattern.map(|s| s.to_string()),
    });
    // Base case
    script.push(Tactic::Focus(vec![Tactic::Simp(vec![]), Tactic::Omega]));
    // Inductive step
    script.push(Tactic::Focus(vec![
        Tactic::Simp(vec![]),
        Tactic::First(vec![Tactic::Linarith, Tactic::Omega]),
    ]));
    script
}

/// Build a case-split strategy for an expression.
///
/// Performs case analysis then tries to close each case with `simp` and `omega`.
#[must_use]
pub fn case_split_strategy(theorem_name: &str, expr: &str) -> TacticScript {
    let mut script = TacticScript::new(theorem_name);
    script.push(Tactic::Cases(expr.to_string()));
    script.push(Tactic::AllGoals(Box::new(Tactic::First(vec![
        Tactic::Simp(vec![]),
        Tactic::Omega,
        Tactic::Decide,
    ]))));
    script
}

// ---------------------------------------------------------------------------
// Tactic generation from VC structure
// ---------------------------------------------------------------------------

/// Generate a tactic script for a verification condition.
///
/// Uses heuristic tactic selection based on the VC's kind and formula
/// structure. The generated script is a best-effort attempt — it may
/// not succeed for all VCs, but covers common patterns.
///
/// # Heuristic strategy
///
/// 1. Introduce hypotheses from the formula structure
/// 2. Select domain-specific tactics based on `VcKind`
/// 3. Apply structural tactics based on `Formula` connectives
/// 4. Fall back to `omega`/`decide` for arithmetic/decidable goals
#[must_use]
pub fn generate_tactic_script(vc: &VerificationCondition) -> TacticScript {
    let theorem_name = format!("Trust.vc.{}", sanitize_name(vc.function.as_str()));
    let mut script = TacticScript::new(&theorem_name);

    // Phase 1: Introduce hypotheses based on formula structure
    generate_intro_tactics(&vc.formula, &mut script);

    // Phase 2: VC-kind-specific tactics
    generate_kind_tactics(&vc.kind, &mut script);

    // Phase 3: Formula-structure-driven tactics
    generate_formula_tactics(&vc.formula, &mut script);

    // Phase 4: Closing tactic (try to close the goal)
    generate_closing_tactic(&vc.kind, &vc.formula, &mut script);

    script
}

/// Generate intro tactics for top-level quantifiers and implications.
fn generate_intro_tactics(formula: &Formula, script: &mut TacticScript) {
    match formula {
        Formula::Forall(bindings, _body) => {
            for (name, _sort) in bindings {
                script.push(Tactic::Intro(name.to_string()));
            }
        }
        Formula::Implies(_, _) => {
            script.push(Tactic::Intro("h".to_string()));
        }
        _ => {}
    }
}

/// Generate tactics based on the VC kind.
fn generate_kind_tactics(kind: &VcKind, script: &mut TacticScript) {
    match kind {
        VcKind::DivisionByZero | VcKind::RemainderByZero => {
            // Division/remainder by zero: typically need to show divisor != 0
            script.push(Tactic::Simp(vec!["Nat.div_def".to_string()]));
        }
        VcKind::ArithmeticOverflow { .. } => {
            // Overflow: use omega for linear arithmetic bounds
            script.push(Tactic::Simp(vec![]));
        }
        VcKind::IndexOutOfBounds | VcKind::SliceBoundsCheck => {
            // Bounds checking: typically linear arithmetic
            script.push(Tactic::Simp(vec!["Array.size".to_string()]));
        }
        VcKind::Assertion { .. } | VcKind::Precondition { .. } | VcKind::Postcondition => {
            // User assertions: try simp first
            script.push(Tactic::Simp(vec![]));
        }
        _ => {
            // Default: try simplification
            script.push(Tactic::Simp(vec![]));
        }
    }
}

/// Generate tactics based on the formula structure.
fn generate_formula_tactics(formula: &Formula, script: &mut TacticScript) {
    match formula {
        Formula::Not(inner) => {
            // For negation goals, introduce the hypothesis
            script.push(Tactic::Intro("h_neg".to_string()));
            // Then work on the inner formula
            generate_formula_tactics(inner, script);
        }
        Formula::And(children) if !children.is_empty() => {
            // For conjunction goals, use constructor
            script.push(Tactic::Apply("And.intro".to_string()));
        }
        Formula::Or(_) => {
            // For disjunction, try cases
            script.push(Tactic::Cases("h".to_string()));
        }
        Formula::Eq(_, _) if formula_is_arithmetic(formula) => {
            // Equality: try ring for algebraic
            script.push(Tactic::Ring);
        }
        Formula::Le(_, _) | Formula::Lt(_, _) | Formula::Ge(_, _) | Formula::Gt(_, _) => {
            // Inequalities: linarith is the go-to
            script.push(Tactic::Linarith);
        }
        _ => {}
    }
}

/// Generate a closing tactic to finish the proof.
fn generate_closing_tactic(_kind: &VcKind, formula: &Formula, script: &mut TacticScript) {
    if formula_is_decidable(formula) {
        script.push(Tactic::Decide);
    } else if formula_is_linear_arithmetic(formula) {
        script.push(Tactic::Omega);
    } else {
        // Generic fallback: try simp then omega
        script.push(Tactic::Simp(vec![]));
        script.push(Tactic::Omega);
    }
}

// ---------------------------------------------------------------------------
// Formula analysis helpers
// ---------------------------------------------------------------------------

/// Check if a formula involves only arithmetic operations (for `ring` tactic).
fn formula_is_arithmetic(formula: &Formula) -> bool {
    match formula {
        Formula::Eq(lhs, rhs) => is_arith_term(lhs) && is_arith_term(rhs),
        _ => false,
    }
}

/// Check if a term is purely arithmetic.
fn is_arith_term(formula: &Formula) -> bool {
    match formula {
        Formula::Int(_) => true,
        Formula::Var(_, Sort::Int) => true,
        Formula::Add(a, b) | Formula::Sub(a, b) | Formula::Mul(a, b) => {
            is_arith_term(a) && is_arith_term(b)
        }
        Formula::Neg(inner) => is_arith_term(inner),
        _ => false,
    }
}

/// Check if a formula is decidable (can use `decide` tactic).
fn formula_is_decidable(formula: &Formula) -> bool {
    match formula {
        Formula::Bool(_) => true,
        Formula::Eq(lhs, rhs) => is_ground_term(lhs) && is_ground_term(rhs),
        Formula::Not(inner) => formula_is_decidable(inner),
        Formula::And(children) | Formula::Or(children) => children.iter().all(formula_is_decidable),
        _ => false,
    }
}

/// Check if a formula involves only linear arithmetic (for `omega` tactic).
fn formula_is_linear_arithmetic(formula: &Formula) -> bool {
    match formula {
        Formula::Le(a, b)
        | Formula::Lt(a, b)
        | Formula::Ge(a, b)
        | Formula::Gt(a, b)
        | Formula::Eq(a, b) => is_linear_term(a) && is_linear_term(b),
        Formula::And(children) | Formula::Or(children) => {
            children.iter().all(formula_is_linear_arithmetic)
        }
        Formula::Not(inner) => formula_is_linear_arithmetic(inner),
        Formula::Implies(lhs, rhs) => {
            formula_is_linear_arithmetic(lhs) && formula_is_linear_arithmetic(rhs)
        }
        _ => false,
    }
}

/// Check if a term is linear (no multiplication of variables).
fn is_linear_term(formula: &Formula) -> bool {
    match formula {
        Formula::Int(_) => true,
        Formula::Var(_, Sort::Int) => true,
        Formula::Add(a, b) | Formula::Sub(a, b) => is_linear_term(a) && is_linear_term(b),
        Formula::Mul(a, b) => {
            // Linear if at least one side is a constant
            matches!(a.as_ref(), Formula::Int(_)) || matches!(b.as_ref(), Formula::Int(_))
        }
        Formula::Neg(inner) => is_linear_term(inner),
        _ => false,
    }
}

/// Check if a term contains no free variables (ground term).
fn is_ground_term(formula: &Formula) -> bool {
    match formula {
        Formula::Bool(_) | Formula::Int(_) | Formula::BitVec { .. } => true,
        Formula::Var(_, _) => false,
        Formula::Not(inner) | Formula::Neg(inner) => is_ground_term(inner),
        Formula::And(children) | Formula::Or(children) => children.iter().all(is_ground_term),
        Formula::Add(a, b)
        | Formula::Sub(a, b)
        | Formula::Mul(a, b)
        | Formula::Div(a, b)
        | Formula::Rem(a, b)
        | Formula::Eq(a, b)
        | Formula::Lt(a, b)
        | Formula::Le(a, b)
        | Formula::Gt(a, b)
        | Formula::Ge(a, b)
        | Formula::Implies(a, b) => is_ground_term(a) && is_ground_term(b),
        Formula::Ite(c, t, e) => is_ground_term(c) && is_ground_term(t) && is_ground_term(e),
        _ => false,
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

    fn div_by_zero_vc() -> VerificationCondition {
        VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: "safe_div".into(),
            location: SourceSpan::default(),
            formula: Formula::Not(Box::new(Formula::Eq(
                Box::new(Formula::Var("divisor".into(), Sort::Int)),
                Box::new(Formula::Int(0)),
            ))),
            contract_metadata: None,
            obligation: None,
        }
    }

    fn overflow_vc() -> VerificationCondition {
        VerificationCondition {
            kind: VcKind::ArithmeticOverflow {
                op: BinOp::Add,
                operand_tys: (Ty::usize(), Ty::usize()),
            },
            function: "get_midpoint".into(),
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

    fn assertion_vc() -> VerificationCondition {
        VerificationCondition {
            kind: VcKind::Assertion { message: "x > 0".to_string() },
            function: "check_positive".into(),
            location: SourceSpan::default(),
            formula: Formula::Gt(
                Box::new(Formula::Var("x".into(), Sort::Int)),
                Box::new(Formula::Int(0)),
            ),
            contract_metadata: None,
            obligation: None,
        }
    }

    fn forall_vc() -> VerificationCondition {
        VerificationCondition {
            kind: VcKind::Postcondition,
            function: "sorted_insert".into(),
            location: SourceSpan::default(),
            formula: Formula::Forall(
                vec![("i".into(), Sort::Int)],
                Box::new(Formula::Le(
                    Box::new(Formula::Var("i".into(), Sort::Int)),
                    Box::new(Formula::Int(100)),
                )),
            ),
            contract_metadata: None,
            obligation: None,
        }
    }

    // -----------------------------------------------------------------------
    // Tactic::to_lean_code
    // -----------------------------------------------------------------------

    #[test]
    fn test_tactic_intro_to_lean_code() {
        assert_eq!(Tactic::Intro("x".to_string()).to_lean_code(), "intro x");
    }

    #[test]
    fn test_tactic_apply_to_lean_code() {
        assert_eq!(Tactic::Apply("And.intro".to_string()).to_lean_code(), "apply And.intro");
    }

    #[test]
    fn test_tactic_exact_to_lean_code() {
        assert_eq!(Tactic::Exact("rfl".to_string()).to_lean_code(), "exact rfl");
    }

    #[test]
    fn test_tactic_rewrite_to_lean_code() {
        assert_eq!(Tactic::Rewrite("h_eq".to_string()).to_lean_code(), "rewrite [h_eq]");
    }

    #[test]
    fn test_tactic_simp_empty_to_lean_code() {
        assert_eq!(Tactic::Simp(vec![]).to_lean_code(), "simp");
    }

    #[test]
    fn test_tactic_simp_with_lemmas_to_lean_code() {
        assert_eq!(
            Tactic::Simp(vec!["h1".to_string(), "h2".to_string()]).to_lean_code(),
            "simp [h1, h2]"
        );
    }

    #[test]
    fn test_tactic_omega_to_lean_code() {
        assert_eq!(Tactic::Omega.to_lean_code(), "omega");
    }

    #[test]
    fn test_tactic_decide_to_lean_code() {
        assert_eq!(Tactic::Decide.to_lean_code(), "decide");
    }

    #[test]
    fn test_tactic_cases_to_lean_code() {
        assert_eq!(Tactic::Cases("h".to_string()).to_lean_code(), "cases h");
    }

    #[test]
    fn test_tactic_induction_no_pattern_to_lean_code() {
        assert_eq!(
            Tactic::Induction { var: "n".to_string(), pattern: None }.to_lean_code(),
            "induction n"
        );
    }

    #[test]
    fn test_tactic_induction_with_pattern_to_lean_code() {
        assert_eq!(
            Tactic::Induction { var: "n".to_string(), pattern: Some("ih".to_string()) }
                .to_lean_code(),
            "induction n with ih"
        );
    }

    #[test]
    fn test_tactic_ring_to_lean_code() {
        assert_eq!(Tactic::Ring.to_lean_code(), "ring");
    }

    #[test]
    fn test_tactic_linarith_to_lean_code() {
        assert_eq!(Tactic::Linarith.to_lean_code(), "linarith");
    }

    // -----------------------------------------------------------------------
    // TacticScript
    // -----------------------------------------------------------------------

    #[test]
    fn test_tactic_script_new_is_empty() {
        let script = TacticScript::new("test");
        assert!(script.is_empty());
        assert_eq!(script.len(), 0);
    }

    #[test]
    fn test_tactic_script_push() {
        let mut script = TacticScript::new("test");
        script.push(Tactic::Intro("x".to_string()));
        script.push(Tactic::Omega);
        assert!(!script.is_empty());
        assert_eq!(script.len(), 2);
    }

    #[test]
    fn test_tactic_script_to_lean_code() {
        let mut script = TacticScript::new("my_theorem");
        script.push(Tactic::Intro("h".to_string()));
        script.push(Tactic::Simp(vec![]));
        script.push(Tactic::Omega);

        let code = script.to_lean_code();
        assert!(code.starts_with("theorem my_theorem := by\n"));
        assert!(code.contains("  intro h\n"));
        assert!(code.contains("  simp\n"));
        assert!(code.contains("  omega\n"));
    }

    // -----------------------------------------------------------------------
    // generate_tactic_script — division by zero
    // -----------------------------------------------------------------------

    #[test]
    fn test_generate_tactic_script_div_by_zero() {
        let vc = div_by_zero_vc();
        let script = generate_tactic_script(&vc);

        assert!(!script.is_empty(), "div-by-zero script should not be empty");
        assert_eq!(script.theorem_name, "Trust.vc.safe_div");

        let code = script.to_lean_code();
        assert!(code.contains("theorem Trust.vc.safe_div := by"));
        // Should contain simp for div definition
        assert!(code.contains("simp"), "div-by-zero should use simp, got:\n{code}");
    }

    // -----------------------------------------------------------------------
    // generate_tactic_script — arithmetic overflow
    // -----------------------------------------------------------------------

    #[test]
    fn test_generate_tactic_script_overflow() {
        let vc = overflow_vc();
        let script = generate_tactic_script(&vc);

        assert!(!script.is_empty());
        assert_eq!(script.theorem_name, "Trust.vc.get_midpoint");

        let code = script.to_lean_code();
        // Overflow VCs involve linear arithmetic
        assert!(
            code.contains("linarith") || code.contains("omega"),
            "overflow should use linarith or omega, got:\n{code}"
        );
    }

    // -----------------------------------------------------------------------
    // generate_tactic_script — assertion
    // -----------------------------------------------------------------------

    #[test]
    fn test_generate_tactic_script_assertion() {
        let vc = assertion_vc();
        let script = generate_tactic_script(&vc);

        assert!(!script.is_empty());
        let code = script.to_lean_code();
        // Inequality assertion should get linarith
        assert!(
            code.contains("linarith") || code.contains("omega"),
            "assertion with Gt should use linarith or omega, got:\n{code}"
        );
    }

    // -----------------------------------------------------------------------
    // generate_tactic_script — forall
    // -----------------------------------------------------------------------

    #[test]
    fn test_generate_tactic_script_forall() {
        let vc = forall_vc();
        let script = generate_tactic_script(&vc);

        assert!(!script.is_empty());
        let code = script.to_lean_code();
        // Should introduce the quantified variable
        assert!(code.contains("intro i"), "forall VC should introduce variable, got:\n{code}");
    }

    // -----------------------------------------------------------------------
    // Formula analysis helpers
    // -----------------------------------------------------------------------

    #[test]
    fn test_formula_is_decidable_bool() {
        assert!(formula_is_decidable(&Formula::Bool(true)));
        assert!(formula_is_decidable(&Formula::Bool(false)));
    }

    #[test]
    fn test_formula_is_decidable_ground_eq() {
        let formula = Formula::Eq(Box::new(Formula::Int(1)), Box::new(Formula::Int(2)));
        assert!(formula_is_decidable(&formula));
    }

    #[test]
    fn test_formula_is_decidable_with_var() {
        let formula =
            Formula::Eq(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(0)));
        assert!(!formula_is_decidable(&formula), "formula with variable should not be decidable");
    }

    #[test]
    fn test_formula_is_linear_arithmetic() {
        let formula = Formula::Le(
            Box::new(Formula::Add(
                Box::new(Formula::Var("x".into(), Sort::Int)),
                Box::new(Formula::Int(1)),
            )),
            Box::new(Formula::Int(10)),
        );
        assert!(formula_is_linear_arithmetic(&formula));
    }

    #[test]
    fn test_formula_is_arithmetic_ring_eq() {
        let formula = Formula::Eq(
            Box::new(Formula::Mul(
                Box::new(Formula::Var("a".into(), Sort::Int)),
                Box::new(Formula::Var("b".into(), Sort::Int)),
            )),
            Box::new(Formula::Mul(
                Box::new(Formula::Var("b".into(), Sort::Int)),
                Box::new(Formula::Var("a".into(), Sort::Int)),
            )),
        );
        assert!(formula_is_arithmetic(&formula));
    }

    #[test]
    fn test_is_ground_term() {
        assert!(is_ground_term(&Formula::Int(42)));
        assert!(is_ground_term(&Formula::Bool(true)));
        assert!(!is_ground_term(&Formula::Var("x".into(), Sort::Int)));
        assert!(is_ground_term(&Formula::Add(
            Box::new(Formula::Int(1)),
            Box::new(Formula::Int(2)),
        )));
    }

    // -----------------------------------------------------------------------
    // sanitize_name
    // -----------------------------------------------------------------------

    #[test]
    fn test_sanitize_name_simple() {
        assert_eq!(sanitize_name("foo_bar"), "foo_bar");
    }

    #[test]
    fn test_sanitize_name_with_special_chars() {
        assert_eq!(sanitize_name("foo::bar<T>"), "foo__bar_T_");
    }

    // -----------------------------------------------------------------------
    // implies VC
    // -----------------------------------------------------------------------

    #[test]
    fn test_generate_tactic_script_implies() {
        let vc = VerificationCondition {
            kind: VcKind::Postcondition,
            function: "ensure_post".into(),
            location: SourceSpan::default(),
            formula: Formula::Implies(Box::new(Formula::Bool(true)), Box::new(Formula::Bool(true))),
            contract_metadata: None,
            obligation: None,
        };
        let script = generate_tactic_script(&vc);
        let code = script.to_lean_code();
        // Should introduce the hypothesis
        assert!(code.contains("intro h"), "implies should introduce hypothesis, got:\n{code}");
    }

    // -----------------------------------------------------------------------
    // Decidable formula (ground boolean)
    // -----------------------------------------------------------------------

    #[test]
    fn test_generate_tactic_script_decidable_ground() {
        let vc = VerificationCondition {
            kind: VcKind::Assertion { message: "trivial".to_string() },
            function: "trivial_check".into(),
            location: SourceSpan::default(),
            formula: Formula::Eq(Box::new(Formula::Int(1)), Box::new(Formula::Int(1))),
            contract_metadata: None,
            obligation: None,
        };
        let script = generate_tactic_script(&vc);
        let code = script.to_lean_code();
        assert!(code.contains("decide"), "ground equality should use decide, got:\n{code}");
    }

    // -----------------------------------------------------------------------
    // New tactic variants — to_lean_code
    // -----------------------------------------------------------------------

    #[test]
    fn test_tactic_norm_num_to_lean_code() {
        assert_eq!(Tactic::NormNum.to_lean_code(), "norm_num");
    }

    #[test]
    fn test_tactic_ring_nf_to_lean_code() {
        assert_eq!(Tactic::RingNf.to_lean_code(), "ring_nf");
    }

    #[test]
    fn test_tactic_constructor_to_lean_code() {
        assert_eq!(Tactic::Constructor.to_lean_code(), "constructor");
    }

    #[test]
    fn test_tactic_contradiction_to_lean_code() {
        assert_eq!(Tactic::Contradiction.to_lean_code(), "contradiction");
    }

    #[test]
    fn test_tactic_rcases_to_lean_code() {
        let t = Tactic::Rcases { expr: "h".into(), pattern: "⟨a, b⟩".into() };
        assert_eq!(t.to_lean_code(), "rcases h with ⟨a, b⟩");
    }

    #[test]
    fn test_tactic_obtain_to_lean_code() {
        let t = Tactic::Obtain { pattern: "⟨x, hx⟩".into(), expr: "h".into() };
        assert_eq!(t.to_lean_code(), "obtain ⟨x, hx⟩ := h");
    }

    #[test]
    fn test_tactic_have_to_lean_code() {
        let t = Tactic::Have { name: "h1".into(), ty: "x > 0".into(), proof: "by omega".into() };
        assert_eq!(t.to_lean_code(), "have h1 : x > 0 := by omega");
    }

    #[test]
    fn test_tactic_suffices_to_lean_code() {
        let t = Tactic::Suffices { name: "h".into(), ty: "n > 0".into() };
        assert_eq!(t.to_lean_code(), "suffices h : n > 0");
    }

    #[test]
    fn test_tactic_focus_to_lean_code() {
        let t = Tactic::Focus(vec![Tactic::Simp(vec![]), Tactic::Omega]);
        assert_eq!(t.to_lean_code(), "· simp omega");
    }

    #[test]
    fn test_tactic_all_goals_to_lean_code() {
        let t = Tactic::AllGoals(Box::new(Tactic::Simp(vec![])));
        assert_eq!(t.to_lean_code(), "all_goals simp");
    }

    #[test]
    fn test_tactic_first_to_lean_code() {
        let t = Tactic::First(vec![Tactic::Ring, Tactic::Omega, Tactic::Decide]);
        assert_eq!(t.to_lean_code(), "first | ring | omega | decide");
    }

    #[test]
    fn test_tactic_repeat_to_lean_code() {
        let t = Tactic::Repeat(Box::new(Tactic::Simp(vec![])));
        assert_eq!(t.to_lean_code(), "repeat simp");
    }

    // -----------------------------------------------------------------------
    // Tactic classification and cost
    // -----------------------------------------------------------------------

    #[test]
    fn test_tactic_is_arithmetic() {
        assert!(Tactic::Omega.is_arithmetic());
        assert!(Tactic::Linarith.is_arithmetic());
        assert!(Tactic::NormNum.is_arithmetic());
        assert!(Tactic::Ring.is_arithmetic());
        assert!(Tactic::RingNf.is_arithmetic());
        assert!(!Tactic::Intro("x".into()).is_arithmetic());
        assert!(!Tactic::Cases("h".into()).is_arithmetic());
    }

    #[test]
    fn test_tactic_is_case_analysis() {
        assert!(Tactic::Cases("h".into()).is_case_analysis());
        assert!(Tactic::Rcases { expr: "h".into(), pattern: "p".into() }.is_case_analysis());
        assert!(Tactic::Obtain { pattern: "p".into(), expr: "h".into() }.is_case_analysis());
        assert!(!Tactic::Omega.is_case_analysis());
    }

    #[test]
    fn test_tactic_estimated_cost_ordering() {
        // Exact/Decide should be cheapest
        assert!(Tactic::Exact("rfl".into()).estimated_cost() <= Tactic::Omega.estimated_cost());
        // Omega should be cheaper than Cases
        assert!(Tactic::Omega.estimated_cost() <= Tactic::Cases("h".into()).estimated_cost());
        // Induction should be most expensive among simple tactics
        let ind = Tactic::Induction { var: "n".into(), pattern: None };
        assert!(ind.estimated_cost() >= Tactic::Cases("h".into()).estimated_cost());
    }

    // -----------------------------------------------------------------------
    // compose_tactics
    // -----------------------------------------------------------------------

    #[test]
    fn test_compose_tactics_empty() {
        let result = compose_tactics("thm", &[]);
        assert!(result.is_empty());
        assert_eq!(result.theorem_name, "thm");
    }

    #[test]
    fn test_compose_tactics_single() {
        let mut s1 = TacticScript::new("s1");
        s1.push(Tactic::Omega);
        let result = compose_tactics("composed", &[s1]);
        assert_eq!(result.len(), 1);
        assert_eq!(result.tactics[0], Tactic::Omega);
    }

    #[test]
    fn test_compose_tactics_multiple() {
        let mut s1 = TacticScript::new("s1");
        s1.push(Tactic::Intro("x".into()));
        let mut s2 = TacticScript::new("s2");
        s2.push(Tactic::Simp(vec![]));
        s2.push(Tactic::Omega);
        let result = compose_tactics("composed", &[s1, s2]);
        assert_eq!(result.len(), 3);
        assert_eq!(result.tactics[0], Tactic::Intro("x".into()));
        assert_eq!(result.tactics[1], Tactic::Simp(vec![]));
        assert_eq!(result.tactics[2], Tactic::Omega);
    }

    // -----------------------------------------------------------------------
    // Strategy builders
    // -----------------------------------------------------------------------

    #[test]
    fn test_arithmetic_strategy_generates_valid_lean() {
        let script = arithmetic_strategy("arith_thm");
        let code = script.to_lean_code();
        assert!(code.contains("theorem arith_thm := by"));
        assert!(code.contains("simp"));
        assert!(code.contains("first"));
        assert!(code.contains("norm_num"));
        assert!(code.contains("omega"));
    }

    #[test]
    fn test_induction_strategy_no_pattern() {
        let script = induction_strategy("ind_thm", "n", None);
        let code = script.to_lean_code();
        assert!(code.contains("intro n"));
        assert!(code.contains("induction n"));
        // Should have focused blocks for base and inductive cases
        let tactic_count = script.len();
        assert!(
            tactic_count >= 4,
            "induction strategy should have >= 4 tactics, got {tactic_count}"
        );
    }

    #[test]
    fn test_induction_strategy_with_pattern() {
        let script = induction_strategy("ind_thm", "n", Some("| zero => | succ ih =>"));
        let code = script.to_lean_code();
        assert!(code.contains("induction n with | zero => | succ ih =>"));
    }

    #[test]
    fn test_case_split_strategy_generates_valid_lean() {
        let script = case_split_strategy("case_thm", "h");
        let code = script.to_lean_code();
        assert!(code.contains("cases h"));
        assert!(code.contains("all_goals"));
    }

    // -----------------------------------------------------------------------
    // TacticScript::total_cost and extend
    // -----------------------------------------------------------------------

    #[test]
    fn test_tactic_script_total_cost() {
        let mut script = TacticScript::new("test");
        script.push(Tactic::Intro("x".into())); // cost 2
        script.push(Tactic::Omega); // cost 3
        assert_eq!(script.total_cost(), 5);
    }

    #[test]
    fn test_tactic_script_extend() {
        let mut s1 = TacticScript::new("base");
        s1.push(Tactic::Intro("x".into()));
        let mut s2 = TacticScript::new("extra");
        s2.push(Tactic::Omega);
        s1.extend(&s2);
        assert_eq!(s1.len(), 2);
        assert_eq!(s1.theorem_name, "base"); // keeps original name
    }
}
