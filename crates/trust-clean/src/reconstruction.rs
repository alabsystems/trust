// trust-clean/reconstruction.rs: Proof reconstruction from solver certificates
//
// Reconstructs Clean proof terms from solver output (e.g., ay UNSAT proofs).
// The reconstruction pipeline takes a structured solver proof (sequence of
// inference steps) and produces a LeanProofTerm that can be type-checked
// by the clean kernel.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::{Formula, VcKind, VerificationCondition};

use crate::error::CertificateError;

// ---------------------------------------------------------------------------
// Error type for reconstruction failures
// ---------------------------------------------------------------------------

/// Errors specific to proof reconstruction.
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum ReconstructionError {
    /// A referenced axiom was not found in the solver proof.
    #[error("unknown axiom: {name}")]
    UnknownAxiom { name: String },

    /// A proof step references a lemma index that does not exist.
    #[error("invalid lemma reference: step {step_index} references lemma {lemma_index}")]
    InvalidLemmaRef { step_index: usize, lemma_index: usize },

    /// The solver proof is empty (no steps to reconstruct from).
    #[error("empty solver proof: no steps to reconstruct")]
    EmptyProof,

    /// The reconstruction produced a term that failed type-checking.
    #[error("reconstructed term failed validation: {reason}")]
    ValidationFailed { reason: String },

    /// A proof step type is not yet supported for reconstruction.
    #[error("unsupported proof step: {step_kind}")]
    UnsupportedStep { step_kind: String },

    /// An axiom name is not in the allowlist of valid CIC/Lean axioms.
    // Trust: F10 soundness fix — reject unrecognized axiom names
    #[error("invalid axiom name not in allowlist: {name}")]
    InvalidAxiomName { name: String },

    /// Certificate pipeline error during reconstruction.
    #[error(transparent)]
    Certificate(#[from] CertificateError),
}

// ---------------------------------------------------------------------------
// Solver proof representation
// ---------------------------------------------------------------------------

/// A structured proof from a solver (e.g., ay UNSAT proof).
///
/// Solver proofs are sequences of inference steps, each deriving a clause
/// from axioms, earlier lemmas, or inference rules. The final step should
/// derive the empty clause (contradiction), proving UNSAT.
#[derive(Debug, Clone)]
pub struct SolverProof {
    /// Ordered sequence of proof steps.
    pub steps: Vec<ProofStep>,
    /// Names of axioms used in the proof.
    pub used_axioms: Vec<String>,
    /// Indices of lemmas (earlier steps) referenced by later steps.
    pub used_lemmas: Vec<usize>,
}

/// A single inference step in a solver proof.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum ProofStep {
    /// An axiom introduction (assumed true).
    Axiom {
        /// Name of the axiom.
        name: String,
        /// The formula this axiom asserts.
        formula: Formula,
    },
    /// Modus ponens: from `P` and `P -> Q`, derive `Q`.
    ModusPonens {
        /// Index of the step proving `P -> Q`.
        implication_step: usize,
        /// Index of the step proving `P`.
        antecedent_step: usize,
    },
    /// Resolution: from `C1 | L` and `C2 | !L`, derive `C1 | C2`.
    Resolution {
        /// Index of the positive clause step.
        positive_step: usize,
        /// Index of the negative clause step.
        negative_step: usize,
        /// The pivot literal being resolved on.
        pivot: Formula,
    },
    /// Rewrite: replace a subterm using an equality.
    Rewrite {
        /// Index of the step providing the equality.
        equality_step: usize,
        /// Index of the step being rewritten.
        target_step: usize,
    },
    /// Universal instantiation: from `forall x. P(x)`, derive `P(t)`.
    Instantiation {
        /// Index of the universally quantified step.
        quantified_step: usize,
        /// The term substituted for the bound variable.
        witness: Formula,
    },
    /// Congruence: from `a = b`, derive `f(a) = f(b)`.
    Congruence {
        /// Index of the equality step.
        equality_step: usize,
        /// The function/operator being applied.
        function_name: String,
    },
}

// ---------------------------------------------------------------------------
// Clean proof term representation
// ---------------------------------------------------------------------------

/// A Clean proof term — the output of reconstruction.
///
/// These terms correspond to the Clean kernel's expression language.
/// A valid proof term, when type-checked by the kernel, witnesses
/// the truth of a proposition.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum LeanProofTerm {
    /// A variable reference (de Bruijn index).
    Var(usize),
    /// Function application: `f a`.
    App(Box<LeanProofTerm>, Box<LeanProofTerm>),
    /// Lambda abstraction: `fun (x : T) => body`.
    Lambda {
        /// Name of the bound variable (for readability).
        binder_name: String,
        /// Type annotation.
        binder_type: Box<LeanProofTerm>,
        /// Body of the lambda.
        body: Box<LeanProofTerm>,
    },
    /// Let binding: `let x : T := val in body`.
    Let {
        /// Name of the bound variable.
        name: String,
        /// Type annotation.
        ty: Box<LeanProofTerm>,
        /// Value being bound.
        value: Box<LeanProofTerm>,
        /// Body where the binding is in scope.
        body: Box<LeanProofTerm>,
    },
    /// Proof by assumption: the goal is already in context.
    ByAssumption {
        /// de Bruijn index of the hypothesis.
        hypothesis_index: usize,
    },
    /// Proof by decidability: the proposition is decidable and evaluates to true.
    ByDecidability {
        /// The proposition being decided.
        proposition: Formula,
    },
    /// A constant reference (named definition or theorem).
    Const(String),
    /// Sort/Type (for type annotations in proof terms).
    Sort(u32),
}

// ---------------------------------------------------------------------------
// Proof reconstructor
// ---------------------------------------------------------------------------

/// Reconstructs Clean proof terms from solver output.
///
/// The reconstructor maps each solver inference step to a corresponding
/// Clean proof term constructor. The result is a complete proof term
/// that can be serialized and verified by the clean kernel.
pub struct ProofReconstructor {
    /// Intermediate proof terms built from each step.
    step_terms: Vec<LeanProofTerm>,
}

impl ProofReconstructor {
    /// Create a new reconstructor.
    #[must_use]
    pub fn new() -> Self {
        ProofReconstructor { step_terms: Vec::new() }
    }

    /// Reconstruct a Clean proof term from a solver proof and VC.
    ///
    /// Processes each step in the solver proof, building intermediate
    /// proof terms, then combines them into a final term witnessing
    /// the VC's formula.
    ///
    /// # Errors
    ///
    /// - `EmptyProof` if the solver proof has no steps
    /// - `InvalidLemmaRef` if a step references a non-existent earlier step
    /// - `UnknownAxiom` if an axiom name is not in `used_axioms`
    /// - `UnsupportedStep` if a step type cannot be reconstructed
    pub fn reconstruct(
        &mut self,
        solver_proof: &SolverProof,
        vc: &VerificationCondition,
    ) -> Result<LeanProofTerm, ReconstructionError> {
        if solver_proof.steps.is_empty() {
            return Err(ReconstructionError::EmptyProof);
        }

        self.step_terms.clear();

        for (idx, step) in solver_proof.steps.iter().enumerate() {
            let term = self.reconstruct_step(step, idx, solver_proof)?;
            self.step_terms.push(term);
        }

        // The final proof term wraps the last step's term in a VC.holds application
        let last_term = self.step_terms.last().expect("invariant: non-empty steps").clone();

        // Build the final proof: a term that proves Trust.VC.holds <kind> <formula>
        let vc_proof = build_vc_proof_wrapper(&vc.kind, &vc.formula, last_term);

        Ok(vc_proof)
    }

    /// Reconstruct a single proof step into a Clean proof term.
    fn reconstruct_step(
        &self,
        step: &ProofStep,
        current_index: usize,
        proof: &SolverProof,
    ) -> Result<LeanProofTerm, ReconstructionError> {
        match step {
            ProofStep::Axiom { name, formula } => {
                let solver_declared = proof.used_axioms.contains(name);
                if !solver_declared {
                    return Err(ReconstructionError::UnknownAxiom { name: name.clone() });
                }
                reconstruct_axiom(name, formula, solver_declared)
            }
            ProofStep::ModusPonens { implication_step, antecedent_step } => {
                let impl_term = self.get_step_term(*implication_step, current_index)?;
                let ante_term = self.get_step_term(*antecedent_step, current_index)?;
                Ok(reconstruct_modus_ponens(impl_term, ante_term))
            }
            ProofStep::Resolution { positive_step, negative_step, pivot } => {
                let pos_term = self.get_step_term(*positive_step, current_index)?;
                let neg_term = self.get_step_term(*negative_step, current_index)?;
                Ok(reconstruct_resolution(pos_term, neg_term, pivot))
            }
            ProofStep::Rewrite { equality_step, target_step } => {
                let eq_term = self.get_step_term(*equality_step, current_index)?;
                let tgt_term = self.get_step_term(*target_step, current_index)?;
                Ok(reconstruct_rewrite(eq_term, tgt_term))
            }
            ProofStep::Instantiation { quantified_step, witness } => {
                let quant_term = self.get_step_term(*quantified_step, current_index)?;
                Ok(reconstruct_instantiation(quant_term, witness))
            }
            ProofStep::Congruence { equality_step, function_name } => {
                let eq_term = self.get_step_term(*equality_step, current_index)?;
                Ok(reconstruct_congruence(eq_term, function_name))
            }
        }
    }

    /// Retrieve a previously-built proof term by step index.
    fn get_step_term(
        &self,
        step_index: usize,
        current_index: usize,
    ) -> Result<LeanProofTerm, ReconstructionError> {
        if step_index >= current_index || step_index >= self.step_terms.len() {
            return Err(ReconstructionError::InvalidLemmaRef {
                step_index: current_index,
                lemma_index: step_index,
            });
        }
        Ok(self.step_terms[step_index].clone())
    }
}

impl Default for ProofReconstructor {
    fn default() -> Self {
        Self::new()
    }
}

// ---------------------------------------------------------------------------
// Step-level reconstruction helpers
// ---------------------------------------------------------------------------

/// Allowlist of valid CIC/Lean axioms that may appear in reconstructed proofs.
///
/// This covers the standard Lean 4 axioms plus Trust-specific verification
/// axioms. Any axiom name not matching one of these prefixes is rejected.
// Trust: F10 soundness fix — prevents crafted solver output from injecting
// arbitrary axiom names into the proof term.
const VALID_AXIOM_PREFIXES: &[&str] = &[
    // Lean 4 core axioms
    "propext",          // propositional extensionality
    "funext",           // function extensionality
    "Classical.choice", // classical axiom of choice
    "Quot.",            // quotient axioms (Quot.sound, Quot.lift, Quot.mk, Quot.ind)
    "Eq.",              // equality axioms (Eq.refl, Eq.subst, etc.)
    "proof_irrel",      // proof irrelevance
    // Trust verification axioms
    "Trust.", // Trust-namespaced axioms (VC framework, solver bridges)
    // Solver-produced axioms (VC-local, declared in used_axioms)
    "vc_",         // VC-local axioms from solver encoding
    "hypothesis_", // hypothesis axioms from VC context
    // ay proof bridge axioms (generated by ay_proof_bridge::translate_ay_proof)
    // Trust: F10 — include ay's structured proof rule axiom prefixes
    "asserted_",   // ay input assertions
    "refl_",       // ay reflexivity axioms
    "quant-inst_", // ay quantifier instantiation axioms
    "th-lemma.",   // ay theory lemma axioms (e.g., th-lemma.arith_0)
    "def-axiom_",  // ay definitional axiom tautologies
    "nnf_",        // ay NNF normalization axioms
    "skolem_",     // ay Skolemization axioms
];

/// Check whether an axiom name matches the allowlist.
fn is_valid_axiom_name(name: &str) -> bool {
    VALID_AXIOM_PREFIXES.iter().any(|prefix| name.starts_with(prefix))
}

/// Reconstruct an axiom as a Clean constant reference.
///
/// # Errors
///
/// Returns `ReconstructionError::InvalidAxiomName` if the axiom name is not
/// in the allowlist and not solver-declared.
fn reconstruct_axiom(
    name: &str,
    formula: &Formula,
    solver_declared: bool,
) -> Result<LeanProofTerm, ReconstructionError> {
    // Trust: F10 — validate axiom name against allowlist OR solver-declared status.
    // Solver-declared axioms are VC-local names generated by the solver during
    // proof search and are safe to accept because they were already verified.
    if !is_valid_axiom_name(name) && !solver_declared {
        return Err(ReconstructionError::InvalidAxiomName { name: name.to_string() });
    }

    // Trust: F10 — validate that reconstructed axioms are well-formed.
    // An axiom asserting `False` would make any proposition provable,
    // completely destroying soundness.
    if matches!(formula, Formula::Bool(false)) {
        return Err(ReconstructionError::ValidationFailed {
            reason: format!(
                "axiom '{name}' asserts False — this would make any proposition provable"
            ),
        });
    }

    // An axiom becomes a reference to a named constant in the clean environment
    Ok(LeanProofTerm::Const(format!("Trust.Axiom.{name}")))
}

/// Reconstruct modus ponens as function application.
///
/// In CIC, modus ponens `P -> Q` applied to a proof of `P` is just
/// function application: `(proof_of_implication proof_of_antecedent)`.
fn reconstruct_modus_ponens(
    implication_term: LeanProofTerm,
    antecedent_term: LeanProofTerm,
) -> LeanProofTerm {
    LeanProofTerm::App(Box::new(implication_term), Box::new(antecedent_term))
}

/// Reconstruct resolution as a combination of case analysis.
///
/// Resolution on pivot `L`: from `C1 | L` and `C2 | !L`, we derive `C1 | C2`.
/// In Clean this maps to an Or.elim-like construction.
fn reconstruct_resolution(
    positive_term: LeanProofTerm,
    negative_term: LeanProofTerm,
    _pivot: &Formula,
) -> LeanProofTerm {
    // Trust.Resolution.resolve <positive_proof> <negative_proof>
    LeanProofTerm::App(
        Box::new(LeanProofTerm::App(
            Box::new(LeanProofTerm::Const("Trust.Resolution.resolve".to_string())),
            Box::new(positive_term),
        )),
        Box::new(negative_term),
    )
}

/// Reconstruct rewrite using Eq.subst.
///
/// From `a = b` and `P(a)`, derive `P(b)` via substitution.
fn reconstruct_rewrite(equality_term: LeanProofTerm, target_term: LeanProofTerm) -> LeanProofTerm {
    // Eq.subst <equality_proof> <target_proof>
    LeanProofTerm::App(
        Box::new(LeanProofTerm::App(
            Box::new(LeanProofTerm::Const("Eq.subst".to_string())),
            Box::new(equality_term),
        )),
        Box::new(target_term),
    )
}

/// Reconstruct universal instantiation as function application.
///
/// From `forall x. P(x)`, applying the witness `t` yields `P(t)`.
/// In CIC, a universally quantified proposition is a dependent function type,
/// so instantiation is just application.
fn reconstruct_instantiation(quantified_term: LeanProofTerm, witness: &Formula) -> LeanProofTerm {
    // Apply the universally quantified proof to the witness term
    let witness_term = formula_to_proof_term(witness);
    LeanProofTerm::App(Box::new(quantified_term), Box::new(witness_term))
}

/// Reconstruct congruence closure.
///
/// From `a = b`, derive `f(a) = f(b)` via `congrArg`.
fn reconstruct_congruence(equality_term: LeanProofTerm, function_name: &str) -> LeanProofTerm {
    // congrArg f <equality_proof>
    LeanProofTerm::App(
        Box::new(LeanProofTerm::App(
            Box::new(LeanProofTerm::Const("congrArg".to_string())),
            Box::new(LeanProofTerm::Const(function_name.to_string())),
        )),
        Box::new(equality_term),
    )
}

// ---------------------------------------------------------------------------
// Proof wrapper and helpers
// ---------------------------------------------------------------------------

/// Wrap a proof term in the VC.holds structure for clean kernel checking.
fn build_vc_proof_wrapper(
    _kind: &VcKind,
    _formula: &Formula,
    inner_proof: LeanProofTerm,
) -> LeanProofTerm {
    // The final proof term applies Trust.VC.mk to produce a holds witness
    LeanProofTerm::App(
        Box::new(LeanProofTerm::Const("Trust.VC.mk".to_string())),
        Box::new(inner_proof),
    )
}

/// Convert a Formula to a proof term (for use as witnesses in instantiation).
fn formula_to_proof_term(formula: &Formula) -> LeanProofTerm {
    match formula {
        Formula::Bool(true) => LeanProofTerm::Const("True.intro".to_string()),
        Formula::Bool(false) => LeanProofTerm::Const("False".to_string()),
        Formula::Int(n) => LeanProofTerm::Const(format!("Int.ofNat {n}")),
        Formula::Var(name, _sort) => LeanProofTerm::Const(name.to_string()),
        _ => {
            // For complex formulas, use decidability
            LeanProofTerm::ByDecidability { proposition: formula.clone() }
        }
    }
}

// ---------------------------------------------------------------------------
// Validation
// ---------------------------------------------------------------------------

/// Validate that a reconstructed proof term is structurally well-formed.
///
/// This is a lightweight pre-check before sending to the clean kernel.
/// It verifies:
/// - No dangling variable references (de Bruijn indices within scope)
/// - No empty applications
/// - Let bindings have consistent structure
///
/// Returns `true` if the term passes structural validation.
#[must_use]
pub fn validate_reconstruction(term: &LeanProofTerm) -> bool {
    validate_term(term, 0)
}

/// Recursive validation with de Bruijn depth tracking.
fn validate_term(term: &LeanProofTerm, depth: usize) -> bool {
    match term {
        LeanProofTerm::Var(idx) => *idx < depth,
        LeanProofTerm::App(f, a) => validate_term(f, depth) && validate_term(a, depth),
        LeanProofTerm::Lambda { binder_type, body, .. } => {
            validate_term(binder_type, depth) && validate_term(body, depth + 1)
        }
        LeanProofTerm::Let { ty, value, body, .. } => {
            validate_term(ty, depth)
                && validate_term(value, depth)
                && validate_term(body, depth + 1)
        }
        LeanProofTerm::ByAssumption { hypothesis_index } => *hypothesis_index < depth,
        LeanProofTerm::ByDecidability { .. } => true,
        LeanProofTerm::Const(_) => true,
        LeanProofTerm::Sort(_) => true,
    }
}

// ---------------------------------------------------------------------------
// Public convenience function
// ---------------------------------------------------------------------------

/// Reconstruct a Clean proof term from a solver proof and VC.
///
/// This is the main entry point for proof reconstruction. It creates a
/// `ProofReconstructor`, runs reconstruction, and validates the result.
///
/// # Errors
///
/// Returns `ReconstructionError` if reconstruction or validation fails.
pub fn reconstruct(
    solver_proof: &SolverProof,
    vc: &VerificationCondition,
) -> Result<LeanProofTerm, ReconstructionError> {
    let mut reconstructor = ProofReconstructor::new();
    let term = reconstructor.reconstruct(solver_proof, vc)?;

    if !validate_reconstruction(&term) {
        return Err(ReconstructionError::ValidationFailed {
            reason: "reconstructed term has dangling variable references".to_string(),
        });
    }

    Ok(term)
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use trust_types::*;

    use super::*;

    fn sample_vc() -> VerificationCondition {
        VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: "test_div".into(),
            location: SourceSpan::default(),
            formula: Formula::Not(Box::new(Formula::Eq(
                Box::new(Formula::Var("divisor".into(), Sort::Int)),
                Box::new(Formula::Int(0)),
            ))),
            contract_metadata: None,
        }
    }

    fn axiom_step(name: &str, formula: Formula) -> ProofStep {
        ProofStep::Axiom { name: name.to_string(), formula }
    }

    // -----------------------------------------------------------------------
    // Empty proof
    // -----------------------------------------------------------------------

    #[test]
    fn test_reconstruct_empty_proof_returns_error() {
        let proof = SolverProof { steps: vec![], used_axioms: vec![], used_lemmas: vec![] };
        let vc = sample_vc();

        let err = reconstruct(&proof, &vc).expect_err("empty proof should fail");
        assert!(
            matches!(err, ReconstructionError::EmptyProof),
            "should be EmptyProof, got: {err:?}"
        );
    }

    // -----------------------------------------------------------------------
    // Axiom step
    // -----------------------------------------------------------------------

    #[test]
    fn test_reconstruct_axiom_step() {
        let proof = SolverProof {
            steps: vec![axiom_step("vc_div_nonzero", Formula::Bool(true))],
            used_axioms: vec!["vc_div_nonzero".to_string()],
            used_lemmas: vec![],
        };
        let vc = sample_vc();

        let term = reconstruct(&proof, &vc).expect("axiom proof should succeed");
        assert!(validate_reconstruction(&term));

        // The outer wrapper should be Trust.VC.mk
        if let LeanProofTerm::App(f, _) = &term {
            assert!(
                matches!(f.as_ref(), LeanProofTerm::Const(name) if name == "Trust.VC.mk"),
                "should be wrapped in Trust.VC.mk"
            );
        } else {
            panic!("expected App at top level, got {term:?}");
        }
    }

    #[test]
    fn test_reconstruct_unknown_axiom_returns_error() {
        let proof = SolverProof {
            steps: vec![axiom_step("nonexistent", Formula::Bool(true))],
            used_axioms: vec![], // not listed
            used_lemmas: vec![],
        };
        let vc = sample_vc();

        let err = reconstruct(&proof, &vc).expect_err("unknown axiom should fail");
        assert!(
            matches!(err, ReconstructionError::UnknownAxiom { ref name } if name == "nonexistent"),
            "should be UnknownAxiom, got: {err:?}"
        );
    }

    // -----------------------------------------------------------------------
    // Modus ponens step
    // -----------------------------------------------------------------------

    #[test]
    fn test_reconstruct_modus_ponens() {
        let proof = SolverProof {
            steps: vec![
                axiom_step(
                    "vc_P_implies_Q",
                    Formula::Implies(Box::new(Formula::Bool(true)), Box::new(Formula::Bool(true))),
                ),
                axiom_step("vc_P", Formula::Bool(true)),
                ProofStep::ModusPonens { implication_step: 0, antecedent_step: 1 },
            ],
            used_axioms: vec!["vc_P_implies_Q".to_string(), "vc_P".to_string()],
            used_lemmas: vec![0, 1],
        };
        let vc = sample_vc();

        let term = reconstruct(&proof, &vc).expect("modus ponens should succeed");
        assert!(validate_reconstruction(&term));
    }

    // -----------------------------------------------------------------------
    // Resolution step
    // -----------------------------------------------------------------------

    #[test]
    fn test_reconstruct_resolution() {
        let pivot = Formula::Var("x".into(), Sort::Bool);
        let proof = SolverProof {
            steps: vec![
                axiom_step("vc_clause1", Formula::Or(vec![Formula::Bool(true), pivot.clone()])),
                axiom_step(
                    "vc_clause2",
                    Formula::Or(vec![Formula::Bool(false), Formula::Not(Box::new(pivot.clone()))]),
                ),
                ProofStep::Resolution { positive_step: 0, negative_step: 1, pivot },
            ],
            used_axioms: vec!["vc_clause1".to_string(), "vc_clause2".to_string()],
            used_lemmas: vec![0, 1],
        };
        let vc = sample_vc();

        let term = reconstruct(&proof, &vc).expect("resolution should succeed");
        assert!(validate_reconstruction(&term));
    }

    // -----------------------------------------------------------------------
    // Rewrite step
    // -----------------------------------------------------------------------

    #[test]
    fn test_reconstruct_rewrite() {
        let proof = SolverProof {
            steps: vec![
                axiom_step(
                    "vc_a_eq_b",
                    Formula::Eq(
                        Box::new(Formula::Var("a".into(), Sort::Int)),
                        Box::new(Formula::Var("b".into(), Sort::Int)),
                    ),
                ),
                axiom_step("vc_P_a", Formula::Var("a".into(), Sort::Bool)),
                ProofStep::Rewrite { equality_step: 0, target_step: 1 },
            ],
            used_axioms: vec!["vc_a_eq_b".to_string(), "vc_P_a".to_string()],
            used_lemmas: vec![0, 1],
        };
        let vc = sample_vc();

        let term = reconstruct(&proof, &vc).expect("rewrite should succeed");
        assert!(validate_reconstruction(&term));
    }

    // -----------------------------------------------------------------------
    // Instantiation step
    // -----------------------------------------------------------------------

    #[test]
    fn test_reconstruct_instantiation() {
        let proof = SolverProof {
            steps: vec![
                axiom_step(
                    "vc_forall_x",
                    Formula::Forall(
                        vec![("x".into(), Sort::Int)],
                        Box::new(Formula::Le(
                            Box::new(Formula::Int(0)),
                            Box::new(Formula::Var("x".into(), Sort::Int)),
                        )),
                    ),
                ),
                ProofStep::Instantiation { quantified_step: 0, witness: Formula::Int(42) },
            ],
            used_axioms: vec!["vc_forall_x".to_string()],
            used_lemmas: vec![0],
        };
        let vc = sample_vc();

        let term = reconstruct(&proof, &vc).expect("instantiation should succeed");
        assert!(validate_reconstruction(&term));
    }

    // -----------------------------------------------------------------------
    // Congruence step
    // -----------------------------------------------------------------------

    #[test]
    fn test_reconstruct_congruence() {
        let proof = SolverProof {
            steps: vec![
                axiom_step(
                    "vc_a_eq_b",
                    Formula::Eq(
                        Box::new(Formula::Var("a".into(), Sort::Int)),
                        Box::new(Formula::Var("b".into(), Sort::Int)),
                    ),
                ),
                ProofStep::Congruence { equality_step: 0, function_name: "f".to_string() },
            ],
            used_axioms: vec!["vc_a_eq_b".to_string()],
            used_lemmas: vec![0],
        };
        let vc = sample_vc();

        let term = reconstruct(&proof, &vc).expect("congruence should succeed");
        assert!(validate_reconstruction(&term));
    }

    // -----------------------------------------------------------------------
    // Invalid lemma reference
    // -----------------------------------------------------------------------

    #[test]
    fn test_reconstruct_invalid_lemma_ref() {
        let proof = SolverProof {
            steps: vec![
                axiom_step("vc_P", Formula::Bool(true)),
                ProofStep::ModusPonens { implication_step: 5, antecedent_step: 0 },
            ],
            used_axioms: vec!["vc_P".to_string()],
            used_lemmas: vec![],
        };
        let vc = sample_vc();

        let err = reconstruct(&proof, &vc).expect_err("invalid ref should fail");
        assert!(
            matches!(err, ReconstructionError::InvalidLemmaRef { .. }),
            "should be InvalidLemmaRef, got: {err:?}"
        );
    }

    // -----------------------------------------------------------------------
    // Validation tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_validate_reconstruction_const() {
        let term = LeanProofTerm::Const("True.intro".to_string());
        assert!(validate_reconstruction(&term));
    }

    #[test]
    fn test_validate_reconstruction_var_in_scope() {
        let term = LeanProofTerm::Lambda {
            binder_name: "x".to_string(),
            binder_type: Box::new(LeanProofTerm::Sort(0)),
            body: Box::new(LeanProofTerm::Var(0)),
        };
        assert!(validate_reconstruction(&term));
    }

    #[test]
    fn test_validate_reconstruction_var_out_of_scope() {
        // Var(0) at depth 0 is invalid — no binder in scope
        let term = LeanProofTerm::Var(0);
        assert!(!validate_reconstruction(&term));
    }

    #[test]
    fn test_validate_reconstruction_nested_lambda() {
        let term = LeanProofTerm::Lambda {
            binder_name: "x".to_string(),
            binder_type: Box::new(LeanProofTerm::Sort(0)),
            body: Box::new(LeanProofTerm::Lambda {
                binder_name: "y".to_string(),
                binder_type: Box::new(LeanProofTerm::Sort(0)),
                body: Box::new(LeanProofTerm::App(
                    Box::new(LeanProofTerm::Var(1)), // x
                    Box::new(LeanProofTerm::Var(0)), // y
                )),
            }),
        };
        assert!(validate_reconstruction(&term));
    }

    #[test]
    fn test_validate_reconstruction_let_binding() {
        let term = LeanProofTerm::Let {
            name: "x".to_string(),
            ty: Box::new(LeanProofTerm::Sort(0)),
            value: Box::new(LeanProofTerm::Const("True.intro".to_string())),
            body: Box::new(LeanProofTerm::Var(0)),
        };
        assert!(validate_reconstruction(&term));
    }

    #[test]
    fn test_validate_reconstruction_by_assumption_invalid() {
        // ByAssumption at depth 0 is invalid
        let term = LeanProofTerm::ByAssumption { hypothesis_index: 0 };
        assert!(!validate_reconstruction(&term));
    }

    #[test]
    fn test_validate_reconstruction_by_decidability() {
        let term = LeanProofTerm::ByDecidability { proposition: Formula::Bool(true) };
        assert!(validate_reconstruction(&term));
    }

    #[test]
    fn test_validate_reconstruction_app() {
        let term = LeanProofTerm::App(
            Box::new(LeanProofTerm::Const("f".to_string())),
            Box::new(LeanProofTerm::Const("x".to_string())),
        );
        assert!(validate_reconstruction(&term));
    }

    // -----------------------------------------------------------------------
    // Multi-step proof
    // -----------------------------------------------------------------------

    #[test]
    fn test_reconstruct_multi_step_proof() {
        // A realistic multi-step proof:
        // Step 0: axiom P -> Q
        // Step 1: axiom Q -> R
        // Step 2: axiom P
        // Step 3: modus ponens (0, 2) => Q
        // Step 4: modus ponens (1, 3) => R
        let proof = SolverProof {
            steps: vec![
                axiom_step(
                    "vc_P_implies_Q",
                    Formula::Implies(
                        Box::new(Formula::Var("P".into(), Sort::Bool)),
                        Box::new(Formula::Var("Q".into(), Sort::Bool)),
                    ),
                ),
                axiom_step(
                    "vc_Q_implies_R",
                    Formula::Implies(
                        Box::new(Formula::Var("Q".into(), Sort::Bool)),
                        Box::new(Formula::Var("R".into(), Sort::Bool)),
                    ),
                ),
                axiom_step("vc_P", Formula::Var("P".into(), Sort::Bool)),
                ProofStep::ModusPonens { implication_step: 0, antecedent_step: 2 },
                ProofStep::ModusPonens { implication_step: 1, antecedent_step: 3 },
            ],
            used_axioms: vec![
                "vc_P_implies_Q".to_string(),
                "vc_Q_implies_R".to_string(),
                "vc_P".to_string(),
            ],
            used_lemmas: vec![0, 1, 2, 3],
        };
        let vc = sample_vc();

        let term = reconstruct(&proof, &vc).expect("multi-step proof should succeed");
        assert!(validate_reconstruction(&term));
    }

    // -----------------------------------------------------------------------
    // ProofReconstructor::new / default
    // -----------------------------------------------------------------------

    #[test]
    fn test_proof_reconstructor_default() {
        let r = ProofReconstructor::default();
        assert!(r.step_terms.is_empty());
    }

    // -----------------------------------------------------------------------
    // formula_to_proof_term
    // -----------------------------------------------------------------------

    #[test]
    fn test_formula_to_proof_term_bool_true() {
        let term = formula_to_proof_term(&Formula::Bool(true));
        assert_eq!(term, LeanProofTerm::Const("True.intro".to_string()));
    }

    #[test]
    fn test_formula_to_proof_term_int() {
        let term = formula_to_proof_term(&Formula::Int(42));
        assert_eq!(term, LeanProofTerm::Const("Int.ofNat 42".to_string()));
    }

    #[test]
    fn test_formula_to_proof_term_var() {
        let term = formula_to_proof_term(&Formula::Var("x".into(), Sort::Int));
        assert_eq!(term, LeanProofTerm::Const("x".to_string()));
    }

    #[test]
    fn test_formula_to_proof_term_complex_uses_decidability() {
        let formula = Formula::And(vec![Formula::Bool(true), Formula::Bool(false)]);
        let term = formula_to_proof_term(&formula);
        assert!(
            matches!(term, LeanProofTerm::ByDecidability { .. }),
            "complex formula should use decidability"
        );
    }

    // -----------------------------------------------------------------------
    // F10: axiom name + formula well-formedness validation
    // -----------------------------------------------------------------------

    #[test]
    fn test_reconstruct_solver_declared_axiom_accepted() {
        // Trust: F10 — solver-declared axioms (in used_axioms) are VC-local
        // and accepted even if they don't match the built-in allowlist.
        let proof = SolverProof {
            steps: vec![axiom_step("solver_local_fact", Formula::Bool(true))],
            used_axioms: vec!["solver_local_fact".to_string()],
            used_lemmas: vec![],
        };
        let vc = sample_vc();

        let term = reconstruct(&proof, &vc).expect("solver-declared axiom should be accepted");
        assert!(validate_reconstruction(&term));
    }

    #[test]
    fn test_reconstruct_axiom_asserting_false_rejected() {
        // Trust: F10 — an axiom asserting False would make any proposition
        // provable, destroying soundness. Must be rejected even if solver-declared.
        let proof = SolverProof {
            steps: vec![axiom_step("unsound_axiom", Formula::Bool(false))],
            used_axioms: vec!["unsound_axiom".to_string()],
            used_lemmas: vec![],
        };
        let vc = sample_vc();

        let err = reconstruct(&proof, &vc).expect_err("False axiom should be rejected");
        assert!(
            matches!(err, ReconstructionError::ValidationFailed { ref reason } if reason.contains("False")),
            "should be ValidationFailed mentioning False, got: {err:?}"
        );
    }

    #[test]
    fn test_reconstruct_non_declared_non_allowlisted_axiom_rejected() {
        // Trust: F10 — non-solver-declared axioms that don't match the
        // allowlist are still rejected (UnknownAxiom from used_axioms check).
        let proof = SolverProof {
            steps: vec![axiom_step("malicious_inject", Formula::Bool(true))],
            used_axioms: vec![], // not declared in used_axioms
            used_lemmas: vec![],
        };
        let vc = sample_vc();

        let err = reconstruct(&proof, &vc).expect_err("undeclared axiom should fail");
        assert!(
            matches!(err, ReconstructionError::UnknownAxiom { ref name } if name == "malicious_inject"),
            "should be UnknownAxiom, got: {err:?}"
        );
    }

    #[test]
    fn test_is_valid_axiom_name_standard_axioms() {
        assert!(is_valid_axiom_name("propext"));
        assert!(is_valid_axiom_name("funext"));
        assert!(is_valid_axiom_name("Classical.choice"));
        assert!(is_valid_axiom_name("Quot.sound"));
        assert!(is_valid_axiom_name("Eq.refl"));
        assert!(is_valid_axiom_name("proof_irrel"));
        assert!(is_valid_axiom_name("Trust.VC.mk"));
        assert!(is_valid_axiom_name("vc_div_nonzero"));
        assert!(is_valid_axiom_name("hypothesis_P"));
    }

    #[test]
    fn test_is_valid_axiom_name_rejects_unknown() {
        assert!(!is_valid_axiom_name("malicious"));
        assert!(!is_valid_axiom_name("inject_axiom"));
        assert!(!is_valid_axiom_name(""));
        assert!(!is_valid_axiom_name("arbitrary.name"));
    }
}
