// trust-clean/certification/generation.rs: Proof term generation from solver proofs
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::{Formula, VerificationCondition};

use super::types::{ProofGeneration, ProofTheory};
use crate::logic_classification::{
    CertificationScope, SmtLogic, classify_formula, degradation_strategy, is_certifiable,
    scope_from_logic,
};
#[cfg(test)]
use crate::reconstruction::LeanProofTerm;
use crate::reconstruction::{ProofStep, SolverProof, reconstruct};

// ---------------------------------------------------------------------------
// Trust: Proof term generation from solver proofs
// ---------------------------------------------------------------------------

/// Trust: Generate a clean proof term from a solver proof, classified by theory.
///
/// This is the entry point for theory-aware proof generation. It:
/// 1. Classifies the formula into an SMT logic fragment
/// 2. Returns `Unsupported` if the logic is not certifiable
/// 3. Reconstructs a clean proof term using the reconstruction pipeline
/// 4. Tags the result with the appropriate theory
///
/// Supports QF_LIA, QF_UF, and QF_LIA+UF theories.
pub fn generate_proof_term(
    vc: &VerificationCondition,
    solver_proof: &SolverProof,
) -> ProofGeneration {
    // Step 1: Classify the formula
    let logic = classify_formula(&vc.formula);
    let strategy = degradation_strategy(&logic);

    // Step 2: Determine theory and certifiability
    let theory = match &logic {
        SmtLogic::QfLia => ProofTheory::QfLia,
        SmtLogic::QfUf => ProofTheory::QfUf,
        SmtLogic::QfLiaUf => ProofTheory::QfLiaUf,
        other => {
            let reason = if strategy.is_none() {
                format!("logic {} has no certification strategy", other.name())
            } else {
                format!("logic {} only has partial certification support", other.name())
            };
            return ProofGeneration::Unsupported { logic: other.clone(), reason };
        }
    };

    // Step 3: Reconstruct the clean proof term
    match reconstruct(solver_proof, vc) {
        Ok(term) => ProofGeneration::Generated { proof_term: term, theory },
        Err(e) => ProofGeneration::Failed { reason: format!("{e}") },
    }
}

/// Trust: Build a QF_LIA axiom step for linear integer arithmetic facts.
///
/// Constructs a `ProofStep::Axiom` from a QF_LIA formula. This is used
/// to build solver proofs for integer arithmetic obligations like:
/// - `x + y >= 0` (non-negativity)
/// - `a != 0` (division-by-zero guard)
/// - `x < MAX` (overflow guard)
#[must_use]
pub fn qf_lia_axiom(name: &str, formula: Formula) -> ProofStep {
    ProofStep::Axiom { name: name.to_string(), formula }
}

/// Trust: Build a QF_UF axiom step for uninterpreted function / equality facts.
///
/// Constructs a `ProofStep::Axiom` from a QF_UF formula. This is used
/// to build solver proofs for equality reasoning like:
/// - `a = b` (congruence)
/// - `f(a) = f(b)` when `a = b`
/// - Boolean combinations of equalities
#[must_use]
pub fn qf_uf_axiom(name: &str, formula: Formula) -> ProofStep {
    ProofStep::Axiom { name: name.to_string(), formula }
}

/// Trust: Serialize a `LeanProofTerm` to bytes for use as a certificate payload.
///
/// Uses a compact JSON representation since `LeanProofTerm` is our intermediate
/// form (not a clean-kernel `ProofCert`). The serialized bytes are stored in the
/// certificate's `proof_term` field.
#[cfg(test)]
#[must_use]
pub(crate) fn serialize_lean_proof_term(term: &LeanProofTerm) -> Vec<u8> {
    // Trust: Use debug format as a stable serialization for our intermediate form.
    // This is sufficient for Trusted certificates. For Certified certificates,
    // the clean-kernel ProofCert serialization is used instead (via bincode).
    format!("{term:?}").into_bytes()
}

/// Trust: Classify a VC's formula and determine if it can be certified.
///
/// Returns `(logic, is_certifiable)` — a convenience wrapper over
/// `classify_formula` and `is_certifiable` for callers that just
/// need a quick yes/no plus the logic.
#[must_use]
pub fn classify_vc_for_certification(vc: &VerificationCondition) -> (SmtLogic, bool) {
    let logic = classify_formula(&vc.formula);
    let certifiable = is_certifiable(&logic);
    (logic, certifiable)
}

/// Classify a VC and return the full certification scope.
///
/// Returns `(logic, scope)` — a richer version of `classify_vc_for_certification`
/// that tells callers exactly what level of certification is available and why.
#[must_use]
pub fn classify_vc_scope(vc: &VerificationCondition) -> (SmtLogic, CertificationScope) {
    let logic = classify_formula(&vc.formula);
    let scope = scope_from_logic(&logic);
    (logic, scope)
}
