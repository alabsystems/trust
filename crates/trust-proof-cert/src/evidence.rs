// trust-proof-cert/evidence.rs: Derive non-authoritative evidence from public records
//
// Maps raw solver proof certificates (e.g., LRAT from ay) into
// the trust-types ProofEvidence type, combining reasoning kind with assurance
// level based on certificate validation status.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::{ProofEvidence, ProofStrength};

#[cfg(test)]
use trust_types::{AssuranceLevel, ReasoningKind};

/// Derive non-authoritative `ProofEvidence` from a public result record.
///
/// Public `ProofStrength` values are constructible and deserializable, including
/// strengths that report certified assurance. This function therefore caps
/// assurance at SMT-backed even when no raw certificate bytes are present. The
/// old behavior capped only `Some(nonempty_bytes)`, so a caller could obtain
/// `Certified` simply by passing a certified strength with `None`.
#[must_use]
pub fn evidence_from_unchecked_record(strength: &ProofStrength) -> ProofEvidence {
    cap_unvalidated_certificate_assurance(strength.clone().into())
}

pub(crate) fn cap_unvalidated_certificate_assurance(mut evidence: ProofEvidence) -> ProofEvidence {
    // R-U Phase C (grade migration): gate and mint through the grade record;
    // verdict-identical on the from_legacy image (is_certified ⇔ Certified,
    // smt_backed().to_legacy() == SmtBacked — both pinned in trust-types).
    if evidence.grade().is_certified() {
        evidence.assurance = trust_types::grade::GradeRecord::smt_backed().to_legacy();
    }
    evidence
}

/// Classify the reasoning kind from a solver name string.
///
/// Maps known solver identifiers to their corresponding `ReasoningKind`.
#[cfg(test)]
#[must_use]
fn reasoning_from_solver(solver: &str) -> ReasoningKind {
    match solver {
        "ay" => ReasoningKind::Smt,
        "trust-mc" => ReasoningKind::BoundedModelCheck { depth: 0 },
        "trust-wp" => ReasoningKind::Deductive,
        "trust-vc" => ReasoningKind::OwnershipAnalysis,
        "clean" => ReasoningKind::Constructive,
        "ty" => ReasoningKind::ExplicitStateModel,
        "ny" => ReasoningKind::NeuralBounding,
        _ => ReasoningKind::Smt,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_evidence_from_unchecked_record() {
        let strength = ProofStrength::smt_unsat();
        let evidence = evidence_from_unchecked_record(&strength);
        assert_eq!(evidence.reasoning, ReasoningKind::Smt);
        assert_eq!(evidence.assurance, AssuranceLevel::SmtBacked);
    }

    #[test]
    fn test_unvalidated_certificate_caps_certified_strength() {
        let strength = ProofStrength::smt_unsat_certified();
        let evidence = evidence_from_unchecked_record(&strength);
        assert_eq!(evidence.reasoning, ReasoningKind::Smt);
        assert_eq!(evidence.assurance, AssuranceLevel::SmtBacked);
    }

    #[test]
    fn test_certified_strength_without_bytes_is_still_capped() {
        let evidence = evidence_from_unchecked_record(&ProofStrength::smt_unsat_certified());
        assert_ne!(evidence.assurance, AssuranceLevel::Certified);
        assert_eq!(evidence.assurance, AssuranceLevel::SmtBacked);
    }

    #[test]
    fn test_reasoning_from_solver_known() {
        assert_eq!(reasoning_from_solver("ay"), ReasoningKind::Smt);
        assert_eq!(reasoning_from_solver("trust-wp"), ReasoningKind::Deductive);
        assert_eq!(reasoning_from_solver("clean"), ReasoningKind::Constructive);
        assert_eq!(reasoning_from_solver("ny"), ReasoningKind::NeuralBounding);
    }

    #[test]
    fn test_reasoning_from_solver_unknown_defaults_to_smt() {
        assert_eq!(reasoning_from_solver("unknown-solver"), ReasoningKind::Smt);
    }
}
