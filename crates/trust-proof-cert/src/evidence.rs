// trust-proof-cert/evidence.rs: Derive non-authoritative evidence from public records
//
// Maps raw solver proof certificates (e.g., LRAT from ay) into
// the trust-types ProofEvidence type, combining reasoning kind with assurance
// level based on certificate validation status.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

#[cfg(test)]
use trust_types::{AssuranceLevel, ReasoningKind};
use trust_types::{ProofEvidence, ProofStrength};

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

pub(crate) fn cap_unvalidated_certificate_assurance(evidence: ProofEvidence) -> ProofEvidence {
    cap_unvalidated_certificate_assurance_carrying(evidence).0
}

/// The carrying form of the assurance cap (2026-08-20 carrier increment): the
/// [`trust_types::grade::GradeRecord`] this site mints no longer collapses to
/// its legacy projection and evaporates — it is RETURNED alongside the capped
/// evidence so the caller can store it on the row
/// ([`crate::generate::VcResultRecord::grade`]) next to the legacy
/// `AssuranceLevel` it projects to.
///
/// * Capped branch (input claimed certified assurance on a no-replay packaging
///   path): the row's standing IS `GradeRecord::smt_backed()` — that record is
///   minted once, drives the legacy downgrade via `.to_legacy()`, and travels.
/// * Uncapped branch: the carried record is the lossless `from_legacy` import
///   of the evidence (`ProofEvidence::grade`) — axes the legacy pair never
///   recorded stay `Unrecorded`, never claims (§7).
///
/// Invariant either way (pinned by `carried_record_projects_to_row_assurance`):
/// the carried record's `to_legacy()` equals the returned evidence's
/// `assurance`, so the typed and legacy fields cannot disagree about standing.
pub(crate) fn cap_unvalidated_certificate_assurance_carrying(
    mut evidence: ProofEvidence,
) -> (ProofEvidence, trust_types::grade::GradeRecord) {
    // R-U Phase C (grade migration): gate and mint through the grade record;
    // verdict-identical on the from_legacy image (is_certified ⇔ Certified,
    // smt_backed().to_legacy() == SmtBacked — both pinned in trust-types).
    if evidence.grade().is_certified() {
        let record = trust_types::grade::GradeRecord::smt_backed();
        evidence.assurance = record.to_legacy();
        return (evidence, record);
    }
    let record = evidence.grade();
    (evidence, record)
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

    /// 2026-08-20 carrier increment: the record the cap mints (or imports)
    /// must PROJECT to exactly the legacy assurance the row carries — the
    /// typed field and the legacy field may never disagree about standing.
    #[test]
    fn carried_record_projects_to_row_assurance() {
        let levels = [
            AssuranceLevel::Sound,
            AssuranceLevel::BoundedSound { depth: 7 },
            AssuranceLevel::Heuristic,
            AssuranceLevel::Unchecked,
            AssuranceLevel::Trusted,
            AssuranceLevel::SmtBacked,
            AssuranceLevel::Certified,
        ];
        for level in levels {
            let evidence = ProofEvidence::new(ReasoningKind::Smt, level);
            let (capped, record) = cap_unvalidated_certificate_assurance_carrying(evidence);
            assert_eq!(
                record.to_legacy(),
                capped.assurance,
                "carried record must project to the row's legacy assurance"
            );
            assert!(!record.is_certified(), "a no-replay packaging path never carries Certified");
        }
    }

    /// The capped branch carries the very record whose projection drives the
    /// downgrade — `GradeRecord::smt_backed()` — instead of discarding it.
    #[test]
    fn capped_certified_input_carries_smt_backed_record() {
        let evidence = ProofEvidence::new(ReasoningKind::Smt, AssuranceLevel::Certified);
        let (capped, record) = cap_unvalidated_certificate_assurance_carrying(evidence);
        assert_eq!(capped.assurance, AssuranceLevel::SmtBacked);
        assert_eq!(record, trust_types::grade::GradeRecord::smt_backed());
    }
}
