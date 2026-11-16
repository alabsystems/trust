//! The final consumer predicate for reviewed native structural stop claims.

use crate::{
    API_VERSION, EngineKind, EvidenceStatus, NATIVE_PRE_SOLVE_INPUT_REFUSAL_DIAGNOSTIC,
    NATIVE_REFUTATION_FIDELITY_DEMOTION_DIAGNOSTIC, ObligationEvidence,
    ROUTED_NATIVE_PRE_SOLVE_INPUT_REFUSAL_DIAGNOSTIC,
    ROUTED_NATIVE_REFUTATION_FIDELITY_DEMOTION_DIAGNOSTIC,
};

/// A reviewed structural explanation for an unproved native row.
/// This grants no proof, counterexample, retry or execution authority.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NativeStructuralStop {
    /// Native instruction input refused before solver dispatch.
    PreSolveInputRefusal,
    /// Completed refutation withheld by the source-fidelity gate.
    CompletedRefutationFidelityDemotion,
}

/// Recognize exactly one router-qualified claim on a clean Unsupported row
/// from the current built-in composite. Raw, duplicated or conflicting
/// claims cannot recover a cause. Callers must still combine any existing
/// clock/resource/unclassified stop, rather than replacing it with this cause.
#[must_use]
pub fn qualified_native_structural_stop(
    evidence: &ObligationEvidence,
) -> Option<NativeStructuralStop> {
    if evidence.status != EvidenceStatus::Unsupported
        || evidence.engine.name != "trust-full-verifier"
        || evidence.engine.kind != EngineKind::Composite
        || evidence.engine.version != API_VERSION
        || evidence.engine.api_version != API_VERSION
        || evidence.engine.repository.is_some()
        || evidence.engine.revision.is_some()
        || evidence.proof_strength.is_some()
        || !evidence.artifacts.is_empty()
        || evidence.counterexample.is_some()
        || evidence.decline.is_some()
    {
        return None;
    }
    let mut stop = None;
    for diagnostic in &evidence.diagnostics {
        let claim = match diagnostic.as_str() {
            ROUTED_NATIVE_PRE_SOLVE_INPUT_REFUSAL_DIAGNOSTIC => {
                NativeStructuralStop::PreSolveInputRefusal
            }
            ROUTED_NATIVE_REFUTATION_FIDELITY_DEMOTION_DIAGNOSTIC => {
                NativeStructuralStop::CompletedRefutationFidelityDemotion
            }
            NATIVE_PRE_SOLVE_INPUT_REFUSAL_DIAGNOSTIC
            | NATIVE_REFUTATION_FIDELITY_DEMOTION_DIAGNOSTIC => return None,
            _ => continue,
        };
        if stop.replace(claim).is_some() {
            return None;
        }
    }
    stop
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        ArtifactHash, Counterexample, DeclineClass, EngineManifest, EvidenceArtifact,
        EvidenceArtifactKind, EvidencePublicationMetadata, ProofStrength,
    };

    fn evidence(marker: &str) -> ObligationEvidence {
        ObligationEvidence {
            evidence_id: "row-evidence".into(),
            obligation_id: "row".into(),
            engine: EngineManifest::new("trust-full-verifier", API_VERSION, EngineKind::Composite),
            status: EvidenceStatus::Unsupported,
            decline: None,
            proof_strength: None,
            artifacts: Vec::new(),
            counterexample: None,
            publication: EvidencePublicationMetadata::default(),
            diagnostics: vec![marker.into()],
        }
    }

    #[test]
    fn native_stop_consumer_accepts_only_one_distinct_qualified_phase() {
        for (marker, expected) in [
            (
                ROUTED_NATIVE_PRE_SOLVE_INPUT_REFUSAL_DIAGNOSTIC,
                NativeStructuralStop::PreSolveInputRefusal,
            ),
            (
                ROUTED_NATIVE_REFUTATION_FIDELITY_DEMOTION_DIAGNOSTIC,
                NativeStructuralStop::CompletedRefutationFidelityDemotion,
            ),
        ] {
            let mut row = evidence(marker);
            row.diagnostics.push("ordinary diagnostic, not a protocol claim".into());
            assert_eq!(qualified_native_structural_stop(&row), Some(expected));
        }
        let markers = [
            NATIVE_PRE_SOLVE_INPUT_REFUSAL_DIAGNOSTIC,
            NATIVE_REFUTATION_FIDELITY_DEMOTION_DIAGNOSTIC,
            ROUTED_NATIVE_PRE_SOLVE_INPUT_REFUSAL_DIAGNOSTIC,
            ROUTED_NATIVE_REFUTATION_FIDELITY_DEMOTION_DIAGNOSTIC,
        ];
        // Every raw/qualified pair, including duplicate and mixed-phase claims,
        // must refuse. The real producer/relay emits exactly one claim.
        for first in markers {
            for second in markers {
                let mut row = evidence(first);
                row.diagnostics.push(second.into());
                assert_eq!(qualified_native_structural_stop(&row), None, "{first}; {second}");
            }
        }
        for marker in [
            "",
            NATIVE_PRE_SOLVE_INPUT_REFUSAL_DIAGNOSTIC,
            NATIVE_REFUTATION_FIDELITY_DEMOTION_DIAGNOSTIC,
        ] {
            assert_eq!(qualified_native_structural_stop(&evidence(marker)), None);
        }
    }

    #[test]
    fn native_stop_consumer_rejects_proof_counterexample_and_retry_payloads() {
        for marker in [
            ROUTED_NATIVE_PRE_SOLVE_INPUT_REFUSAL_DIAGNOSTIC,
            ROUTED_NATIVE_REFUTATION_FIDELITY_DEMOTION_DIAGNOSTIC,
        ] {
            let original = evidence(marker);
            let mut cases = Vec::new();
            let mut row = original.clone();
            row.proof_strength = Some(ProofStrength::smt_unsat());
            cases.push(row);
            let mut row = original.clone();
            row.artifacts.push(EvidenceArtifact {
                kind: EvidenceArtifactKind::ProofCertificate,
                uri: "artifact://candidate".into(),
                hash: ArtifactHash { algorithm: "sha256".into(), value: "00".repeat(32) },
                materialization: None,
            });
            cases.push(row);
            let mut row = original.clone();
            row.counterexample =
                Some(Counterexample { format: "json".into(), data: serde_json::json!({"x": 0}) });
            cases.push(row);
            let mut row = original;
            row.decline = Some(DeclineClass::Capability);
            cases.push(row);
            for row in cases {
                assert_eq!(qualified_native_structural_stop(&row), None);
            }
        }
    }

    #[test]
    fn native_stop_consumer_rejects_wrong_identity_status_and_lookalikes() {
        let marker = ROUTED_NATIVE_REFUTATION_FIDELITY_DEMOTION_DIAGNOSTIC;
        let original = evidence(marker);
        let mut cases = Vec::new();
        for status in [
            EvidenceStatus::Proved,
            EvidenceStatus::Failed,
            EvidenceStatus::Unknown,
            EvidenceStatus::Timeout,
            EvidenceStatus::Canceled,
        ] {
            let mut row = original.clone();
            row.status = status;
            cases.push(row);
        }
        let mut row = original.clone();
        row.engine.name = "trust-mc".into();
        cases.push(row);
        let mut row = original.clone();
        row.engine.kind = EngineKind::Reachability;
        cases.push(row);
        let mut row = original.clone();
        row.engine.version = "foreign-version".into();
        cases.push(row);
        let mut row = original.clone();
        row.engine.api_version = "foreign-api".into();
        cases.push(row);
        let mut row = original.clone();
        row.engine.repository = Some("foreign".into());
        cases.push(row);
        let mut row = original.clone();
        row.engine.revision = Some("foreign".into());
        cases.push(row);
        let mut row = original;
        row.diagnostics = vec![format!("{marker} lookalike")];
        cases.push(row);
        for row in cases {
            assert_eq!(qualified_native_structural_stop(&row), None);
        }
    }
}
