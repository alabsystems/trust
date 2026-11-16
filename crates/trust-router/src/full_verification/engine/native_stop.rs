//! Preserve reviewed structural stops across the built-in native BMC dispatch boundary.

use trust_verifier_api::{
    EngineKind, EvidenceStatus, NATIVE_PRE_SOLVE_INPUT_REFUSAL_DIAGNOSTIC,
    NATIVE_REFUTATION_FIDELITY_DEMOTION_DIAGNOSTIC, ObligationEvidence,
    ROUTED_NATIVE_PRE_SOLVE_INPUT_REFUSAL_DIAGNOSTIC,
    ROUTED_NATIVE_REFUTATION_FIDELITY_DEMOTION_DIAGNOSTIC,
};

pub(super) fn qualify_native_stops(
    evidence: &mut [ObligationEvidence],
    built_in_native_mc_batch: bool,
) {
    for row in evidence {
        // This flag is derived from the actual built-in native call, before
        // generic-primary fallback and before the composite rewrites identity.
        // A generic engine cannot qualify a copied diagnostic, even if its
        // manifest claims the native producer's name.
        let raw_claim_count = row
            .diagnostics
            .iter()
            .filter(|diagnostic| {
                matches!(
                    diagnostic.as_str(),
                    NATIVE_PRE_SOLVE_INPUT_REFUSAL_DIAGNOSTIC
                        | NATIVE_REFUTATION_FIDELITY_DEMOTION_DIAGNOSTIC
                )
            })
            .count();
        let has_qualified_claim = row.diagnostics.iter().any(|diagnostic| {
            matches!(
                diagnostic.as_str(),
                ROUTED_NATIVE_PRE_SOLVE_INPUT_REFUSAL_DIAGNOSTIC
                    | ROUTED_NATIVE_REFUTATION_FIDELITY_DEMOTION_DIAGNOSTIC
            )
        });
        let pre_solve =
            row.diagnostics.iter().any(|claim| claim == NATIVE_PRE_SOLVE_INPUT_REFUSAL_DIAGNOSTIC);
        let qualify = built_in_native_mc_batch
            && row.engine.name == "trust-mc"
            && row.engine.kind == EngineKind::Reachability
            && row.status == EvidenceStatus::Unsupported
            && row.proof_strength.is_none()
            && row.artifacts.is_empty()
            && row.counterexample.is_none()
            && row.decline.is_none()
            // Incoming qualification is never producer authority. Require one
            // raw claim, no duplicate/other phase and no copied qualification.
            && raw_claim_count == 1
            && !has_qualified_claim;
        row.diagnostics.retain(|d| {
            d != NATIVE_PRE_SOLVE_INPUT_REFUSAL_DIAGNOSTIC
                && d != ROUTED_NATIVE_PRE_SOLVE_INPUT_REFUSAL_DIAGNOSTIC
                && d != NATIVE_REFUTATION_FIDELITY_DEMOTION_DIAGNOSTIC
                && d != ROUTED_NATIVE_REFUTATION_FIDELITY_DEMOTION_DIAGNOSTIC
        });
        if qualify {
            row.diagnostics.push(
                if pre_solve {
                    ROUTED_NATIVE_PRE_SOLVE_INPUT_REFUSAL_DIAGNOSTIC
                } else {
                    ROUTED_NATIVE_REFUTATION_FIDELITY_DEMOTION_DIAGNOSTIC
                }
                .to_string(),
            );
        }
    }
}

#[cfg(test)]
mod tests {
    use trust_verifier_api::{
        API_VERSION, EngineManifest, EvidencePublicationMetadata, ProofStrength,
    };

    use super::*;

    fn evidence() -> ObligationEvidence {
        ObligationEvidence {
            evidence_id: "row-evidence".into(),
            obligation_id: "row".into(),
            engine: EngineManifest::new("trust-mc", API_VERSION, EngineKind::Reachability),
            status: EvidenceStatus::Unsupported,
            decline: None,
            proof_strength: None,
            artifacts: Vec::new(),
            counterexample: None,
            publication: EvidencePublicationMetadata::default(),
            diagnostics: vec![NATIVE_PRE_SOLVE_INPUT_REFUSAL_DIAGNOSTIC.into()],
        }
    }

    #[test]
    fn pre_solve_stop_relay_requires_builtin_native_dispatch_and_exact_child() {
        let mut row = evidence();
        qualify_native_stops(std::slice::from_mut(&mut row), true);
        assert_eq!(row.diagnostics, [ROUTED_NATIVE_PRE_SOLVE_INPUT_REFUSAL_DIAGNOSTIC]);
        assert_eq!(row.status, EvidenceStatus::Unsupported);
        assert!(row.proof_strength.is_none() && row.artifacts.is_empty() && row.decline.is_none());

        for (builtin, engine, kind) in [
            (false, "trust-mc", EngineKind::Reachability),
            (true, "unrelated-engine", EngineKind::Reachability),
            (true, "trust-mc", EngineKind::Composite),
        ] {
            let mut row = evidence();
            row.engine.name = engine.into();
            row.engine.kind = kind;
            // A pre-qualified lookalike is also stripped on every incoming row.
            row.diagnostics.push(ROUTED_NATIVE_PRE_SOLVE_INPUT_REFUSAL_DIAGNOSTIC.into());
            qualify_native_stops(std::slice::from_mut(&mut row), builtin);
            assert!(row.diagnostics.is_empty(), "foreign producer or dispatch retained a marker");
        }
    }

    #[test]
    fn pre_solve_stop_relay_rejects_proved_rejected_and_prequalified_rows() {
        for status in [EvidenceStatus::Proved, EvidenceStatus::Unknown, EvidenceStatus::Timeout] {
            let mut row = evidence();
            row.status = status;
            qualify_native_stops(std::slice::from_mut(&mut row), true);
            assert!(row.diagnostics.is_empty());
        }
        let mut rejected = evidence();
        rejected.proof_strength = Some(ProofStrength::smt_unsat());
        qualify_native_stops(std::slice::from_mut(&mut rejected), true);
        assert!(rejected.diagnostics.is_empty());
        let mut copied = evidence();
        copied.diagnostics = vec![ROUTED_NATIVE_PRE_SOLVE_INPUT_REFUSAL_DIAGNOSTIC.into()];
        qualify_native_stops(std::slice::from_mut(&mut copied), true);
        assert!(copied.diagnostics.is_empty());
    }
    #[test]
    fn completed_refutation_demotion_relay_is_separate_and_requires_actual_native_dispatch() {
        let raw = NATIVE_REFUTATION_FIDELITY_DEMOTION_DIAGNOSTIC;
        let qualified = ROUTED_NATIVE_REFUTATION_FIDELITY_DEMOTION_DIAGNOSTIC;
        let mut row = evidence();
        row.diagnostics = vec![raw.into()];
        qualify_native_stops(std::slice::from_mut(&mut row), true);
        assert_eq!(row.diagnostics, [qualified]);
        assert_eq!(row.status, EvidenceStatus::Unsupported);
        assert!(row.proof_strength.is_none() && row.artifacts.is_empty() && row.decline.is_none());

        for (builtin, engine, kind, status) in [
            (false, "trust-mc", EngineKind::Reachability, EvidenceStatus::Unsupported),
            (true, "foreign", EngineKind::Reachability, EvidenceStatus::Unsupported),
            (true, "trust-mc", EngineKind::Composite, EvidenceStatus::Unsupported),
            (true, "trust-mc", EngineKind::Reachability, EvidenceStatus::Unknown),
            (true, "trust-mc", EngineKind::Reachability, EvidenceStatus::Timeout),
            (true, "trust-mc", EngineKind::Reachability, EvidenceStatus::Proved),
        ] {
            let mut row = evidence();
            row.engine.name = engine.into();
            row.engine.kind = kind;
            row.status = status;
            row.diagnostics = vec![raw.into(), qualified.into()];
            qualify_native_stops(std::slice::from_mut(&mut row), builtin);
            assert!(row.diagnostics.is_empty());
        }
        for diagnostics in [
            vec![qualified.into()],
            vec![raw.into(), NATIVE_PRE_SOLVE_INPUT_REFUSAL_DIAGNOSTIC.into()],
        ] {
            let mut row = evidence();
            row.diagnostics = diagnostics;
            qualify_native_stops(std::slice::from_mut(&mut row), true);
            assert!(row.diagnostics.is_empty(), "copied or contradictory phase must not qualify");
        }
        let mut row = evidence();
        row.diagnostics = vec![raw.into()];
        row.proof_strength = Some(ProofStrength::smt_unsat());
        qualify_native_stops(std::slice::from_mut(&mut row), true);
        assert!(row.diagnostics.is_empty(), "rejected proof candidates are not source demotions");
    }
    #[test]
    fn native_stop_relay_rejects_every_duplicate_or_prequalified_claim_set() {
        let claims = [
            NATIVE_PRE_SOLVE_INPUT_REFUSAL_DIAGNOSTIC,
            NATIVE_REFUTATION_FIDELITY_DEMOTION_DIAGNOSTIC,
            ROUTED_NATIVE_PRE_SOLVE_INPUT_REFUSAL_DIAGNOSTIC,
            ROUTED_NATIVE_REFUTATION_FIDELITY_DEMOTION_DIAGNOSTIC,
        ];
        for first in claims {
            for second in claims {
                let mut row = evidence();
                row.diagnostics = vec![first.into(), second.into()];
                qualify_native_stops(std::slice::from_mut(&mut row), true);
                assert!(
                    row.diagnostics.is_empty(),
                    "invalid incoming claim set: {first}; {second}"
                );
            }
        }
    }
}
