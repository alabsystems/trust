// trust-clean/transfer_bridge.rs: Bridge composition DAG to clean proof transfer
//
// Searches the composition DAG for proofs that may transfer to new obligations.
// Transfer results are warm-start hints — every transferred result MUST be
// re-discharged by ay or clean. Transfer results are candidate generation
// and search ordering, not proofs.
//
// Part of #611 (Phase 4: Clean proof transfer integration)
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use serde::{Deserialize, Serialize};
use trust_proof_cert::ProofCertificate;
use trust_proof_cert::composition::ProofComposition;
use trust_types::Formula;

use crate::proof_transfer::{
    Adaptation, LemmaSignature, TransferCandidate, adapt_proof, find_transferable,
};

// ---------------------------------------------------------------------------
// TransferProvenance — audit trail for transfer-based proofs
// ---------------------------------------------------------------------------

/// Records how a proof was informed by transfer from a prior certificate.
///
/// Stored in `ProofCertificate` metadata (not in `CertificateChain`, which
/// has rigid step ordering). The re-verified proof stands on its own —
/// provenance is for audit, not for soundness.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TransferProvenance {
    /// Certificate ID of the source proof that was transferred.
    pub source_cert_id: String,
    /// Function name of the source proof.
    pub source_function: String,
    /// Similarity score between source and target, stored as integer
    /// millionths (e.g., 950000 = 0.95) for `Eq` compatibility.
    pub similarity_millionths: u64,
    /// Adaptations that were applied to make the source proof fit.
    pub adaptations: Vec<String>,
}

// ---------------------------------------------------------------------------
// AdaptedObligation — result of applying a transfer
// ---------------------------------------------------------------------------

/// The result of applying a proof transfer to a target obligation.
///
/// Contains the adapted formula that must still be dispatched to ay for
/// re-verification. The transfer provides search ordering, not soundness.
#[derive(Debug, Clone, PartialEq)]
pub struct AdaptedObligation {
    /// The adapted formula to re-verify.
    pub formula: Formula,
    /// Certificate ID of the source proof.
    pub source_cert_id: String,
    /// Human-readable description of adaptations applied.
    pub adaptations_applied: Vec<String>,
    /// Similarity score that motivated this transfer.
    pub similarity: f64,
}

// ---------------------------------------------------------------------------
// cert_to_lemma_signature — convert a certificate to a LemmaSignature
// ---------------------------------------------------------------------------

/// Convert a [`ProofCertificate`] to a [`LemmaSignature`] for proof transfer.
///
/// Decomposition rules:
/// - `Implies(And([h1, h2, ...]), conclusion)` -> hypotheses=\[h1, h2, ...\], conclusion
/// - `Implies(h, conclusion)` -> hypotheses=\[h\], conclusion
/// - Otherwise: entire formula becomes conclusion, empty hypotheses
///
/// Returns `None` if `formula_json` cannot be deserialized.
#[must_use]
pub fn cert_to_lemma_signature(cert: &ProofCertificate) -> Option<LemmaSignature> {
    let formula: Formula = serde_json::from_str(&cert.vc_snapshot.formula_json).ok()?;

    let (hypotheses, conclusion) = match formula {
        Formula::Implies(lhs, rhs) => match *lhs {
            Formula::And(conjuncts) => (conjuncts, *rhs),
            other => (vec![other], *rhs),
        },
        other => (vec![], other),
    };

    Some(LemmaSignature { name: cert.function.clone(), hypotheses, conclusion })
}

// ---------------------------------------------------------------------------
// find_transfer_candidates — search composition DAG for transferable proofs
// ---------------------------------------------------------------------------

/// Minimum similarity threshold for considering a transfer candidate.
///
/// Kept in sync with `proof_transfer::TRANSFER_THRESHOLD`. Raised from
/// 0.3 to 0.5 per audit finding F17.
#[cfg(test)]
const TRANSFER_THRESHOLD: f64 = 0.5;

/// Search the composition DAG for proofs that may transfer to a new obligation.
///
/// Builds a library of [`LemmaSignature`]s from all certificates in the
/// composition, then delegates to [`find_transferable`] for similarity
/// ranking. Only candidates above the threshold are returned,
/// sorted by descending similarity score.
///
/// `target_function` is the name of the function being verified.
/// `target_formula` is the formula to prove.
/// `target_hypotheses` are the hypotheses (preconditions) of the target.
#[must_use]
pub fn find_transfer_candidates(
    composition: &ProofComposition,
    target_function: &str,
    target_formula: &Formula,
    target_hypotheses: &[Formula],
) -> Vec<TransferCandidate> {
    let target = LemmaSignature {
        name: target_function.to_string(),
        hypotheses: target_hypotheses.to_vec(),
        conclusion: target_formula.clone(),
    };

    // Build library from all certificates in the composition
    let library: Vec<LemmaSignature> = composition
        .functions()
        .iter()
        .filter_map(|func_name| {
            let cert = composition.get_certificate(func_name)?;
            cert_to_lemma_signature(cert)
        })
        .collect();

    find_transferable(&library, &target)
}

/// Search a flat slice of certificates for proofs that may transfer.
///
/// Convenience function for callers that don't have a `ProofComposition`
/// but do have a collection of certificates.
#[must_use]
pub fn find_transfer_candidates_from_certs(
    certs: &[&ProofCertificate],
    target_function: &str,
    target_formula: &Formula,
    target_hypotheses: &[Formula],
) -> Vec<TransferCandidate> {
    let target = LemmaSignature {
        name: target_function.to_string(),
        hypotheses: target_hypotheses.to_vec(),
        conclusion: target_formula.clone(),
    };

    let library: Vec<LemmaSignature> =
        certs.iter().filter_map(|cert| cert_to_lemma_signature(cert)).collect();

    find_transferable(&library, &target)
}

// ---------------------------------------------------------------------------
// apply_transfer — apply a transfer candidate to produce an adapted obligation
// ---------------------------------------------------------------------------

/// Apply a transfer candidate to produce an [`AdaptedObligation`].
///
/// The adapted obligation contains the formula that must be re-dispatched
/// to ay for verification. Transfer does not weaken assurance — the
/// re-verified proof stands on its own.
///
/// Returns `None` if the transfer result is `NoTransfer`.
#[must_use]
pub fn apply_transfer(
    candidate: &TransferCandidate,
    target_formula: &Formula,
    source_cert_id: &str,
) -> Option<AdaptedObligation> {
    let target_sig = LemmaSignature {
        name: String::new(),
        hypotheses: vec![],
        conclusion: target_formula.clone(),
    };

    let result = adapt_proof(&candidate.source, &target_sig);

    match result {
        crate::proof_transfer::TransferResult::DirectApply => Some(AdaptedObligation {
            formula: target_formula.clone(),
            source_cert_id: source_cert_id.to_string(),
            adaptations_applied: vec!["direct_apply".to_string()],
            similarity: candidate.score,
        }),
        crate::proof_transfer::TransferResult::NeedsAdaptation(adaptations) => {
            let descriptions: Vec<String> = adaptations
                .iter()
                .map(|a| match a {
                    Adaptation::Rename { from, to } => format!("rename({from} -> {to})"),
                    Adaptation::Specialize { variable, .. } => {
                        format!("specialize({variable})")
                    }
                    Adaptation::Generalize { variable, .. } => {
                        format!("generalize({variable})")
                    }
                    Adaptation::AddHypothesis { .. } => "add_hypothesis".to_string(),
                })
                .collect();
            Some(AdaptedObligation {
                formula: target_formula.clone(),
                source_cert_id: source_cert_id.to_string(),
                adaptations_applied: descriptions,
                similarity: candidate.score,
            })
        }
        crate::proof_transfer::TransferResult::NoTransfer => None,
    }
}

// ---------------------------------------------------------------------------
// build_transfer_provenance — create provenance from an adapted obligation
// ---------------------------------------------------------------------------

/// Create a [`TransferProvenance`] record from an adapted obligation
/// and the source certificate's function name.
///
/// This provenance should be attached to the new certificate's metadata
/// after the re-verification succeeds.
#[must_use]
pub fn build_transfer_provenance(
    adapted: &AdaptedObligation,
    source_function: &str,
) -> TransferProvenance {
    TransferProvenance {
        source_cert_id: adapted.source_cert_id.clone(),
        source_function: source_function.into(),
        similarity_millionths: (adapted.similarity * 1_000_000.0) as u64,
        adaptations: adapted.adaptations_applied.clone(),
    }
}

// ===========================================================================
// Tests
// ===========================================================================

#[cfg(test)]
mod tests {
    use trust_proof_cert::{FunctionHash, SolverInfo, VcSnapshot};
    use trust_types::{Formula, ProofStrength, Sort, SourceSpan, VcKind, VerificationCondition};

    use super::*;
    use crate::proof_transfer::Adaptation;

    // -----------------------------------------------------------------------
    // Helpers
    // -----------------------------------------------------------------------

    fn var(name: &str) -> Formula {
        Formula::Var(name.to_string(), Sort::Int)
    }

    fn sample_solver() -> SolverInfo {
        SolverInfo {
            name: "ay".to_string(),
            version: "1.0.0".to_string(),
            time_ms: 42,
            strength: ProofStrength::smt_unsat(),
            evidence: None,
        }
    }

    fn sample_vc_with_formula(function: &str, formula: &Formula) -> VerificationCondition {
        VerificationCondition {
            kind: VcKind::Assertion { message: "must hold".to_string() },
            function: function.into(),
            location: SourceSpan {
                file: "src/lib.rs".to_string(),
                line_start: 10,
                col_start: 4,
                line_end: 10,
                col_end: 18,
            },
            formula: formula.clone(),
            contract_metadata: None,
        }
    }

    fn make_cert_with_formula(
        function: &str,
        formula: &Formula,
        timestamp: &str,
    ) -> ProofCertificate {
        let vc = sample_vc_with_formula(function, formula);
        let snapshot = VcSnapshot::from_vc(&vc).expect("snapshot should serialize");
        ProofCertificate::new_trusted(
            function.to_string(),
            FunctionHash::from_bytes(format!("{function}-body").as_bytes()),
            snapshot,
            sample_solver(),
            vec![1, 2, 3, 4],
            timestamp.to_string(),
        )
    }

    // -----------------------------------------------------------------------
    // cert_to_lemma_signature
    // -----------------------------------------------------------------------

    #[test]
    fn test_cert_to_lemma_signature_simple_formula() {
        let formula = Formula::Bool(true);
        let cert = make_cert_with_formula("crate::foo", &formula, "2026-04-12T00:00:00Z");

        let sig = cert_to_lemma_signature(&cert).expect("should parse");
        assert_eq!(sig.name, "crate::foo");
        assert!(sig.hypotheses.is_empty());
        assert_eq!(sig.conclusion, Formula::Bool(true));
    }

    #[test]
    fn test_cert_to_lemma_signature_implies_single_hypothesis() {
        let h = var("x");
        let c = Formula::Bool(true);
        let formula = Formula::Implies(Box::new(h.clone()), Box::new(c.clone()));
        let cert = make_cert_with_formula("crate::bar", &formula, "2026-04-12T00:00:00Z");

        let sig = cert_to_lemma_signature(&cert).expect("should parse");
        assert_eq!(sig.hypotheses, vec![h]);
        assert_eq!(sig.conclusion, c);
    }

    #[test]
    fn test_cert_to_lemma_signature_implies_and_hypotheses() {
        let h1 = var("x");
        let h2 = var("y");
        let c = Formula::Bool(false);
        let formula = Formula::Implies(
            Box::new(Formula::And(vec![h1.clone(), h2.clone()])),
            Box::new(c.clone()),
        );
        let cert = make_cert_with_formula("crate::baz", &formula, "2026-04-12T00:00:00Z");

        let sig = cert_to_lemma_signature(&cert).expect("should parse");
        assert_eq!(sig.hypotheses, vec![h1, h2]);
        assert_eq!(sig.conclusion, c);
    }

    #[test]
    fn test_cert_to_lemma_signature_unparseable_returns_none() {
        let mut cert =
            make_cert_with_formula("crate::bad", &Formula::Bool(true), "2026-04-12T00:00:00Z");
        cert.vc_snapshot.formula_json = "not valid json {{{".to_string();

        assert!(cert_to_lemma_signature(&cert).is_none());
    }

    // -----------------------------------------------------------------------
    // find_transfer_candidates via composition DAG
    // -----------------------------------------------------------------------

    #[test]
    fn test_find_transfer_candidates_empty_composition() {
        let comp = ProofComposition::new();
        let target = Formula::Bool(true);

        let candidates = find_transfer_candidates(&comp, "goal", &target, &[]);
        assert!(candidates.is_empty());
    }

    #[test]
    fn test_find_transfer_candidates_finds_similar() {
        let mut comp = ProofComposition::new();

        // Source: x == 0
        let src_formula = Formula::Eq(Box::new(var("x")), Box::new(Formula::Int(0)));
        let src_cert =
            make_cert_with_formula("crate::source", &src_formula, "2026-04-12T00:00:00Z");
        comp.add_certificate(src_cert, vec![]);

        // Target: y == 0 (same shape, different variable name)
        let target_formula = Formula::Eq(Box::new(var("y")), Box::new(Formula::Int(0)));

        let candidates = find_transfer_candidates(&comp, "crate::target", &target_formula, &[]);
        assert!(!candidates.is_empty(), "should find similar proof");
        assert!(
            candidates[0].score >= TRANSFER_THRESHOLD,
            "score {} should be >= {}",
            candidates[0].score,
            TRANSFER_THRESHOLD
        );
    }

    #[test]
    fn test_find_transfer_candidates_excludes_below_threshold() {
        let mut comp = ProofComposition::new();

        // Source: Bool(true)
        let src_cert =
            make_cert_with_formula("crate::src", &Formula::Bool(true), "2026-04-12T00:00:00Z");
        comp.add_certificate(src_cert, vec![]);

        // Target: completely unrelated formula
        let target_formula = Formula::Eq(
            Box::new(Formula::Add(Box::new(var("a")), Box::new(var("b")))),
            Box::new(Formula::Int(999)),
        );

        let candidates = find_transfer_candidates(&comp, "crate::target", &target_formula, &[]);
        // All candidates (if any) should be above threshold
        for c in &candidates {
            assert!(
                c.score >= TRANSFER_THRESHOLD,
                "candidate score {} should be >= {}",
                c.score,
                TRANSFER_THRESHOLD
            );
        }
    }

    #[test]
    fn test_find_transfer_candidates_sorted_descending() {
        let mut comp = ProofComposition::new();

        // Close match: x == 0
        let close = Formula::Eq(Box::new(var("x")), Box::new(Formula::Int(0)));
        let close_cert = make_cert_with_formula("crate::close", &close, "2026-04-12T00:00:00Z");
        comp.add_certificate(close_cert, vec![]);

        // Distant match: a < b
        let distant = Formula::Lt(Box::new(var("a")), Box::new(var("b")));
        let distant_cert =
            make_cert_with_formula("crate::distant", &distant, "2026-04-12T00:01:00Z");
        comp.add_certificate(distant_cert, vec![]);

        // Target: y == 0
        let target = Formula::Eq(Box::new(var("y")), Box::new(Formula::Int(0)));

        let candidates = find_transfer_candidates(&comp, "crate::target", &target, &[]);
        if candidates.len() >= 2 {
            assert!(
                candidates[0].score >= candidates[1].score,
                "candidates should be sorted by descending score: {} >= {}",
                candidates[0].score,
                candidates[1].score
            );
        }
    }

    // -----------------------------------------------------------------------
    // apply_transfer
    // -----------------------------------------------------------------------

    #[test]
    fn test_apply_transfer_direct_apply() {
        let sig = LemmaSignature {
            name: "source".to_string(),
            hypotheses: vec![],
            conclusion: Formula::Bool(true),
        };
        let candidate = TransferCandidate { source: sig, score: 1.0, required_adaptations: vec![] };
        let target = Formula::Bool(true);

        let adapted = apply_transfer(&candidate, &target, "cert-123");
        assert!(adapted.is_some());
        let adapted = adapted.unwrap();
        assert_eq!(adapted.source_cert_id, "cert-123");
        assert_eq!(adapted.formula, Formula::Bool(true));
        assert!(adapted.adaptations_applied.contains(&"direct_apply".to_string()));
    }

    #[test]
    fn test_apply_transfer_with_rename() {
        let source_sig = LemmaSignature {
            name: "source".to_string(),
            hypotheses: vec![],
            conclusion: Formula::Eq(Box::new(var("x")), Box::new(Formula::Int(0))),
        };
        let candidate = TransferCandidate {
            source: source_sig,
            score: 0.9,
            required_adaptations: vec![Adaptation::Rename {
                from: "x".to_string(),
                to: "y".to_string(),
            }],
        };
        // Target with different variable
        let target = Formula::Eq(Box::new(var("y")), Box::new(Formula::Int(0)));

        let adapted = apply_transfer(&candidate, &target, "cert-456");
        assert!(adapted.is_some());
        let adapted = adapted.unwrap();
        assert!(
            adapted.adaptations_applied.iter().any(|a| a.contains("rename")),
            "should contain rename adaptation: {:?}",
            adapted.adaptations_applied
        );
    }

    #[test]
    fn test_apply_transfer_no_transfer_returns_none() {
        // Source and target completely unrelated -> NoTransfer
        let source_sig = LemmaSignature {
            name: "source".to_string(),
            hypotheses: vec![var("a"), var("b"), var("c")],
            conclusion: Formula::Int(999),
        };
        let candidate = TransferCandidate {
            source: source_sig,
            score: 0.1, // below threshold
            required_adaptations: vec![],
        };
        let target = Formula::Bool(true);

        let adapted = apply_transfer(&candidate, &target, "cert-789");
        assert!(adapted.is_none(), "should return None for NoTransfer");
    }

    // -----------------------------------------------------------------------
    // build_transfer_provenance
    // -----------------------------------------------------------------------

    #[test]
    fn test_build_transfer_provenance() {
        let adapted = AdaptedObligation {
            formula: Formula::Bool(true),
            source_cert_id: "cert-123".to_string(),
            adaptations_applied: vec!["direct_apply".to_string()],
            similarity: 0.95,
        };

        let provenance = build_transfer_provenance(&adapted, "crate::source_fn");
        assert_eq!(provenance.source_cert_id, "cert-123");
        assert_eq!(provenance.source_function, "crate::source_fn");
        assert_eq!(provenance.similarity_millionths, 950_000);
        assert_eq!(provenance.adaptations, vec!["direct_apply"]);
    }

    #[test]
    fn test_transfer_provenance_serialization_roundtrip() {
        let provenance = TransferProvenance {
            source_cert_id: "cert-abc".to_string(),
            source_function: "crate::helper".into(),
            similarity_millionths: 870_000,
            adaptations: vec!["rename(x -> y)".to_string(), "add_hypothesis".to_string()],
        };

        let json = serde_json::to_string(&provenance).expect("should serialize");
        let restored: TransferProvenance = serde_json::from_str(&json).expect("should deserialize");
        assert_eq!(restored, provenance);
    }

    // -----------------------------------------------------------------------
    // find_transfer_candidates_from_certs
    // -----------------------------------------------------------------------

    #[test]
    fn test_find_transfer_candidates_from_certs_works() {
        let src_formula = Formula::Eq(Box::new(var("x")), Box::new(Formula::Int(0)));
        let src_cert =
            make_cert_with_formula("crate::source", &src_formula, "2026-04-12T00:00:00Z");

        let target = Formula::Eq(Box::new(var("y")), Box::new(Formula::Int(0)));

        let candidates =
            find_transfer_candidates_from_certs(&[&src_cert], "crate::target", &target, &[]);
        assert!(!candidates.is_empty());
    }

    // -----------------------------------------------------------------------
    // Integration: composition DAG with multiple certificates
    // -----------------------------------------------------------------------

    #[test]
    fn test_integration_composition_transfer_pipeline() {
        let mut comp = ProofComposition::new();

        // Add several certificates with related formulas
        let f1 = Formula::Eq(Box::new(var("x")), Box::new(Formula::Int(0)));
        let cert1 = make_cert_with_formula("crate::init", &f1, "2026-04-12T00:00:00Z");
        comp.add_certificate(cert1, vec![]);

        let f2 = Formula::Implies(
            Box::new(var("p")),
            Box::new(Formula::Eq(Box::new(var("x")), Box::new(Formula::Int(0)))),
        );
        let cert2 = make_cert_with_formula("crate::check", &f2, "2026-04-12T00:01:00Z");
        comp.add_certificate(cert2, vec!["crate::init".to_string()]);

        // Search for transfers to a new target: y == 0
        let target = Formula::Eq(Box::new(var("y")), Box::new(Formula::Int(0)));
        let candidates = find_transfer_candidates(&comp, "crate::new_fn", &target, &[]);

        // Should find at least one candidate (crate::init has x == 0)
        assert!(!candidates.is_empty(), "should find transfer candidates from composition");

        // Apply best candidate
        let best = &candidates[0];
        let adapted = apply_transfer(best, &target, "test-cert-id");
        assert!(adapted.is_some(), "best candidate should produce an adapted obligation");

        let adapted = adapted.unwrap();
        // Build provenance
        let provenance = build_transfer_provenance(&adapted, &best.source.name);
        assert!(!provenance.source_function.is_empty());
        assert!(provenance.similarity_millionths >= (TRANSFER_THRESHOLD * 1_000_000.0) as u64);
    }

    #[test]
    fn test_self_exclusion_in_dag_transfer() {
        let mut comp = ProofComposition::new();

        let formula = Formula::Eq(Box::new(var("x")), Box::new(Formula::Int(42)));
        let cert = make_cert_with_formula("crate::self_fn", &formula, "2026-04-12T00:00:00Z");
        comp.add_certificate(cert, vec![]);

        // Searching for the same function should return empty
        // (find_transferable excludes same-name lemmas)
        let candidates = find_transfer_candidates(&comp, "crate::self_fn", &formula, &[]);
        assert!(candidates.is_empty(), "should not find self as transfer candidate");
    }
}
