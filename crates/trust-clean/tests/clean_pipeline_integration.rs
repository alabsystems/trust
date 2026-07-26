// trust-clean integration tests: end-to-end pipeline validation
//
// These tests exercise the full VC-to-solver-to-clean pipeline as integration
// tests (not inline #[cfg(test)]). They verify that:
//
// 1. A known VC produces an expected clean proof term (golden reference)
// 2. Two proofs can be composed and exported through the pipeline
// 3. Invalid VCs/proofs produce meaningful errors
// 4. The clean binary can verify generated proofs (feature-gated)
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use clean_kernel::cert::ProofCert;
use clean_kernel::level::Level as LeanLevel;
use trust_clean::certification::{CertificationPipeline, CertificationResult};
use trust_clean::error::CertificateError;
use trust_clean::integration::{CertificationBridge, PipelineOutput};
use trust_clean::{
    TrustProofCertificateBundle, clean_bridge, compute_vc_fingerprint, generate_certificate,
    generate_certificate_unchecked,
};
use trust_proof_cert::{CertificateStore, CertificationStatus, ChainStepType, ChainValidator};
use trust_types::*;

// ---------------------------------------------------------------------------
// Test helpers: realistic VC construction
// ---------------------------------------------------------------------------

/// Arithmetic overflow VC: `a + b` does not overflow usize.
fn overflow_vc() -> VerificationCondition {
    VerificationCondition {
        kind: VcKind::ArithmeticOverflow {
            op: BinOp::Add,
            operand_tys: (Ty::usize(), Ty::usize()),
        },
        function: "get_midpoint".into(),
        location: SourceSpan {
            file: "src/math.rs".to_string(),
            line_start: 15,
            col_start: 4,
            line_end: 15,
            col_end: 30,
        },
        formula: Formula::Not(Box::new(Formula::And(vec![
            Formula::Le(
                Box::new(Formula::Int(0)),
                Box::new(Formula::Add(
                    Box::new(Formula::Var("a".into(), Sort::Int)),
                    Box::new(Formula::Var("b".into(), Sort::Int)),
                )),
            ),
            Formula::Le(
                Box::new(Formula::Add(
                    Box::new(Formula::Var("a".into(), Sort::Int)),
                    Box::new(Formula::Var("b".into(), Sort::Int)),
                )),
                Box::new(Formula::Int((1i128 << 64) - 1)),
            ),
        ]))),
        contract_metadata: None,
    }
}

/// Division-by-zero VC: divisor != 0.
fn divzero_vc() -> VerificationCondition {
    VerificationCondition {
        kind: VcKind::DivisionByZero,
        function: "safe_div".into(),
        location: SourceSpan::default(),
        formula: Formula::Not(Box::new(Formula::Eq(
            Box::new(Formula::Var("divisor".into(), Sort::Int)),
            Box::new(Formula::Int(0)),
        ))),
        contract_metadata: None,
    }
}

/// Bounds check VC: index < array.len().
fn bounds_check_vc() -> VerificationCondition {
    VerificationCondition {
        kind: VcKind::IndexOutOfBounds,
        function: "get_element".into(),
        location: SourceSpan {
            file: "src/container.rs".to_string(),
            line_start: 42,
            col_start: 8,
            line_end: 42,
            col_end: 24,
        },
        formula: Formula::Lt(
            Box::new(Formula::Var("index".into(), Sort::Int)),
            Box::new(Formula::Var("array_len".into(), Sort::Int)),
        ),
        contract_metadata: None,
    }
}

fn proved_result(solver: &str) -> VerificationResult {
    VerificationResult::Proved {
        solver: solver.into(),
        time_ms: 8,
        strength: ProofStrength::smt_unsat(),
        proof_certificate: None,
        solver_warnings: None,
        native_proof_envelope: None,
    }
}

fn mock_proof_term() -> Vec<u8> {
    vec![0xDE, 0xAD, 0xBE, 0xEF]
}

/// Serialize a valid clean ProofCert to bytes.
fn valid_clean_proof_bytes() -> Vec<u8> {
    let cert = ProofCert::Sort { level: LeanLevel::zero() };
    bincode::serialize(&cert).expect("ProofCert should serialize")
}

// ===========================================================================
// AC1: Golden-reference integration test — known VC produces expected clean
//      proof term structure (no clean binary required)
// ===========================================================================

/// End-to-end golden reference: VC -> certificate -> clean theorem translation
/// -> fingerprint consistency -> bundle roundtrip.
///
/// Verifies the FULL pipeline without needing a clean binary: the certificate
/// is generated via the unchecked (Trusted) path, the clean theorem translation
/// is structurally validated, and the bundle survives serialization roundtrip.
#[test]
fn test_golden_reference_vc_to_clean_pipeline() {
    // Phase 1: Construct a known VC (overflow check for a + b)
    let vc = overflow_vc();
    let result = proved_result("ay");
    let proof_term = mock_proof_term();

    // Phase 2: Generate certificate through the unchecked pipeline
    let cert = generate_certificate_unchecked(&vc, &result, proof_term.clone(), "ay 1.0.0")
        .expect("certificate generation should succeed for overflow VC");

    // Phase 3: Verify certificate structure matches expectations
    assert_eq!(cert.prover, "ay", "prover should be ay");
    assert_eq!(cert.prover_version, "ay 1.0.0");
    assert_eq!(cert.proof_term, proof_term, "proof term should be preserved exactly");

    // Phase 4: Verify fingerprint is deterministic
    let fp1 = compute_vc_fingerprint(&vc);
    let fp2 = compute_vc_fingerprint(&vc);
    assert_eq!(fp1, fp2, "fingerprint must be deterministic");
    assert_eq!(cert.vc_fingerprint, fp1, "certificate fingerprint must match VC fingerprint");

    // Phase 5: Verify clean theorem translation produces valid structure
    let theorem = clean_bridge::translate_vc_to_clean_theorem(&vc.kind, &vc.formula);
    let debug = format!("{theorem:?}");
    assert!(
        debug.contains("holds"),
        "clean theorem should contain Trust.VC.holds wrapper, got: {debug}"
    );
    assert!(
        debug.contains("arithmeticOverflow"),
        "theorem should reference arithmeticOverflow kind, got: {debug}"
    );

    // Phase 6: Verify formula translation contains expected operators
    let formula_expr = clean_bridge::translate_formula(&vc.formula);
    let formula_debug = format!("{formula_expr:?}");
    assert!(
        formula_debug.contains("not") || formula_debug.contains("Not"),
        "formula should contain negation (Not(...)), got: {formula_debug}"
    );
    assert!(
        formula_debug.contains("and") || formula_debug.contains("And"),
        "formula should contain conjunction (And), got: {formula_debug}"
    );

    // Phase 7: Certificate bundle roundtrip
    let bundle = TrustProofCertificateBundle::single("golden-test", cert.clone());
    let bytes = bundle.to_bytes().expect("bundle should serialize");
    let recovered =
        TrustProofCertificateBundle::from_bytes(&bytes).expect("bundle should deserialize");
    assert_eq!(recovered.len(), 1);
    let recovered_cert = recovered.iter().next().expect("one cert");
    assert_eq!(recovered_cert.vc_fingerprint, cert.vc_fingerprint);
    assert_eq!(recovered_cert.proof_term, cert.proof_term);

    // Phase 8: Recovered certificate is still valid for the original VC
    assert!(
        recovered_cert.is_valid_for(&vc),
        "recovered certificate must still be valid for its source VC"
    );
}

/// Golden reference: verify that the same VC always produces the same
/// canonical bytes and fingerprint (stability across pipeline invocations).
#[test]
fn test_golden_reference_fingerprint_stability() {
    let vc = divzero_vc();

    let cert1 =
        generate_certificate_unchecked(&vc, &proved_result("ay"), vec![1, 2, 3], "ay 1.0.0")
            .expect("cert1");
    let cert2 =
        generate_certificate_unchecked(&vc, &proved_result("ay"), vec![1, 2, 3], "ay 1.0.0")
            .expect("cert2");

    assert_eq!(
        cert1.vc_fingerprint, cert2.vc_fingerprint,
        "same VC must produce identical fingerprints across invocations"
    );
    assert_eq!(
        cert1.canonical_vc, cert2.canonical_vc,
        "canonical VC bytes must be identical across invocations"
    );
}

// ===========================================================================
// AC1+: Full bridge pipeline test — VC through CertificationBridge to
//       ProofCertificate + CertificateChain + CertificateStore
// ===========================================================================

/// Integration test: full bridge pipeline from VC to stored ProofCertificate.
///
/// Exercises: CertificationPipeline -> CertificationBridge -> ProofCertificate
///            -> CertificateChain (with integrity) -> CertificateStore
#[test]
fn test_full_bridge_pipeline_to_store() {
    let bridge = CertificationBridge::new();
    let mut store = CertificateStore::new("integration-test-crate");

    // Certify three different VCs through the full pipeline
    let vcs = vec![
        (overflow_vc(), "2026-04-13T10:00:00Z"),
        (divzero_vc(), "2026-04-13T10:01:00Z"),
        (bounds_check_vc(), "2026-04-13T10:02:00Z"),
    ];

    for (vc, timestamp) in &vcs {
        let result = proved_result("ay");
        let output = bridge
            .certify_and_store(vc, &result, mock_proof_term(), timestamp, &mut store)
            .expect("certify_and_store should succeed");

        assert!(output.has_record(), "pipeline should produce a certificate");

        if let PipelineOutput::Record { certificate, chain, .. } = &output {
            // Verify ProofCertificate
            assert_eq!(certificate.function, vc.function.as_str());
            assert_eq!(certificate.status, CertificationStatus::Trusted);
            assert_eq!(certificate.solver.name, "ay");

            // Verify CertificateChain
            assert_eq!(chain.len(), 2, "unchecked path: VcGeneration + SolverProof");
            assert_eq!(chain.steps[0].step_type, ChainStepType::VcGeneration);
            assert_eq!(chain.steps[1].step_type, ChainStepType::SolverProof);
            chain.verify_integrity().expect("chain integrity must hold");

            // ChainValidator should also pass
            let validation = ChainValidator::validate(chain);
            assert!(
                validation.valid,
                "ChainValidator should pass for pipeline-generated chain: {:?}",
                validation.findings
            );
        }
    }

    // Verify all certificates are in the store
    assert_eq!(store.len(), 3, "store should contain 3 certificates");
    assert_eq!(store.find_by_function("get_midpoint").len(), 1);
    assert_eq!(store.find_by_function("safe_div").len(), 1);
    assert_eq!(store.find_by_function("get_element").len(), 1);

    // Verify all certificates have distinct fingerprints
    let certs_a = store.find_by_function("get_midpoint");
    let certs_b = store.find_by_function("safe_div");
    assert_ne!(
        certs_a[0].id, certs_b[0].id,
        "certificates for different functions should have different IDs"
    );
}

// ===========================================================================
// AC2: Integration test invoking clean kernel on generated proof
//      (gated by cfg(feature = "clean-integration"))
// ===========================================================================

/// Test that the clean kernel correctly rejects a structurally valid but
/// semantically wrong proof for a given VC.
///
/// This exercises the CHECKED (kernel-validated) path of the pipeline.
/// A `ProofCert::Sort` is a valid clean term but cannot witness an
/// arithmetic overflow theorem — the kernel must reject it.
#[test]
fn test_clean_kernel_rejects_wrong_proof_for_vc() {
    let pipeline = CertificationPipeline::new();
    let vc = overflow_vc();
    let result = proved_result("ay");

    // Valid clean ProofCert bytes, but wrong proof for this VC
    let proof_bytes = valid_clean_proof_bytes();
    let cert_result = pipeline.certify(&vc, &result, proof_bytes);

    assert!(
        cert_result.is_rejected(),
        "clean kernel should reject Sort cert for overflow VC, got: {cert_result:?}"
    );

    if let CertificationResult::Rejected { reason, time_ms } = &cert_result {
        assert!(
            reason.contains("kernel") || reason.contains("rejected"),
            "rejection reason should mention kernel, got: {reason}"
        );
        assert!(*time_ms < 5000, "rejection should complete quickly");
    }
}

/// Test that the bridge checked path produces NoRecord for invalid proofs,
/// not an error.
#[test]
fn test_bridge_checked_path_rejects_invalid_proof() {
    let bridge = CertificationBridge::new();
    let vc = divzero_vc();
    let result = proved_result("ay");

    // Completely invalid bytes (not a valid clean ProofCert)
    let output = bridge
        .certify(&vc, &result, vec![0xFF, 0x00], "2026-04-13T00:00:00Z")
        .expect("should return NoRecord, not an error");

    assert!(!output.has_record());
    if let PipelineOutput::NoRecord { reason } = &output {
        assert!(reason.contains("rejected"), "reason should indicate rejection, got: {reason}");
    }
}

/// Test the clean kernel checked path with a valid clean ProofCert through
/// the bridge. The proof (Sort) is structurally valid but semantically wrong,
/// so the bridge should produce NoRecord.
#[test]
fn test_bridge_checked_and_store_rejects_wrong_proof() {
    let bridge = CertificationBridge::new();
    let mut store = CertificateStore::new("clean-kernel-test");
    let vc = bounds_check_vc();
    let result = proved_result("ay");

    let proof_bytes = valid_clean_proof_bytes();
    let output = bridge
        .certify_checked_and_store(&vc, &result, proof_bytes, "2026-04-13T00:00:00Z", &mut store)
        .expect("should produce NoRecord, not error");

    assert!(!output.has_record(), "wrong proof should not be certified");
    assert!(store.is_empty(), "store should remain empty when certification fails");
}

// ===========================================================================
// AC3: Error cases — invalid VCs and proof terms produce meaningful errors
// ===========================================================================

/// Empty proof term should be rejected by the certificate generator.
#[test]
fn test_empty_proof_term_produces_meaningful_error() {
    let vc = overflow_vc();
    let result = proved_result("ay");

    let err = generate_certificate(&vc, &result, vec![], "ay 1.0.0")
        .expect_err("empty proof term should fail");

    assert!(
        matches!(err, CertificateError::InvalidProofTerm { .. }),
        "error should be InvalidProofTerm, got: {err:?}"
    );

    let msg = format!("{err}");
    assert!(
        msg.contains("empty") || msg.contains("proof term"),
        "error message should explain the problem, got: {msg}"
    );
}

/// Invalid clean bytes should produce a meaningful error through the pipeline.
#[test]
fn test_invalid_clean_bytes_produce_meaningful_error() {
    let pipeline = CertificationPipeline::new();
    let vc = divzero_vc();
    let result = proved_result("ay");

    // Garbage bytes that are not a valid ProofCert
    let cert_result = pipeline.certify(&vc, &result, vec![0xBA, 0xAD, 0xF0, 0x0D]);

    assert!(cert_result.is_rejected(), "garbage bytes should be rejected, got: {cert_result:?}");

    if let CertificationResult::Rejected { reason, .. } = &cert_result {
        assert!(!reason.is_empty(), "rejection reason should not be empty");
    }
}

/// Non-proved VerificationResult should be skipped (not error).
#[test]
fn test_non_proved_result_skipped_not_errored() {
    let pipeline = CertificationPipeline::new();
    let vc = overflow_vc();

    let failed =
        VerificationResult::Failed { solver: "ay".into(), time_ms: 3, counterexample: None };
    let cert_result = pipeline.certify(&vc, &failed, mock_proof_term());
    assert!(cert_result.is_skipped(), "failed result should be skipped, got: {cert_result:?}");

    if let CertificationResult::Skipped { reason } = &cert_result {
        assert!(
            reason.contains("Proved"),
            "skip reason should mention expected Proved status, got: {reason}"
        );
    }
}

/// Stale certificate detection: changing the formula invalidates the cert.
#[test]
fn test_stale_certificate_detection_after_formula_change() {
    let vc_v1 = divzero_vc();
    let cert =
        generate_certificate_unchecked(&vc_v1, &proved_result("ay"), mock_proof_term(), "ay 1.0.0")
            .expect("cert generation should succeed");

    // Original VC: divisor != 0 (using Not(Eq(...)))
    assert!(cert.is_valid_for(&vc_v1), "cert should be valid for original VC");

    // Modified VC: change formula to divisor > 0 (different semantics)
    let vc_v2 = VerificationCondition {
        kind: VcKind::DivisionByZero,
        function: "safe_div".into(),
        location: SourceSpan::default(),
        formula: Formula::Gt(
            Box::new(Formula::Var("divisor".into(), Sort::Int)),
            Box::new(Formula::Int(0)),
        ),
        contract_metadata: None,
    };

    assert!(
        !cert.is_valid_for(&vc_v2),
        "certificate should be STALE after formula change (Not(Eq(..)) -> Gt(..))"
    );

    // The fingerprints should differ
    let fp_v1 = compute_vc_fingerprint(&vc_v1);
    let fp_v2 = compute_vc_fingerprint(&vc_v2);
    assert_ne!(fp_v1, fp_v2, "different formulas must have different fingerprints");
}

// ===========================================================================
// Composition: two proofs through the pipeline
// ===========================================================================

/// Integration test: certify two related VCs (same function, different checks)
/// through the pipeline and verify both certificates coexist in the store.
#[test]
fn test_two_proofs_composed_in_store() {
    let bridge = CertificationBridge::new();
    let mut store = CertificateStore::new("composition-test");

    // VC 1: overflow check for get_midpoint
    let vc1 = overflow_vc();
    // VC 2: a different check for the same function (bounds check with different name)
    let vc2 = VerificationCondition {
        kind: VcKind::IndexOutOfBounds,
        function: "get_midpoint".into(), // Same function, different VC kind
        location: SourceSpan {
            file: "src/math.rs".to_string(),
            line_start: 16,
            col_start: 4,
            line_end: 16,
            col_end: 20,
        },
        formula: Formula::Lt(
            Box::new(Formula::Var("mid".into(), Sort::Int)),
            Box::new(Formula::Var("len".into(), Sort::Int)),
        ),
        contract_metadata: None,
    };

    let result = proved_result("ay");

    // Certify both VCs
    let out1 = bridge
        .certify_and_store(&vc1, &result, vec![0xA1], "2026-04-13T10:00:00Z", &mut store)
        .expect("vc1 certification should succeed");
    let out2 = bridge
        .certify_and_store(&vc2, &result, vec![0xA2], "2026-04-13T10:00:01Z", &mut store)
        .expect("vc2 certification should succeed");

    assert!(out1.has_record());
    assert!(out2.has_record());

    // Both should be in the store under the same function name
    let certs = store.find_by_function("get_midpoint");
    assert_eq!(
        certs.len(),
        2,
        "two different VCs for get_midpoint should produce two certificates"
    );

    // Verify the two certificates have different IDs and fingerprints
    assert_ne!(certs[0].id, certs[1].id, "certificates should have distinct IDs");

    // Verify chains for both are valid
    if let PipelineOutput::Record { chain: chain1, .. } = &out1
        && let PipelineOutput::Record { chain: chain2, .. } = &out2
    {
        let v1 = ChainValidator::validate(chain1);
        let v2 = ChainValidator::validate(chain2);
        assert!(v1.valid, "chain1 should be valid: {:?}", v1.findings);
        assert!(v2.valid, "chain2 should be valid: {:?}", v2.findings);
    }
}

// ===========================================================================
// ProofCert serialization roundtrip through clean_bridge
// ===========================================================================

/// Verify that ProofCert survives serialization/deserialization through
/// the clean_bridge API (used in the pipeline for proof term storage).
#[test]
fn test_proof_cert_serialization_roundtrip() {
    let cert = ProofCert::Sort { level: LeanLevel::succ(LeanLevel::zero()) };

    let bytes =
        clean_bridge::serialize_proof_cert(&cert).expect("ProofCert serialization should succeed");
    assert!(!bytes.is_empty(), "serialized bytes should be non-empty");

    let recovered = clean_bridge::deserialize_proof_cert(&bytes)
        .expect("ProofCert deserialization should succeed");
    assert_eq!(cert, recovered, "ProofCert should survive roundtrip through clean_bridge");
}

/// Invalid bytes should produce InvalidProofTerm error from clean_bridge.
#[test]
fn test_proof_cert_deserialization_invalid_bytes() {
    let err = clean_bridge::deserialize_proof_cert(&[0xFF, 0x00, 0xDE])
        .expect_err("invalid bytes should fail deserialization");

    assert!(
        matches!(err, CertificateError::InvalidProofTerm { .. }),
        "error should be InvalidProofTerm, got: {err:?}"
    );
}

// ===========================================================================
// Bundle multi-certificate roundtrip
// ===========================================================================

/// Integration test: bundle multiple certificates and verify roundtrip
/// preserves all data. Tests the serialization path used for proof caching.
#[test]
fn test_multi_certificate_bundle_roundtrip() {
    let pipeline = CertificationPipeline::new();
    let proof_term = mock_proof_term();
    let vcs = vec![overflow_vc(), divzero_vc(), bounds_check_vc()];
    let mut certificates = Vec::new();

    for vc in &vcs {
        let result = proved_result("ay");
        let cert_result = pipeline.certify_unchecked(vc, &result, proof_term.clone());
        if let CertificationResult::Certified { certificate, .. }
        | CertificationResult::Trusted { certificate, .. } = cert_result
        {
            certificates.push(certificate);
        }
    }
    assert_eq!(certificates.len(), 3);

    let bundle = TrustProofCertificateBundle::new("integration-test", certificates.clone())
        .expect("bundle creation should succeed");

    // Serialize -> deserialize roundtrip
    let bytes = bundle.to_bytes().expect("serialize");
    let recovered = TrustProofCertificateBundle::from_bytes(&bytes).expect("deserialize");
    assert_eq!(recovered.len(), 3);

    // Each recovered cert should still be valid for its source VC
    for (vc, cert) in vcs.iter().zip(recovered.iter()) {
        assert!(
            cert.is_valid_for(vc),
            "recovered certificate should be valid for VC '{}'",
            vc.function
        );
    }
}
