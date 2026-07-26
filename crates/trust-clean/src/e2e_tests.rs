// trust-clean/e2e_tests.rs: End-to-end certification pipeline tests
//
// These tests exercise the full pipeline: VC construction -> mock solver
// proof -> certificate generation -> clean verification -> certified result.
// They span multiple modules (certification, certificate, clean_bridge,
// bundle, integration) to verify the components work together.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use clean_kernel::cert::ProofCert;
use clean_kernel::level::Level as LeanLevel;
use trust_proof_cert::{CertificateStore, CertificationStatus, ChainStepType};
use trust_types::*;

use crate::bundle::TrustProofCertificateBundle;
use crate::certificate::generate_certificate_unchecked;
use crate::certification::{CertificationPipeline, CertificationResult};
use crate::clean_bridge;
use crate::fingerprint::compute_vc_fingerprint;
use crate::integration::{CertificationBridge, PipelineOutput};

// ---------------------------------------------------------------------------
// Helpers: VC construction for realistic verification scenarios
// ---------------------------------------------------------------------------

/// Integer overflow VC for `a + b` where both are usize.
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

/// Bounds check VC: index < array.len()
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

/// Postcondition VC with quantified formula.
fn postcondition_vc() -> VerificationCondition {
    VerificationCondition {
        kind: VcKind::Postcondition,
        function: "sort_slice".into(),
        location: SourceSpan::default(),
        formula: Formula::Forall(
            vec![("i".into(), Sort::Int)],
            Box::new(Formula::Implies(
                Box::new(Formula::And(vec![
                    Formula::Le(
                        Box::new(Formula::Int(0)),
                        Box::new(Formula::Var("i".into(), Sort::Int)),
                    ),
                    Formula::Lt(
                        Box::new(Formula::Var("i".into(), Sort::Int)),
                        Box::new(Formula::Var("n".into(), Sort::Int)),
                    ),
                ])),
                Box::new(Formula::Le(
                    Box::new(Formula::Select(
                        Box::new(Formula::Var(
                            "arr".into(),
                            Sort::Array(Box::new(Sort::Int), Box::new(Sort::Int)),
                        )),
                        Box::new(Formula::Var("i".into(), Sort::Int)),
                    )),
                    Box::new(Formula::Select(
                        Box::new(Formula::Var(
                            "arr".into(),
                            Sort::Array(Box::new(Sort::Int), Box::new(Sort::Int)),
                        )),
                        Box::new(Formula::Add(
                            Box::new(Formula::Var("i".into(), Sort::Int)),
                            Box::new(Formula::Int(1)),
                        )),
                    )),
                )),
            )),
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

/// Serialize a clean ProofCert to bytes (valid bincode but wrong proof).
fn valid_clean_proof_bytes() -> Vec<u8> {
    let cert = ProofCert::Sort { level: LeanLevel::zero() };
    bincode::serialize(&cert).expect("ProofCert should serialize")
}

// ---------------------------------------------------------------------------
// Test 1: Certify simple overflow VC (full pipeline)
// ---------------------------------------------------------------------------

#[test]
fn test_certify_simple_overflow_vc() {
    // Phase 1: Generate a VC for integer overflow
    let vc = overflow_vc();
    let result = proved_result("ay");
    let proof_term = mock_proof_term();

    // Phase 2: Generate an unchecked certificate (Trusted path)
    let cert = generate_certificate_unchecked(&vc, &result, proof_term.clone(), "ay 1.0.0")
        .expect("unchecked certificate generation should succeed");

    // Phase 3: Verify certificate structure
    assert_eq!(cert.prover, "ay");
    assert_eq!(cert.prover_version, "ay 1.0.0");
    assert_eq!(cert.proof_term, proof_term);
    assert!(cert.is_valid_for(&vc), "certificate should be valid for its source VC");

    // Phase 4: Verify fingerprint consistency
    let fingerprint = compute_vc_fingerprint(&vc);
    assert_eq!(cert.vc_fingerprint, fingerprint);

    // Phase 5: Run through the CertificationPipeline (unchecked = Trusted, #758)
    let pipeline = CertificationPipeline::new();
    let cert_result = pipeline.certify_unchecked(&vc, &result, proof_term);
    assert!(
        cert_result.is_trusted(),
        "pipeline.certify_unchecked should produce Trusted, got: {cert_result:?}"
    );

    // Phase 6: Verify the certificate matches the VC
    if let CertificationResult::Trusted { certificate, time_ms } = &cert_result {
        assert!(certificate.is_valid_for(&vc));
        assert!(*time_ms < 1000, "certification should be fast, got {time_ms}ms");
    }
}

// ---------------------------------------------------------------------------
// Test 2: Certify bounds check VC
// ---------------------------------------------------------------------------

#[test]
fn test_certify_bounds_check_vc() {
    let vc = bounds_check_vc();
    let result = proved_result("ay");
    let proof_term = mock_proof_term();

    // Full pipeline: generate -> verify staleness -> translate to clean
    let cert = generate_certificate_unchecked(&vc, &result, proof_term.clone(), "ay 1.0.0")
        .expect("should generate certificate for bounds check VC");

    // Verify the certificate is valid for the original VC
    assert!(cert.is_valid_for(&vc));

    // Verify the clean translation produces a theorem
    let theorem = clean_bridge::translate_vc_to_clean_theorem(&vc.kind, &vc.formula);
    let debug = format!("{theorem:?}");
    assert!(
        debug.contains("holds") || debug.contains("VC"),
        "clean theorem should wrap formula in Trust.VC.holds, got: {debug}"
    );
    assert!(
        debug.contains("indexOutOfBounds"),
        "theorem should reference indexOutOfBounds kind, got: {debug}"
    );

    // Verify staleness detection: change the formula, cert should be stale
    let mutated_vc = VerificationCondition {
        kind: VcKind::IndexOutOfBounds,
        function: "get_element".into(),
        location: SourceSpan::default(),
        formula: Formula::Le(
            Box::new(Formula::Var("index".into(), Sort::Int)),
            Box::new(Formula::Var("array_len".into(), Sort::Int)),
        ),
        contract_metadata: None,
    };
    assert!(
        !cert.is_valid_for(&mutated_vc),
        "certificate should be stale after formula change (Lt -> Le)"
    );
}

// ---------------------------------------------------------------------------
// Test 3: Certification pipeline batch processing
// ---------------------------------------------------------------------------

#[test]
fn test_certification_pipeline_batch() {
    let pipeline = CertificationPipeline::new();
    let proof_term = mock_proof_term();

    let vcs = vec![
        ("overflow", overflow_vc(), proved_result("ay")),
        ("bounds", bounds_check_vc(), proved_result("ay")),
        ("divzero", divzero_vc(), proved_result("trust-wp")),
        ("postcondition", postcondition_vc(), proved_result("clean")),
    ];

    let mut certified_count = 0;
    let mut certificates = Vec::new();

    for (label, vc, result) in &vcs {
        let cert_result = pipeline.certify_unchecked(vc, result, proof_term.clone());
        assert!(
            cert_result.is_trusted(),
            "batch: {label} should produce a Trusted certificate, got: {cert_result:?}"
        );

        if let CertificationResult::Trusted { certificate, .. } = cert_result {
            assert!(
                certificate.is_valid_for(vc),
                "batch: {label} certificate should be valid for its VC"
            );
            certificates.push(certificate);
            certified_count += 1;
        }
    }

    assert_eq!(certified_count, 4, "all 4 VCs should produce Trusted certificates");

    // Verify all certificates have distinct fingerprints
    let fingerprints: Vec<_> = certificates.iter().map(|c| c.vc_fingerprint).collect();
    for i in 0..fingerprints.len() {
        for j in (i + 1)..fingerprints.len() {
            assert_ne!(
                fingerprints[i], fingerprints[j],
                "certificates for different VCs must have distinct fingerprints"
            );
        }
    }

    // Verify that a failed result is properly skipped
    let failed =
        VerificationResult::Failed { solver: "ay".into(), time_ms: 3, counterexample: None };
    let skip_result = pipeline.certify_unchecked(&overflow_vc(), &failed, proof_term);
    assert!(skip_result.is_skipped(), "failed result should be skipped");
}

// ---------------------------------------------------------------------------
// Test 4: CertificationBridge roundtrip (clean <-> trust-proof-cert)
// ---------------------------------------------------------------------------

#[test]
fn test_certification_bridge_roundtrip() {
    let bridge = CertificationBridge::new();
    let vc = overflow_vc();
    let result = proved_result("ay");
    let proof_term = mock_proof_term();
    let timestamp = "2026-03-29T12:00:00Z";

    // Step 1: Produce a ProofCertificate via the bridge (unchecked path)
    let output = bridge
        .certify_unchecked(&vc, &result, proof_term.clone(), timestamp)
        .expect("bridge unchecked certification should succeed");

    assert!(output.has_record());
    let (proof_cert, chain) = match &output {
        PipelineOutput::Record { certificate, chain, .. } => (certificate, chain),
        PipelineOutput::NoRecord { reason } => {
            panic!("expected a record, got NoRecord: {reason}")
        }
    };

    // Step 2: Verify the ProofCertificate fields
    assert_eq!(proof_cert.function, "get_midpoint");
    assert_eq!(proof_cert.status, CertificationStatus::Trusted);
    assert_eq!(proof_cert.proof_trace, proof_term);
    assert_eq!(proof_cert.solver.name, "ay");
    assert_eq!(proof_cert.solver.strength, ProofStrength::smt_unsat());
    assert!(proof_cert.timestamp.contains("2026-03-29"));
    // Step 3: Verify the CertificateChain structure
    assert_eq!(chain.len(), 2, "unchecked path should have VcGeneration + SolverProof");
    assert_eq!(chain.steps[0].step_type, ChainStepType::VcGeneration);
    assert_eq!(chain.steps[1].step_type, ChainStepType::SolverProof);
    assert!(!chain.is_clean_certified(), "unchecked path should not be clean-certified");
    chain.verify_integrity().expect("chain integrity should hold");

    // Step 4: JSON roundtrip of the ProofCertificate
    let json = proof_cert.to_json().expect("certificate should serialize to JSON");
    let restored = trust_proof_cert::ProofCertificate::from_json(&json)
        .expect("certificate should deserialize from JSON");
    assert_eq!(*proof_cert, restored, "ProofCertificate should survive JSON roundtrip");

    // Step 5: JSON roundtrip of the CertificateChain
    let chain_json = chain.to_json().expect("chain should serialize");
    let chain_restored = trust_proof_cert::CertificateChain::from_json(&chain_json)
        .expect("chain should deserialize");
    assert_eq!(*chain, chain_restored, "CertificateChain should survive JSON roundtrip");

    // Step 6: Verify the bridge handles non-proved results correctly
    let failed =
        VerificationResult::Failed { solver: "ay".into(), time_ms: 3, counterexample: None };
    let skip_output = bridge
        .certify_unchecked(&vc, &failed, vec![1], timestamp)
        .expect("bridge should return NoRecord for failed result");
    assert!(!skip_output.has_record());
}

// ---------------------------------------------------------------------------
// Test 5: Certificate bundle serialize/deserialize
// ---------------------------------------------------------------------------

#[test]
fn test_certificate_bundle_serialize_deserialize() {
    let pipeline = CertificationPipeline::new();
    let proof_term = mock_proof_term();

    // Generate certificates for multiple VCs
    let vcs = vec![overflow_vc(), bounds_check_vc(), divzero_vc()];
    let mut certificates = Vec::new();

    for vc in &vcs {
        let result = proved_result("ay");
        let cert_result = pipeline.certify_unchecked(vc, &result, proof_term.clone());
        if let CertificationResult::Trusted { certificate, .. } = cert_result {
            certificates.push(certificate);
        }
    }
    assert_eq!(certificates.len(), 3, "should have 3 Trusted certificates");

    // Build a bundle
    let bundle = TrustProofCertificateBundle::new("trust-e2e-test", certificates.clone())
        .expect("bundle construction should succeed");
    assert_eq!(bundle.project(), "trust-e2e-test");
    assert_eq!(bundle.len(), 3);

    // Serialize to bytes
    let bytes = bundle.to_bytes().expect("bundle serialization should succeed");
    assert!(!bytes.is_empty(), "serialized bundle should be non-empty");

    // Deserialize from bytes
    let recovered = TrustProofCertificateBundle::from_bytes(&bytes)
        .expect("bundle deserialization should succeed");
    assert_eq!(recovered.project(), "trust-e2e-test");
    assert_eq!(recovered.len(), 3);

    // Verify each certificate in the recovered bundle matches the original
    for (orig, recov) in certificates.iter().zip(recovered.iter()) {
        assert_eq!(orig.vc_fingerprint, recov.vc_fingerprint);
        assert_eq!(orig.proof_term, recov.proof_term);
        assert_eq!(orig.prover_version, recov.prover_version);
        assert_eq!(orig.canonical_vc, recov.canonical_vc);
    }

    // Verify each recovered certificate is still valid for its VC
    for (vc, cert) in vcs.iter().zip(recovered.iter()) {
        assert!(cert.is_valid_for(vc), "recovered certificate should still be valid for its VC");
    }

    // File roundtrip
    let path = std::env::temp_dir()
        .join(format!("trust-clean-e2e-bundle-{}.trust-cert", std::process::id()));
    bundle.write_to_path(&path).expect("write should succeed");
    let file_recovered =
        TrustProofCertificateBundle::read_from_path(&path).expect("read should succeed");
    let _ = std::fs::remove_file(&path);

    assert_eq!(file_recovered.project(), bundle.project());
    assert_eq!(file_recovered.len(), bundle.len());
    for (orig, recov) in bundle.iter().zip(file_recovered.iter()) {
        assert_eq!(orig.vc_fingerprint, recov.vc_fingerprint);
    }
}

// ---------------------------------------------------------------------------
// Test 6: Full pipeline with clean kernel validation (checked path)
// ---------------------------------------------------------------------------

#[test]
fn test_checked_pipeline_rejects_wrong_proof() {
    // The checked path deserializes the proof and runs clean kernel.
    // A valid clean ProofCert that doesn't match the VC theorem should be rejected.
    let pipeline = CertificationPipeline::new();
    let vc = divzero_vc();
    let result = proved_result("ay");

    // Valid clean ProofCert bytes (Sort { level: zero }) but wrong proof for this VC
    let proof_bytes = valid_clean_proof_bytes();
    let cert_result = pipeline.certify(&vc, &result, proof_bytes);

    assert!(
        cert_result.is_rejected(),
        "Sort cert should be rejected by clean kernel for div-by-zero VC, got: {cert_result:?}"
    );

    if let CertificationResult::Rejected { reason, time_ms } = &cert_result {
        assert!(
            reason.contains("kernel") || reason.contains("rejected"),
            "rejection reason should mention kernel, got: {reason}"
        );
        assert!(*time_ms < 5000, "rejection should be fast");
    }
}

// ---------------------------------------------------------------------------
// Test 7: Bridge checked path rejects and produces NoRecord
// ---------------------------------------------------------------------------

#[test]
fn test_bridge_checked_path_rejects_invalid() {
    let bridge = CertificationBridge::new();
    let vc = bounds_check_vc();
    let result = proved_result("ay");

    // Invalid clean bytes
    let output = bridge
        .certify(&vc, &result, vec![0xFF, 0x00], "2026-03-29T00:00:00Z")
        .expect("should return NoRecord, not error");

    assert!(!output.has_record());
    if let PipelineOutput::NoRecord { reason } = &output {
        assert!(reason.contains("rejected"), "reason should mention rejection, got: {reason}");
    }
}

// ---------------------------------------------------------------------------
// Test 8: Bridge store integration with multiple functions
// ---------------------------------------------------------------------------

#[test]
fn test_bridge_store_integration_batch() {
    let bridge = CertificationBridge::new();
    let mut store = CertificateStore::new("e2e-test-crate");

    let vcs = vec![
        (overflow_vc(), "2026-03-29T12:00:00Z"),
        (bounds_check_vc(), "2026-03-29T12:01:00Z"),
        (divzero_vc(), "2026-03-29T12:02:00Z"),
        (postcondition_vc(), "2026-03-29T12:03:00Z"),
    ];

    for (vc, timestamp) in &vcs {
        let result = proved_result("ay");
        let output = bridge
            .certify_and_store(vc, &result, mock_proof_term(), timestamp, &mut store)
            .expect("certify_and_store should succeed");
        assert!(output.has_record());
    }

    assert_eq!(store.len(), 4, "store should contain 4 certificates");

    // Verify each function is findable
    assert_eq!(store.find_by_function("get_midpoint").len(), 1);
    assert_eq!(store.find_by_function("get_element").len(), 1);
    assert_eq!(store.find_by_function("safe_div").len(), 1);
    assert_eq!(store.find_by_function("sort_slice").len(), 1);
    assert!(
        store.find_by_function("nonexistent").is_empty(),
        "nonexistent function should not be found"
    );

    // All stored certificates should be Trusted (unchecked path)
    for cert in store.find_by_function("get_midpoint") {
        assert_eq!(cert.status, CertificationStatus::Trusted);
    }
}

// ---------------------------------------------------------------------------
// Test 9: Verify staleness detection across the full pipeline
// ---------------------------------------------------------------------------

#[test]
fn test_staleness_detection_across_pipeline() {
    let pipeline = CertificationPipeline::new();
    let vc_v1 = overflow_vc();
    let result = proved_result("ay");

    // Generate Trusted certificate for v1
    let cert_result = pipeline.certify_unchecked(&vc_v1, &result, mock_proof_term());
    let certificate = match cert_result {
        CertificationResult::Trusted { certificate, .. } => certificate,
        other => panic!("expected Trusted, got: {other:?}"),
    };

    // Certificate fingerprint should match v1
    assert!(certificate.is_valid_for(&vc_v1), "certificate fingerprint should match its source VC");

    // verify_existing runs clean kernel validation, which rejects mock proof bytes.
    // This is correct behavior: unchecked certificates are Trusted, not Certified.
    // The verify_existing method is the full clean re-check.
    let v1_err = pipeline.verify_existing(&vc_v1, &certificate);
    assert!(v1_err.is_err(), "verify_existing should reject mock proof bytes via clean kernel");

    // Simulate code change: different formula for same function
    let vc_v2 = VerificationCondition {
        kind: VcKind::ArithmeticOverflow {
            op: BinOp::Add,
            operand_tys: (Ty::usize(), Ty::usize()),
        },
        function: "get_midpoint".into(),
        location: SourceSpan::default(),
        // Changed: uses saturating add check instead
        formula: Formula::Le(
            Box::new(Formula::Add(
                Box::new(Formula::Var("a".into(), Sort::Int)),
                Box::new(Formula::Var("b".into(), Sort::Int)),
            )),
            Box::new(Formula::Int(i128::MAX)),
        ),
        contract_metadata: None,
    };

    // Certificate should be stale for v2 (fingerprint mismatch before even reaching kernel)
    let err = pipeline
        .verify_existing(&vc_v2, &certificate)
        .expect_err("certificate should be stale after code change");
    assert!(
        matches!(err, crate::error::CertificateError::StaleCertificate { .. }),
        "error should be StaleCertificate, got: {err:?}"
    );

    // Fingerprint-level staleness check (no kernel involved)
    assert!(
        !certificate.is_valid_for(&vc_v2),
        "certificate fingerprint should not match changed VC"
    );
}

// ---------------------------------------------------------------------------
// Test 10: Clean translation fidelity for complex formulas
// ---------------------------------------------------------------------------

#[test]
fn test_clean_translation_fidelity_complex() {
    // Verify that translate_vc_to_clean_theorem produces structurally
    // correct clean expressions for complex VCs.
    let vc = postcondition_vc();
    let theorem = clean_bridge::translate_vc_to_clean_theorem(&vc.kind, &vc.formula);
    let debug = format!("{theorem:?}");

    // The theorem should contain the VC.holds wrapper
    assert!(debug.contains("holds"), "theorem should contain Trust.VC.holds");
    assert!(debug.contains("postcondition"), "theorem should reference postcondition kind");
    // Forall quantifier should appear in the translation
    assert!(debug.contains("forall"), "theorem should contain forall quantifier");

    // Translate the formula standalone and verify it's embeddable
    let formula_expr = clean_bridge::translate_formula(&vc.formula);
    let formula_debug = format!("{formula_expr:?}");
    assert!(formula_debug.contains("forall"), "formula translation should contain forall");
    assert!(formula_debug.contains("implies"), "formula translation should contain implies");
    assert!(formula_debug.contains("select"), "formula should contain array select operations");
}

// ---------------------------------------------------------------------------
// Test 11: ProofCert serialization roundtrip through clean_bridge
// ---------------------------------------------------------------------------

#[test]
fn test_proof_cert_serialization_through_bridge() {
    // Create a clean ProofCert, serialize via clean_bridge, deserialize, verify equality
    let cert = ProofCert::Sort { level: LeanLevel::succ(LeanLevel::zero()) };

    let bytes =
        clean_bridge::serialize_proof_cert(&cert).expect("ProofCert serialization should succeed");
    assert!(!bytes.is_empty());

    let recovered = clean_bridge::deserialize_proof_cert(&bytes)
        .expect("ProofCert deserialization should succeed");
    assert_eq!(cert, recovered, "ProofCert should survive roundtrip through clean_bridge");

    // Invalid bytes should fail
    let err = clean_bridge::deserialize_proof_cert(&[0xFF, 0x00, 0xDE])
        .expect_err("invalid bytes should fail deserialization");
    assert!(
        matches!(err, crate::error::CertificateError::InvalidProofTerm { .. }),
        "error should be InvalidProofTerm, got: {err:?}"
    );
}

// ---------------------------------------------------------------------------
// Test 12: Empty bundle rejected, single-cert bundle works
// ---------------------------------------------------------------------------

#[test]
fn test_bundle_edge_cases() {
    let pipeline = CertificationPipeline::new();
    let vc = divzero_vc();
    let result = proved_result("ay");

    // Empty bundle rejected
    let err = TrustProofCertificateBundle::new("test", vec![])
        .expect_err("empty bundle should be rejected");
    assert!(
        matches!(err, crate::error::CertificateError::EmptyCertificateBundle { .. }),
        "error should be EmptyCertificateBundle, got: {err:?}"
    );

    // Single certificate bundle
    // Trust: #758 — certify_unchecked produces Trusted (not kernel-verified)
    let cert_result = pipeline.certify_unchecked(&vc, &result, mock_proof_term());
    let certificate = match cert_result {
        CertificationResult::Certified { certificate, .. }
        | CertificationResult::Trusted { certificate, .. } => certificate,
        other => panic!("expected certificate, got: {other:?}"),
    };

    let single = TrustProofCertificateBundle::single("single-test", certificate.clone());
    assert_eq!(single.len(), 1);
    assert_eq!(single.project(), "single-test");

    // Roundtrip single bundle
    let bytes = single.to_bytes().expect("serialize");
    let recovered = TrustProofCertificateBundle::from_bytes(&bytes).expect("deserialize");
    assert_eq!(recovered.len(), 1);
    assert_eq!(
        recovered.iter().next().expect("one cert").vc_fingerprint,
        certificate.vc_fingerprint
    );
}

// ===========================================================================
// #665: Integration tests for clean export pipeline and proof chain validation
// ===========================================================================

// ---------------------------------------------------------------------------
// Test 13: Golden-reference integration test — known VC produces expected
// clean proof term structure (no clean binary required)
// ---------------------------------------------------------------------------

#[test]
fn test_golden_reference_vc_to_clean_export() {
    // Golden VC: division-by-zero guard "divisor != 0"
    let vc = divzero_vc();

    // Step 1: Translate VC to clean theorem statement
    let theorem = clean_bridge::translate_vc_to_clean_theorem(&vc.kind, &vc.formula);
    let theorem_debug = format!("{theorem:?}");

    // Golden assertions: the theorem must have this exact structure:
    // Trust.VC.holds(Trust.VcKind.divisionByZero, Not(Trust.Formula.eq(var("divisor"), int(0))))
    assert!(
        theorem_debug.contains("holds"),
        "golden: theorem must wrap in Trust.VC.holds, got: {theorem_debug}"
    );
    assert!(
        theorem_debug.contains("divisionByZero"),
        "golden: theorem must reference divisionByZero kind, got: {theorem_debug}"
    );
    assert!(
        theorem_debug.contains("Not"),
        "golden: formula must contain Not (negation of equality), got: {theorem_debug}"
    );
    assert!(
        theorem_debug.contains("\"eq\""),
        "golden: formula must contain eq operation, got: {theorem_debug}"
    );
    assert!(
        theorem_debug.contains("\"divisor\""),
        "golden: formula must reference divisor variable, got: {theorem_debug}"
    );

    // Step 2: Translate the formula standalone
    let formula_expr = clean_bridge::translate_formula(&vc.formula);
    let formula_debug = format!("{formula_expr:?}");
    assert!(formula_debug.contains("Not"), "golden: standalone formula must contain Not");
    assert!(formula_debug.contains("\"eq\""), "golden: standalone formula must contain eq");

    // Step 3: Generate a certificate via the full pipeline
    let result = proved_result("ay");
    let proof_term = mock_proof_term();
    let pipeline = CertificationPipeline::new();
    let cert_result = pipeline.certify_unchecked(&vc, &result, proof_term.clone());
    // Trust: #758 — certify_unchecked returns Trusted (not kernel-verified)
    assert!(
        cert_result.is_certified() || cert_result.is_trusted(),
        "golden: pipeline should produce certificate for divzero VC, got: {cert_result:?}"
    );

    // Step 4: Verify via bridge — produces ProofCertificate + CertificateChain
    let bridge = CertificationBridge::new();
    let output = bridge
        .certify_unchecked(&vc, &result, proof_term, "2026-04-13T00:00:00Z")
        .expect("golden: bridge should produce output");
    // Bridge unchecked path produces non-empty output
    assert!(output.has_record());

    let (proof_cert, chain) = match &output {
        PipelineOutput::Record { certificate, chain, .. } => (certificate, chain),
        PipelineOutput::NoRecord { reason } => {
            panic!("golden: expected certificate, got NoRecord: {reason}");
        }
    };

    // Step 5: Verify chain structure
    assert_eq!(chain.len(), 2, "golden: unchecked path = VcGeneration + SolverProof");
    assert_eq!(chain.steps[0].step_type, ChainStepType::VcGeneration);
    assert_eq!(chain.steps[1].step_type, ChainStepType::SolverProof);
    chain.verify_integrity().expect("golden: chain integrity should hold");

    // Step 6: Validate chain via ChainValidator
    let validation = trust_proof_cert::ChainValidator::validate(chain);
    assert!(
        validation.valid,
        "golden: ChainValidator should pass for well-formed chain: {validation:?}"
    );

    // Step 7: Verify certificate fields
    assert_eq!(proof_cert.function, "safe_div");
    assert_eq!(proof_cert.solver.name, "ay");
}

// ---------------------------------------------------------------------------
// Test 14: Golden-reference — overflow VC export fidelity
// ---------------------------------------------------------------------------

#[test]
fn test_golden_reference_overflow_vc_export() {
    let vc = overflow_vc();

    // Translate to clean theorem
    let theorem = clean_bridge::translate_vc_to_clean_theorem(&vc.kind, &vc.formula);
    let debug = format!("{theorem:?}");

    // Golden structure: Trust.VC.holds(arithmeticOverflow, Not(And(le(...), le(...))))
    assert!(debug.contains("holds"), "golden: must contain holds");
    assert!(debug.contains("arithmeticOverflow"), "golden: must contain arithmeticOverflow");
    assert!(debug.contains("Not"), "golden: overflow formula must contain Not");
    assert!(debug.contains("And"), "golden: overflow formula must contain And (conjunction)");
    assert!(debug.contains("\"le\""), "golden: must contain le comparison");
    assert!(debug.contains("\"add\""), "golden: must contain add operation");
    assert!(debug.contains("\"a\""), "golden: must reference variable a");
    assert!(debug.contains("\"b\""), "golden: must reference variable b");

    // Full pipeline roundtrip
    let result = proved_result("ay");
    let bridge = CertificationBridge::new();
    let output = bridge
        .certify_unchecked(&vc, &result, mock_proof_term(), "2026-04-13T00:00:00Z")
        .expect("golden: overflow VC should produce output");
    assert!(output.has_record());
}

// ---------------------------------------------------------------------------
// Test 15: Golden-reference — postcondition VC with quantifier export
// ---------------------------------------------------------------------------

#[test]
fn test_golden_reference_quantified_postcondition_export() {
    let vc = postcondition_vc();

    let theorem = clean_bridge::translate_vc_to_clean_theorem(&vc.kind, &vc.formula);
    let debug = format!("{theorem:?}");

    // Golden structure for forall quantifier over array sortedness
    assert!(debug.contains("holds"), "golden: must contain holds");
    assert!(debug.contains("postcondition"), "golden: must contain postcondition");
    assert!(debug.contains("\"forall\""), "golden: must contain forall quantifier");
    assert!(debug.contains("\"implies\""), "golden: quantifier body must contain implies");
    assert!(debug.contains("\"select\""), "golden: must contain array select");
    assert!(debug.contains("\"le\""), "golden: sorted comparison must use le");

    // Verify the standalone formula preserves quantifier structure
    let formula_expr = clean_bridge::translate_formula(&vc.formula);
    let f_debug = format!("{formula_expr:?}");
    assert!(f_debug.contains("\"forall\""), "golden: standalone must preserve forall");
    assert!(f_debug.contains("\"i\""), "golden: quantifier variable must be 'i'");
}

// ---------------------------------------------------------------------------
// Test 16: Full pipeline golden — VC -> certificate -> chain validation
// ---------------------------------------------------------------------------

#[test]
fn test_golden_full_pipeline_chain_validation() {
    // Exercise the full pipeline for 4 different VC types and validate
    // every chain passes ChainValidator.
    let bridge = CertificationBridge::new();
    let proof_term = mock_proof_term();

    let vcs = vec![
        ("overflow", overflow_vc()),
        ("bounds", bounds_check_vc()),
        ("divzero", divzero_vc()),
        ("postcondition", postcondition_vc()),
    ];

    for (label, vc) in &vcs {
        let result = proved_result("ay");
        let output = bridge
            .certify_unchecked(vc, &result, proof_term.clone(), "2026-04-13T00:00:00Z")
            .unwrap_or_else(|e| panic!("golden pipeline: {label} should succeed: {e}"));

        let chain = match &output {
            PipelineOutput::Record { chain, .. } => chain,
            PipelineOutput::NoRecord { reason } => {
                panic!("golden pipeline: {label} expected a record, got: {reason}")
            }
        };

        // Every chain must pass integrity
        chain
            .verify_integrity()
            .unwrap_or_else(|e| panic!("golden pipeline: {label} chain integrity failed: {e}"));

        // Every chain must pass ChainValidator
        let validation = trust_proof_cert::ChainValidator::validate(chain);
        assert!(validation.valid, "golden pipeline: {label} ChainValidator failed: {validation:?}");
    }
}

// ---------------------------------------------------------------------------
// Test 17: Clean translation determinism — same VC always produces same output
// ---------------------------------------------------------------------------

#[test]
fn test_clean_translation_determinism() {
    let vc = overflow_vc();

    let t1 = clean_bridge::translate_vc_to_clean_theorem(&vc.kind, &vc.formula);
    let t2 = clean_bridge::translate_vc_to_clean_theorem(&vc.kind, &vc.formula);

    let debug1 = format!("{t1:?}");
    let debug2 = format!("{t2:?}");
    assert_eq!(debug1, debug2, "clean translation must be deterministic");
}

// ---------------------------------------------------------------------------
// Test 18: Feature-gated clean binary integration test
// ---------------------------------------------------------------------------

#[cfg(feature = "clean-integration")]
#[test]
fn test_clean_binary_verifies_generated_proof() {
    // This test requires the clean binary to be installed and on PATH.
    // It is gated behind cfg(feature = "clean-integration") so it only
    // runs when explicitly enabled.
    //
    // The test generates a proof certificate for a simple VC, then
    // invokes the clean kernel verification.

    use clean_kernel::cert::ProofCert;
    use clean_kernel::level::Level as LeanLevel;

    let vc = divzero_vc();

    // Translate the VC to a clean theorem
    let theorem = clean_bridge::translate_vc_to_clean_theorem(&vc.kind, &vc.formula);

    // Create a Sort proof cert (this will be rejected by the kernel
    // since Sort doesn't prove a Prop, but it exercises the pipeline)
    let cert = ProofCert::Sort { level: LeanLevel::zero() };

    // Verify through the clean bridge
    let verify_result = clean_bridge::verify_proof_cert(&cert, &theorem);

    // We expect rejection: Sort{level=0} is Prop, but it doesn't
    // prove the div-by-zero theorem. This confirms the kernel is
    // reachable and actively checking proofs.
    assert!(verify_result.is_err(), "clean kernel should reject Sort cert for div-by-zero VC");
}
