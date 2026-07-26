// trust-clean integration tests: CertificateChain and ChainValidator
//
// These tests exercise chain.rs validate() from an integration perspective:
// chains are produced by the CertificationBridge (not hand-constructed),
// and then validated using ChainValidator. Additional hand-constructed
// chains test specific failure modes.
//
// Acceptance criteria from #665:
// - chain.rs validate() tests: valid chain passes
// - Mismatched hashes fail
// - Wrong step ordering fails
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_clean::integration::{CertificationBridge, PipelineOutput};
use trust_proof_cert::{
    CertificateChain, CertificateStore, ChainFindingKind, ChainStep, ChainStepType, ChainValidator,
};
use trust_types::*;

// ---------------------------------------------------------------------------
// Test helpers
// ---------------------------------------------------------------------------

fn sample_vc() -> VerificationCondition {
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

fn overflow_vc() -> VerificationCondition {
    VerificationCondition {
        kind: VcKind::ArithmeticOverflow {
            op: BinOp::Add,
            operand_tys: (Ty::usize(), Ty::usize()),
        },
        function: "get_midpoint".into(),
        location: SourceSpan::default(),
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

fn proved_result() -> VerificationResult {
    VerificationResult::Proved {
        solver: "ay".into(),
        time_ms: 5,
        strength: ProofStrength::smt_unsat(),
        proof_certificate: None,
        solver_warnings: None,
        native_proof_envelope: None,
    }
}

/// Extract chain from a PipelineOutput, panicking if not Certified.
fn extract_chain(output: &PipelineOutput) -> &CertificateChain {
    match output {
        PipelineOutput::Record { chain, .. } => chain,
        PipelineOutput::NoRecord { reason } => {
            panic!("expected a record, got NoRecord: {reason}")
        }
        _ => panic!("unexpected PipelineOutput variant"),
    }
}

// ===========================================================================
// AC3-a: Valid chain passes ChainValidator (pipeline-generated chains)
// ===========================================================================

/// Chain produced by the unchecked bridge path should pass validation.
#[test]
fn test_pipeline_generated_chain_passes_validation() {
    let bridge = CertificationBridge::new();
    let vc = sample_vc();
    let result = proved_result();

    let output = bridge
        .certify_unchecked(&vc, &result, vec![0xCA, 0xFE], "2026-04-13T00:00:00Z")
        .expect("should succeed");

    let chain = extract_chain(&output);

    // verify_integrity (hash linkage only)
    chain.verify_integrity().expect("pipeline-generated chain should have valid hash linkage");

    // Full ChainValidator (hash linkage + ordering + gap detection + duplicates)
    let validation = ChainValidator::validate(chain);
    assert!(
        validation.valid,
        "pipeline-generated chain should pass full validation: {:?}",
        validation.findings
    );
    assert!(validation.findings.is_empty());
}

/// Chain produced for multiple VCs stored together should all pass validation.
#[test]
fn test_multiple_pipeline_chains_all_valid() {
    let bridge = CertificationBridge::new();
    let mut store = CertificateStore::new("chain-test");

    let vcs = vec![(sample_vc(), "2026-04-13T10:00:00Z"), (overflow_vc(), "2026-04-13T10:01:00Z")];

    let mut chains = Vec::new();

    for (vc, timestamp) in &vcs {
        let result = proved_result();
        let output = bridge
            .certify_and_store(vc, &result, vec![0xAB], timestamp, &mut store)
            .expect("should succeed");

        let chain = extract_chain(&output).clone();
        chains.push(chain);
    }

    for (i, chain) in chains.iter().enumerate() {
        let validation = ChainValidator::validate(chain);
        assert!(validation.valid, "chain {i} should pass validation: {:?}", validation.findings);
    }

    // Validate via validate_chain (returns Result) too
    for (i, chain) in chains.iter().enumerate() {
        ChainValidator::validate_chain(chain)
            .unwrap_or_else(|e| panic!("chain {i} should pass validate_chain: {e}"));
    }
}

/// Pipeline chain structure should have correct step types and ordering.
#[test]
fn test_pipeline_chain_step_structure() {
    let bridge = CertificationBridge::new();
    let vc = sample_vc();
    let result = proved_result();

    let output = bridge
        .certify_unchecked(&vc, &result, vec![0x01], "2026-04-13T00:00:00Z")
        .expect("should succeed");

    let chain = extract_chain(&output);

    assert_eq!(chain.len(), 2, "unchecked path: VcGeneration + SolverProof");
    assert_eq!(chain.steps[0].step_type, ChainStepType::VcGeneration);
    assert_eq!(chain.steps[1].step_type, ChainStepType::SolverProof);
    assert!(!chain.is_clean_certified());
    assert!(!chain.is_empty());
    assert!(chain.total_time_ms() < 10_000, "pipeline should be fast");
}

// ===========================================================================
// AC3-b: Mismatched hashes fail validation
// ===========================================================================

/// Chain with mismatched output/input hashes between steps should fail.
#[test]
fn test_hash_mismatch_fails_validation() {
    let mut chain = CertificateChain::new();
    chain.push(ChainStep {
        step_type: ChainStepType::VcGeneration,
        tool: "trust_vcgen".to_string(),
        tool_version: "0.1.0".to_string(),
        input_hash: "mir-hash".to_string(),
        output_hash: "vc-hash-CORRECT".to_string(),
        time_ms: 1,
        timestamp: "2026-04-13T00:00:00Z".to_string(),
    });
    chain.push(ChainStep {
        step_type: ChainStepType::SolverProof,
        tool: "ay".to_string(),
        tool_version: "1.0.0".to_string(),
        input_hash: "vc-hash-WRONG".to_string(), // Mismatch!
        output_hash: "proof-hash".to_string(),
        time_ms: 10,
        timestamp: "2026-04-13T00:00:01Z".to_string(),
    });

    // verify_integrity should fail
    let err = chain.verify_integrity().expect_err("mismatched hashes should fail integrity check");
    let msg = format!("{err}");
    assert!(
        msg.contains("step 0") || msg.contains("hash"),
        "error should reference the step and hash mismatch, got: {msg}"
    );

    // ChainValidator should also catch it
    let validation = ChainValidator::validate(&chain);
    assert!(!validation.valid, "mismatched hashes should fail validation");
    assert!(
        validation.findings.iter().any(|f| f.kind == ChainFindingKind::HashMismatch),
        "should report HashMismatch finding"
    );
}

/// Three-step chain with hash mismatch between step 1 and step 2.
#[test]
fn test_hash_mismatch_in_three_step_chain() {
    let mut chain = CertificateChain::new();
    chain.push(ChainStep {
        step_type: ChainStepType::VcGeneration,
        tool: "trust_vcgen".to_string(),
        tool_version: "0.1.0".to_string(),
        input_hash: "mir".to_string(),
        output_hash: "vc-hash".to_string(),
        time_ms: 1,
        timestamp: "2026-04-13T00:00:00Z".to_string(),
    });
    chain.push(ChainStep {
        step_type: ChainStepType::SolverProof,
        tool: "ay".to_string(),
        tool_version: "1.0.0".to_string(),
        input_hash: "vc-hash".to_string(), // Correct linkage from step 0
        output_hash: "proof-hash-A".to_string(),
        time_ms: 10,
        timestamp: "2026-04-13T00:00:01Z".to_string(),
    });
    chain.push(ChainStep {
        step_type: ChainStepType::CleanCertification,
        tool: "clean".to_string(),
        tool_version: "5.0.0".to_string(),
        input_hash: "proof-hash-B".to_string(), // MISMATCH: should be proof-hash-A
        output_hash: "certified".to_string(),
        time_ms: 5,
        timestamp: "2026-04-13T00:00:02Z".to_string(),
    });

    let validation = ChainValidator::validate(&chain);
    assert!(!validation.valid);
    assert!(
        validation.findings.iter().any(|f| f.kind == ChainFindingKind::HashMismatch),
        "should detect hash mismatch between steps 1 and 2"
    );

    // The specific step index should be 1 (between step 1 output and step 2 input)
    let mismatch = validation
        .findings
        .iter()
        .find(|f| f.kind == ChainFindingKind::HashMismatch)
        .expect("should have HashMismatch finding");
    assert_eq!(mismatch.step_index, 1, "hash mismatch should be reported at step index 1");
}

// ===========================================================================
// AC3-c: Wrong step ordering fails validation
// ===========================================================================

/// SolverProof before VcGeneration should fail ordering validation.
#[test]
fn test_wrong_step_ordering_solver_before_vcgen() {
    let mut chain = CertificateChain::new();
    // SolverProof (rank 1) before VcGeneration (rank 0) — invalid order
    chain.push(ChainStep {
        step_type: ChainStepType::SolverProof,
        tool: "ay".to_string(),
        tool_version: "1.0.0".to_string(),
        input_hash: "a".to_string(),
        output_hash: "b".to_string(),
        time_ms: 10,
        timestamp: "2026-04-13T00:00:00Z".to_string(),
    });
    chain.push(ChainStep {
        step_type: ChainStepType::VcGeneration,
        tool: "trust_vcgen".to_string(),
        tool_version: "0.1.0".to_string(),
        input_hash: "b".to_string(),
        output_hash: "c".to_string(),
        time_ms: 1,
        timestamp: "2026-04-13T00:00:01Z".to_string(),
    });

    let validation = ChainValidator::validate(&chain);
    assert!(!validation.valid);
    assert!(
        validation.findings.iter().any(|f| f.kind == ChainFindingKind::OutOfOrder),
        "should report OutOfOrder finding: {:?}",
        validation.findings
    );
}

/// CleanCertification before SolverProof should fail ordering.
#[test]
fn test_wrong_step_ordering_clean_before_solver() {
    let mut chain = CertificateChain::new();
    chain.push(ChainStep {
        step_type: ChainStepType::VcGeneration,
        tool: "trust_vcgen".to_string(),
        tool_version: "0.1.0".to_string(),
        input_hash: "mir".to_string(),
        output_hash: "vc".to_string(),
        time_ms: 1,
        timestamp: "2026-04-13T00:00:00Z".to_string(),
    });
    chain.push(ChainStep {
        step_type: ChainStepType::CleanCertification,
        tool: "clean".to_string(),
        tool_version: "5.0.0".to_string(),
        input_hash: "vc".to_string(),
        output_hash: "certified".to_string(),
        time_ms: 5,
        timestamp: "2026-04-13T00:00:01Z".to_string(),
    });
    chain.push(ChainStep {
        step_type: ChainStepType::SolverProof,
        tool: "ay".to_string(),
        tool_version: "1.0.0".to_string(),
        input_hash: "certified".to_string(),
        output_hash: "proof".to_string(),
        time_ms: 10,
        timestamp: "2026-04-13T00:00:02Z".to_string(),
    });

    let validation = ChainValidator::validate(&chain);
    assert!(!validation.valid);
    assert!(
        validation.findings.iter().any(|f| f.kind == ChainFindingKind::OutOfOrder),
        "CleanCertification (rank 2) followed by SolverProof (rank 1) is out of order"
    );
}

// ===========================================================================
// Additional chain validation: empty, missing steps, duplicates
// ===========================================================================

/// Empty chain should fail validation with EmptyChain finding.
#[test]
fn test_empty_chain_fails_validation() {
    let chain = CertificateChain::new();

    let validation = ChainValidator::validate(&chain);
    assert!(!validation.valid);
    assert_eq!(validation.findings.len(), 1);
    assert_eq!(validation.findings[0].kind, ChainFindingKind::EmptyChain);

    // Structural validation and integrity both reject an empty provenance chain.
    chain
        .verify_integrity()
        .expect_err("empty chain has no provenance record for integrity checking");
}

/// Chain missing VcGeneration step should fail.
#[test]
fn test_missing_vc_generation_step_fails() {
    let mut chain = CertificateChain::new();
    chain.push(ChainStep {
        step_type: ChainStepType::SolverProof,
        tool: "ay".to_string(),
        tool_version: "1.0.0".to_string(),
        input_hash: "vc".to_string(),
        output_hash: "proof".to_string(),
        time_ms: 10,
        timestamp: "2026-04-13T00:00:00Z".to_string(),
    });

    let validation = ChainValidator::validate(&chain);
    assert!(!validation.valid);
    assert!(
        validation.findings.iter().any(|f| f.kind == ChainFindingKind::MissingStep),
        "should report MissingStep for VcGeneration"
    );
}

/// Duplicate step types should fail validation.
#[test]
fn test_duplicate_step_type_fails() {
    let mut chain = CertificateChain::new();
    chain.push(ChainStep {
        step_type: ChainStepType::VcGeneration,
        tool: "trust_vcgen".to_string(),
        tool_version: "0.1.0".to_string(),
        input_hash: "a".to_string(),
        output_hash: "b".to_string(),
        time_ms: 1,
        timestamp: "2026-04-13T00:00:00Z".to_string(),
    });
    chain.push(ChainStep {
        step_type: ChainStepType::VcGeneration, // Duplicate!
        tool: "trust_vcgen".to_string(),
        tool_version: "0.1.0".to_string(),
        input_hash: "b".to_string(),
        output_hash: "c".to_string(),
        time_ms: 1,
        timestamp: "2026-04-13T00:00:01Z".to_string(),
    });

    let validation = ChainValidator::validate(&chain);
    assert!(!validation.valid);
    assert!(
        validation.findings.iter().any(|f| f.kind == ChainFindingKind::DuplicateStep),
        "should report DuplicateStep"
    );
}

/// validate_chain returns Err on invalid chains, Ok on valid ones.
#[test]
fn test_validate_chain_result_api() {
    // Invalid: empty chain
    let empty = CertificateChain::new();
    let err = ChainValidator::validate_chain(&empty).expect_err("empty chain should error");
    let msg = format!("{err}");
    assert!(msg.contains("no steps"), "error should mention no steps, got: {msg}");

    // Valid: well-formed two-step chain
    let mut valid = CertificateChain::new();
    valid.push(ChainStep {
        step_type: ChainStepType::VcGeneration,
        tool: "trust_vcgen".to_string(),
        tool_version: "0.1.0".to_string(),
        input_hash: "mir".to_string(),
        output_hash: "vc-hash".to_string(),
        time_ms: 1,
        timestamp: "2026-04-13T00:00:00Z".to_string(),
    });
    valid.push(ChainStep {
        step_type: ChainStepType::SolverProof,
        tool: "ay".to_string(),
        tool_version: "1.0.0".to_string(),
        input_hash: "vc-hash".to_string(),
        output_hash: "proof-hash".to_string(),
        time_ms: 10,
        timestamp: "2026-04-13T00:00:01Z".to_string(),
    });

    let result = ChainValidator::validate_chain(&valid).expect("valid chain should pass");
    assert!(result.valid);
}

// ===========================================================================
// Chain JSON roundtrip
// ===========================================================================

/// Chain should survive JSON serialization roundtrip.
#[test]
fn test_chain_json_roundtrip() {
    let bridge = CertificationBridge::new();
    let vc = sample_vc();
    let result = proved_result();

    let output = bridge
        .certify_unchecked(&vc, &result, vec![0x01], "2026-04-13T00:00:00Z")
        .expect("should succeed");

    let chain = extract_chain(&output);

    let json = chain.to_json().expect("chain should serialize to JSON");
    let recovered = CertificateChain::from_json(&json).expect("chain should deserialize from JSON");

    assert_eq!(*chain, recovered, "chain should survive JSON roundtrip");

    // The recovered chain should also pass validation
    let validation = ChainValidator::validate(&recovered);
    assert!(validation.valid, "recovered chain should pass validation: {:?}", validation.findings);
}

// ===========================================================================
// ChainSummary from pipeline-generated chains
// ===========================================================================

/// Verify ChainSummary correctly summarizes pipeline-generated chains.
#[test]
fn test_chain_summary_from_pipeline_chains() {
    use trust_proof_cert::ChainSummary;

    let bridge = CertificationBridge::new();
    let result = proved_result();

    let out1 = bridge
        .certify_unchecked(&sample_vc(), &result, vec![0x01], "2026-04-13T10:00:00Z")
        .expect("should succeed");
    let out2 = bridge
        .certify_unchecked(&overflow_vc(), &result, vec![0x02], "2026-04-13T10:01:00Z")
        .expect("should succeed");

    let chain1 = extract_chain(&out1);
    let chain2 = extract_chain(&out2);
    let chains = vec![chain1, chain2];

    let summary = ChainSummary::from_chains(&chains);
    assert_eq!(summary.total_vcs, 2);
    assert_eq!(summary.proved, 2, "both chains have SolverProof steps");
    assert_eq!(summary.certified, 0, "unchecked path: no CleanCertification");
    assert_eq!(summary.valid_chains, 2, "both chains should be valid");
    assert_eq!(summary.invalid_chains, 0);
    assert!((summary.coverage_percent() - 100.0).abs() < f64::EPSILON);
    assert!((summary.certification_percent() - 0.0).abs() < f64::EPSILON);
}
