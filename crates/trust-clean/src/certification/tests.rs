// trust-clean/certification/tests.rs: Tests for the certification pipeline
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::*;

use super::generation::serialize_lean_proof_term;
use super::*;
use crate::error::CertificateError;
use crate::logic_classification::{CertificationScope, SmtLogic};
use crate::reconstruction::{LeanProofTerm, ProofStep, SolverProof, validate_reconstruction};

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

fn failed_result() -> VerificationResult {
    VerificationResult::Failed { solver: "ay".into(), time_ms: 3, counterexample: None }
}

/// The FIRST live path to a real kernel `Certified`: a VC whose violation is a
/// direct contradiction (`p ∧ ¬p`) is certified end-to-end by the clean CIC
/// kernel (via the genuine universal refutation `∀ P, (And P (Not P)) → False`),
/// NOT trusted-fallback. Soundness reduces to the kernel.
#[test]
fn direct_contradiction_vc_is_kernel_certified_end_to_end() {
    let pipeline = CertificationPipeline::new();
    let p = Formula::Var("p".into(), Sort::Bool);
    let vc = VerificationCondition {
        kind: VcKind::Assertion { message: "direct contradiction".to_string() },
        function: "test_direct_contradiction".into(),
        location: SourceSpan::default(),
        formula: Formula::And(vec![p.clone(), Formula::Not(Box::new(p))]),
        contract_metadata: None,
    };
    let result = proved_result();
    // Any non-empty solver proof; the genuine-kernel fast path keys on vc.formula.
    let solver_proof = simple_axiom_proof("contradiction", Formula::Bool(true));

    let cert = pipeline.certify_from_solver_proof(&vc, &result, &solver_proof);
    assert!(
        cert.is_certified(),
        "direct-contradiction VC must reach kernel Certified end-to-end, got: {cert:?}"
    );
    // And a NON-contradiction VC must NOT be spuriously certified by this path
    // (it has no resolution proof either, so it stays non-Certified).
    let non = pipeline.certify_from_solver_proof(&sample_vc(), &result, &solver_proof);
    assert!(
        !non.is_certified(),
        "non-contradiction VC must not be falsely kernel-Certified, got: {non:?}"
    );
}

/// Live end-to-end Certified via the GENERAL propositional path: a multi-clause
/// resolution VC `(p ∨ q) ∧ ¬p ∧ ¬q` — which the direct-contradiction path
/// cannot handle — is certified by the clean kernel through exhaustive nested
/// `Bool.rec` over the formula's Boolean skeleton. Soundness reduces to the
/// kernel; theory-dependent VCs still decline (see the unit tests in clean_bridge).
#[test]
fn multi_clause_resolution_vc_is_kernel_certified_end_to_end() {
    let pipeline = CertificationPipeline::new();
    let p = Formula::Var("p".into(), Sort::Bool);
    let q = Formula::Var("q".into(), Sort::Bool);
    let vc = VerificationCondition {
        kind: VcKind::Assertion { message: "two-clause resolution".to_string() },
        function: "test_resolution".into(),
        location: SourceSpan::default(),
        formula: Formula::And(vec![
            Formula::Or(vec![p.clone(), q.clone()]),
            Formula::Not(Box::new(p)),
            Formula::Not(Box::new(q)),
        ]),
        contract_metadata: None,
    };
    let result = proved_result();
    let solver_proof = simple_axiom_proof("resolution", Formula::Bool(true));

    let cert = pipeline.certify_from_solver_proof(&vc, &result, &solver_proof);
    assert!(
        cert.is_certified(),
        "multi-clause resolution VC must reach kernel Certified end-to-end, got: {cert:?}"
    );
}

/// Live end-to-end Certified via the EUF path: a transitivity-chain VC
/// `a=b ∧ b=c ∧ ¬(a=c)` — invisible to both the direct-contradiction and the
/// propositional paths — is certified by the clean kernel through an
/// `Eq.trans` chain. Soundness reduces to the kernel.
#[test]
fn euf_transitivity_vc_is_kernel_certified_end_to_end() {
    let pipeline = CertificationPipeline::new();
    let a = Formula::Var("a".into(), Sort::Int);
    let b = Formula::Var("b".into(), Sort::Int);
    let c = Formula::Var("c".into(), Sort::Int);
    let eq = |l: Formula, r: Formula| Formula::Eq(Box::new(l), Box::new(r));
    let vc = VerificationCondition {
        kind: VcKind::Assertion { message: "euf transitivity".to_string() },
        function: "test_euf".into(),
        location: SourceSpan::default(),
        formula: Formula::And(vec![
            eq(a.clone(), b.clone()),
            eq(b, c.clone()),
            Formula::Not(Box::new(eq(a, c))),
        ]),
        contract_metadata: None,
    };
    let result = proved_result();
    let solver_proof = simple_axiom_proof("euf", Formula::Bool(true));

    let cert = pipeline.certify_from_solver_proof(&vc, &result, &solver_proof);
    assert!(
        cert.is_certified(),
        "EUF transitivity VC must reach kernel Certified end-to-end, got: {cert:?}"
    );
}

/// Helper: build a QF_LIA VC for overflow checking.
fn qf_lia_overflow_vc() -> VerificationCondition {
    VerificationCondition {
        kind: VcKind::ArithmeticOverflow {
            op: BinOp::Add,
            operand_tys: (Ty::usize(), Ty::usize()),
        },
        function: "get_midpoint".into(),
        location: SourceSpan::default(),
        formula: Formula::Le(
            Box::new(Formula::Add(
                Box::new(Formula::Var("a".into(), Sort::Int)),
                Box::new(Formula::Var("b".into(), Sort::Int)),
            )),
            Box::new(Formula::Int((1i128 << 64) - 1)),
        ),
        contract_metadata: None,
    }
}

/// Helper: build a QF_UF VC for equality reasoning.
fn qf_uf_equality_vc() -> VerificationCondition {
    VerificationCondition {
        kind: VcKind::Assertion { message: "equality check".to_string() },
        function: "test_eq".into(),
        location: SourceSpan::default(),
        formula: Formula::Eq(
            Box::new(Formula::Var("a".into(), Sort::Bool)),
            Box::new(Formula::Var("b".into(), Sort::Bool)),
        ),
        contract_metadata: None,
    }
}

/// Helper: build a simple solver proof with one axiom step.
fn simple_axiom_proof(axiom_name: &str, formula: Formula) -> SolverProof {
    SolverProof {
        steps: vec![ProofStep::Axiom { name: axiom_name.to_string(), formula }],
        used_axioms: vec![axiom_name.to_string()],
        used_lemmas: vec![],
    }
}

// -----------------------------------------------------------------------
// CertificationPipeline construction
// -----------------------------------------------------------------------

#[test]
fn test_pipeline_new_creates_instance() {
    let pipeline = CertificationPipeline::new();
    assert_eq!(pipeline.default_prover_version, "clean-kernel 0.1.0");
}

#[test]
fn test_pipeline_with_prover_version() {
    let pipeline = CertificationPipeline::with_prover_version("trust-wp 0.2.0");
    assert_eq!(pipeline.default_prover_version, "trust-wp 0.2.0");
}

#[test]
fn test_pipeline_default_trait() {
    let pipeline = CertificationPipeline::default();
    assert_eq!(pipeline.default_prover_version, "clean-kernel 0.1.0");
}

// -----------------------------------------------------------------------
// CertificationResult variants
// -----------------------------------------------------------------------

#[test]
fn test_certification_result_is_trusted_for_unchecked() {
    let vc = sample_vc();
    let result = proved_result();
    let pipeline = CertificationPipeline::new();

    // Unchecked path produces Trusted, NOT Certified
    let cert_result = pipeline.certify_unchecked(&vc, &result, vec![0xDE, 0xAD]);
    assert!(cert_result.is_trusted(), "unchecked should be Trusted, got: {cert_result:?}");
    assert!(!cert_result.is_certified(), "unchecked must NOT be Certified");
    assert!(!cert_result.is_rejected());
    assert!(!cert_result.is_skipped());
}

#[test]
fn test_certification_result_is_skipped_for_failed() {
    let vc = sample_vc();
    let result = failed_result();
    let pipeline = CertificationPipeline::new();

    let cert_result = pipeline.certify(&vc, &result, vec![1, 2, 3]);
    assert!(cert_result.is_skipped());
    assert!(!cert_result.is_certified());
    assert!(!cert_result.is_rejected());

    if let CertificationResult::Skipped { reason } = &cert_result {
        assert!(reason.contains("Failed"), "reason should mention Failed, got: {reason}");
    }
}

#[test]
fn test_certification_result_is_skipped_for_unknown() {
    let vc = sample_vc();
    let result = VerificationResult::Unknown {
        solver: "ay".into(),
        time_ms: 10,
        reason: "incomplete".to_string(),
    };
    let pipeline = CertificationPipeline::new();

    let cert_result = pipeline.certify(&vc, &result, vec![1]);
    assert!(cert_result.is_skipped());
}

#[test]
fn test_certification_result_is_skipped_for_timeout() {
    let vc = sample_vc();
    let result = VerificationResult::Timeout { solver: "ay".into(), timeout_ms: 5000 };
    let pipeline = CertificationPipeline::new();

    let cert_result = pipeline.certify(&vc, &result, vec![1]);
    assert!(cert_result.is_skipped());
}

#[test]
fn test_certification_skipped_for_empty_proof_term() {
    let vc = sample_vc();
    let result = proved_result();
    let pipeline = CertificationPipeline::new();

    let cert_result = pipeline.certify(&vc, &result, vec![]);
    assert!(cert_result.is_skipped());

    if let CertificationResult::Skipped { reason } = &cert_result {
        assert!(reason.contains("empty"), "reason should mention empty, got: {reason}");
    }
}

// -----------------------------------------------------------------------
// Certification with clean kernel (full pipeline)
// -----------------------------------------------------------------------

#[test]
fn test_certify_rejects_invalid_proof_bytes() {
    let vc = sample_vc();
    let result = proved_result();
    let pipeline = CertificationPipeline::new();

    // Random bytes that aren't a valid clean ProofCert
    let cert_result = pipeline.certify(&vc, &result, vec![0xFF, 0x00, 0xDE, 0xAD]);
    assert!(
        cert_result.is_rejected(),
        "invalid proof bytes should be rejected, got: {cert_result:?}"
    );

    if let CertificationResult::Rejected { reason, .. } = &cert_result {
        assert!(
            reason.contains("proof term") || reason.contains("deserialize"),
            "reason should mention deserialization failure, got: {reason}"
        );
    }
}

#[test]
fn test_unchecked_fallback_only_for_kernel_rejection() {
    assert!(super::pipeline::should_fallback_to_unchecked(&CertificateError::KernelRejected {
        reason: "type mismatch".to_string()
    }));
    assert!(!super::pipeline::should_fallback_to_unchecked(&CertificateError::InvalidProofTerm {
        reason: "deserialize failed".to_string()
    }));
    assert!(!super::pipeline::should_fallback_to_unchecked(
        &CertificateError::SerializationFailed { reason: "bincode failed".to_string() }
    ));
}

#[test]
fn test_certify_reaches_kernel_with_valid_clean_bytes() {
    use clean_kernel::cert::ProofCert;
    use clean_kernel::level::Level as LeanLevel;

    let vc = sample_vc();
    let result = proved_result();
    let pipeline = CertificationPipeline::new();

    // Valid bincode-serialized ProofCert, but wrong proof for this VC
    let clean_cert = ProofCert::Sort { level: LeanLevel::zero() };
    let proof_bytes = bincode::serialize(&clean_cert).expect("should serialize");

    // Should reach the kernel and be rejected (Sort cert doesn't prove a div-by-zero VC)
    let cert_result = pipeline.certify(&vc, &result, proof_bytes);
    assert!(
        cert_result.is_rejected(),
        "Sort cert should be rejected by kernel, got: {cert_result:?}"
    );

    if let CertificationResult::Rejected { reason, .. } = &cert_result {
        assert!(
            reason.contains("kernel") || reason.contains("rejected"),
            "reason should mention kernel rejection, got: {reason}"
        );
    }
}

// -----------------------------------------------------------------------
// Unchecked certification (Trusted path)
// -----------------------------------------------------------------------

#[test]
fn test_certify_unchecked_produces_trusted_certificate() {
    let vc = sample_vc();
    let result = proved_result();
    let pipeline = CertificationPipeline::new();

    // certify_unchecked returns Trusted, not Certified
    let cert_result = pipeline.certify_unchecked(&vc, &result, vec![0xCA, 0xFE]);
    assert!(cert_result.is_trusted(), "unchecked should be Trusted, got: {cert_result:?}");

    if let CertificationResult::Trusted { certificate, .. } = &cert_result {
        assert_eq!(certificate.proof_term, vec![0xCA, 0xFE]);
        assert!(certificate.prover_version.contains("ay"));
    } else {
        panic!("expected Trusted variant, got: {cert_result:?}");
    }
}

#[test]
fn test_certify_unchecked_skips_non_proved() {
    let vc = sample_vc();
    let result = failed_result();
    let pipeline = CertificationPipeline::new();

    let cert_result = pipeline.certify_unchecked(&vc, &result, vec![1]);
    assert!(cert_result.is_skipped());
}

#[test]
fn test_certify_unchecked_skips_empty_proof() {
    let vc = sample_vc();
    let result = proved_result();
    let pipeline = CertificationPipeline::new();

    let cert_result = pipeline.certify_unchecked(&vc, &result, vec![]);
    assert!(cert_result.is_skipped());
}

// -----------------------------------------------------------------------
// Verify existing certificate
// -----------------------------------------------------------------------

#[test]
fn test_verify_existing_detects_stale() {
    let vc1 = sample_vc();
    let result = proved_result();
    let pipeline = CertificationPipeline::new();

    // Build a certificate for vc1 (unchecked returns Trusted, #758)
    let cert_result = pipeline.certify_unchecked(&vc1, &result, vec![0xBE, 0xEF]);
    let CertificationResult::Trusted { certificate, .. } = cert_result else {
        panic!("should produce Trusted certificate, got: {cert_result:?}");
    };

    // Verify against a different VC — should detect staleness
    let vc2 = VerificationCondition {
        kind: VcKind::RemainderByZero,
        function: "other".into(),
        location: SourceSpan::default(),
        formula: Formula::Bool(true),
        contract_metadata: None,
    };

    let err =
        pipeline.verify_existing(&vc2, &certificate).expect_err("should detect stale certificate");
    assert!(
        matches!(err, CertificateError::StaleCertificate { .. }),
        "should be StaleCertificate, got: {err:?}"
    );
}

// -----------------------------------------------------------------------
// translate_to_clean helper
// -----------------------------------------------------------------------

#[test]
fn test_translate_to_clean_produces_expr() {
    let vc = sample_vc();
    let expr = CertificationPipeline::translate_to_clean(&vc);
    let debug = format!("{expr:?}");
    // Should contain the VC.holds wrapper
    assert!(
        debug.contains("holds") || debug.contains("VC"),
        "translated expression should reference Trust.VC.holds, got: {debug}"
    );
}

// -----------------------------------------------------------------------
// result_status_name helper
// -----------------------------------------------------------------------

#[test]
fn test_result_status_name_all_variants() {
    assert_eq!(result_status_name(&proved_result()), "Proved");
    assert_eq!(result_status_name(&failed_result()), "Failed");
    assert_eq!(
        result_status_name(&VerificationResult::Unknown {
            solver: "ay".into(),
            time_ms: 0,
            reason: String::new(),
        }),
        "Unknown"
    );
    assert_eq!(
        result_status_name(&VerificationResult::Timeout { solver: "ay".into(), timeout_ms: 0 }),
        "Timeout"
    );
}

// =======================================================================
// Proof term generation and solver proof certification tests
// =======================================================================

// -----------------------------------------------------------------------
// 1. ProofTheory names
// -----------------------------------------------------------------------

#[test]
fn test_proof_theory_names() {
    assert_eq!(ProofTheory::QfLia.name(), "QF_LIA");
    assert_eq!(ProofTheory::QfUf.name(), "QF_UF");
}

// -----------------------------------------------------------------------
// 2. classify_vc_for_certification on QF_LIA formula
// -----------------------------------------------------------------------

#[test]
fn test_classify_vc_qf_lia_is_certifiable() {
    let vc = qf_lia_overflow_vc();
    let (logic, certifiable) = classify_vc_for_certification(&vc);
    assert_eq!(logic, SmtLogic::QfLia);
    assert!(certifiable, "QF_LIA should be certifiable");
}

// -----------------------------------------------------------------------
// 3. classify_vc_for_certification on QF_UF formula
// -----------------------------------------------------------------------

#[test]
fn test_classify_vc_qf_uf_is_certifiable() {
    let vc = qf_uf_equality_vc();
    let (logic, certifiable) = classify_vc_for_certification(&vc);
    assert_eq!(logic, SmtLogic::QfUf);
    assert!(certifiable, "QF_UF should be certifiable");
}

// -----------------------------------------------------------------------
// 4. classify_vc_for_certification on non-certifiable formula (QF_BV)
// -----------------------------------------------------------------------

#[test]
fn test_classify_vc_qf_bv_not_certifiable() {
    let vc = VerificationCondition {
        kind: VcKind::ArithmeticOverflow {
            op: BinOp::Add,
            operand_tys: (Ty::usize(), Ty::usize()),
        },
        function: "bv_func".into(),
        location: SourceSpan::default(),
        formula: Formula::BvAdd(
            Box::new(Formula::Var("x".into(), Sort::BitVec(32))),
            Box::new(Formula::Var("y".into(), Sort::BitVec(32))),
            32,
        ),
        contract_metadata: None,
    };
    let (logic, certifiable) = classify_vc_for_certification(&vc);
    assert_eq!(logic, SmtLogic::QfBv);
    assert!(!certifiable, "QF_BV should not be certifiable");
}

// -----------------------------------------------------------------------
// 5. generate_proof_term for QF_LIA produces Generated with QfLia theory
// -----------------------------------------------------------------------

#[test]
fn test_generate_proof_term_qf_lia() {
    let vc = qf_lia_overflow_vc();
    let solver_proof = simple_axiom_proof(
        "overflow_guard",
        Formula::Le(
            Box::new(Formula::Add(
                Box::new(Formula::Var("a".into(), Sort::Int)),
                Box::new(Formula::Var("b".into(), Sort::Int)),
            )),
            Box::new(Formula::Int((1i128 << 64) - 1)),
        ),
    );

    let pg = generate_proof_term(&vc, &solver_proof);
    assert!(pg.is_generated(), "QF_LIA proof should be generated, got: {pg:?}");

    if let ProofGeneration::Generated { proof_term, theory } = &pg {
        assert_eq!(*theory, ProofTheory::QfLia);
        assert!(validate_reconstruction(proof_term));
    }
}

// -----------------------------------------------------------------------
// 6. generate_proof_term for QF_UF produces Generated with QfUf theory
// -----------------------------------------------------------------------

#[test]
fn test_generate_proof_term_qf_uf() {
    let vc = qf_uf_equality_vc();
    let solver_proof = simple_axiom_proof(
        "eq_refl",
        Formula::Eq(
            Box::new(Formula::Var("a".into(), Sort::Bool)),
            Box::new(Formula::Var("b".into(), Sort::Bool)),
        ),
    );

    let pg = generate_proof_term(&vc, &solver_proof);
    assert!(pg.is_generated(), "QF_UF proof should be generated, got: {pg:?}");

    if let ProofGeneration::Generated { proof_term, theory } = &pg {
        assert_eq!(*theory, ProofTheory::QfUf);
        assert!(validate_reconstruction(proof_term));
    }
}

// -----------------------------------------------------------------------
// 7. generate_proof_term returns Unsupported for QF_BV
// -----------------------------------------------------------------------

#[test]
fn test_generate_proof_term_unsupported_qf_bv() {
    let vc = VerificationCondition {
        kind: VcKind::ArithmeticOverflow {
            op: BinOp::Add,
            operand_tys: (Ty::usize(), Ty::usize()),
        },
        function: "bv_func".into(),
        location: SourceSpan::default(),
        formula: Formula::BvAdd(
            Box::new(Formula::Var("x".into(), Sort::BitVec(32))),
            Box::new(Formula::Var("y".into(), Sort::BitVec(32))),
            32,
        ),
        contract_metadata: None,
    };
    let solver_proof = simple_axiom_proof("bv_axiom", Formula::Bool(true));

    let pg = generate_proof_term(&vc, &solver_proof);
    assert!(pg.is_unsupported(), "QF_BV should be unsupported, got: {pg:?}");

    if let ProofGeneration::Unsupported { logic, reason } = &pg {
        assert_eq!(*logic, SmtLogic::QfBv);
        assert!(reason.contains("partial"), "reason: {reason}");
    }
}

// -----------------------------------------------------------------------
// 8. generate_proof_term returns Failed for invalid solver proof
// -----------------------------------------------------------------------

#[test]
fn test_generate_proof_term_failed_invalid_axiom() {
    let vc = sample_vc();
    // Axiom not in used_axioms list
    let solver_proof = SolverProof {
        steps: vec![ProofStep::Axiom {
            name: "missing_axiom".to_string(),
            formula: Formula::Bool(true),
        }],
        used_axioms: vec![], // axiom not declared
        used_lemmas: vec![],
    };

    let pg = generate_proof_term(&vc, &solver_proof);
    assert!(pg.is_failed(), "invalid axiom should fail, got: {pg:?}");

    if let ProofGeneration::Failed { reason } = &pg {
        assert!(reason.contains("unknown axiom") || reason.contains("Unknown"), "reason: {reason}");
    }
}

// -----------------------------------------------------------------------
// 9. certify_from_solver_proof produces certificate for QF_LIA
// -----------------------------------------------------------------------

#[test]
fn test_certify_from_solver_proof_qf_lia() {
    let pipeline = CertificationPipeline::new();
    let vc = qf_lia_overflow_vc();
    let result = proved_result();
    let solver_proof = simple_axiom_proof(
        "overflow_bound",
        Formula::Le(
            Box::new(Formula::Add(
                Box::new(Formula::Var("a".into(), Sort::Int)),
                Box::new(Formula::Var("b".into(), Sort::Int)),
            )),
            Box::new(Formula::Int((1i128 << 64) - 1)),
        ),
    );

    let cert_result = pipeline.certify_from_solver_proof(&vc, &result, &solver_proof);
    // Trust: #758 — kernel may reject reconstructed proof terms and fall back to Trusted
    assert!(
        cert_result.is_certified() || cert_result.is_trusted(),
        "QF_LIA solver proof should produce certificate, got: {cert_result:?}"
    );

    match &cert_result {
        CertificationResult::Certified { certificate, .. }
        | CertificationResult::Trusted { certificate, .. } => {
            assert!(!certificate.proof_term.is_empty());
            assert!(certificate.prover_version.contains("ay"));
        }
        _ => {}
    }
}

// -----------------------------------------------------------------------
// 10. certify_from_solver_proof produces certificate for QF_UF
// -----------------------------------------------------------------------

#[test]
fn test_certify_from_solver_proof_qf_uf() {
    let pipeline = CertificationPipeline::new();
    let vc = qf_uf_equality_vc();
    let result = proved_result();
    let solver_proof = simple_axiom_proof(
        "eq_assumption",
        Formula::Eq(
            Box::new(Formula::Var("a".into(), Sort::Bool)),
            Box::new(Formula::Var("b".into(), Sort::Bool)),
        ),
    );

    let cert_result = pipeline.certify_from_solver_proof(&vc, &result, &solver_proof);
    // Trust: #758 — kernel may reject reconstructed proof terms and fall back to Trusted
    assert!(
        cert_result.is_certified() || cert_result.is_trusted(),
        "QF_UF solver proof should produce certificate, got: {cert_result:?}"
    );

    match &cert_result {
        CertificationResult::Certified { certificate, .. }
        | CertificationResult::Trusted { certificate, .. } => {
            assert!(!certificate.proof_term.is_empty());
        }
        _ => {}
    }
}

// -----------------------------------------------------------------------
// 11. certify_from_solver_proof skips non-Proved results
// -----------------------------------------------------------------------

#[test]
fn test_certify_from_solver_proof_skips_failed() {
    let pipeline = CertificationPipeline::new();
    let vc = sample_vc();
    let result = failed_result();
    let solver_proof = simple_axiom_proof("any", Formula::Bool(true));

    let cert_result = pipeline.certify_from_solver_proof(&vc, &result, &solver_proof);
    assert!(cert_result.is_skipped());

    if let CertificationResult::Skipped { reason } = &cert_result {
        assert!(reason.contains("Failed"), "reason: {reason}");
    }
}

// -----------------------------------------------------------------------
// 12. certify_from_solver_proof skips empty solver proof
// -----------------------------------------------------------------------

#[test]
fn test_certify_from_solver_proof_skips_empty() {
    let pipeline = CertificationPipeline::new();
    let vc = sample_vc();
    let result = proved_result();
    let solver_proof = SolverProof { steps: vec![], used_axioms: vec![], used_lemmas: vec![] };

    let cert_result = pipeline.certify_from_solver_proof(&vc, &result, &solver_proof);
    assert!(cert_result.is_skipped());

    if let CertificationResult::Skipped { reason } = &cert_result {
        assert!(reason.contains("no steps"), "reason: {reason}");
    }
}

// -----------------------------------------------------------------------
// 13. certify_from_solver_proof handles reconstruction failure
// -----------------------------------------------------------------------

#[test]
fn test_certify_from_solver_proof_rejects_invalid_proof() {
    let pipeline = CertificationPipeline::new();
    let vc = sample_vc();
    let result = proved_result();
    // Invalid: modus ponens references non-existent steps
    let solver_proof = SolverProof {
        steps: vec![ProofStep::ModusPonens { implication_step: 99, antecedent_step: 100 }],
        used_axioms: vec![],
        used_lemmas: vec![],
    };

    let cert_result = pipeline.certify_from_solver_proof(&vc, &result, &solver_proof);
    assert!(
        cert_result.is_rejected(),
        "invalid step references should reject, got: {cert_result:?}"
    );

    if let CertificationResult::Rejected { reason, .. } = &cert_result {
        assert!(reason.contains("reconstruction") || reason.contains("lemma"), "reason: {reason}");
    }
}

// -----------------------------------------------------------------------
// 14. Multi-step QF_LIA proof with modus ponens
// -----------------------------------------------------------------------

#[test]
fn test_certify_from_solver_proof_multi_step_qf_lia() {
    let pipeline = CertificationPipeline::new();
    let vc = VerificationCondition {
        kind: VcKind::DivisionByZero,
        function: "safe_div".into(),
        location: SourceSpan::default(),
        formula: Formula::Not(Box::new(Formula::Eq(
            Box::new(Formula::Var("d".into(), Sort::Int)),
            Box::new(Formula::Int(0)),
        ))),
        contract_metadata: None,
    };
    let result = proved_result();

    // Multi-step proof:
    // Step 0: axiom "d_positive" — d > 0
    // Step 1: axiom "positive_implies_nonzero" — d > 0 => d != 0
    // Step 2: modus ponens (1, 0) — d != 0
    let solver_proof = SolverProof {
        steps: vec![
            ProofStep::Axiom {
                name: "d_positive".to_string(),
                formula: Formula::Gt(
                    Box::new(Formula::Var("d".into(), Sort::Int)),
                    Box::new(Formula::Int(0)),
                ),
            },
            ProofStep::Axiom {
                name: "positive_implies_nonzero".to_string(),
                formula: Formula::Implies(
                    Box::new(Formula::Gt(
                        Box::new(Formula::Var("d".into(), Sort::Int)),
                        Box::new(Formula::Int(0)),
                    )),
                    Box::new(Formula::Not(Box::new(Formula::Eq(
                        Box::new(Formula::Var("d".into(), Sort::Int)),
                        Box::new(Formula::Int(0)),
                    )))),
                ),
            },
            ProofStep::ModusPonens { implication_step: 1, antecedent_step: 0 },
        ],
        used_axioms: vec!["d_positive".to_string(), "positive_implies_nonzero".to_string()],
        used_lemmas: vec![0, 1],
    };

    let cert_result = pipeline.certify_from_solver_proof(&vc, &result, &solver_proof);
    // Trust: #758 — kernel may reject reconstructed proof terms and fall back to Trusted
    assert!(
        cert_result.is_certified() || cert_result.is_trusted(),
        "multi-step QF_LIA proof should produce certificate, got: {cert_result:?}"
    );
}

// -----------------------------------------------------------------------
// 15. QF_UF congruence proof
// -----------------------------------------------------------------------

#[test]
fn test_certify_from_solver_proof_qf_uf_congruence() {
    let pipeline = CertificationPipeline::new();
    let vc = VerificationCondition {
        kind: VcKind::Assertion { message: "congruence check".to_string() },
        function: "test_cong".into(),
        location: SourceSpan::default(),
        formula: Formula::Eq(
            Box::new(Formula::Var("a".into(), Sort::Bool)),
            Box::new(Formula::Var("b".into(), Sort::Bool)),
        ),
        contract_metadata: None,
    };
    let result = proved_result();

    // Step 0: axiom a = b
    // Step 1: congruence — f(a) = f(b) via congrArg
    let solver_proof = SolverProof {
        steps: vec![
            ProofStep::Axiom {
                name: "a_eq_b".to_string(),
                formula: Formula::Eq(
                    Box::new(Formula::Var("a".into(), Sort::Bool)),
                    Box::new(Formula::Var("b".into(), Sort::Bool)),
                ),
            },
            ProofStep::Congruence { equality_step: 0, function_name: "f".to_string() },
        ],
        used_axioms: vec!["a_eq_b".to_string()],
        used_lemmas: vec![0],
    };

    let cert_result = pipeline.certify_from_solver_proof(&vc, &result, &solver_proof);
    // Trust: #758 — kernel may reject reconstructed proof terms and fall back to Trusted
    assert!(
        cert_result.is_certified() || cert_result.is_trusted(),
        "QF_UF congruence proof should produce certificate, got: {cert_result:?}"
    );
}

// -----------------------------------------------------------------------
// 16. qf_lia_axiom and qf_uf_axiom helpers
// -----------------------------------------------------------------------

#[test]
fn test_qf_lia_axiom_helper() {
    let step = qf_lia_axiom(
        "bound_check",
        Formula::Le(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(100))),
    );
    if let ProofStep::Axiom { name, formula } = &step {
        assert_eq!(name, "bound_check");
        assert!(matches!(formula, Formula::Le(..)));
    } else {
        panic!("expected Axiom step");
    }
}

#[test]
fn test_qf_uf_axiom_helper() {
    let step = qf_uf_axiom(
        "eq_sym",
        Formula::Eq(
            Box::new(Formula::Var("p".into(), Sort::Bool)),
            Box::new(Formula::Var("q".into(), Sort::Bool)),
        ),
    );
    if let ProofStep::Axiom { name, formula } = &step {
        assert_eq!(name, "eq_sym");
        assert!(matches!(formula, Formula::Eq(..)));
    } else {
        panic!("expected Axiom step");
    }
}

// -----------------------------------------------------------------------
// 17. ProofGeneration variant checks
// -----------------------------------------------------------------------

#[test]
fn test_proof_generation_variant_checks() {
    let generated = ProofGeneration::Generated {
        proof_term: LeanProofTerm::Const("True.intro".to_string()),
        theory: ProofTheory::QfLia,
    };
    assert!(generated.is_generated());
    assert!(!generated.is_unsupported());
    assert!(!generated.is_failed());

    let unsupported =
        ProofGeneration::Unsupported { logic: SmtLogic::QfBv, reason: "not supported".to_string() };
    assert!(!unsupported.is_generated());
    assert!(unsupported.is_unsupported());
    assert!(!unsupported.is_failed());

    let failed = ProofGeneration::Failed { reason: "error".to_string() };
    assert!(!failed.is_generated());
    assert!(!failed.is_unsupported());
    assert!(failed.is_failed());
}

// -----------------------------------------------------------------------
// 18. serialize_lean_proof_term produces non-empty bytes
// -----------------------------------------------------------------------

#[test]
fn test_serialize_lean_proof_term() {
    let term = LeanProofTerm::App(
        Box::new(LeanProofTerm::Const("Trust.VC.mk".to_string())),
        Box::new(LeanProofTerm::Const("True.intro".to_string())),
    );
    let bytes = serialize_lean_proof_term(&term);
    assert!(!bytes.is_empty());
    let debug_str = String::from_utf8_lossy(&bytes);
    assert!(debug_str.contains("Trust.VC.mk"), "serialized term should contain Trust.VC.mk");
    assert!(debug_str.contains("True.intro"), "serialized term should contain True.intro");
}

// -----------------------------------------------------------------------
// 19. certify_from_solver_proof skips uncertifiable logic (Full)
// -----------------------------------------------------------------------

#[test]
fn test_certify_from_solver_proof_skips_quantified() {
    let pipeline = CertificationPipeline::new();
    let vc = VerificationCondition {
        kind: VcKind::Assertion { message: "quantified".to_string() },
        function: "forall_fn".into(),
        location: SourceSpan::default(),
        formula: Formula::Forall(
            vec![("x".into(), Sort::Int)],
            Box::new(Formula::Ge(
                Box::new(Formula::Var("x".into(), Sort::Int)),
                Box::new(Formula::Int(0)),
            )),
        ),
        contract_metadata: None,
    };
    let result = proved_result();
    let solver_proof = simple_axiom_proof("forall_axiom", Formula::Bool(true));

    let cert_result = pipeline.certify_from_solver_proof(&vc, &result, &solver_proof);
    assert!(cert_result.is_skipped(), "quantified formula should be skipped, got: {cert_result:?}");

    if let CertificationResult::Skipped { reason } = &cert_result {
        assert!(reason.contains("not certifiable") || reason.contains("ALL"), "reason: {reason}");
    }
}

// -----------------------------------------------------------------------
// 20. End-to-end: QF_LIA division-by-zero VC with resolution proof
// -----------------------------------------------------------------------

#[test]
fn test_e2e_qf_lia_divbyzero_resolution_proof() {
    let pipeline = CertificationPipeline::new();
    let vc = sample_vc();
    let result = proved_result();

    // Resolution proof: from two clauses, derive the conclusion
    let pivot = Formula::Var("divisor_is_zero".into(), Sort::Bool);
    let solver_proof = SolverProof {
        steps: vec![
            ProofStep::Axiom {
                name: "clause1".to_string(),
                formula: Formula::Or(vec![
                    Formula::Not(Box::new(Formula::Eq(
                        Box::new(Formula::Var("divisor".into(), Sort::Int)),
                        Box::new(Formula::Int(0)),
                    ))),
                    pivot.clone(),
                ]),
            },
            ProofStep::Axiom {
                name: "clause2".to_string(),
                formula: Formula::Or(vec![
                    Formula::Not(Box::new(pivot.clone())),
                    Formula::Bool(true),
                ]),
            },
            ProofStep::Resolution { positive_step: 0, negative_step: 1, pivot },
        ],
        used_axioms: vec!["clause1".to_string(), "clause2".to_string()],
        used_lemmas: vec![0, 1],
    };

    let cert_result = pipeline.certify_from_solver_proof(&vc, &result, &solver_proof);
    // Trust: #758 — kernel may reject reconstructed proof terms and fall back to Trusted
    assert!(
        cert_result.is_certified() || cert_result.is_trusted(),
        "resolution proof for div-by-zero should produce certificate, got: {cert_result:?}"
    );

    match &cert_result {
        CertificationResult::Certified { certificate, .. }
        | CertificationResult::Trusted { certificate, .. } => {
            assert!(!certificate.proof_term.is_empty());
            assert_eq!(certificate.prover, "ay");
        }
        _ => {}
    }
}

// =======================================================================
// Theory-scoped certification tests
// =======================================================================

// -----------------------------------------------------------------------
// 21. ProofTheory::QfLiaUf name
// -----------------------------------------------------------------------

#[test]
fn test_proof_theory_qf_lia_uf_name() {
    assert_eq!(ProofTheory::QfLiaUf.name(), "QF_LIA+UF");
}

// -----------------------------------------------------------------------
// 22. classify_vc_scope for QF_LIA
// -----------------------------------------------------------------------

#[test]
fn test_classify_vc_scope_qf_lia() {
    let vc = qf_lia_overflow_vc();
    let (logic, scope) = classify_vc_scope(&vc);
    assert_eq!(logic, SmtLogic::QfLia);
    assert!(scope.is_fully_certified());
}

// -----------------------------------------------------------------------
// 23. classify_vc_scope for QF_UF
// -----------------------------------------------------------------------

#[test]
fn test_classify_vc_scope_qf_uf() {
    let vc = qf_uf_equality_vc();
    let (logic, scope) = classify_vc_scope(&vc);
    assert_eq!(logic, SmtLogic::QfUf);
    assert!(scope.is_fully_certified());
}

// -----------------------------------------------------------------------
// 24. classify_vc_scope for QF_LIA+UF
// -----------------------------------------------------------------------

#[test]
fn test_classify_vc_scope_qf_lia_uf() {
    let vc = VerificationCondition {
        kind: VcKind::Assertion { message: "mixed".to_string() },
        function: "mixed_fn".into(),
        location: SourceSpan::default(),
        formula: Formula::And(vec![
            Formula::Lt(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(10))),
            Formula::Var("flag".into(), Sort::Bool),
        ]),
        contract_metadata: None,
    };
    let (logic, scope) = classify_vc_scope(&vc);
    assert_eq!(logic, SmtLogic::QfLiaUf);
    assert!(scope.is_fully_certified());
}

// -----------------------------------------------------------------------
// 25. classify_vc_scope for QF_BV (partially certified)
// -----------------------------------------------------------------------

#[test]
fn test_classify_vc_scope_qf_bv_partially_certified() {
    let vc = VerificationCondition {
        kind: VcKind::ArithmeticOverflow {
            op: BinOp::Add,
            operand_tys: (Ty::usize(), Ty::usize()),
        },
        function: "bv_fn".into(),
        location: SourceSpan::default(),
        formula: Formula::BvAdd(
            Box::new(Formula::Var("a".into(), Sort::BitVec(32))),
            Box::new(Formula::Var("b".into(), Sort::BitVec(32))),
            32,
        ),
        contract_metadata: None,
    };
    let (logic, scope) = classify_vc_scope(&vc);
    assert_eq!(logic, SmtLogic::QfBv);
    assert!(scope.is_partially_certified());
}

// -----------------------------------------------------------------------
// 26. classify_vc_scope for Full (uncertified)
// -----------------------------------------------------------------------

#[test]
fn test_classify_vc_scope_full_uncertified() {
    let vc = VerificationCondition {
        kind: VcKind::Assertion { message: "quantified".to_string() },
        function: "forall_fn".into(),
        location: SourceSpan::default(),
        formula: Formula::Forall(
            vec![("x".into(), Sort::Int)],
            Box::new(Formula::Ge(
                Box::new(Formula::Var("x".into(), Sort::Int)),
                Box::new(Formula::Int(0)),
            )),
        ),
        contract_metadata: None,
    };
    let (logic, scope) = classify_vc_scope(&vc);
    assert_eq!(logic, SmtLogic::Full);
    assert!(scope.is_uncertified());
}

// -----------------------------------------------------------------------
// 27. generate_proof_term for QF_LIA+UF returns QfLiaUf theory
// -----------------------------------------------------------------------

#[test]
fn test_generate_proof_term_qf_lia_uf() {
    let vc = VerificationCondition {
        kind: VcKind::Assertion { message: "mixed guard".to_string() },
        function: "mixed_guard".into(),
        location: SourceSpan::default(),
        formula: Formula::And(vec![
            Formula::Gt(Box::new(Formula::Var("n".into(), Sort::Int)), Box::new(Formula::Int(0))),
            Formula::Var("valid".into(), Sort::Bool),
        ]),
        contract_metadata: None,
    };
    let solver_proof = simple_axiom_proof(
        "guard_axiom",
        Formula::And(vec![
            Formula::Gt(Box::new(Formula::Var("n".into(), Sort::Int)), Box::new(Formula::Int(0))),
            Formula::Var("valid".into(), Sort::Bool),
        ]),
    );

    let pg = generate_proof_term(&vc, &solver_proof);
    assert!(pg.is_generated(), "QF_LIA+UF proof should be generated, got: {pg:?}");

    if let ProofGeneration::Generated { proof_term, theory } = &pg {
        assert_eq!(*theory, ProofTheory::QfLiaUf);
        assert!(validate_reconstruction(proof_term));
    }
}

// -----------------------------------------------------------------------
// 28. classify_vc_for_certification includes QF_LIA+UF
// -----------------------------------------------------------------------

#[test]
fn test_classify_vc_for_certification_qf_lia_uf() {
    let vc = VerificationCondition {
        kind: VcKind::Assertion { message: "mixed".to_string() },
        function: "mixed_fn".into(),
        location: SourceSpan::default(),
        formula: Formula::And(vec![
            Formula::Le(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(100))),
            Formula::Var("enabled".into(), Sort::Bool),
        ]),
        contract_metadata: None,
    };
    let (logic, certifiable) = classify_vc_for_certification(&vc);
    assert_eq!(logic, SmtLogic::QfLiaUf);
    assert!(certifiable, "QF_LIA+UF should be certifiable");
}

// -----------------------------------------------------------------------
// 29. certify_with_scope: FullyCertified for QF_LIA
// -----------------------------------------------------------------------

#[test]
fn test_certify_with_scope_fully_certified_qf_lia() {
    let pipeline = CertificationPipeline::new();
    let vc = qf_lia_overflow_vc();
    let result = proved_result();
    let solver_proof = simple_axiom_proof(
        "overflow_bound",
        Formula::Le(
            Box::new(Formula::Add(
                Box::new(Formula::Var("a".into(), Sort::Int)),
                Box::new(Formula::Var("b".into(), Sort::Int)),
            )),
            Box::new(Formula::Int((1i128 << 64) - 1)),
        ),
    );

    let (cert_result, scope) = pipeline.certify_with_scope(&vc, &result, &solver_proof);
    // Trust: #758 — kernel may reject reconstructed proof terms and fall back to Trusted
    assert!(
        cert_result.is_certified() || cert_result.is_trusted(),
        "should produce certificate: {cert_result:?}"
    );
    // Scope is fully certified if the logic is certifiable, regardless of kernel result
    assert!(scope.is_fully_certified() || scope.is_partially_certified());
}

// -----------------------------------------------------------------------
// 30. certify_with_scope: FullyCertified for QF_LIA+UF
// -----------------------------------------------------------------------

#[test]
fn test_certify_with_scope_fully_certified_qf_lia_uf() {
    let pipeline = CertificationPipeline::new();
    let vc = VerificationCondition {
        kind: VcKind::Assertion { message: "mixed".to_string() },
        function: "mixed_fn".into(),
        location: SourceSpan::default(),
        formula: Formula::And(vec![
            Formula::Gt(Box::new(Formula::Var("n".into(), Sort::Int)), Box::new(Formula::Int(0))),
            Formula::Var("flag".into(), Sort::Bool),
        ]),
        contract_metadata: None,
    };
    let result = proved_result();
    let solver_proof = simple_axiom_proof(
        "mixed_axiom",
        Formula::And(vec![
            Formula::Gt(Box::new(Formula::Var("n".into(), Sort::Int)), Box::new(Formula::Int(0))),
            Formula::Var("flag".into(), Sort::Bool),
        ]),
    );

    let (cert_result, scope) = pipeline.certify_with_scope(&vc, &result, &solver_proof);
    // Trust: #758 — kernel may reject reconstructed proof terms and fall back to Trusted
    assert!(
        cert_result.is_certified() || cert_result.is_trusted(),
        "QF_LIA+UF should produce certificate: {cert_result:?}"
    );
    assert!(scope.is_fully_certified() || scope.is_partially_certified());
}

// -----------------------------------------------------------------------
// 31. certify_with_scope: Uncertified for Full (quantifiers)
// -----------------------------------------------------------------------

#[test]
fn test_certify_with_scope_uncertified_quantified() {
    let pipeline = CertificationPipeline::new();
    let vc = VerificationCondition {
        kind: VcKind::Assertion { message: "quantified".to_string() },
        function: "forall_fn".into(),
        location: SourceSpan::default(),
        formula: Formula::Forall(
            vec![("x".into(), Sort::Int)],
            Box::new(Formula::Ge(
                Box::new(Formula::Var("x".into(), Sort::Int)),
                Box::new(Formula::Int(0)),
            )),
        ),
        contract_metadata: None,
    };
    let result = proved_result();
    let solver_proof = simple_axiom_proof("forall_axiom", Formula::Bool(true));

    let (cert_result, scope) = pipeline.certify_with_scope(&vc, &result, &solver_proof);
    // Graceful degradation: skipped, not failed
    assert!(cert_result.is_skipped(), "should skip gracefully: {cert_result:?}");
    assert!(scope.is_uncertified());

    if let CertificationScope::Uncertified { reason } = &scope {
        assert!(reason.contains("quantifier"), "reason should explain why: {reason}");
    }
}

// -----------------------------------------------------------------------
// 32. certify_with_scope: PartiallyCertified for QF_BV
// -----------------------------------------------------------------------

#[test]
fn test_certify_with_scope_partially_certified_qf_bv() {
    let pipeline = CertificationPipeline::new();
    let vc = VerificationCondition {
        kind: VcKind::ArithmeticOverflow {
            op: BinOp::Add,
            operand_tys: (Ty::usize(), Ty::usize()),
        },
        function: "bv_fn".into(),
        location: SourceSpan::default(),
        formula: Formula::BvAdd(
            Box::new(Formula::Var("a".into(), Sort::BitVec(32))),
            Box::new(Formula::Var("b".into(), Sort::BitVec(32))),
            32,
        ),
        contract_metadata: None,
    };
    let result = proved_result();
    let solver_proof = simple_axiom_proof("bv_axiom", Formula::Bool(true));

    let (_cert_result, scope) = pipeline.certify_with_scope(&vc, &result, &solver_proof);
    // QF_BV has partial strategy but certify_from_solver_proof may skip it
    // because it's not fully certifiable
    assert!(scope.is_partially_certified());

    if let CertificationScope::PartiallyCertified { logic, reason } = &scope {
        assert_eq!(*logic, SmtLogic::QfBv);
        assert!(reason.contains("bitvector"), "reason: {reason}");
    }
}

// -----------------------------------------------------------------------
// 33. certify_with_scope: skipped for non-Proved result
// -----------------------------------------------------------------------

#[test]
fn test_certify_with_scope_skips_failed_result() {
    let pipeline = CertificationPipeline::new();
    let vc = sample_vc();
    let result = failed_result();
    let solver_proof = simple_axiom_proof("any", Formula::Bool(true));

    let (cert_result, scope) = pipeline.certify_with_scope(&vc, &result, &solver_proof);
    assert!(cert_result.is_skipped());
    assert!(scope.is_uncertified());

    if let CertificationScope::Uncertified { reason } = &scope {
        assert!(reason.contains("not Proved"), "reason: {reason}");
    }
}

// -----------------------------------------------------------------------
// 34. certify_with_scope: skipped for empty solver proof
// -----------------------------------------------------------------------

#[test]
fn test_certify_with_scope_skips_empty_proof() {
    let pipeline = CertificationPipeline::new();
    let vc = sample_vc();
    let result = proved_result();
    let solver_proof = SolverProof { steps: vec![], used_axioms: vec![], used_lemmas: vec![] };

    let (cert_result, scope) = pipeline.certify_with_scope(&vc, &result, &solver_proof);
    assert!(cert_result.is_skipped());
    assert!(scope.is_uncertified());

    if let CertificationScope::Uncertified { reason } = &scope {
        assert!(reason.contains("no steps"), "reason: {reason}");
    }
}

// -----------------------------------------------------------------------
// 35. ProofGeneration variant checks include QfLiaUf
// -----------------------------------------------------------------------

#[test]
fn test_proof_generation_qf_lia_uf_variant() {
    let generated = ProofGeneration::Generated {
        proof_term: LeanProofTerm::Const("True.intro".to_string()),
        theory: ProofTheory::QfLiaUf,
    };
    assert!(generated.is_generated());
    assert!(!generated.is_unsupported());
    assert!(!generated.is_failed());

    if let ProofGeneration::Generated { theory, .. } = &generated {
        assert_eq!(theory.name(), "QF_LIA+UF");
    }
}

// -----------------------------------------------------------------------
// 36. certify_from_solver_proof with QF_LIA+UF VC
// -----------------------------------------------------------------------

#[test]
fn test_certify_from_solver_proof_qf_lia_uf() {
    let pipeline = CertificationPipeline::new();
    let vc = VerificationCondition {
        kind: VcKind::Assertion { message: "mixed check".to_string() },
        function: "mixed_fn".into(),
        location: SourceSpan::default(),
        formula: Formula::And(vec![
            Formula::Le(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(100))),
            Formula::Var("enabled".into(), Sort::Bool),
        ]),
        contract_metadata: None,
    };
    let result = proved_result();
    let solver_proof = simple_axiom_proof(
        "mixed_check",
        Formula::And(vec![
            Formula::Le(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(100))),
            Formula::Var("enabled".into(), Sort::Bool),
        ]),
    );

    let cert_result = pipeline.certify_from_solver_proof(&vc, &result, &solver_proof);
    // Trust: #758 — kernel may reject reconstructed proof terms and fall back to Trusted
    assert!(
        cert_result.is_certified() || cert_result.is_trusted(),
        "QF_LIA+UF solver proof should produce certificate, got: {cert_result:?}"
    );

    match &cert_result {
        CertificationResult::Certified { certificate, .. }
        | CertificationResult::Trusted { certificate, .. } => {
            assert!(!certificate.proof_term.is_empty());
        }
        _ => {}
    }
}

// -----------------------------------------------------------------------
// 37. certify_with_scope graceful degradation: does not fail the build
// -----------------------------------------------------------------------

#[test]
fn test_certify_with_scope_graceful_degradation_no_panic() {
    let pipeline = CertificationPipeline::new();
    let result = proved_result();
    let solver_proof = simple_axiom_proof("axiom", Formula::Bool(true));

    // Test all unsupported logic classes — none should panic or error,
    // they should all produce skipped/uncertified results
    let unsupported_formulas: Vec<(&str, Formula)> = vec![
        (
            "quantified",
            Formula::Forall(
                vec![("x".into(), Sort::Int)],
                Box::new(Formula::Var("x".into(), Sort::Int)),
            ),
        ),
        (
            "nonlinear",
            Formula::Mul(
                Box::new(Formula::Var("x".into(), Sort::Int)),
                Box::new(Formula::Var("y".into(), Sort::Int)),
            ),
        ),
    ];

    for (name, formula) in unsupported_formulas {
        let vc = VerificationCondition {
            kind: VcKind::Assertion { message: name.to_string() },
            function: name.into(),
            location: SourceSpan::default(),
            formula,
            contract_metadata: None,
        };

        let (cert_result, scope) = pipeline.certify_with_scope(&vc, &result, &solver_proof);
        assert!(
            cert_result.is_skipped(),
            "formula '{name}' should skip gracefully, got: {cert_result:?}"
        );
        assert!(scope.is_uncertified(), "formula '{name}' should be uncertified, got: {scope:?}");
    }
}
