use trust_router::Router;
use trust_transval::{ReconstructionOutputValidator, TranslationValidator};
use trust_types::{
    BasicBlock, BinOp, BlockId, DecompileTarget, DecompiledOutput, LocalDecl, Operand, Place,
    ReconstructionCandidateKind, ReconstructionValidationDirection,
    ReconstructionValidationEvidence, ReconstructionValidationRecord,
    ReconstructionValidationStatus, Rvalue, SourceSpan, Statement, Terminator, TrustLevel, Ty,
    ValidatedRustReconstruction, VerifiableBody, VerifiableFunction,
};

fn simple_binop(name: &str, op: BinOp) -> VerifiableFunction {
    VerifiableFunction {
        name: name.to_string(),
        def_path: format!("test::{name}"),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i32(), name: None },
                LocalDecl { index: 1, ty: Ty::i32(), name: Some("a".into()) },
                LocalDecl { index: 2, ty: Ty::i32(), name: Some("b".into()) },
                LocalDecl { index: 3, ty: Ty::i32(), name: None },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![
                    Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::BinaryOp(
                            op,
                            Operand::Copy(Place::local(1)),
                            Operand::Copy(Place::local(2)),
                        ),
                        span: SourceSpan::default(),
                    },
                    Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Copy(Place::local(3))),
                        span: SourceSpan::default(),
                    },
                ],
                terminator: Terminator::Return,
            }],
            arg_count: 2,
            return_ty: Ty::i32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

#[test]
fn strict_rust_metadata_without_compile_back_trust_ir_is_not_proof_grade() {
    let lifted = simple_binop("lifted", BinOp::Add);
    let output = DecompiledOutput {
        target: DecompileTarget::Rust,
        text: Some("pub fn lifted(a: i32, b: i32) -> i32 { a + b }".to_string()),
        validation: ReconstructionValidationStatus::Validated,
        trust_level: TrustLevel::ProofGrade,
        validated_rust: Some(ValidatedRustReconstruction {
            status: ReconstructionValidationStatus::Validated,
            trust_level: TrustLevel::ProofGrade,
            validation_records: vec![ReconstructionValidationRecord {
                target: DecompileTarget::Rust,
                function: Some("lifted".to_string()),
                candidate: ReconstructionCandidateKind::ValidatedRustStrictSubset,
                status: ReconstructionValidationStatus::Validated,
                trust_level: TrustLevel::ProofGrade,
                evidence: vec![ReconstructionValidationEvidence::StrictRustSubsetEligible],
                ..ReconstructionValidationRecord::default()
            }],
            ..ValidatedRustReconstruction::default()
        }),
        ..DecompiledOutput::default()
    };

    let report =
        ReconstructionOutputValidator::new().validate_output(Some(&lifted), None, Some(&output));

    assert_eq!(report.status, ReconstructionValidationStatus::Unknown);
    assert_eq!(report.candidate, ReconstructionCandidateKind::ValidatedRustStrictSubset);
    assert_eq!(report.trust_level, TrustLevel::Exploratory);
    assert!(!report.is_proof_grade());
    assert!(report.forward.is_none());
    assert!(report.reverse.is_none());
    assert!(report.diagnostics.iter().any(|msg| msg.contains("no comparable")));

    let record = report.to_record();
    assert_eq!(record.status, ReconstructionValidationStatus::Unknown);
    assert_eq!(record.candidate, ReconstructionCandidateKind::ValidatedRustStrictSubset);
    assert_eq!(record.trust_level, TrustLevel::Exploratory);
    assert!(record.forward.is_none());
    assert!(record.reverse.is_none());
    assert!(record.evidence.contains(&ReconstructionValidationEvidence::StrictRustSubsetEligible));
    assert!(record.evidence.contains(&ReconstructionValidationEvidence::NoCheckedProofCertificate));
    assert!(record.evidence.contains(&ReconstructionValidationEvidence::NoBinaryProofObligation));
}

#[test]
fn compile_back_trust_ir_candidate_records_bidirectional_equivalence_only_as_partial() {
    let lifted = simple_binop("lifted", BinOp::Add);
    let compiled_back = simple_binop("compiled_back_rust", BinOp::Add);

    let validator = ReconstructionOutputValidator::with_translation_validator(
        TranslationValidator::with_router(Router::new()),
    );
    let report = validator.validate_output(
        Some(&lifted),
        Some(&compiled_back),
        Some(&DecompiledOutput {
            target: DecompileTarget::Rust,
            text: Some("pub fn lifted(a: i32, b: i32) -> i32 { a + b }".to_string()),
            validation: ReconstructionValidationStatus::Unknown,
            trust_level: TrustLevel::Exploratory,
            ..DecompiledOutput::default()
        }),
    );

    assert_eq!(report.status, ReconstructionValidationStatus::Validated);
    assert_eq!(report.candidate, ReconstructionCandidateKind::StructuredTrustIr);
    assert_eq!(report.trust_level, TrustLevel::Partial);
    assert!(!report.is_proof_grade());
    assert!(report.forward.is_some());
    assert!(report.reverse.is_some());

    let record = report.to_record();
    assert_eq!(record.status, ReconstructionValidationStatus::Validated);
    assert_eq!(record.trust_level, TrustLevel::Partial);
    assert_eq!(
        record.forward.as_ref().map(|direction| direction.direction),
        Some(ReconstructionValidationDirection::LiftedToOutput)
    );
    assert_eq!(
        record.reverse.as_ref().map(|direction| direction.direction),
        Some(ReconstructionValidationDirection::OutputToLifted)
    );
    assert!(
        record.evidence.contains(&ReconstructionValidationEvidence::BidirectionalTrustIrRefinement)
    );
    assert!(record.evidence.contains(&ReconstructionValidationEvidence::NoCheckedProofCertificate));
    assert!(record.evidence.contains(&ReconstructionValidationEvidence::NoBinaryProofObligation));
}

#[test]
fn compile_back_trust_ir_divergence_is_refuted_not_validated() {
    let lifted = simple_binop("lifted", BinOp::Add);
    let compiled_back = simple_binop("compiled_back_rust", BinOp::Sub);

    let validator = ReconstructionOutputValidator::with_translation_validator(
        TranslationValidator::with_router(Router::new()),
    );
    let report = validator.validate_pair(&lifted, &compiled_back);

    assert_eq!(report.status, ReconstructionValidationStatus::Refuted);
    assert_eq!(report.candidate, ReconstructionCandidateKind::StructuredTrustIr);
    assert_eq!(report.trust_level, TrustLevel::Rejected);
    assert!(!report.is_proof_grade());
    assert!(report.forward.is_some());
    assert!(report.reverse.is_none());
    assert!(report.diagnostics.iter().any(|msg| msg.contains("refuted")));
}
