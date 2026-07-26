use trust_cg_bridge::binary_conversion::BinaryTrustCgTargetSemanticConsumptionEvidence;
use trust_cg_bridge::{
    BinaryTrustCgProofConsumerStatus, BinaryTrustCgValidationBlocker,
    BinaryTrustCgValidationStatus, lower_binary_decompiled_function_to_lir,
    lower_binary_trust_ir_to_lir, lower_canonical_trust_ir_to_lir,
};
use trust_cg_lower::instructions::Opcode;
use trust_cg_lower::types::Type as LirType;
use trust_types::{
    BasicBlock, BinaryArtifactDigest, BinaryArtifactDigestIdentity, BinaryOrigin,
    BinarySelectedImageIdentity, BinaryVerificationSummary, BlockId, DecompileTarget,
    DecompiledFunction, DecompiledOutput, Formula, LocalDecl, Operand, Place,
    ProofCertificateStatus, ReconstructionCandidateKind, ReconstructionValidationDirection,
    ReconstructionValidationDirectionRecord, ReconstructionValidationEvidence,
    ReconstructionValidationRecord, ReconstructionValidationStatus, ReplayStatus, Rvalue,
    SolverDispatchRecord, Sort, SourceSpan, Statement, TargetValidationBlocker, Terminator,
    TrustLevel, Ty, UnsupportedLedger, UnsupportedRecord, VerifiableBody, VerifiableFunction,
    infer_sort,
};

const REPLAY_ROOT_ARTIFACT_SHA256: &str =
    "1111111111111111111111111111111111111111111111111111111111111111";
const REPLAY_SELECTED_IMAGE_SHA256: &str =
    "2222222222222222222222222222222222222222222222222222222222222222";

fn replay_grade_binary_artifact_identity() -> BinaryArtifactDigestIdentity {
    BinaryArtifactDigestIdentity {
        root_artifact_digest: Some(BinaryArtifactDigest::sha256(REPLAY_ROOT_ARTIFACT_SHA256)),
        selected_image: Some(BinarySelectedImageIdentity {
            file_offset: 0,
            file_size: 16,
            sha256: REPLAY_SELECTED_IMAGE_SHA256.to_string(),
        }),
    }
}

fn symbolic_binary_trust_ir(formula: Formula) -> VerifiableFunction {
    VerifiableFunction {
        name: "canonical_symbolic_binary".to_string(),
        def_path: "binary::canonical_symbolic_binary".to_string(),
        span: SourceSpan::binary_address(0x401000),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i32(), name: None },
                LocalDecl { index: 1, ty: Ty::i32(), name: Some("x0".to_string()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Use(Operand::Symbolic(formula)),
                    span: SourceSpan::binary_address(0x401004),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty: Ty::i32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

fn scalar_bool_true_binary_trust_ir() -> VerifiableFunction {
    VerifiableFunction {
        name: "scalar_bool_true_binary".to_string(),
        def_path: "binary::scalar_bool_true_binary".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![LocalDecl { index: 0, ty: Ty::Bool, name: None }],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Use(Operand::Symbolic(Formula::Bool(true))),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 0,
            return_ty: Ty::Bool,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

fn scalar_bool_true_decompiled_function(
    certificate: ProofCertificateStatus,
    replay: ReplayStatus,
    binary_artifact_digest_identity: Option<BinaryArtifactDigestIdentity>,
) -> DecompiledFunction {
    DecompiledFunction {
        name: "scalar_bool_true_binary".to_string(),
        entry: 0x401000,
        lifted: Some(scalar_bool_true_binary_trust_ir()),
        verification: BinaryVerificationSummary {
            solver_dispatch: vec![SolverDispatchRecord {
                id: "vc:scalar-bool-true".to_string(),
                function: Some("scalar_bool_true_binary".to_string()),
                origin: Some(BinaryOrigin {
                    binary_path: Some("fixture.bin".to_string()),
                    function_entry: Some(0x401000),
                    instruction_address: 0x401004,
                    instruction_size: Some(4),
                    encoding: Some(0xd503_201f),
                    instruction_bytes: vec![0x1f, 0x20, 0x03, 0xd5],
                    source: Some(SourceSpan::binary_address(0x401004)),
                }),
                solver: "ay".to_string(),
                replay,
                binary_artifact_digest_identity,
                certificate,
                ..Default::default()
            }],
            ..Default::default()
        },
        ..Default::default()
    }
}

fn trust_cg_blocker_output(
    validation: ReconstructionValidationStatus,
    trust_level: TrustLevel,
    blockers: &[BinaryTrustCgValidationBlocker],
    diagnostics: &[String],
) -> DecompiledOutput {
    DecompiledOutput {
        target: DecompileTarget::TrustCg,
        text: Some("; structurally valid trust_cg LIR omitted".to_string()),
        validation,
        trust_level,
        target_validation_blockers: blockers
            .iter()
            .map(|blocker| TargetValidationBlocker {
                target: DecompileTarget::TrustCg,
                code: blocker.code.clone(),
                stage: "trust-cg-bridge::target-validation".to_string(),
                feature: blocker.code.clone(),
                reason: blocker.detail.clone(),
                diagnostics: diagnostics.to_vec(),
                ..Default::default()
            })
            .collect(),
        diagnostics: diagnostics.to_vec(),
        ..Default::default()
    }
}

fn assert_residual_refinement_and_proof_obligation_blockers(
    blockers: &[BinaryTrustCgValidationBlocker],
) {
    assert!(blockers.iter().any(|blocker| {
        blocker.code == "missing-refinement-metadata"
            && blocker.detail.contains("bidirectional refinement metadata")
    }));
    assert!(blockers.iter().any(|blocker| {
        blocker.code == "missing-binary-proof-obligation"
            && blocker.detail.contains("machine-code proof obligations")
    }));
}

fn assert_refinement_and_target_consumed_proof_obligation_blockers(
    blockers: &[BinaryTrustCgValidationBlocker],
) {
    assert!(blockers.iter().any(|blocker| {
        blocker.code == "refinement-metadata-not-consumed"
            && blocker.detail.contains("structured refinement metadata")
            && blocker.detail.contains("bidirectional refinement consumer")
    }));
    assert!(blockers.iter().any(|blocker| {
        blocker.code == "binary-proof-obligation-pending-refinement-consumption"
            && blocker.detail.contains("target proof consumer consumed")
            && blocker.detail.contains("proof-grade remains closed")
    }));
}

fn assert_no_refinement_consumption_residual_blockers(blockers: &[BinaryTrustCgValidationBlocker]) {
    for code in [
        "missing-refinement-metadata",
        "refinement-metadata-not-consumed",
        "binary-proof-obligation-pending-refinement-metadata",
        "binary-proof-obligation-pending-refinement-consumption",
    ] {
        assert!(
            !blockers.iter().any(|blocker| blocker.code == code),
            "unexpected residual blocker `{code}` after accepted refinement consumption"
        );
    }
}

fn assert_target_consumed_missing_refinement_blockers(blockers: &[BinaryTrustCgValidationBlocker]) {
    assert!(blockers.iter().any(|blocker| {
        blocker.code == "missing-refinement-metadata"
            && blocker.detail.contains("bidirectional refinement metadata")
    }));
    assert!(blockers.iter().any(|blocker| {
        blocker.code == "binary-proof-obligation-pending-refinement-metadata"
            && blocker.detail.contains("target proof consumer consumed")
            && blocker.detail.contains("bidirectional refinement metadata")
    }));
}

fn assert_refinement_present_and_pending_proof_obligation_blockers(
    blockers: &[BinaryTrustCgValidationBlocker],
) {
    assert!(blockers.iter().any(|blocker| {
        blocker.code == "refinement-metadata-not-consumed"
            && blocker.detail.contains("structured refinement metadata")
    }));
    assert!(blockers.iter().any(|blocker| {
        blocker.code == "missing-binary-proof-obligation"
            && blocker.detail.contains("machine-code proof obligations")
    }));
}

const EXACT_CANONICAL_BINARY_PROVENANCE_ATTRS: &str = r#"[schema=str:"trust-types.BinaryProvenance@1"] [source=str:"unit-test"] [binary_path=str:"fixture.bin"] [function_entry=str:"0x401000"] [instruction_address=str:"0x401004"] [instruction_size=str:"4"] [encoding=str:"0xd503201f"] [instruction_bytes=str:"1f2003d5"]"#;
const EXACT_CANONICAL_UNSUPPORTED_LEDGER_ATTRS: &str = r#"[schema=str:"trust-types.UnsupportedLedger@1"] [source=str:"bounded-empty-unsupported-ledger"] [unsupported_records=str:"0"] [verification_unsupported=str:"0"] [target_semantics_consumed=str:"false"]"#;

fn replayed_wasm_consumption_for_trust_cg() -> BinaryTrustCgTargetSemanticConsumptionEvidence {
    BinaryTrustCgTargetSemanticConsumptionEvidence {
        consumer: "trust-wasm-bridge::target-semantic-consumption-gate".to_string(),
        target_semantics_consumed: true,
        input_claimed_target_semantics_consumed: None,
        code: "bounded-empty-wasm-target-consumed".to_string(),
        detail: "forged replay of Wasm target proof-consumer evidence".to_string(),
    }
}

fn canonical_binary_provenance_trust_ir(function: &str, provenance_attrs: &str) -> String {
    format!(
        r#"; TrustIr text format v1
module "{function}"

fn @{function}(functy.0) {{
bb0(%0: i32):
        %1 = dialect_op trust_binary.provenance() -> i32 {provenance_attrs}
        ret %0
}}
"#
    )
}

fn canonical_symbolic_with_binary_provenance_trust_ir(
    function: &str,
    provenance_attrs: &str,
) -> String {
    let formula = Formula::BitVec { value: 1, width: 32 };
    let formula_json = serde_json::to_string(&formula).expect("formula should serialize");
    format!(
        r#"; TrustIr text format v1
module "{function}"

fn @{function}(functy.0) {{
bb0(%0: i32):
        %1 = dialect_op trust_symbolic.formula() -> i32 [schema=str:"trust-types.Formula@1"] [formula_json=str:{formula_json:?}] [formula.smtlib2=str:"(_ bv1 32)"] [formula.sort=str:"(_ BitVec 32)"]
        %2 = dialect_op trust_binary.provenance() -> i32 {provenance_attrs}
        ret %0
}}
"#
    )
}

fn canonical_proof_metadata_trust_ir(
    function: &str,
    certificate_attrs: &str,
    replay_attrs: &str,
) -> String {
    format!(
        r#"; TrustIr text format v1
module "{function}"

fn @{function}(functy.0) {{
bb0(%0: i32):
        %1 = dialect_op trust_proof.checked_certificate() -> i32 {certificate_attrs}
        %2 = dialect_op trust_proof.proof_replay() -> i32 {replay_attrs}
        ret %0
}}
"#
    )
}

fn canonical_bounded_empty_consumer_trust_ir(
    function: &str,
    formula: &Formula,
    provenance_attrs: &str,
    certificate_attrs: &str,
    replay_attrs: &str,
) -> String {
    let formula_json = serde_json::to_string(formula).expect("formula should serialize");
    let formula_smtlib = formula.to_smtlib();
    let formula_sort = infer_sort(formula).to_smtlib();
    format!(
        r#"; TrustIr text format v1
module "{function}"

fn @{function}(functy.0) {{
bb0(%0: bool):
        %1 = dialect_op trust_symbolic.formula() -> bool [schema=str:"trust-types.Formula@1"] [formula_json=str:{formula_json:?}] [formula.smtlib2=str:{:?}] [formula.sort=str:"{}"]
        %2 = dialect_op trust_binary.provenance() -> i32 {provenance_attrs}
        %3 = dialect_op trust_proof.checked_certificate() -> i32 {certificate_attrs}
        %4 = dialect_op trust_proof.proof_replay() -> i32 {replay_attrs}
        %5 = dialect_op trust_proof.unsupported_ledger() -> i32 {EXACT_CANONICAL_UNSUPPORTED_LEDGER_ATTRS}
        ret %0
}}
"#,
        formula_smtlib, formula_sort
    )
}

#[test]
fn binary_derived_canonical_trust_ir_keeps_symbolic_formula_visible_without_undef() {
    let formula = Formula::BitVec { value: 7, width: 32 };
    let trust_ir = symbolic_binary_trust_ir(formula.clone());

    let conversion = lower_binary_trust_ir_to_lir(&trust_ir)
        .expect("symbolic binary-derived TrustIr should remain inspectable");

    assert_eq!(conversion.symbolic_formulas.len(), 1);
    let preserved = &conversion.symbolic_formulas[0];
    assert_eq!(preserved.function, "canonical_symbolic_binary");
    assert_eq!(preserved.block, 0);
    assert_eq!(preserved.statement_index, 0);
    assert_eq!(preserved.operand, "use");
    assert_eq!(preserved.formula, formula);
    assert_eq!(preserved.sort, "(_ BitVec 32)");
    assert_eq!(preserved.bit_width, Some(32));

    assert_eq!(conversion.symbolic_formula_evidence.len(), 1);
    let evidence = &conversion.symbolic_formula_evidence[0];
    assert_eq!(evidence.inferred_sort.as_deref(), Some("(_ BitVec 32)"));
    assert_eq!(evidence.bit_width, Some(32));
    assert_eq!(evidence.smtlib.as_deref(), Some("(_ bv7 32)"));
    assert!(!evidence.target_semantics_consumed);
    assert_eq!(evidence.target_semantic_consumption.code, "no-trust_cg-target-semantic-consumer");

    assert_eq!(conversion.structural_validation, ReconstructionValidationStatus::Validated);
    assert_eq!(conversion.trust_cg_validation, BinaryTrustCgValidationStatus::InspectableRejected);
    assert_eq!(conversion.trust_level, TrustLevel::Rejected);
    assert_eq!(conversion.provenance_evidence.len(), 2);
    assert!(conversion.provenance_evidence.iter().any(|entry| {
        entry.source == "lifted.function_span" && entry.origin.instruction_address == 0x401000
    }));
    assert!(conversion.provenance_evidence.iter().any(|entry| {
        entry.source == "lifted.bb0.stmt0"
            && entry.block == Some(0)
            && entry.statement_index == Some(0)
            && entry.origin.instruction_address == 0x401004
            && !entry.target_semantics_consumed
    }));
    assert!(
        conversion
            .validation_blockers
            .iter()
            .any(|blocker| blocker.code == "missing-checked-proof-certificate")
    );
    assert!(conversion.validation_blockers.iter().any(|blocker| {
        blocker.code == "binary-provenance-not-consumed-by-target-semantics"
            && blocker.detail.contains("2 binary provenance")
    }));

    let proof_consumer = conversion.target_proof_consumer_evidence();
    assert_eq!(proof_consumer.status, BinaryTrustCgProofConsumerStatus::Rejected);
    assert!(proof_consumer.is_rejected());
    assert!(!proof_consumer.target_semantics_consumed);
    assert_eq!(proof_consumer.binding.target, "trust-cg");
    assert_eq!(proof_consumer.binding.status, BinaryTrustCgProofConsumerStatus::Rejected);
    assert!(proof_consumer.binding.target_output.contains("trust_cg-lir:"));
    assert!(proof_consumer.binding.target_output.contains("canonical_symbolic_binary"));
    assert!(!proof_consumer.binding.target_semantics_consumed);
    assert!(proof_consumer.binding.inputs.iter().any(|input| {
        input.kind == "canonical_trust_ir_formula"
            && input.identifier == "canonical_symbolic_binary::bb0::stmt0::use"
            && input.canonical_source == "trust_symbolic.formula"
            && input.target_output == proof_consumer.binding.target_output
            && !input.consumed_by_target_semantics
    }));
    assert!(proof_consumer.binding.inputs.iter().any(|input| {
        input.kind == "binary_provenance"
            && input.identifier.contains("canonical_symbolic_binary::bb0::stmt0")
            && input.canonical_source == "trust_binary.provenance"
            && input.target_output == proof_consumer.binding.target_output
            && !input.consumed_by_target_semantics
    }));
    assert!(proof_consumer.records.iter().any(|record| {
        record.kind == "symbolic_formula"
            && record.identifier == "canonical_symbolic_binary::bb0::stmt0::use"
            && !record.accepted
            && record.detail.contains("formula JSON/SMT-LIB/sort metadata is preserved")
    }));
    assert!(proof_consumer.records.iter().any(|record| {
        record.kind == "binary_provenance"
            && record.identifier.contains("canonical_symbolic_binary::bb0::stmt0")
            && record.identifier.contains("0x401004")
            && !record.accepted
            && record.detail.contains("target semantics have not consumed")
    }));
    assert!(proof_consumer.blockers.iter().any(|blocker| {
        blocker.code == "target-semantics-not-consumed"
            && blocker.detail.contains("trust-cg target semantics have not consumed")
    }));
    assert_residual_refinement_and_proof_obligation_blockers(&proof_consumer.proof_grade_blockers);
    assert!(proof_consumer.blockers.iter().any(|blocker| {
        blocker.code == "symbolic-formula-not-consumed-by-target-semantics"
            && blocker.detail.contains("trust-cg-bridge::target-semantic-consumption-gate")
            && blocker.detail.contains("formula.smtlib2=(_ bv7 32)")
    }));
    assert!(
        proof_consumer.blockers.iter().any(|blocker| {
            blocker.code == "binary-provenance-not-consumed-by-target-semantics"
        })
    );

    let instructions: Vec<_> =
        conversion.lir.blocks.values().flat_map(|block| block.instructions.iter()).collect();
    assert!(instructions.iter().any(|instruction| {
        matches!(instruction.opcode, Opcode::Iconst { ty: LirType::I32, imm: 7 })
    }));
    assert!(
        !format!("{:#?}", conversion.lir).contains("Undef"),
        "binary symbolic formulas must not be hidden behind an Undef lowering"
    );
}

#[test]
fn decompiled_trust_cg_preserves_checked_certificate_and_symbolic_schema_without_proof_grade() {
    let formula = Formula::BitVec { value: 7, width: 32 };
    let trust_ir = symbolic_binary_trust_ir(formula.clone());
    let audit_schema =
        "checked-certificate.audit.schema=checked-binary-certificate-audit-export.v1";
    let audit_row = "checked-certificate.audit.manifest_entry=vc:symbolic-schema";
    let readback_sha = "checked-certificate.readback.sha256=aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";
    let readback_status = "checked-certificate.readback.status=loaded";
    let function = DecompiledFunction {
        name: "canonical_symbolic_binary".to_string(),
        entry: 0x401000,
        lifted: Some(trust_ir),
        verification: BinaryVerificationSummary {
            solver_dispatch: vec![SolverDispatchRecord {
                id: "vc:symbolic-schema".to_string(),
                function: Some("canonical_symbolic_binary".to_string()),
                origin: Some(BinaryOrigin {
                    binary_path: Some("fixture.bin".to_string()),
                    function_entry: Some(0x401000),
                    instruction_address: 0x401004,
                    instruction_size: Some(4),
                    encoding: Some(0xd503_201f),
                    instruction_bytes: vec![0x1f, 0x20, 0x03, 0xd5],
                    source: Some(SourceSpan::binary_address(0x401004)),
                }),
                solver: "ay".to_string(),
                replay: ReplayStatus::Replayed,
                binary_artifact_digest_identity: Some(replay_grade_binary_artifact_identity()),
                certificate: ProofCertificateStatus::Checked {
                    checker: "trust-proof-cert-check".to_string(),
                    format: "lrat".to_string(),
                    sha256: Some(
                        "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"
                            .to_string(),
                    ),
                },
                diagnostics: vec![
                    audit_schema.to_string(),
                    audit_row.to_string(),
                    readback_sha.to_string(),
                    readback_status.to_string(),
                ],
                ..Default::default()
            }],
            ..Default::default()
        },
        ..Default::default()
    };

    let conversion = lower_binary_decompiled_function_to_lir(&function)
        .expect("symbolic binary-derived TrustIr should remain inspectable");

    assert_eq!(conversion.symbolic_formula_evidence.len(), 1);
    let formula_evidence = &conversion.symbolic_formula_evidence[0];
    assert_eq!(formula_evidence.formula.as_ref(), Some(&formula));
    assert_eq!(formula_evidence.schema.as_deref(), Some("trust-types.Formula@1"));
    assert_eq!(formula_evidence.sort.as_deref(), Some("(_ BitVec 32)"));
    assert_eq!(formula_evidence.inferred_sort.as_deref(), Some("(_ BitVec 32)"));
    assert_eq!(formula_evidence.bit_width, Some(32));
    assert!(formula_evidence.schema_errors.is_empty());

    assert_eq!(conversion.checked_certificate_evidence.len(), 1);
    let certificate = &conversion.checked_certificate_evidence[0];
    assert_eq!(certificate.dispatch_id, "vc:symbolic-schema");
    assert_eq!(certificate.function.as_deref(), Some("canonical_symbolic_binary"));
    assert_eq!(
        certificate.origin.as_ref().map(|origin| origin.instruction_address),
        Some(0x401004)
    );
    assert_eq!(certificate.checker, "trust-proof-cert-check");
    assert_eq!(certificate.format, "lrat");
    assert_eq!(
        certificate.sha256.as_deref(),
        Some("bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb")
    );
    assert_eq!(certificate.replay, ReplayStatus::Replayed);
    assert!(!certificate.target_semantics_consumed);
    assert_eq!(
        certificate.audit_readback_metadata,
        vec![
            audit_schema.to_string(),
            audit_row.to_string(),
            readback_sha.to_string(),
            readback_status.to_string(),
        ]
    );
    assert!(conversion.provenance_evidence.iter().any(|entry| {
        entry.source == "solver_dispatch:vc:symbolic-schema"
            && entry.origin.instruction_address == 0x401004
            && entry.origin.instruction_bytes == vec![0x1f, 0x20, 0x03, 0xd5]
            && !entry.target_semantics_consumed
    }));
    assert_eq!(conversion.proof_replay_evidence.len(), 1);
    let replay = &conversion.proof_replay_evidence[0];
    assert_eq!(replay.dispatch_id, "vc:symbolic-schema");
    assert_eq!(replay.replay, ReplayStatus::Replayed);
    assert!(replay.exact_replay_checked);
    assert_eq!(replay.artifact_sha256.as_deref(), Some(REPLAY_ROOT_ARTIFACT_SHA256));
    assert!(!replay.target_semantics_consumed);

    let proof_consumer = conversion.target_proof_consumer_evidence();
    assert_eq!(proof_consumer.target, "trust-cg");
    assert_eq!(proof_consumer.status, BinaryTrustCgProofConsumerStatus::Rejected);
    assert!(proof_consumer.is_rejected());
    assert!(!proof_consumer.target_semantics_consumed);
    assert_eq!(proof_consumer.binding.status, BinaryTrustCgProofConsumerStatus::Rejected);
    assert!(proof_consumer.binding.target_output.contains("canonical_symbolic_binary"));
    assert!(proof_consumer.binding.inputs.iter().any(|input| {
        input.kind == "checked_certificate"
            && input.identifier == "vc:symbolic-schema"
            && input.canonical_source == "checked-certificate"
            && input.target_output == proof_consumer.binding.target_output
            && !input.consumed_by_target_semantics
    }));
    assert!(proof_consumer.binding.inputs.iter().any(|input| {
        input.kind == "proof_replay"
            && input.identifier == "vc:symbolic-schema"
            && input.canonical_source == "proof-replay"
            && input.detail.contains("Replayed")
            && !input.consumed_by_target_semantics
    }));
    assert!(proof_consumer.records.iter().any(|record| {
        record.kind == "symbolic_formula"
            && record.identifier == "canonical_symbolic_binary::bb0::stmt0::use"
            && !record.accepted
            && record.detail.contains("target semantics have not consumed")
    }));
    assert!(proof_consumer.records.iter().any(|record| {
        record.kind == "checked_certificate"
            && record.identifier == "vc:symbolic-schema"
            && !record.accepted
            && record.detail.contains("trust-proof-cert-check")
    }));
    assert!(proof_consumer.records.iter().any(|record| {
        record.kind == "proof_replay"
            && record.identifier == "vc:symbolic-schema"
            && !record.accepted
            && record.detail.contains("Replayed")
    }));
    assert!(proof_consumer.records.iter().any(|record| {
        record.kind == "binary_provenance"
            && record.identifier.contains("solver_dispatch:vc:symbolic-schema")
            && record.identifier.contains("0x401004")
            && !record.accepted
            && record.detail.contains("bytes=4")
    }));
    for code in [
        "target-semantics-not-consumed",
        "non-empty-scalar-trust_cg-target-consumer-unavailable",
        "non-empty-scalar-canonical-source-shape-validation-missing",
        "missing-scalar-formula-target-op-binding",
        "symbolic-formula-not-consumed-by-target-semantics",
        "binary-provenance-not-consumed-by-target-semantics",
        "checked-certificate-not-consumed-by-target-semantics",
        "proof-replay-not-consumed-by-target-semantics",
    ] {
        assert!(
            proof_consumer.blockers.iter().any(|blocker| blocker.code == code),
            "missing proof-consumer blocker `{code}`"
        );
    }
    assert!(
        !proof_consumer
            .blockers
            .iter()
            .any(|blocker| blocker.code == "non-empty-scalar-replay-artifact-identity-missing"),
        "the regression must prove replay-grade artifact identity is present while scalar target consumption is still rejected"
    );

    assert_eq!(conversion.trust_cg_validation, BinaryTrustCgValidationStatus::InspectableRejected);
    assert_eq!(conversion.trust_level, TrustLevel::Rejected);
    assert_ne!(conversion.trust_level, TrustLevel::ProofGrade);
    assert!(conversion.validation_blockers.iter().any(|blocker| {
        blocker.code == "missing-target-semantic-validation"
            && blocker.detail.contains("trust-cg target semantics")
    }));
    assert!(conversion.validation_blockers.iter().any(|blocker| {
        blocker.code == "checked-certificate-not-consumed-by-target-semantics"
            && blocker.detail.contains("checked certificate audit/readback metadata")
            && blocker.detail.contains("symbolic formula schema metadata")
            && blocker.detail.contains("target semantic validation")
            && blocker.detail.contains("proof-grade remains closed")
    }));
    assert!(conversion.diagnostics.iter().any(|diagnostic| {
        diagnostic.contains("checked_certificate.dispatch_id=vc:symbolic-schema")
            && diagnostic.contains("checked_certificate.target_semantics_consumed=false")
            && diagnostic.contains(readback_sha)
    }));
    assert!(conversion.diagnostics.iter().any(|diagnostic| {
        diagnostic.contains("binary_provenance.source=solver_dispatch:vc:symbolic-schema")
            && diagnostic.contains("binary_provenance.instruction_bytes=1f2003d5")
            && diagnostic.contains("binary_provenance.target_semantics_consumed=false")
    }));
    assert!(conversion.diagnostics.iter().any(|diagnostic| {
        diagnostic.contains("proof_replay.source=solver_dispatch:vc:symbolic-schema")
            && diagnostic.contains("proof_replay.exact_replay_checked=true")
            && diagnostic.contains(REPLAY_ROOT_ARTIFACT_SHA256)
            && diagnostic.contains("proof_replay.consumption.target_semantics_consumed=false")
    }));
}

#[test]
fn decompiled_trust_cg_accepts_narrow_scalar_bool_true_target_consumer() {
    let trust_ir = scalar_bool_true_binary_trust_ir();
    let certificate_status = ProofCertificateStatus::Checked {
        checker: "trust-proof-cert-check".to_string(),
        format: "lrat".to_string(),
        sha256: Some(
            "3333333333333333333333333333333333333333333333333333333333333333".to_string(),
        ),
    };
    let function = DecompiledFunction {
        name: "scalar_bool_true_binary".to_string(),
        entry: 0x401000,
        lifted: Some(trust_ir),
        verification: BinaryVerificationSummary {
            solver_dispatch: vec![SolverDispatchRecord {
                id: "vc:scalar-bool-true".to_string(),
                function: Some("scalar_bool_true_binary".to_string()),
                origin: Some(BinaryOrigin {
                    binary_path: Some("fixture.bin".to_string()),
                    function_entry: Some(0x401000),
                    instruction_address: 0x401004,
                    instruction_size: Some(4),
                    encoding: Some(0xd503_201f),
                    instruction_bytes: vec![0x1f, 0x20, 0x03, 0xd5],
                    source: Some(SourceSpan::binary_address(0x401004)),
                }),
                solver: "ay".to_string(),
                replay: ReplayStatus::Replayed,
                binary_artifact_digest_identity: Some(replay_grade_binary_artifact_identity()),
                certificate: certificate_status,
                ..Default::default()
            }],
            ..Default::default()
        },
        ..Default::default()
    };

    let conversion = lower_binary_decompiled_function_to_lir(&function)
        .expect("scalar Bool(true) TrustIr should lower to trust_cg LIR");

    assert_eq!(conversion.symbolic_formula_evidence.len(), 1);
    let formula = &conversion.symbolic_formula_evidence[0];
    assert_eq!(formula.function, "scalar_bool_true_binary");
    assert_eq!(formula.block, 0);
    assert_eq!(formula.statement_index, 0);
    assert_eq!(formula.operand, "use");
    assert_eq!(formula.formula, Some(Formula::Bool(true)));
    assert_eq!(formula.schema.as_deref(), Some("trust-types.Formula@1"));
    assert_eq!(formula.sort.as_deref(), Some("Bool"));
    assert_eq!(formula.smtlib.as_deref(), Some("true"));
    assert!(formula.target_semantics_consumed);
    assert_eq!(
        formula.target_semantic_consumption.code,
        "scalar-bool-true-trust_cg-target-consumed"
    );

    let instructions: Vec<_> =
        conversion.lir.blocks.values().flat_map(|block| block.instructions.iter()).collect();
    assert_eq!(instructions.len(), 2);
    assert!(matches!(instructions[0].opcode, Opcode::Iconst { ty: LirType::B1, imm: 1 }));

    assert_eq!(conversion.checked_certificate_evidence.len(), 1);
    let certificate = &conversion.checked_certificate_evidence[0];
    assert_eq!(certificate.dispatch_id, "vc:scalar-bool-true");
    assert_eq!(certificate.function.as_deref(), Some("scalar_bool_true_binary"));
    assert_eq!(certificate.checker, "trust-proof-cert-check");
    assert_eq!(certificate.format, "lrat");
    assert_eq!(
        certificate.sha256.as_deref(),
        Some("3333333333333333333333333333333333333333333333333333333333333333")
    );
    assert_eq!(certificate.replay, ReplayStatus::Replayed);
    assert!(certificate.target_semantics_consumed);
    assert_eq!(
        certificate.target_semantic_consumption.code,
        "scalar-bool-true-trust_cg-target-consumed"
    );
    assert_eq!(conversion.proof_replay_evidence.len(), 1);
    let replay = &conversion.proof_replay_evidence[0];
    assert_eq!(replay.dispatch_id, "vc:scalar-bool-true");
    assert_eq!(replay.function.as_deref(), Some("scalar_bool_true_binary"));
    assert_eq!(replay.replay, ReplayStatus::Replayed);
    assert!(replay.exact_replay_checked);
    assert_eq!(replay.artifact_sha256.as_deref(), Some(REPLAY_ROOT_ARTIFACT_SHA256));
    assert!(replay.target_semantics_consumed);
    assert_eq!(
        replay.target_semantic_consumption.code,
        "scalar-bool-true-trust_cg-target-consumed"
    );
    assert_eq!(conversion.provenance_evidence.len(), 1);
    assert!(conversion.provenance_evidence[0].target_semantics_consumed);
    assert_eq!(
        conversion.provenance_evidence[0].target_semantic_consumption.code,
        "scalar-bool-true-trust_cg-target-consumed"
    );
    assert_eq!(conversion.unsupported_ledger_evidence.len(), 1);
    let unsupported_ledger = &conversion.unsupported_ledger_evidence[0];
    assert!(unsupported_ledger.unsupported_ledger_eliminated);
    assert_eq!(unsupported_ledger.unsupported_records, 0);
    assert_eq!(unsupported_ledger.verification_unsupported, 0);
    assert!(unsupported_ledger.target_semantics_consumed);
    assert_eq!(
        unsupported_ledger.target_semantic_consumption.code,
        "scalar-bool-true-trust_cg-target-consumed"
    );
    assert_eq!(conversion.refinement_metadata_evidence.len(), 1);
    let refinement = &conversion.refinement_metadata_evidence[0];
    assert_eq!(refinement.slice, "scalar-bool-true");
    assert_eq!(refinement.source, "lifted-trust_ir");
    assert_eq!(refinement.source_function, "scalar_bool_true_binary");
    assert_eq!(refinement.source_block, Some(0));
    assert_eq!(refinement.source_statement_index, Some(0));
    assert_eq!(refinement.source_formula.as_deref(), Some("true"));
    assert!(refinement.target_output.contains("scalar_bool_true_binary"));
    assert_eq!(refinement.target_function.as_deref(), Some("scalar_bool_true_binary"));
    assert_eq!(refinement.target_block, Some(0));
    assert_eq!(refinement.target_result, Some(2));
    assert!(refinement.bidirectional_refinement_consumed);
    assert_eq!(
        refinement.bidirectional_consumption.code,
        "scalar-bool-true-bidirectional-refinement-consumed"
    );

    let proof_consumer = conversion.target_proof_consumer_evidence();
    assert_eq!(proof_consumer.status, BinaryTrustCgProofConsumerStatus::Accepted);
    assert!(proof_consumer.target_semantics_consumed);
    assert!(proof_consumer.blockers.is_empty());
    assert_eq!(
        proof_consumer.refinement_metadata_evidence,
        conversion.refinement_metadata_evidence
    );
    assert_eq!(proof_consumer.binding.status, BinaryTrustCgProofConsumerStatus::Accepted);
    assert!(proof_consumer.binding.target_output.contains("scalar_bool_true_binary"));
    assert!(proof_consumer.binding.inputs.iter().all(|input| {
        input.target_output == proof_consumer.binding.target_output
            && input.consumed_by_target_semantics
    }));
    assert!(proof_consumer.records.iter().all(|record| record.accepted));
    assert!(proof_consumer.proof_grade_blockers.is_empty());
    assert!(proof_consumer.records.iter().any(|record| {
        record.kind == "target_semantics"
            && record.detail.contains("scalar Bool(true) slice")
            && record.detail.contains("Iconst(B1, 1)")
    }));
    assert!(proof_consumer.binding.inputs.iter().any(|input| {
        input.kind == "canonical_trust_ir_formula"
            && input.identifier == "scalar_bool_true_binary::bb0::stmt0::use"
            && input.detail.contains("scalar Bool(true)")
    }));
    assert!(proof_consumer.binding.inputs.iter().any(|input| {
        input.kind == "checked_certificate"
            && input.identifier == "vc:scalar-bool-true"
            && input.canonical_source == "checked-certificate"
            && input.detail.contains("trust-proof-cert-check")
            && input.detail.contains("lrat")
            && input.consumed_by_target_semantics
    }));
    assert!(proof_consumer.binding.inputs.iter().any(|input| {
        input.kind == "proof_replay"
            && input.identifier == "vc:scalar-bool-true"
            && input.canonical_source == "proof-replay"
            && input.detail.contains(REPLAY_ROOT_ARTIFACT_SHA256)
            && input.consumed_by_target_semantics
    }));
    assert!(proof_consumer.binding.inputs.iter().any(|input| {
        input.kind == "unsupported_ledger"
            && input.canonical_source == "unsupported-ledger"
            && input.detail.contains("eliminated=true")
            && input.consumed_by_target_semantics
    }));
    assert!(
        !conversion.validation_blockers.iter().any(|blocker| {
            matches!(
                blocker.code.as_str(),
                "missing-target-semantic-validation"
                    | "binary-provenance-not-consumed-by-target-semantics"
                    | "checked-certificate-not-consumed-by-target-semantics"
                    | "proof-replay-not-consumed-by-target-semantics"
            )
        }),
        "accepted scalar slice should remove target-consumption blockers"
    );
    let residual_blocker_codes: Vec<_> =
        conversion.validation_blockers.iter().map(|blocker| blocker.code.as_str()).collect();
    assert_eq!(
        residual_blocker_codes,
        Vec::<&str>::new(),
        "accepted scalar target and refinement consumption should clear residual proof-obligation blockers"
    );
    assert_no_refinement_consumption_residual_blockers(&conversion.validation_blockers);
    assert!(
        conversion
            .diagnostics
            .iter()
            .any(|diagnostic| { diagnostic == "binary_proof_obligation.state=discharged" })
    );
    assert!(conversion.diagnostics.iter().any(|diagnostic| {
        diagnostic.contains("refinement_metadata.slice=scalar-bool-true")
            && diagnostic.contains("refinement_metadata.source_function=scalar_bool_true_binary")
            && diagnostic.contains(
                "refinement_metadata.consumption.code=scalar-bool-true-bidirectional-refinement-consumed",
            )
    }));
    assert!(
        !conversion
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.contains("bidirectional-refinement-not-consumed"))
    );
    assert_eq!(conversion.trust_level, TrustLevel::Rejected);
    assert_ne!(conversion.trust_level, TrustLevel::ProofGrade);
}

#[test]
fn decompiled_trust_cg_scalar_consumer_rejects_nonempty_unsupported_ledger() {
    let certificate_status = ProofCertificateStatus::Checked {
        checker: "trust-proof-cert-check".to_string(),
        format: "lrat".to_string(),
        sha256: Some(
            "3333333333333333333333333333333333333333333333333333333333333333".to_string(),
        ),
    };
    let mut function = scalar_bool_true_decompiled_function(
        certificate_status,
        ReplayStatus::Replayed,
        Some(replay_grade_binary_artifact_identity()),
    );
    function.unsupported = UnsupportedLedger {
        records: vec![UnsupportedRecord {
            stage: "trust-lift".to_string(),
            architecture: Some("aarch64".to_string()),
            origin: None,
            opcode: Some("SYS".to_string()),
            operand: None,
            feature: "unsupported system register effect".to_string(),
        }],
    };
    function.verification.unsupported = 1;

    let conversion = lower_binary_decompiled_function_to_lir(&function)
        .expect("scalar Bool(true) TrustIr should remain inspectable with unsupported ledger");

    assert_eq!(conversion.unsupported_ledger_evidence.len(), 1);
    let unsupported_ledger = &conversion.unsupported_ledger_evidence[0];
    assert!(!unsupported_ledger.unsupported_ledger_eliminated);
    assert_eq!(unsupported_ledger.unsupported_records, 1);
    assert_eq!(unsupported_ledger.verification_unsupported, 1);
    assert!(!unsupported_ledger.target_semantics_consumed);

    let proof_consumer = conversion.target_proof_consumer_evidence();
    assert_eq!(proof_consumer.status, BinaryTrustCgProofConsumerStatus::Rejected);
    assert!(proof_consumer.is_rejected());
    assert!(!proof_consumer.target_semantics_consumed);
    assert!(proof_consumer.blockers.iter().any(|blocker| {
        blocker.code == "non-empty-scalar-unsupported-ledger-not-eliminated"
            && blocker.detail.contains("empty unsupported ledgers")
    }));
    assert!(proof_consumer.blockers.iter().any(|blocker| {
        blocker.code == "unsupported-ledger-not-eliminated"
            && blocker.detail.contains("non-empty unsupported records")
    }));
    assert!(proof_consumer.records.iter().any(|record| {
        record.kind == "unsupported_ledger"
            && !record.accepted
            && record.detail.contains("eliminated=false")
    }));
    assert!(proof_consumer.binding.inputs.iter().any(|input| {
        input.kind == "unsupported_ledger"
            && !input.consumed_by_target_semantics
            && input.detail.contains("eliminated=false")
    }));
    assert!(
        conversion
            .validation_blockers
            .iter()
            .any(|blocker| { blocker.code == "unsupported-ledger-not-eliminated" })
    );
    assert_eq!(conversion.trust_level, TrustLevel::Rejected);
    assert_ne!(conversion.trust_level, TrustLevel::ProofGrade);
}

#[test]
fn decompiled_trust_cg_scalar_refinement_consumer_rejects_stale_metadata_row() {
    let certificate_status = ProofCertificateStatus::Checked {
        checker: "trust-proof-cert-check".to_string(),
        format: "lrat".to_string(),
        sha256: Some(
            "3333333333333333333333333333333333333333333333333333333333333333".to_string(),
        ),
    };
    let function = scalar_bool_true_decompiled_function(
        certificate_status,
        ReplayStatus::Replayed,
        Some(replay_grade_binary_artifact_identity()),
    );
    let mut conversion = lower_binary_decompiled_function_to_lir(&function)
        .expect("scalar Bool(true) TrustIr should lower to trust_cg LIR");
    assert!(conversion.refinement_metadata_evidence[0].bidirectional_refinement_consumed);

    conversion.refinement_metadata_evidence[0].target_result = Some(99);
    conversion.refinement_metadata_evidence[0].bidirectional_refinement_consumed = true;
    conversion.refinement_metadata_evidence[0]
        .bidirectional_consumption
        .bidirectional_refinement_consumed = true;
    conversion.refinement_metadata_evidence[0].bidirectional_consumption.code =
        "forged-consumed-refinement".to_string();

    let proof_consumer = conversion.target_proof_consumer_evidence();

    assert_eq!(proof_consumer.status, BinaryTrustCgProofConsumerStatus::Rejected);
    assert!(proof_consumer.target_semantics_consumed);
    let refinement = &proof_consumer.refinement_metadata_evidence[0];
    assert!(!refinement.bidirectional_refinement_consumed);
    assert_eq!(
        refinement.bidirectional_consumption.code,
        "bidirectional-refinement-metadata-rejected"
    );
    assert!(refinement.bidirectional_consumption.detail.contains("target_result mismatch"));
    assert_refinement_and_target_consumed_proof_obligation_blockers(
        &proof_consumer.proof_grade_blockers,
    );
    assert_refinement_and_target_consumed_proof_obligation_blockers(&proof_consumer.blockers);
    assert!(proof_consumer.records.iter().any(|record| {
        record.kind == "target_refinement"
            && !record.accepted
            && record.detail.contains("target_result mismatch")
    }));
    assert_eq!(conversion.trust_level, TrustLevel::Rejected);
    assert_ne!(conversion.trust_level, TrustLevel::ProofGrade);
}

#[test]
fn decompiled_trust_cg_scalar_refinement_consumer_requires_metadata_row() {
    let certificate_status = ProofCertificateStatus::Checked {
        checker: "trust-proof-cert-check".to_string(),
        format: "lrat".to_string(),
        sha256: Some(
            "3333333333333333333333333333333333333333333333333333333333333333".to_string(),
        ),
    };
    let function = scalar_bool_true_decompiled_function(
        certificate_status,
        ReplayStatus::Replayed,
        Some(replay_grade_binary_artifact_identity()),
    );
    let mut conversion = lower_binary_decompiled_function_to_lir(&function)
        .expect("scalar Bool(true) TrustIr should lower to trust_cg LIR");
    conversion.refinement_metadata_evidence.clear();

    let proof_consumer = conversion.target_proof_consumer_evidence();

    assert_eq!(proof_consumer.status, BinaryTrustCgProofConsumerStatus::Rejected);
    assert!(proof_consumer.target_semantics_consumed);
    assert!(proof_consumer.refinement_metadata_evidence.is_empty());
    assert_target_consumed_missing_refinement_blockers(&proof_consumer.proof_grade_blockers);
    assert_target_consumed_missing_refinement_blockers(&proof_consumer.blockers);
    assert!(proof_consumer.records.iter().any(|record| {
        record.kind == "target_refinement" && record.identifier == "missing" && !record.accepted
    }));
    assert_eq!(conversion.trust_level, TrustLevel::Rejected);
    assert_ne!(conversion.trust_level, TrustLevel::ProofGrade);
}

#[test]
fn decompiled_trust_cg_scalar_consumer_stays_rejected_after_refinement_residual_discharge() {
    let certificate_status = ProofCertificateStatus::Checked {
        checker: "trust-proof-cert-check".to_string(),
        format: "lrat".to_string(),
        sha256: Some(
            "4444444444444444444444444444444444444444444444444444444444444444".to_string(),
        ),
    };
    let function = scalar_bool_true_decompiled_function(
        certificate_status,
        ReplayStatus::Replayed,
        Some(replay_grade_binary_artifact_identity()),
    );

    let conversion = lower_binary_decompiled_function_to_lir(&function)
        .expect("scalar Bool(true) TrustIr should lower to trust_cg LIR");

    let proof_consumer = conversion.target_proof_consumer_evidence();
    assert_eq!(proof_consumer.status, BinaryTrustCgProofConsumerStatus::Accepted);
    assert!(proof_consumer.target_semantics_consumed);
    assert!(proof_consumer.blockers.is_empty());
    assert!(proof_consumer.proof_grade_blockers.is_empty());
    assert_eq!(conversion.refinement_metadata_evidence.len(), 1);
    assert_eq!(
        proof_consumer.refinement_metadata_evidence,
        conversion.refinement_metadata_evidence
    );
    assert!(conversion.refinement_metadata_evidence[0].bidirectional_refinement_consumed);
    assert_eq!(conversion.trust_level, TrustLevel::Rejected);
    assert_ne!(conversion.trust_level, TrustLevel::ProofGrade);

    let blocker_codes: Vec<_> =
        conversion.validation_blockers.iter().map(|blocker| blocker.code.as_str()).collect();
    assert_eq!(
        blocker_codes,
        Vec::<&str>::new(),
        "scalar target and refinement consumption discharge the residual blockers"
    );
    assert_no_refinement_consumption_residual_blockers(&conversion.validation_blockers);
    assert!(
        !conversion
            .validation_blockers
            .iter()
            .any(|blocker| blocker.code == "missing-refinement-metadata"),
        "structured scalar refinement metadata should replace the missing-refinement blocker"
    );

    let output = trust_cg_blocker_output(
        conversion.structural_validation,
        conversion.trust_level,
        &conversion.validation_blockers,
        &conversion.diagnostics,
    );
    let json = serde_json::to_value(&output).expect("trust-cg blocker output should serialize");
    assert_eq!(json["target"], "TrustCg");
    assert_eq!(json["validation"], "Validated");
    assert_eq!(json["trust_level"], "Rejected");
    assert_ne!(json["trust_level"], "ProofGrade");
    assert!(
        json["diagnostics"]
            .as_array()
            .unwrap()
            .iter()
            .any(|diagnostic| { diagnostic.as_str() == Some("not-proof-grade") })
    );

    let target_blockers =
        json["target_validation_blockers"].as_array().expect("blockers should be JSON-visible");
    let target_features: Vec<_> =
        target_blockers.iter().map(|blocker| blocker["feature"].as_str().unwrap()).collect();
    assert!(target_features.is_empty());
    assert!(json["diagnostics"].as_array().unwrap().iter().any(|diagnostic| {
        diagnostic.as_str() == Some("trust_cg-validation=inspectable-rejected")
    }));
}

#[test]
fn decompiled_trust_cg_fake_refinement_output_metadata_cannot_force_proof_grade() {
    let certificate_status = ProofCertificateStatus::Checked {
        checker: "trust-proof-cert-check".to_string(),
        format: "lrat".to_string(),
        sha256: Some(
            "5555555555555555555555555555555555555555555555555555555555555555".to_string(),
        ),
    };
    let mut function = scalar_bool_true_decompiled_function(
        certificate_status,
        ReplayStatus::Replayed,
        Some(replay_grade_binary_artifact_identity()),
    );
    function.trust_level = TrustLevel::ProofGrade;
    function.verification.trust_level = TrustLevel::ProofGrade;
    function.output = Some(DecompiledOutput {
        target: DecompileTarget::TrustCg,
        text: Some("; forged proof-grade trust_cg report".to_string()),
        validation: ReconstructionValidationStatus::Validated,
        trust_level: TrustLevel::ProofGrade,
        validation_records: vec![ReconstructionValidationRecord {
            target: DecompileTarget::TrustCg,
            function: Some("scalar_bool_true_binary".to_string()),
            lifted_function: Some("scalar_bool_true_binary".to_string()),
            reconstructed_function: Some("scalar_bool_true_binary".to_string()),
            candidate: ReconstructionCandidateKind::StructuredTrustIr,
            status: ReconstructionValidationStatus::Validated,
            trust_level: TrustLevel::ProofGrade,
            forward: Some(ReconstructionValidationDirectionRecord {
                direction: ReconstructionValidationDirection::LiftedToOutput,
                status: ReconstructionValidationStatus::Validated,
                vc_count: 1,
                proof_certificates: 1,
                diagnostics: vec!["fake-forward-refinement=validated".to_string()],
                ..Default::default()
            }),
            reverse: Some(ReconstructionValidationDirectionRecord {
                direction: ReconstructionValidationDirection::OutputToLifted,
                status: ReconstructionValidationStatus::Validated,
                vc_count: 1,
                proof_certificates: 1,
                diagnostics: vec!["fake-reverse-refinement=validated".to_string()],
                ..Default::default()
            }),
            evidence: vec![ReconstructionValidationEvidence::BidirectionalTrustIrRefinement],
            diagnostics: vec![
                "fake-refinement-metadata=present".to_string(),
                "fake-binary-proof-obligation=discharged".to_string(),
            ],
        }],
        diagnostics: vec![
            "fake-refinement-metadata=present".to_string(),
            "fake-binary-proof-obligation=discharged".to_string(),
        ],
        ..Default::default()
    });

    let conversion = lower_binary_decompiled_function_to_lir(&function)
        .expect("scalar Bool(true) TrustIr should lower despite fake prior output metadata");

    let proof_consumer = conversion.target_proof_consumer_evidence();
    assert_eq!(proof_consumer.status, BinaryTrustCgProofConsumerStatus::Accepted);
    assert!(proof_consumer.target_semantics_consumed);
    assert!(proof_consumer.proof_grade_blockers.is_empty());
    let blocker_codes: Vec<_> =
        conversion.validation_blockers.iter().map(|blocker| blocker.code.as_str()).collect();
    assert_eq!(
        blocker_codes,
        Vec::<&str>::new(),
        "bridge-owned scalar refinement consumption should be independent of fake prior output metadata"
    );
    assert_no_refinement_consumption_residual_blockers(&conversion.validation_blockers);
    assert_eq!(conversion.trust_level, TrustLevel::Rejected);
    assert_ne!(conversion.trust_level, TrustLevel::ProofGrade);
    assert!(
        !conversion.diagnostics.iter().any(|diagnostic| diagnostic.contains("fake-")),
        "fake input output diagnostics must not be re-emitted as trusted trust_cg conversion evidence"
    );
}

#[test]
fn decompiled_trust_cg_partial_scalar_proof_metadata_keeps_target_and_residual_gates_closed() {
    let certificate_status = ProofCertificateStatus::Checked {
        checker: "trust-proof-cert-check".to_string(),
        format: "lrat".to_string(),
        sha256: None,
    };
    let function = scalar_bool_true_decompiled_function(
        certificate_status,
        ReplayStatus::Replayed,
        Some(replay_grade_binary_artifact_identity()),
    );

    let conversion = lower_binary_decompiled_function_to_lir(&function)
        .expect("scalar Bool(true) TrustIr with partial proof metadata should lower inspectably");

    let proof_consumer = conversion.target_proof_consumer_evidence();
    assert_eq!(proof_consumer.status, BinaryTrustCgProofConsumerStatus::Rejected);
    assert!(!proof_consumer.target_semantics_consumed);
    assert!(proof_consumer.blockers.iter().any(|blocker| {
        blocker.code == "non-empty-scalar-checked-certificate-identity-missing"
    }));
    assert!(
        proof_consumer
            .blockers
            .iter()
            .any(|blocker| { blocker.code == "non-empty-scalar-proof-metadata-identity-mismatch" })
    );

    assert_refinement_present_and_pending_proof_obligation_blockers(
        &conversion.validation_blockers,
    );
    assert_eq!(conversion.refinement_metadata_evidence.len(), 1);
    let refinement = &conversion.refinement_metadata_evidence[0];
    assert_eq!(refinement.slice, "scalar-bool-true");
    assert!(!refinement.bidirectional_refinement_consumed);
    assert!(
        !conversion
            .validation_blockers
            .iter()
            .any(|blocker| blocker.code == "missing-refinement-metadata"),
        "scalar metadata presence should change the residual refinement blocker"
    );
    assert!(conversion.diagnostics.iter().any(|diagnostic| {
        diagnostic == "binary_proof_obligation.state=refinement-metadata-present-pending-proof"
    }));
    assert!(conversion.diagnostics.iter().any(|diagnostic| {
        diagnostic.contains("refinement_metadata.slice=scalar-bool-true")
            && diagnostic.contains(
                "refinement_metadata.consumption.code=bidirectional-refinement-not-consumed",
            )
    }));
    assert!(conversion.validation_blockers.iter().any(|blocker| {
        blocker.code == "checked-proof-certificate-incomplete"
            && blocker.detail.contains("checker, format, and sha256 identity")
    }));
    assert!(
        conversion
            .validation_blockers
            .iter()
            .any(|blocker| { blocker.code == "missing-target-semantic-validation" })
    );
    assert_eq!(conversion.trust_level, TrustLevel::Rejected);
    assert_ne!(conversion.trust_level, TrustLevel::ProofGrade);
}

#[test]
fn canonical_trust_ir_symbolic_formula_surfaces_as_trust_cg_blocker_evidence_without_undef() {
    let formula = Formula::BvAdd(
        Box::new(Formula::Var("x0".to_string(), Sort::BitVec(32))),
        Box::new(Formula::BitVec { value: 7, width: 32 }),
        32,
    );
    let formula_json = serde_json::to_string(&formula).expect("formula should serialize");
    let canonical = format!(
        r#"; TrustIr text format v1
module "canonical_symbolic_binary"

fn @canonical_symbolic_binary(functy.0) {{
bb0(%0: i32):
        %1 = dialect_op trust_symbolic.formula() -> i32 [schema=str:"trust-types.Formula@1"] [formula_json=str:{formula_json:?}] [formula.smtlib2=str:"(bvadd x0 (_ bv7 32))"] [formula.sort=str:"(_ BitVec 32)"] [formula.debug=str:"BvAdd(Var(\"x0\", BitVec(32)), BitVec {{ value: 7, width: 32 }}, 32)"]
        ret %1
}}
"#
    );
    assert!(canonical.contains("dialect_op trust_symbolic.formula"));
    assert!(canonical.contains("formula_json"));
    assert!(
        !canonical.to_ascii_lowercase().contains("undef"),
        "canonical symbolic formula fixture must remain a dialect op, not Undef"
    );

    let conversion =
        lower_canonical_trust_ir_to_lir(&canonical).expect("canonical TrustIr should be inspected");

    assert!(conversion.lir.is_empty());
    assert_eq!(conversion.structural_validation, ReconstructionValidationStatus::Failed);
    assert_eq!(conversion.trust_cg_validation, BinaryTrustCgValidationStatus::Rejected);
    assert_eq!(conversion.trust_level, TrustLevel::Rejected);
    assert_eq!(conversion.symbolic_formulas.len(), 1);
    assert_eq!(conversion.symbolic_formulas[0].function, "canonical_symbolic_binary");
    assert_eq!(conversion.symbolic_formulas[0].operand, "dialect_op");
    assert_eq!(conversion.symbolic_formulas[0].formula, formula);
    assert_eq!(conversion.symbolic_formulas[0].sort, "(_ BitVec 32)");
    assert_eq!(conversion.symbolic_formulas[0].bit_width, Some(32));

    assert_eq!(conversion.symbolic_formula_evidence.len(), 1);
    let evidence = &conversion.symbolic_formula_evidence[0];
    assert_eq!(evidence.formula.as_ref(), Some(&formula));
    assert_eq!(evidence.smtlib.as_deref(), Some("(bvadd x0 (_ bv7 32))"));
    assert_eq!(evidence.sort.as_deref(), Some("(_ BitVec 32)"));
    assert_eq!(evidence.inferred_sort.as_deref(), Some("(_ BitVec 32)"));
    assert_eq!(evidence.bit_width, Some(32));
    assert!(evidence.schema_errors.is_empty());
    assert!(!evidence.target_semantics_consumed);
    assert_eq!(evidence.target_semantic_consumption.code, "no-trust_cg-target-semantic-consumer");
    let formula_json = evidence.formula_json.as_deref().expect("formula JSON evidence");
    let reparsed_formula: Formula =
        serde_json::from_str(formula_json).expect("formula JSON evidence should round-trip");
    assert_eq!(reparsed_formula, formula);

    let proof_consumer = conversion.target_proof_consumer_evidence();
    assert_eq!(proof_consumer.status, BinaryTrustCgProofConsumerStatus::Rejected);
    assert_eq!(proof_consumer.binding.target_output, "trust_cg-lir:blocked:no-emitted-functions");
    assert!(proof_consumer.binding.inputs.iter().any(|input| {
        input.kind == "canonical_trust_ir_formula"
            && input.identifier == "canonical_symbolic_binary::bb0::stmt0::dialect_op"
            && input.target_output == "trust_cg-lir:blocked:no-emitted-functions"
            && !input.consumed_by_target_semantics
    }));
    assert!(proof_consumer.records.iter().any(|record| {
        record.kind == "symbolic_formula"
            && record.identifier == "canonical_symbolic_binary::bb0::stmt0::dialect_op"
            && !record.accepted
    }));
    assert!(proof_consumer.records.iter().any(|record| {
        record.kind == "checked_certificate" && record.identifier == "missing" && !record.accepted
    }));
    assert!(proof_consumer.records.iter().any(|record| {
        record.kind == "proof_replay" && record.identifier == "missing" && !record.accepted
    }));
    assert!(proof_consumer.records.iter().any(|record| {
        record.kind == "binary_provenance" && record.identifier == "missing" && !record.accepted
    }));
    assert!(proof_consumer.blockers.iter().any(|blocker| {
        blocker.code == "missing-binary-provenance"
            && blocker.detail.contains("machine instructions")
    }));
    assert_residual_refinement_and_proof_obligation_blockers(&proof_consumer.proof_grade_blockers);
    assert!(proof_consumer.blockers.iter().any(|blocker| {
        blocker.code == "symbolic-formula-not-consumed-by-target-semantics"
            && blocker.detail.contains("trust-cg-bridge::target-semantic-consumption-gate")
            && blocker.detail.contains("formula.smtlib2=(bvadd x0 (_ bv7 32))")
    }));

    assert!(conversion.validation_blockers.iter().any(|blocker| {
        blocker.code == "preserved-symbolic-formula"
            && blocker.detail.contains("formula JSON/SMT-LIB/sort metadata")
            && blocker.detail.contains("formula.smtlib2=(bvadd x0 (_ bv7 32))")
            && blocker.detail.contains("Undef")
    }));
    assert!(conversion.validation_blockers.iter().any(|blocker| {
        blocker.code == "missing-binary-provenance"
            && blocker.detail.contains("machine instructions")
    }));
    assert!(conversion.diagnostics.iter().any(|diagnostic| {
        diagnostic.contains("symbolic formula dialect metadata preserved")
            && diagnostic.contains("not converted to Undef")
    }));
}

#[test]
fn canonical_trust_ir_binary_provenance_is_trust_cg_blocker_evidence_until_consumed() {
    let canonical = canonical_binary_provenance_trust_ir(
        "canonical_provenance_binary",
        EXACT_CANONICAL_BINARY_PROVENANCE_ATTRS,
    );

    let conversion = lower_canonical_trust_ir_to_lir(&canonical)
        .expect("canonical provenance should be inspected");

    assert!(conversion.lir.is_empty());
    assert_eq!(conversion.structural_validation, ReconstructionValidationStatus::Failed);
    assert_eq!(conversion.trust_cg_validation, BinaryTrustCgValidationStatus::Rejected);
    assert_eq!(conversion.trust_level, TrustLevel::Rejected);
    assert!(conversion.symbolic_formula_evidence.is_empty());
    assert_eq!(conversion.provenance_evidence.len(), 1);
    let provenance = &conversion.provenance_evidence[0];
    assert_eq!(provenance.function, "canonical_provenance_binary");
    assert_eq!(provenance.source, "canonical-trust_ir.trust_binary.provenance:unit-test");
    assert_eq!(provenance.block, Some(0));
    assert_eq!(provenance.statement_index, Some(0));
    assert_eq!(provenance.origin.binary_path.as_deref(), Some("fixture.bin"));
    assert_eq!(provenance.origin.function_entry, Some(0x401000));
    assert_eq!(provenance.origin.instruction_address, 0x401004);
    assert_eq!(provenance.origin.instruction_size, Some(4));
    assert_eq!(provenance.origin.encoding, Some(0xd503_201f));
    assert_eq!(provenance.origin.instruction_bytes, vec![0x1f, 0x20, 0x03, 0xd5]);
    assert!(!provenance.target_semantics_consumed);
    assert!(!provenance.target_semantic_consumption.target_semantics_consumed);
    assert_eq!(
        provenance.target_semantic_consumption.consumer,
        "trust-cg-bridge::target-semantic-consumption-gate"
    );
    assert_eq!(provenance.target_semantic_consumption.code, "no-trust_cg-target-semantic-consumer");
    assert_eq!(
        provenance.target_semantic_consumption.input_claimed_target_semantics_consumed,
        None
    );

    assert!(conversion.validation_blockers.iter().any(|blocker| {
        blocker.code == "binary-provenance-not-consumed-by-target-semantics"
            && blocker.detail.contains("1 binary provenance")
    }));
    assert!(
        !conversion
            .validation_blockers
            .iter()
            .any(|blocker| blocker.code == "missing-binary-provenance"),
        "recognized canonical provenance must replace the missing-provenance blocker"
    );

    let proof_consumer = conversion.target_proof_consumer_evidence();
    assert_eq!(proof_consumer.status, BinaryTrustCgProofConsumerStatus::Rejected);
    assert!(proof_consumer.records.iter().any(|record| {
        record.kind == "binary_provenance"
            && record.identifier.contains("canonical_provenance_binary::bb0::stmt0")
            && record.identifier.contains("0x401004")
            && !record.accepted
            && record.detail.contains("target semantics have not consumed")
    }));
    assert!(proof_consumer.blockers.iter().any(|blocker| {
        blocker.code == "binary-provenance-not-consumed-by-target-semantics"
            && blocker.detail.contains("1 binary provenance")
    }));
    assert!(
        !proof_consumer.blockers.iter().any(|blocker| blocker.code == "missing-binary-provenance"),
        "exact-but-unconsumed provenance must not be downgraded to missing provenance"
    );
    assert!(conversion.diagnostics.iter().any(|diagnostic| {
        diagnostic.contains(
            "binary_provenance.source=canonical-trust_ir.trust_binary.provenance:unit-test",
        ) && diagnostic.contains("binary_provenance.instruction_bytes=1f2003d5")
            && diagnostic.contains("binary_provenance.target_semantics_consumed=false")
    }));
}

#[test]
fn canonical_trust_ir_proof_metadata_becomes_trust_cg_binding_records_but_stays_rejected() {
    let certificate_status = ProofCertificateStatus::Checked {
        checker: "trust-proof-cert-check".to_string(),
        format: "lrat".to_string(),
        sha256: Some(
            "cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc".to_string(),
        ),
    };
    let certificate_json =
        serde_json::to_string(&certificate_status).expect("certificate status should serialize");
    let certificate_attrs = format!(
        r#"[schema=str:"trust-types.CheckedCertificate@1"] [source=str:"unit-test-cert"] [status_json=str:{certificate_json:?}] [target_semantics_consumed=str:"true"]"#
    );
    let replay_attrs = r#"[schema=str:"trust-types.ProofReplay@1"] [source=str:"unit-test-replay"] [replay_status=str:"replayed"] [artifact_sha256=str:"dddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd"] [exact_replay_checked=str:"true"] [target_semantics_consumed=str:"true"]"#;
    let canonical = canonical_proof_metadata_trust_ir(
        "canonical_proof_metadata_binary",
        &certificate_attrs,
        replay_attrs,
    );

    let conversion = lower_canonical_trust_ir_to_lir(&canonical)
        .expect("canonical proof metadata should inspect");

    assert!(conversion.lir.is_empty());
    assert_eq!(conversion.structural_validation, ReconstructionValidationStatus::Failed);
    assert_eq!(conversion.trust_cg_validation, BinaryTrustCgValidationStatus::Rejected);
    assert_eq!(conversion.trust_level, TrustLevel::Rejected);
    assert_ne!(conversion.trust_level, TrustLevel::ProofGrade);

    assert_eq!(conversion.checked_certificate_evidence.len(), 1);
    let certificate = &conversion.checked_certificate_evidence[0];
    assert_eq!(certificate.function.as_deref(), Some("canonical_proof_metadata_binary"));
    assert_eq!(
        certificate.source,
        "canonical-trust_ir.trust_proof.checked_certificate:unit-test-cert"
    );
    assert_eq!(certificate.block, Some(0));
    assert_eq!(certificate.statement_index, Some(0));
    assert_eq!(certificate.certificate, certificate_status);
    assert_eq!(certificate.checker, "trust-proof-cert-check");
    assert_eq!(certificate.format, "lrat");
    assert_eq!(
        certificate.sha256.as_deref(),
        Some("cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc")
    );
    assert!(!certificate.target_semantics_consumed);
    assert_eq!(
        certificate.target_semantic_consumption.input_claimed_target_semantics_consumed,
        Some(true)
    );
    assert!(
        !certificate.target_semantic_consumption.target_semantics_consumed,
        "canonical metadata cannot self-attest trust_cg target semantic consumption"
    );

    assert_eq!(conversion.proof_replay_evidence.len(), 1);
    let replay = &conversion.proof_replay_evidence[0];
    assert_eq!(replay.function.as_deref(), Some("canonical_proof_metadata_binary"));
    assert_eq!(replay.source, "canonical-trust_ir.trust_proof.proof_replay:unit-test-replay");
    assert_eq!(replay.block, Some(0));
    assert_eq!(replay.statement_index, Some(1));
    assert_eq!(replay.replay, ReplayStatus::Replayed);
    assert!(replay.exact_replay_checked);
    assert_eq!(
        replay.artifact_sha256.as_deref(),
        Some("dddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd")
    );
    assert!(!replay.target_semantics_consumed);
    assert_eq!(
        replay.target_semantic_consumption.input_claimed_target_semantics_consumed,
        Some(true)
    );
    assert!(!replay.target_semantic_consumption.target_semantics_consumed);

    let proof_consumer = conversion.target_proof_consumer_evidence();
    assert_eq!(proof_consumer.status, BinaryTrustCgProofConsumerStatus::Rejected);
    assert_eq!(proof_consumer.binding.target_output, "trust_cg-lir:blocked:no-emitted-functions");
    assert!(proof_consumer.binding.inputs.iter().any(|input| {
        input.kind == "checked_certificate"
            && input.canonical_source == "trust_proof.checked_certificate"
            && input.identifier.contains("canonical_proof_metadata_binary::bb0::stmt0")
            && input.identifier.contains("trust-proof-cert-check:lrat")
            && !input.consumed_by_target_semantics
    }));
    assert!(proof_consumer.binding.inputs.iter().any(|input| {
        input.kind == "proof_replay"
            && input.canonical_source == "trust_proof.proof_replay"
            && input.identifier.contains("canonical_proof_metadata_binary::bb0::stmt1")
            && input.identifier.contains("Replayed:exact")
            && !input.consumed_by_target_semantics
    }));
    assert!(proof_consumer.records.iter().any(|record| {
        record.kind == "checked_certificate"
            && record.identifier.contains("canonical_proof_metadata_binary::bb0::stmt0")
            && !record.accepted
            && record.detail.contains("target semantics have not consumed")
    }));
    assert!(proof_consumer.records.iter().any(|record| {
        record.kind == "proof_replay"
            && record.identifier.contains("canonical_proof_metadata_binary::bb0::stmt1")
            && !record.accepted
            && record.detail.contains("exact_replay_checked=true")
    }));
    assert!(
        proof_consumer.blockers.iter().any(|blocker| {
            blocker.code == "checked-certificate-not-consumed-by-target-semantics"
        })
    );
    assert!(
        proof_consumer
            .blockers
            .iter()
            .any(|blocker| { blocker.code == "proof-replay-not-consumed-by-target-semantics" })
    );
    assert!(conversion.diagnostics.iter().any(|diagnostic| {
        diagnostic.contains("checked_certificate.source=canonical-trust_ir.trust_proof.checked_certificate:unit-test-cert")
            && diagnostic.contains("checked_certificate.input_claim.target_semantics_consumed=true")
            && diagnostic.contains("checked_certificate.consumption.target_semantics_consumed=false")
    }));
    assert!(conversion.diagnostics.iter().any(|diagnostic| {
        diagnostic.contains(
            "proof_replay.source=canonical-trust_ir.trust_proof.proof_replay:unit-test-replay",
        ) && diagnostic.contains("proof_replay.exact_replay_checked=true")
            && diagnostic.contains("proof_replay.consumption.target_semantics_consumed=false")
    }));
}

#[test]
fn canonical_empty_noop_slice_is_consumed_by_bounded_trust_cg_proof_consumer() {
    let certificate_status = ProofCertificateStatus::Checked {
        checker: "trust-proof-cert-check".to_string(),
        format: "lrat".to_string(),
        sha256: Some(
            "eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee".to_string(),
        ),
    };
    let certificate_json =
        serde_json::to_string(&certificate_status).expect("certificate status should serialize");
    let certificate_attrs = format!(
        r#"[schema=str:"trust-types.CheckedCertificate@1"] [source=str:"bounded-empty-cert"] [status_json=str:{certificate_json:?}] [target_semantics_consumed=str:"false"]"#
    );
    let replay_attrs = r#"[schema=str:"trust-types.ProofReplay@1"] [source=str:"bounded-empty-replay"] [replay_status=str:"replayed"] [artifact_sha256=str:"ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"] [exact_replay_checked=str:"true"] [target_semantics_consumed=str:"false"]"#;
    let canonical = canonical_bounded_empty_consumer_trust_ir(
        "canonical_empty_noop_consumer",
        &Formula::Bool(true),
        EXACT_CANONICAL_BINARY_PROVENANCE_ATTRS,
        &certificate_attrs,
        replay_attrs,
    );

    let conversion =
        lower_canonical_trust_ir_to_lir(&canonical).expect("bounded empty slice should inspect");

    assert!(conversion.lir.is_empty());
    assert_eq!(conversion.trust_cg_validation, BinaryTrustCgValidationStatus::Rejected);
    assert_eq!(conversion.trust_level, TrustLevel::Rejected);
    assert_ne!(conversion.trust_level, TrustLevel::ProofGrade);
    assert_eq!(conversion.symbolic_formula_evidence.len(), 1);
    assert!(conversion.symbolic_formula_evidence[0].target_semantics_consumed);
    assert_eq!(
        conversion.symbolic_formula_evidence[0].target_semantic_consumption.code,
        "bounded-empty-trust_cg-target-consumed"
    );
    assert_eq!(conversion.provenance_evidence.len(), 1);
    assert_eq!(conversion.checked_certificate_evidence.len(), 1);
    assert_eq!(conversion.proof_replay_evidence.len(), 1);
    assert_eq!(conversion.unsupported_ledger_evidence.len(), 1);
    assert!(conversion.provenance_evidence[0].target_semantics_consumed);
    assert_eq!(
        conversion.provenance_evidence[0].target_semantic_consumption.code,
        "bounded-empty-trust_cg-target-consumed"
    );
    assert!(conversion.checked_certificate_evidence[0].target_semantics_consumed);
    assert!(conversion.proof_replay_evidence[0].target_semantics_consumed);
    assert!(conversion.unsupported_ledger_evidence[0].unsupported_ledger_eliminated);
    assert!(conversion.unsupported_ledger_evidence[0].target_semantics_consumed);
    assert_eq!(
        conversion.unsupported_ledger_evidence[0].target_semantic_consumption.code,
        "bounded-empty-trust_cg-target-consumed"
    );
    assert_eq!(conversion.refinement_metadata_evidence.len(), 1);
    let refinement = &conversion.refinement_metadata_evidence[0];
    assert_eq!(refinement.slice, "bounded-empty-noop");
    assert_eq!(refinement.source, "canonical-trust_ir");
    assert_eq!(refinement.source_function, "canonical_empty_noop_consumer");
    assert_eq!(refinement.source_block, Some(0));
    assert_eq!(refinement.source_statement_index, Some(0));
    assert_eq!(refinement.source_formula.as_deref(), Some("true"));
    assert_eq!(refinement.target_output, "trust_cg-lir:blocked:no-emitted-functions");
    assert_eq!(refinement.target_function, None);
    assert_eq!(refinement.target_block, None);
    assert_eq!(refinement.target_result, None);
    assert!(refinement.bidirectional_refinement_consumed);
    assert_eq!(
        refinement.bidirectional_consumption.code,
        "bounded-empty-noop-bidirectional-refinement-consumed"
    );
    assert!(
        !conversion.validation_blockers.iter().any(|blocker| {
            matches!(
                blocker.code.as_str(),
                "binary-provenance-not-consumed-by-target-semantics"
                    | "checked-certificate-not-consumed-by-target-semantics"
                    | "proof-replay-not-consumed-by-target-semantics"
            )
        }),
        "bounded slice should not report consumed metadata as unconsumed"
    );
    assert!(
        conversion.validation_blockers.iter().any(|blocker| {
            blocker.code == "preserved-symbolic-formula"
                && blocker.detail.contains("formula JSON/SMT-LIB/sort metadata")
        }),
        "target proof-consumer acceptance for the bounded slice must not erase the conversion-level formula preservation blocker"
    );
    assert_no_refinement_consumption_residual_blockers(&conversion.validation_blockers);
    assert!(
        !conversion
            .validation_blockers
            .iter()
            .any(|blocker| blocker.code == "missing-binary-proof-obligation"),
        "bounded bridge consumption should narrow the binary proof-obligation blocker"
    );
    assert!(
        !conversion
            .validation_blockers
            .iter()
            .any(|blocker| blocker.code == "missing-refinement-metadata"),
        "bounded refinement metadata should replace the missing-refinement blocker"
    );
    assert!(
        conversion
            .diagnostics
            .iter()
            .any(|diagnostic| { diagnostic == "binary_proof_obligation.state=discharged" })
    );

    let proof_consumer = conversion.target_proof_consumer_evidence();
    assert_eq!(proof_consumer.status, BinaryTrustCgProofConsumerStatus::Accepted);
    assert!(proof_consumer.target_semantics_consumed);
    assert!(proof_consumer.blockers.is_empty());
    assert_eq!(
        proof_consumer.refinement_metadata_evidence,
        conversion.refinement_metadata_evidence
    );
    assert!(proof_consumer.proof_grade_blockers.is_empty());
    assert_eq!(proof_consumer.binding.target_output, "trust_cg-lir:blocked:no-emitted-functions");
    assert_eq!(proof_consumer.binding.status, BinaryTrustCgProofConsumerStatus::Accepted);
    assert!(proof_consumer.binding.target_semantics_consumed);
    assert!(proof_consumer.records.iter().all(|record| record.accepted));
    assert!(proof_consumer.binding.inputs.iter().all(|input| {
        input.target_output == "trust_cg-lir:blocked:no-emitted-functions"
            && input.consumed_by_target_semantics
    }));
    assert!(proof_consumer.records.iter().any(|record| {
        record.kind == "target_semantics" && record.detail.contains("bounded empty/no-op slice")
    }));
    assert!(proof_consumer.binding.inputs.iter().any(|input| {
        input.kind == "unsupported_ledger"
            && input.canonical_source == "trust_proof.unsupported_ledger"
            && input.detail.contains("eliminated=true")
            && input.consumed_by_target_semantics
    }));
    assert!(conversion.diagnostics.iter().any(|diagnostic| {
        diagnostic
            .contains("binary_provenance.consumption.code=bounded-empty-trust_cg-target-consumed")
            && diagnostic.contains("binary_provenance.consumption.target_semantics_consumed=true")
    }));
    assert!(conversion.diagnostics.iter().any(|diagnostic| {
        diagnostic.contains("formula.consumption.code=bounded-empty-trust_cg-target-consumed")
            && diagnostic.contains("formula.consumption.target_semantics_consumed=true")
    }));
    assert!(conversion.diagnostics.iter().any(|diagnostic| {
        diagnostic.contains("unsupported_ledger.source=canonical-trust_ir.trust_proof.unsupported_ledger:bounded-empty-unsupported-ledger")
            && diagnostic.contains("unsupported_ledger.eliminated=true")
            && diagnostic.contains("unsupported_ledger.consumption.target_semantics_consumed=true")
    }));
    assert!(conversion.diagnostics.iter().any(|diagnostic| {
        diagnostic.contains("refinement_metadata.slice=bounded-empty-noop")
            && diagnostic.contains(
                "refinement_metadata.consumption.code=bounded-empty-noop-bidirectional-refinement-consumed",
            )
    }));
}

#[test]
fn canonical_empty_noop_trust_cg_consumer_rejects_replayed_wasm_target_evidence() {
    let certificate_status = ProofCertificateStatus::Checked {
        checker: "trust-proof-cert-check".to_string(),
        format: "lrat".to_string(),
        sha256: Some(
            "eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee".to_string(),
        ),
    };
    let certificate_json =
        serde_json::to_string(&certificate_status).expect("certificate status should serialize");
    let certificate_attrs = format!(
        r#"[schema=str:"trust-types.CheckedCertificate@1"] [source=str:"bounded-empty-cert"] [status_json=str:{certificate_json:?}] [target_semantics_consumed=str:"false"]"#
    );
    let replay_attrs = r#"[schema=str:"trust-types.ProofReplay@1"] [source=str:"bounded-empty-replay"] [replay_status=str:"replayed"] [artifact_sha256=str:"ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"] [exact_replay_checked=str:"true"] [target_semantics_consumed=str:"false"]"#;
    let canonical = canonical_bounded_empty_consumer_trust_ir(
        "canonical_empty_noop_consumer",
        &Formula::Bool(true),
        EXACT_CANONICAL_BINARY_PROVENANCE_ATTRS,
        &certificate_attrs,
        replay_attrs,
    );
    let mut conversion =
        lower_canonical_trust_ir_to_lir(&canonical).expect("bounded empty slice should inspect");
    let replayed_wasm_consumption = replayed_wasm_consumption_for_trust_cg();
    for formula in &mut conversion.symbolic_formula_evidence {
        formula.target_semantic_consumption = replayed_wasm_consumption.clone();
        formula.target_semantics_consumed = true;
    }
    for provenance in &mut conversion.provenance_evidence {
        provenance.target_semantic_consumption = replayed_wasm_consumption.clone();
        provenance.target_semantics_consumed = true;
    }
    for certificate in &mut conversion.checked_certificate_evidence {
        certificate.target_semantic_consumption = replayed_wasm_consumption.clone();
        certificate.target_semantics_consumed = true;
    }
    for replay in &mut conversion.proof_replay_evidence {
        replay.target_semantic_consumption = replayed_wasm_consumption.clone();
        replay.target_semantics_consumed = true;
    }
    for unsupported_ledger in &mut conversion.unsupported_ledger_evidence {
        unsupported_ledger.target_semantic_consumption = replayed_wasm_consumption.clone();
        unsupported_ledger.target_semantics_consumed = true;
    }

    let proof_consumer = conversion.target_proof_consumer_evidence();

    assert_eq!(proof_consumer.status, BinaryTrustCgProofConsumerStatus::Rejected);
    assert!(proof_consumer.is_rejected());
    assert!(!proof_consumer.target_semantics_consumed);
    assert!(proof_consumer.blockers.iter().any(|blocker| {
        blocker.code == "bounded-empty-slice-not-bridge-consumed"
            && blocker.detail.contains("target-specific")
            && blocker.detail.contains("trust-cg")
    }));
    assert!(proof_consumer.records.iter().any(|record| {
        record.kind == "binary_provenance"
            && !record.accepted
            && record.detail.contains("trust-wasm-bridge::target-semantic-consumption-gate")
    }));
    assert!(proof_consumer.binding.inputs.iter().all(|input| {
        input.target_output == "trust_cg-lir:blocked:no-emitted-functions"
            && !input.consumed_by_target_semantics
    }));
    assert_refinement_present_and_pending_proof_obligation_blockers(
        &proof_consumer.proof_grade_blockers,
    );
    assert_eq!(conversion.trust_level, TrustLevel::Rejected);
    assert_ne!(conversion.trust_level, TrustLevel::ProofGrade);
}

#[test]
fn canonical_empty_noop_refinement_consumer_rejects_stale_metadata_row() {
    let certificate_status = ProofCertificateStatus::Checked {
        checker: "trust-proof-cert-check".to_string(),
        format: "lrat".to_string(),
        sha256: Some(
            "eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee".to_string(),
        ),
    };
    let certificate_json =
        serde_json::to_string(&certificate_status).expect("certificate status should serialize");
    let certificate_attrs = format!(
        r#"[schema=str:"trust-types.CheckedCertificate@1"] [source=str:"bounded-empty-cert"] [status_json=str:{certificate_json:?}]"#
    );
    let replay_attrs = r#"[schema=str:"trust-types.ProofReplay@1"] [source=str:"bounded-empty-replay"] [replay_status=str:"replayed"] [artifact_sha256=str:"ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"] [exact_replay_checked=str:"true"] [target_semantics_consumed=str:"false"]"#;
    let canonical = canonical_bounded_empty_consumer_trust_ir(
        "canonical_empty_noop_consumer",
        &Formula::Bool(true),
        EXACT_CANONICAL_BINARY_PROVENANCE_ATTRS,
        &certificate_attrs,
        replay_attrs,
    );
    let mut conversion =
        lower_canonical_trust_ir_to_lir(&canonical).expect("bounded empty slice should inspect");
    assert!(conversion.refinement_metadata_evidence[0].bidirectional_refinement_consumed);

    conversion.refinement_metadata_evidence[0].source_function =
        "canonical_empty_noop_consumer_stale".to_string();
    conversion.refinement_metadata_evidence[0].bidirectional_refinement_consumed = true;
    conversion.refinement_metadata_evidence[0]
        .bidirectional_consumption
        .bidirectional_refinement_consumed = true;
    conversion.refinement_metadata_evidence[0].bidirectional_consumption.code =
        "forged-consumed-refinement".to_string();

    let proof_consumer = conversion.target_proof_consumer_evidence();

    assert_eq!(proof_consumer.status, BinaryTrustCgProofConsumerStatus::Rejected);
    assert!(proof_consumer.target_semantics_consumed);
    let refinement = &proof_consumer.refinement_metadata_evidence[0];
    assert!(!refinement.bidirectional_refinement_consumed);
    assert_eq!(
        refinement.bidirectional_consumption.code,
        "bidirectional-refinement-metadata-rejected"
    );
    assert!(refinement.bidirectional_consumption.detail.contains("source_function mismatch"));
    assert_refinement_and_target_consumed_proof_obligation_blockers(
        &proof_consumer.proof_grade_blockers,
    );
    assert_refinement_and_target_consumed_proof_obligation_blockers(&proof_consumer.blockers);
    assert!(proof_consumer.records.iter().any(|record| {
        record.kind == "target_refinement"
            && !record.accepted
            && record.detail.contains("source_function mismatch")
    }));
    assert_eq!(conversion.trust_level, TrustLevel::Rejected);
    assert_ne!(conversion.trust_level, TrustLevel::ProofGrade);
}

#[test]
fn canonical_empty_slice_with_nontrivial_formula_stays_rejected_for_trust_cg() {
    let formula = Formula::BvAdd(
        Box::new(Formula::Var("x0".to_string(), Sort::BitVec(32))),
        Box::new(Formula::BitVec { value: 1, width: 32 }),
        32,
    );
    let certificate_status = ProofCertificateStatus::Checked {
        checker: "trust-proof-cert-check".to_string(),
        format: "lrat".to_string(),
        sha256: Some(
            "abababababababababababababababababababababababababababababababab".to_string(),
        ),
    };
    let certificate_json =
        serde_json::to_string(&certificate_status).expect("certificate status should serialize");
    let certificate_attrs = format!(
        r#"[schema=str:"trust-types.CheckedCertificate@1"] [source=str:"nontrivial-cert"] [status_json=str:{certificate_json:?}]"#
    );
    let replay_attrs = r#"[schema=str:"trust-types.ProofReplay@1"] [source=str:"nontrivial-replay"] [replay_status=str:"replayed"] [artifact_sha256=str:"cdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcd"] [exact_replay_checked=str:"true"]"#;
    let canonical = canonical_bounded_empty_consumer_trust_ir(
        "canonical_empty_nontrivial_consumer",
        &formula,
        EXACT_CANONICAL_BINARY_PROVENANCE_ATTRS,
        &certificate_attrs,
        replay_attrs,
    );

    let conversion =
        lower_canonical_trust_ir_to_lir(&canonical).expect("nontrivial empty slice should inspect");

    let proof_consumer = conversion.target_proof_consumer_evidence();
    assert_eq!(proof_consumer.status, BinaryTrustCgProofConsumerStatus::Rejected);
    assert!(!proof_consumer.target_semantics_consumed);
    assert!(proof_consumer.blockers.iter().any(|blocker| {
        blocker.code == "bounded-empty-slice-nontrivial-formula"
            && blocker.detail.contains("rejects nontrivial")
    }));
    assert!(
        proof_consumer
            .records
            .iter()
            .any(|record| { record.kind == "symbolic_formula" && !record.accepted }),
        "nontrivial formula metadata must keep the proof-consumer gate closed"
    );
}

#[test]
fn canonical_empty_slice_with_extra_nonmetadata_op_stays_rejected_for_trust_cg() {
    let certificate_status = ProofCertificateStatus::Checked {
        checker: "trust-proof-cert-check".to_string(),
        format: "lrat".to_string(),
        sha256: Some(
            "1212121212121212121212121212121212121212121212121212121212121212".to_string(),
        ),
    };
    let certificate_json =
        serde_json::to_string(&certificate_status).expect("certificate status should serialize");
    let certificate_attrs = format!(
        r#"[schema=str:"trust-types.CheckedCertificate@1"] [source=str:"extra-op-cert"] [status_json=str:{certificate_json:?}]"#
    );
    let replay_attrs = r#"[schema=str:"trust-types.ProofReplay@1"] [source=str:"extra-op-replay"] [replay_status=str:"replayed"] [artifact_sha256=str:"3434343434343434343434343434343434343434343434343434343434343434"] [exact_replay_checked=str:"true"]"#;
    let canonical = canonical_bounded_empty_consumer_trust_ir(
        "canonical_empty_extra_op_consumer",
        &Formula::Bool(true),
        EXACT_CANONICAL_BINARY_PROVENANCE_ATTRS,
        &certificate_attrs,
        replay_attrs,
    )
    .replace(
        "        ret %0",
        "        %6 = dialect_op trust_exec.not_empty() -> i32\n        ret %0",
    );

    let conversion =
        lower_canonical_trust_ir_to_lir(&canonical).expect("extra op slice should inspect");

    assert!(!conversion.provenance_evidence[0].target_semantics_consumed);
    let proof_consumer = conversion.target_proof_consumer_evidence();
    assert_eq!(proof_consumer.status, BinaryTrustCgProofConsumerStatus::Rejected);
    assert!(proof_consumer.blockers.iter().any(|blocker| {
        blocker.code == "bounded-empty-slice-not-bridge-consumed"
            && blocker.detail.contains("source-shape validation")
    }));
}

#[test]
fn canonical_trust_ir_malformed_binary_provenance_row_stays_missing_for_trust_cg() {
    let malformed_attrs = r#"[schema=str:"trust-types.BinaryProvenance@1"] [source=str:"malformed"] [binary_path=str:"fixture.bin"] [function_entry=str:"0x401000"] [instruction_address=str:"0x401004"] [instruction_size=str:"4"] [encoding=str:"0xd503201f"] [instruction_bytes=str:"not-hex"] [target_semantics_consumed=str:"true"]"#;
    let canonical = canonical_symbolic_with_binary_provenance_trust_ir(
        "canonical_malformed_provenance",
        malformed_attrs,
    );

    let conversion = lower_canonical_trust_ir_to_lir(&canonical)
        .expect("symbolic metadata should keep malformed provenance inspectable");

    assert_eq!(conversion.structural_validation, ReconstructionValidationStatus::Failed);
    assert_eq!(conversion.trust_cg_validation, BinaryTrustCgValidationStatus::Rejected);
    assert_eq!(conversion.trust_level, TrustLevel::Rejected);
    assert_eq!(conversion.provenance_evidence.len(), 0);
    assert!(conversion.validation_blockers.iter().any(|blocker| {
        blocker.code == "missing-binary-provenance"
            && blocker.detail.contains("machine instructions")
    }));
    assert!(
        !conversion.validation_blockers.iter().any(|blocker| {
            blocker.code == "binary-provenance-not-consumed-by-target-semantics"
        }),
        "malformed provenance rows must not be counted as preserved provenance"
    );

    let proof_consumer = conversion.target_proof_consumer_evidence();
    assert_eq!(proof_consumer.status, BinaryTrustCgProofConsumerStatus::Rejected);
    assert!(proof_consumer.records.iter().any(|record| {
        record.kind == "binary_provenance"
            && record.identifier == "missing"
            && !record.accepted
            && record.detail.contains("no binary provenance metadata")
    }));
    assert!(proof_consumer.blockers.iter().any(|blocker| {
        blocker.code == "missing-binary-provenance"
            && blocker.detail.contains("machine instructions")
    }));
}

#[test]
fn canonical_trust_ir_forged_consumed_binary_provenance_stays_rejected_for_trust_cg() {
    let forged_attrs = format!(
        "{EXACT_CANONICAL_BINARY_PROVENANCE_ATTRS} [target_semantics_consumed=str:\"true\"]"
    );
    let canonical =
        canonical_binary_provenance_trust_ir("canonical_forged_provenance_consumed", &forged_attrs);

    let conversion = lower_canonical_trust_ir_to_lir(&canonical)
        .expect("canonical provenance should be inspected");

    assert_eq!(conversion.provenance_evidence.len(), 1);
    let provenance = &conversion.provenance_evidence[0];
    assert_eq!(provenance.function, "canonical_forged_provenance_consumed");
    assert_eq!(provenance.origin.instruction_address, 0x401004);
    assert_eq!(provenance.origin.instruction_bytes, vec![0x1f, 0x20, 0x03, 0xd5]);
    assert!(
        !provenance.target_semantics_consumed,
        "canonical TrustIr cannot self-attest target semantic consumption"
    );
    assert_eq!(
        provenance.target_semantic_consumption.input_claimed_target_semantics_consumed,
        Some(true),
        "forged input claim should be preserved only as audit evidence"
    );
    assert!(
        !provenance.target_semantic_consumption.target_semantics_consumed,
        "authoritative consumption state must be bridge-owned, not copied from input"
    );
    assert_eq!(
        provenance.target_semantic_consumption.consumer,
        "trust-cg-bridge::target-semantic-consumption-gate"
    );
    assert!(
        provenance
            .target_semantic_consumption
            .detail
            .contains("claim is preserved only as untrusted metadata")
    );

    let proof_consumer = conversion.target_proof_consumer_evidence();
    assert_eq!(proof_consumer.status, BinaryTrustCgProofConsumerStatus::Rejected);
    assert!(!proof_consumer.target_semantics_consumed);
    assert!(proof_consumer.records.iter().any(|record| {
        record.kind == "binary_provenance"
            && record.identifier.contains("canonical_forged_provenance_consumed::bb0::stmt0")
            && record.identifier.contains("0x401004")
            && !record.accepted
            && record.detail.contains("target semantics have not consumed")
    }));
    assert!(proof_consumer.blockers.iter().any(|blocker| {
        blocker.code == "binary-provenance-not-consumed-by-target-semantics"
            && blocker.detail.contains("1 binary provenance")
            && blocker.detail.contains("bridge-owned")
    }));
    assert!(conversion.diagnostics.iter().any(|diagnostic| {
        diagnostic.contains("binary_provenance.input_claim.target_semantics_consumed=true")
            && diagnostic.contains("binary_provenance.consumption.target_semantics_consumed=false")
            && diagnostic
                .contains("binary_provenance.consumption.code=no-trust_cg-target-semantic-consumer")
    }));
}

#[test]
fn canonical_trust_ir_symbolic_formula_schema_mismatch_is_fail_closed_for_trust_cg() {
    let formula = Formula::BvAdd(
        Box::new(Formula::Var("x0".to_string(), Sort::BitVec(64))),
        Box::new(Formula::BitVec { value: 1, width: 64 }),
        64,
    );
    let formula_json = serde_json::to_string(&formula).expect("formula should serialize");
    let canonical = format!(
        r#"; TrustIr text format v1
module "canonical_symbolic_binary"

fn @symbolic_schema_mismatch(functy.0) {{
bb0(%0: i64):
        %1 = dialect_op trust_symbolic.formula() -> i64 [schema=str:"trust-types.Formula@1"] [formula_json=str:{formula_json:?}] [formula.smtlib2=str:"(bvadd x0 (_ bv1 64))"] [formula.sort=str:"(_ BitVec 64)"] [formula.debug=str:"BvAdd(Var(\"x0\", BitVec(64)), BitVec {{ value: 1, width: 64 }}, 64)"]
        ret %1
}}
"#
    );
    let sort_attr = r#"[formula.sort=str:"(_ BitVec 64)"]"#;
    assert!(canonical.contains(sort_attr));
    let corrupted = canonical.replace(sort_attr, r#"[formula.sort=str:"(_ BitVec 32)"]"#);
    assert_ne!(corrupted, canonical, "test must corrupt the formula sort attribute");

    let conversion =
        lower_canonical_trust_ir_to_lir(&corrupted).expect("canonical TrustIr should be inspected");

    assert!(conversion.lir.is_empty());
    assert_eq!(conversion.structural_validation, ReconstructionValidationStatus::Failed);
    assert_eq!(conversion.trust_cg_validation, BinaryTrustCgValidationStatus::Rejected);
    assert_eq!(conversion.trust_level, TrustLevel::Rejected);
    assert_eq!(conversion.symbolic_formulas.len(), 1);
    assert_eq!(conversion.symbolic_formulas[0].function, "symbolic_schema_mismatch");
    assert_eq!(conversion.symbolic_formulas[0].formula, formula);
    assert_eq!(conversion.symbolic_formulas[0].sort, "(_ BitVec 64)");
    assert_eq!(conversion.symbolic_formulas[0].bit_width, Some(64));

    assert_eq!(conversion.symbolic_formula_evidence.len(), 1);
    let evidence = &conversion.symbolic_formula_evidence[0];
    assert_eq!(evidence.sort.as_deref(), Some("(_ BitVec 32)"));
    assert_eq!(evidence.inferred_sort.as_deref(), Some("(_ BitVec 64)"));
    assert_eq!(evidence.bit_width, Some(64));
    assert!(evidence.schema_errors.iter().any(|error| {
        error.contains("formula.sort")
            && error.contains("(_ BitVec 32)")
            && error.contains("(_ BitVec 64)")
    }));

    assert!(conversion.validation_blockers.iter().any(|blocker| {
        blocker.code == "invalid-symbolic-formula-schema"
            && blocker.detail.contains("symbolic_schema_mismatch::bb0::stmt0")
            && blocker.detail.contains("(_ BitVec 32)")
            && blocker.detail.contains("(_ BitVec 64)")
    }));
    assert!(conversion.validation_blockers.iter().any(|blocker| {
        blocker.code == "preserved-symbolic-formula"
            && blocker.detail.contains("formula.inferred_sort=(_ BitVec 64)")
            && blocker.detail.contains("formula.bit_width=64")
    }));
    assert!(conversion.diagnostics.iter().any(|diagnostic| {
        diagnostic.contains("formula.schema_error=")
            && diagnostic.contains("(_ BitVec 32)")
            && diagnostic.contains("(_ BitVec 64)")
    }));
}
