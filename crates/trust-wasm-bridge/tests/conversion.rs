use trust_ir::inst::Inst;
use trust_ir_bridge::{
    SYMBOLIC_FORMULA_ATTR_JSON, SYMBOLIC_FORMULA_ATTR_SCHEMA, SYMBOLIC_FORMULA_ATTR_SMTLIB,
    SYMBOLIC_FORMULA_ATTR_SORT, SYMBOLIC_FORMULA_DIALECT, SYMBOLIC_FORMULA_OP, lower_to_trust_ir,
};
use trust_types::{
    BasicBlock, BinOp, BinaryOrigin, BlockId, ConstValue, Formula, LocalDecl, Operand, Place,
    ProofCertificateStatus, ReconstructionValidationEvidence, ReconstructionValidationStatus,
    ReplayStatus, Rvalue, Sort, SourceSpan, Statement, Terminator, TrustLevel, Ty,
    UnsupportedLedger, UnsupportedRecord, VerifiableBody, VerifiableFunction, infer_sort,
};
use trust_wasm_bridge::{
    WasmCheckedCertificateEvidence, WasmConversion, WasmProofConsumerStatus,
    WasmProofReplayEvidence, WasmProvenanceEvidence, WasmSymbolicFormula,
    WasmTargetSemanticConsumptionEvidence, WasmTargetValidationStatus,
    WasmUnsupportedLedgerEvidence, convert_canonical_trust_ir_to_wat, convert_function_to_wat,
};

fn constant_return_function(name: &str, value: i128, return_ty: Ty) -> VerifiableFunction {
    VerifiableFunction {
        name: name.to_string(),
        def_path: format!("binary::{name}"),
        span: SourceSpan::binary_address(0x1000),
        body: VerifiableBody {
            locals: vec![LocalDecl { index: 0, ty: return_ty.clone(), name: None }],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(value))),
                    span: SourceSpan::binary_address(0x1000),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 0,
            return_ty,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

fn unconsumed_wasm_semantics() -> WasmTargetSemanticConsumptionEvidence {
    WasmTargetSemanticConsumptionEvidence {
        consumer: "trust-wasm-bridge::target-semantic-consumption-gate".to_string(),
        target_semantics_consumed: false,
        input_claimed_target_semantics_consumed: None,
        code: "no-wasm-target-semantic-consumer".to_string(),
        detail: "unit test fixture has no bridge-owned Wasm target consumption".to_string(),
    }
}

fn replayed_trust_cg_consumption_for_wasm() -> WasmTargetSemanticConsumptionEvidence {
    WasmTargetSemanticConsumptionEvidence {
        consumer: "trust-cg-bridge::target-semantic-consumption-gate".to_string(),
        target_semantics_consumed: true,
        input_claimed_target_semantics_consumed: None,
        code: "bounded-empty-trust_cg-target-consumed".to_string(),
        detail: "forged replay of trust_cg target proof-consumer evidence".to_string(),
    }
}

fn eliminated_unsupported_ledger(function: &str, source: &str) -> WasmUnsupportedLedgerEvidence {
    WasmUnsupportedLedgerEvidence {
        function: function.to_string(),
        source: source.to_string(),
        block: None,
        statement_index: None,
        unsupported_records: 0,
        verification_unsupported: 0,
        unsupported_ledger_eliminated: true,
        target_semantic_consumption: unconsumed_wasm_semantics(),
        target_semantics_consumed: false,
    }
}

fn proof_grade_shaped_scalar_conversion(function: &str) -> WasmConversion {
    WasmConversion {
        wat: Some(format!(
            "(module\n  (func ${function} (result i32)\n    i32.const 1)\n  (export \"{function}\" (func ${function}))\n)\n"
        )),
        lifted_trust_ir_artifact_digest: None,
        bound_lifted_trust_ir_artifact_digest: None,
        validation: ReconstructionValidationStatus::Validated,
        wasm_validation: WasmTargetValidationStatus::InspectableRejected,
        trust_level: TrustLevel::ProofGrade,
        validation_blockers: vec![],
        symbolic_formulas: vec![],
        provenance_evidence: vec![],
        checked_certificate_evidence: vec![],
        proof_replay_evidence: vec![],
        unsupported_ledger_evidence: vec![],
        validation_records: vec![],
        unsupported: UnsupportedLedger::default(),
        diagnostics: vec![],
    }
}

const EXACT_SCALAR_CERTIFICATE_SHA: &str =
    "abababababababababababababababababababababababababababababababab";
const EXACT_SCALAR_REPLAY_SHA: &str =
    "cdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcd";
const EXACT_SCALAR_LIFTED_TRUST_IR_SHA: &str =
    "1212121212121212121212121212121212121212121212121212121212121212";

fn exact_non_empty_scalar_conversion(function: &str, trust_level: TrustLevel) -> WasmConversion {
    exact_non_empty_bool_scalar_conversion(function, trust_level, true)
}

fn exact_non_empty_bool_scalar_conversion(
    function: &str,
    trust_level: TrustLevel,
    value: bool,
) -> WasmConversion {
    let proof_source = format!("solver_dispatch:vc:{function}");
    let wat_const = if value { 1 } else { 0 };
    WasmConversion {
        wat: Some(format!(
            "(module\n  (func ${function} (result i32)\n    i32.const {wat_const})\n  (export \"{function}\" (func ${function}))\n)\n"
        )),
        lifted_trust_ir_artifact_digest: Some(EXACT_SCALAR_LIFTED_TRUST_IR_SHA.to_string()),
        bound_lifted_trust_ir_artifact_digest: Some(EXACT_SCALAR_LIFTED_TRUST_IR_SHA.to_string()),
        validation: ReconstructionValidationStatus::Validated,
        wasm_validation: WasmTargetValidationStatus::InspectableRejected,
        trust_level,
        validation_blockers: vec![],
        symbolic_formulas: vec![WasmSymbolicFormula {
            function: function.to_string(),
            block: 0,
            statement_index: 0,
            operand: "use".to_string(),
            formula: Formula::Bool(value),
            sort: "Bool".to_string(),
            bit_width: None,
        }],
        provenance_evidence: vec![WasmProvenanceEvidence {
            function: function.to_string(),
            source: proof_source.clone(),
            block: Some(0),
            statement_index: Some(0),
            origin: BinaryOrigin {
                binary_path: Some("fixture.bin".to_string()),
                function_entry: Some(0x1000),
                instruction_address: 0x1004,
                instruction_size: Some(4),
                encoding: Some(0xd503_201f),
                instruction_bytes: vec![0x1f, 0x20, 0x03, 0xd5],
                source: Some(SourceSpan::binary_address(0x1004)),
            },
            target_semantic_consumption: unconsumed_wasm_semantics(),
            target_semantics_consumed: false,
        }],
        checked_certificate_evidence: vec![WasmCheckedCertificateEvidence {
            function: function.to_string(),
            source: proof_source.clone(),
            block: None,
            statement_index: None,
            certificate: ProofCertificateStatus::Checked {
                checker: "trust-proof-cert-check".to_string(),
                format: "lrat".to_string(),
                sha256: Some(EXACT_SCALAR_CERTIFICATE_SHA.to_string()),
            },
            target_semantic_consumption: unconsumed_wasm_semantics(),
            target_semantics_consumed: false,
        }],
        proof_replay_evidence: vec![WasmProofReplayEvidence {
            function: function.to_string(),
            source: proof_source,
            block: None,
            statement_index: None,
            replay: ReplayStatus::Replayed,
            artifact_sha256: Some(EXACT_SCALAR_REPLAY_SHA.to_string()),
            exact_replay_checked: true,
            target_semantic_consumption: unconsumed_wasm_semantics(),
            target_semantics_consumed: false,
        }],
        unsupported_ledger_evidence: vec![eliminated_unsupported_ledger(
            function,
            "decompiled.unsupported_ledger",
        )],
        validation_records: vec![],
        unsupported: UnsupportedLedger::default(),
        diagnostics: vec![],
    }
}

const EXACT_CANONICAL_BINARY_PROVENANCE_ATTRS: &str = r#"[schema=str:"trust-types.BinaryProvenance@1"] [source=str:"unit-test"] [binary_path=str:"fixture.bin"] [function_entry=str:"0x401000"] [instruction_address=str:"0x401004"] [instruction_size=str:"4"] [encoding=str:"0xd503201f"] [instruction_bytes=str:"1f2003d5"]"#;
const EXACT_CANONICAL_UNSUPPORTED_LEDGER_ATTRS: &str = r#"[schema=str:"trust-types.UnsupportedLedger@1"] [source=str:"bounded-empty-unsupported-ledger"] [unsupported_records=str:"0"] [verification_unsupported=str:"0"] [target_semantics_consumed=str:"false"]"#;

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

fn canonical_bounded_empty_consumer_trust_ir(
    function: &str,
    formula: &Formula,
    provenance_attrs: &str,
    certificate_attrs: &str,
    replay_attrs: &str,
    unsupported_ledger_attrs: &str,
) -> String {
    let formula_json = serde_json::to_string(formula).expect("formula should serialize");
    let formula_smtlib = formula.to_smtlib();
    let formula_sort = infer_sort(formula).to_smtlib();
    format!(
        r#"; TrustIr text format v1
module "{function}"

fn @{function}(functy.0) {{
bb0(%0: bool):
        %1 = dialect_op trust_symbolic.formula() -> bool [schema=str:"trust-types.Formula@1"] [formula_json=str:{formula_json:?}] [formula.smtlib2=str:{formula_smtlib:?}] [formula.sort=str:{formula_sort:?}]
        %2 = dialect_op trust_binary.provenance() -> i32 {provenance_attrs}
        %3 = dialect_op trust_proof.checked_certificate() -> i32 {certificate_attrs}
        %4 = dialect_op trust_proof.proof_replay() -> i32 {replay_attrs}
        %5 = dialect_op trust_proof.unsupported_ledger() -> i32 {unsupported_ledger_attrs}
        ret %0
}}
"#
    )
}

#[test]
fn accepts_constant_integer_return_as_wat_without_proof_grade() {
    let function = constant_return_function("answer", 42, Ty::i32());

    let conversion = convert_function_to_wat(&function);

    assert!(!conversion.is_accepted());
    assert!(conversion.is_inspectable());
    assert_eq!(conversion.validation, ReconstructionValidationStatus::Validated);
    assert_eq!(conversion.wasm_validation, WasmTargetValidationStatus::InspectableRejected);
    assert_eq!(conversion.trust_level, TrustLevel::Rejected);
    assert_ne!(conversion.trust_level, TrustLevel::ProofGrade);
    for code in [
        "missing-target-semantic-validation",
        "missing-refinement-metadata",
        "missing-checked-proof-certificate",
        "missing-proof-replay-metadata",
        "missing-binary-proof-obligation",
    ] {
        assert!(
            conversion.validation_blockers.iter().any(|blocker| blocker.code == code),
            "missing proof-grade blocker `{code}`"
        );
    }
    let proof_consumer = conversion.target_proof_consumer_evidence();
    assert_eq!(proof_consumer.target, "wasm");
    assert_eq!(proof_consumer.status, WasmProofConsumerStatus::Rejected);
    assert!(proof_consumer.is_rejected());
    assert!(!proof_consumer.target_semantics_consumed);
    assert_eq!(proof_consumer.binding.target, "wasm");
    assert_eq!(proof_consumer.binding.status, WasmProofConsumerStatus::Rejected);
    assert!(proof_consumer.binding.target_output.contains("wat:emitted"));
    assert!(proof_consumer.binding.target_output.contains("answer"));
    assert!(!proof_consumer.binding.target_semantics_consumed);
    assert!(proof_consumer.binding.inputs.iter().any(|input| {
        input.kind == "binary_provenance"
            && input.identifier.contains("answer::bb0::stmt0")
            && input.canonical_source == "trust_binary.provenance"
            && input.target_output == proof_consumer.binding.target_output
            && !input.consumed_by_target_semantics
    }));
    assert!(proof_consumer.binding.inputs.iter().any(|input| {
        input.kind == "checked_certificate"
            && input.identifier == "missing"
            && input.canonical_source == "checked-certificate"
            && input.target_output == proof_consumer.binding.target_output
            && !input.consumed_by_target_semantics
    }));
    assert!(proof_consumer.records.iter().any(|record| {
        record.kind == "target_semantics" && record.identifier == "wasm32" && !record.accepted
    }));
    assert!(proof_consumer.records.iter().any(|record| {
        record.kind == "checked_certificate" && record.identifier == "missing" && !record.accepted
    }));
    assert!(proof_consumer.records.iter().any(|record| {
        record.kind == "proof_replay" && record.identifier == "missing" && !record.accepted
    }));
    assert!(proof_consumer.proof_grade_blockers.iter().any(|blocker| {
        blocker.code == "missing-refinement-metadata"
            && blocker.detail.contains("bidirectional refinement metadata")
    }));
    assert!(proof_consumer.binding.inputs.iter().any(|input| {
        input.kind == "target_refinement"
            && input.identifier == "missing"
            && !input.consumed_by_target_semantics
    }));
    assert_eq!(conversion.provenance_evidence.len(), 2);
    assert!(conversion.provenance_evidence.iter().any(|entry| {
        entry.source == "lifted.function_span" && entry.origin.instruction_address == 0x1000
    }));
    assert!(conversion.provenance_evidence.iter().any(|entry| {
        entry.source == "lifted.bb0.stmt0"
            && entry.block == Some(0)
            && entry.statement_index == Some(0)
            && entry.origin.instruction_address == 0x1000
            && !entry.target_semantics_consumed
    }));
    assert!(proof_consumer.records.iter().any(|record| {
        record.kind == "binary_provenance"
            && record.identifier.contains("answer::bb0::stmt0")
            && record.identifier.contains("0x1000")
            && !record.accepted
            && record.detail.contains("target semantics have not consumed")
    }));
    for code in [
        "target-semantics-not-consumed",
        "binary-provenance-not-consumed-by-target-semantics",
        "missing-checked-proof-certificate",
        "missing-proof-replay-metadata",
    ] {
        assert!(
            proof_consumer.blockers.iter().any(|blocker| blocker.code == code),
            "missing proof-consumer blocker `{code}`"
        );
    }
    assert!(conversion.unsupported.is_empty());
    let wat = conversion.wat.expect("accepted WAT");
    assert!(wat.contains("(module"));
    assert!(wat.contains("(func $answer (result i32)"));
    assert!(wat.contains("i32.const 42"));
    assert!(wat.contains("(export \"answer\" (func $answer))"));
    assert_eq!(conversion.validation_records.len(), 1);
    assert_eq!(conversion.validation_records[0].trust_level, TrustLevel::Rejected);
    assert!(
        conversion.validation_records[0]
            .evidence
            .contains(&ReconstructionValidationEvidence::NoCheckedProofCertificate)
    );
}

#[test]
fn non_empty_i32_const_one_wasm_stays_rejected_without_scalar_formula_and_proof_metadata() {
    let function = constant_return_function("wasm_one", 1, Ty::i32());

    let conversion = convert_function_to_wat(&function);

    assert!(conversion.is_inspectable());
    assert_eq!(conversion.wasm_validation, WasmTargetValidationStatus::InspectableRejected);
    let wat = conversion.wat.as_deref().expect("WAT should be emitted for i32 const one");
    assert!(wat.contains("(func $wasm_one (result i32)"));
    assert!(wat.contains("i32.const 1"));
    assert!(conversion.symbolic_formulas.is_empty());
    assert!(conversion.checked_certificate_evidence.is_empty());
    assert!(conversion.proof_replay_evidence.is_empty());
    assert_eq!(conversion.trust_level, TrustLevel::Rejected);

    let proof_consumer = conversion.target_proof_consumer_evidence();
    assert_eq!(proof_consumer.status, WasmProofConsumerStatus::Rejected);
    assert!(!proof_consumer.target_semantics_consumed);
    assert!(proof_consumer.binding.target_output.contains("wat:emitted"));
    assert!(proof_consumer.binding.target_output.contains("wasm_one"));

    for code in [
        "target-semantics-not-consumed",
        "non-empty-scalar-wasm-target-consumer-unavailable",
        "missing-scalar-formula-target-op-binding",
        "non-empty-scalar-checked-certificate-identity-missing",
        "non-empty-scalar-replay-artifact-identity-missing",
        "non-empty-scalar-proof-metadata-identity-mismatch",
        "non-empty-scalar-binary-provenance-missing",
        "binary-provenance-not-consumed-by-target-semantics",
        "missing-checked-proof-certificate",
        "missing-proof-replay-metadata",
    ] {
        assert!(
            proof_consumer.blockers.iter().any(|blocker| blocker.code == code),
            "missing proof-consumer blocker `{code}`"
        );
    }
    assert!(proof_consumer.blockers.iter().any(|blocker| {
        blocker.code == "missing-scalar-formula-target-op-binding"
            && blocker.detail.contains("i32.const 1")
            && blocker.detail.contains("no exactly matching canonical Bool(true)")
    }));
}

#[test]
fn non_empty_i32_const_zero_wasm_stays_rejected_without_scalar_formula_and_proof_metadata() {
    let function = constant_return_function("wasm_zero", 0, Ty::i32());

    let conversion = convert_function_to_wat(&function);

    assert!(conversion.is_inspectable());
    let wat = conversion.wat.as_deref().expect("WAT should be emitted for i32 const zero");
    assert!(wat.contains("(func $wasm_zero (result i32)"));
    assert!(wat.contains("i32.const 0"));
    assert_eq!(conversion.trust_level, TrustLevel::Rejected);

    let proof_consumer = conversion.target_proof_consumer_evidence();
    assert_eq!(proof_consumer.status, WasmProofConsumerStatus::Rejected);
    assert!(!proof_consumer.target_semantics_consumed);
    assert!(proof_consumer.blockers.iter().any(|blocker| {
        blocker.code == "missing-scalar-formula-target-op-binding"
            && blocker.detail.contains("i32.const 0")
            && blocker.detail.contains("Bool(false)")
    }));
    assert!(
        proof_consumer
            .blockers
            .iter()
            .any(|blocker| { blocker.code == "non-empty-scalar-wasm-target-consumer-unavailable" })
    );
    assert!(
        proof_consumer
            .blockers
            .iter()
            .any(|blocker| { blocker.code == "missing-checked-proof-certificate" })
    );
    assert!(!conversion.is_accepted());
}

#[test]
fn emitted_scalar_wat_with_formula_still_requires_certificate_and_exact_replay_identity() {
    let conversion = WasmConversion {
        wat: Some(
            "(module\n  (func $guard (result i32)\n    i32.const 1)\n  (export \"guard\" (func $guard))\n)\n"
                .to_string(),
        ),
        lifted_trust_ir_artifact_digest: None,
        bound_lifted_trust_ir_artifact_digest: None,
        validation: ReconstructionValidationStatus::Validated,
        wasm_validation: WasmTargetValidationStatus::InspectableRejected,
        trust_level: TrustLevel::Rejected,
        validation_blockers: vec![],
        symbolic_formulas: vec![WasmSymbolicFormula {
            function: "guard".to_string(),
            block: 0,
            statement_index: 0,
            operand: "use".to_string(),
            formula: Formula::Bool(true),
            sort: "Bool".to_string(),
            bit_width: None,
        }],
        provenance_evidence: vec![WasmProvenanceEvidence {
            function: "guard".to_string(),
            source: "lifted.bb0.stmt0".to_string(),
            block: Some(0),
            statement_index: Some(0),
            origin: BinaryOrigin {
                binary_path: Some("fixture.bin".to_string()),
                function_entry: Some(0x1000),
                instruction_address: 0x1004,
                instruction_size: Some(4),
                encoding: Some(0xd503_201f),
                instruction_bytes: vec![0x1f, 0x20, 0x03, 0xd5],
                source: Some(SourceSpan::binary_address(0x1004)),
            },
            target_semantic_consumption: unconsumed_wasm_semantics(),
            target_semantics_consumed: false,
        }],
        checked_certificate_evidence: vec![],
        proof_replay_evidence: vec![],
        unsupported_ledger_evidence: vec![],
        validation_records: vec![],
        unsupported: UnsupportedLedger::default(),
        diagnostics: vec![],
    };

    let proof_consumer = conversion.target_proof_consumer_evidence();

    assert!(!conversion.is_accepted());
    assert_ne!(conversion.trust_level, TrustLevel::ProofGrade);
    assert_eq!(proof_consumer.status, WasmProofConsumerStatus::Rejected);
    assert!(!proof_consumer.target_semantics_consumed);
    assert!(proof_consumer.binding.target_output.contains("wat:emitted"));
    assert!(proof_consumer.records.iter().any(|record| {
        record.kind == "symbolic_formula"
            && record.identifier == "guard::bb0::stmt0::use"
            && !record.accepted
    }));

    for code in [
        "target-semantics-not-consumed",
        "non-empty-scalar-wasm-target-consumer-unavailable",
        "non-empty-scalar-checked-certificate-identity-missing",
        "non-empty-scalar-replay-artifact-identity-missing",
        "non-empty-scalar-proof-metadata-identity-mismatch",
        "missing-checked-proof-certificate",
        "missing-proof-replay-metadata",
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
            .any(|blocker| blocker.code == "missing-scalar-formula-target-op-binding"),
        "the fixture has the Bool(true) formula and i32.const 1 target shape; cert/replay gates must still keep it rejected"
    );
    assert!(
        !proof_consumer
            .blockers
            .iter()
            .any(|blocker| blocker.code == "non-empty-scalar-binary-provenance-missing"),
        "the fixture has exact no-op provenance; cert/replay gates must still keep it rejected"
    );
}

#[test]
fn emitted_scalar_wat_with_complete_evidence_is_consumed_by_non_empty_target_consumer() {
    let conversion = exact_non_empty_scalar_conversion("guard", TrustLevel::Rejected);

    let proof_consumer = conversion.target_proof_consumer_evidence();

    assert!(!conversion.is_accepted(), "target consumption alone must not promote trust level");
    assert_eq!(proof_consumer.status, WasmProofConsumerStatus::Accepted);
    assert!(proof_consumer.target_semantics_consumed);
    assert!(proof_consumer.blockers.is_empty());
    assert!(proof_consumer.proof_grade_blockers.is_empty());
    assert_eq!(proof_consumer.refinement_metadata_evidence.len(), 1);
    assert_eq!(
        proof_consumer.refinement_metadata_evidence[0].code,
        "non-empty-scalar-wasm-refinement-consumed"
    );
    assert_eq!(proof_consumer.refinement_metadata_evidence[0].target_operation, "i32.const 1");
    assert_eq!(proof_consumer.binding.status, WasmProofConsumerStatus::Accepted);
    assert!(proof_consumer.binding.target_semantics_consumed);
    assert!(proof_consumer.binding.target_output.contains("wat:emitted"));
    assert!(proof_consumer.records.iter().all(|record| record.accepted));
    assert!(proof_consumer.binding.inputs.iter().all(|input| {
        input.target_output == proof_consumer.binding.target_output
            && input.consumed_by_target_semantics
    }));
    assert!(proof_consumer.records.iter().any(|record| {
        record.kind == "target_semantics"
            && record.detail.contains("non-empty scalar slice")
            && record.detail.contains("i32.const 1")
            && record.detail.contains("proof identity guard:vc:guard")
    }));
    assert!(proof_consumer.records.iter().any(|record| {
        record.kind == "target_refinement"
            && record.identifier.contains("non-empty-scalar-bool")
            && record.identifier.contains("i32.const 1")
            && record.accepted
    }));
    assert!(proof_consumer.binding.inputs.iter().any(|input| {
        input.kind == "target_refinement"
            && input.identifier.contains("non-empty-scalar-bool")
            && input.consumed_by_target_semantics
    }));
    assert!(proof_consumer.records.iter().any(|record| {
        record.kind == "checked_certificate"
            && record.identifier.contains(EXACT_SCALAR_CERTIFICATE_SHA)
            && record.accepted
    }));
    assert!(proof_consumer.records.iter().any(|record| {
        record.kind == "proof_replay"
            && record.identifier.contains(EXACT_SCALAR_REPLAY_SHA)
            && record.accepted
    }));
    assert!(proof_consumer.binding.inputs.iter().any(|input| {
        input.kind == "checked_certificate"
            && input.identifier.contains(EXACT_SCALAR_CERTIFICATE_SHA)
            && input.consumed_by_target_semantics
    }));
    assert!(proof_consumer.binding.inputs.iter().any(|input| {
        input.kind == "proof_replay"
            && input.identifier.contains(EXACT_SCALAR_REPLAY_SHA)
            && input.consumed_by_target_semantics
    }));
    assert!(proof_consumer.records.iter().any(|record| {
        record.kind == "unsupported_ledger"
            && record.identifier.contains("eliminated=true")
            && record.accepted
    }));
    assert!(proof_consumer.binding.inputs.iter().any(|input| {
        input.kind == "unsupported_ledger"
            && input.canonical_source == "trust_proof.unsupported_ledger"
            && input.consumed_by_target_semantics
    }));
    for absent in [
        "target-semantics-not-consumed",
        "non-empty-scalar-wasm-target-consumer-unavailable",
        "missing-scalar-formula-target-op-binding",
        "non-empty-scalar-checked-certificate-identity-missing",
        "non-empty-scalar-replay-artifact-identity-missing",
        "non-empty-scalar-proof-metadata-identity-mismatch",
        "non-empty-scalar-binary-provenance-missing",
        "non-empty-scalar-unsupported-ledger-evidence-missing",
        "non-empty-scalar-unsupported-ledger-not-eliminated",
        "missing-checked-proof-certificate",
        "missing-proof-replay-metadata",
        "missing-unsupported-ledger-evidence",
        "checked-proof-certificate-incomplete",
        "proof-replay-incomplete",
        "unsupported-ledger-not-eliminated",
    ] {
        assert!(
            !proof_consumer.blockers.iter().any(|blocker| blocker.code == absent),
            "complete exact evidence should not leave proof-consumer blocker `{absent}`"
        );
    }
}

#[test]
fn non_empty_scalar_wasm_requires_unsupported_ledger_elimination_evidence() {
    let mut conversion =
        exact_non_empty_scalar_conversion("guard_missing_ledger", TrustLevel::ProofGrade);
    conversion.unsupported_ledger_evidence.clear();

    let proof_consumer = conversion.target_proof_consumer_evidence();

    assert_eq!(proof_consumer.status, WasmProofConsumerStatus::Rejected);
    assert!(!proof_consumer.target_semantics_consumed);
    assert!(proof_consumer.blockers.iter().any(|blocker| {
        blocker.code == "non-empty-scalar-unsupported-ledger-evidence-missing"
            && blocker.detail.contains("unsupported-ledger elimination evidence")
    }));
    assert!(proof_consumer.blockers.iter().any(|blocker| {
        blocker.code == "missing-unsupported-ledger-evidence"
            && blocker.detail.contains("no unsupported-ledger elimination evidence")
    }));
    assert!(proof_consumer.records.iter().any(|record| {
        record.kind == "unsupported_ledger" && record.identifier == "missing" && !record.accepted
    }));
    assert!(!conversion.is_accepted());
}

#[test]
fn non_empty_scalar_wasm_rejects_nonempty_unsupported_ledger_evidence() {
    let mut conversion =
        exact_non_empty_scalar_conversion("guard_nonempty_ledger", TrustLevel::ProofGrade);
    conversion.unsupported_ledger_evidence[0].unsupported_records = 1;
    conversion.unsupported_ledger_evidence[0].verification_unsupported = 1;
    conversion.unsupported_ledger_evidence[0].unsupported_ledger_eliminated = false;

    let proof_consumer = conversion.target_proof_consumer_evidence();

    assert_eq!(proof_consumer.status, WasmProofConsumerStatus::Rejected);
    assert!(!proof_consumer.target_semantics_consumed);
    assert!(proof_consumer.blockers.iter().any(|blocker| {
        blocker.code == "non-empty-scalar-unsupported-ledger-not-eliminated"
            && blocker.detail.contains("zero unsupported verification counters")
    }));
    assert!(proof_consumer.blockers.iter().any(|blocker| {
        blocker.code == "unsupported-ledger-not-eliminated"
            && blocker.detail.contains("non-empty unsupported records")
    }));
    assert!(proof_consumer.records.iter().any(|record| {
        record.kind == "unsupported_ledger"
            && record.identifier.contains("eliminated=false")
            && !record.accepted
    }));
    assert!(!conversion.is_accepted());
}

#[test]
fn proof_grade_non_empty_scalar_with_exact_binding_is_accepted() {
    let conversion = exact_non_empty_scalar_conversion("guard_grade", TrustLevel::ProofGrade);

    let proof_consumer = conversion.target_proof_consumer_evidence();

    assert!(conversion.validation_blockers.is_empty());
    assert!(conversion.unsupported.is_empty());
    assert_eq!(proof_consumer.status, WasmProofConsumerStatus::Accepted);
    assert!(proof_consumer.target_semantics_consumed);
    assert!(conversion.is_accepted());
}

#[test]
fn proof_grade_bool_false_scalar_with_exact_binding_is_accepted() {
    let conversion =
        exact_non_empty_bool_scalar_conversion("guard_false_grade", TrustLevel::ProofGrade, false);

    let proof_consumer = conversion.target_proof_consumer_evidence();

    assert!(conversion.validation_blockers.is_empty());
    assert!(conversion.unsupported.is_empty());
    assert_eq!(proof_consumer.status, WasmProofConsumerStatus::Accepted);
    assert!(proof_consumer.target_semantics_consumed);
    assert!(proof_consumer.records.iter().all(|record| record.accepted));
    assert!(proof_consumer.records.iter().any(|record| {
        record.kind == "target_semantics"
            && record.detail.contains("i32.const 0")
            && record.detail.contains("guard_false_grade::bb0::stmt0::use=false")
    }));
    assert!(conversion.is_accepted());
}

#[test]
fn bool_false_scalar_target_rejects_mismatched_formula_evidence() {
    let mut conversion = exact_non_empty_bool_scalar_conversion(
        "guard_false_mismatch",
        TrustLevel::ProofGrade,
        false,
    );
    conversion.symbolic_formulas[0].formula = Formula::Bool(true);

    let proof_consumer = conversion.target_proof_consumer_evidence();

    assert_eq!(proof_consumer.status, WasmProofConsumerStatus::Rejected);
    assert!(!proof_consumer.target_semantics_consumed);
    assert!(proof_consumer.blockers.iter().any(|blocker| {
        blocker.code == "missing-scalar-formula-target-op-binding"
            && blocker.detail.contains("i32.const 0")
            && blocker.detail.contains("Bool(false)")
    }));
    assert!(proof_consumer.records.iter().any(|record| {
        record.kind == "symbolic_formula"
            && record.identifier == "guard_false_mismatch::bb0::stmt0::use"
            && !record.accepted
    }));
    assert!(!conversion.is_accepted());
}

#[test]
fn exact_non_empty_scalar_consumption_still_requires_empty_unsupported_ledger_for_acceptance() {
    let mut conversion =
        exact_non_empty_scalar_conversion("guard_unsupported", TrustLevel::ProofGrade);
    conversion.unsupported = UnsupportedLedger {
        records: vec![UnsupportedRecord {
            stage: "trust-wasm-bridge".to_string(),
            architecture: Some("wasm32".to_string()),
            origin: None,
            opcode: Some("trust_symbolic.formula".to_string()),
            operand: Some("guard_unsupported::bb0::stmt0".to_string()),
            feature: "synthetic unsupported evidence must block proof-grade acceptance".to_string(),
        }],
    };

    let proof_consumer = conversion.target_proof_consumer_evidence();

    assert_eq!(proof_consumer.status, WasmProofConsumerStatus::Rejected);
    assert!(proof_consumer.target_semantics_consumed);
    assert!(proof_consumer.blockers.iter().any(|blocker| {
        blocker.code == "unsupported-ledger-not-empty"
            && blocker.detail.contains("1 unsupported ledger")
    }));
    assert!(!conversion.is_accepted());
}

#[test]
fn proof_grade_shape_without_target_consumed_evidence_is_rejected() {
    let conversion = proof_grade_shaped_scalar_conversion("forged_grade");

    assert_eq!(conversion.trust_level, TrustLevel::ProofGrade);
    assert!(conversion.validation_blockers.is_empty());
    assert!(conversion.unsupported.is_empty());
    assert!(
        !conversion.is_accepted(),
        "headline proof-grade fields are insufficient without bridge-owned target consumption"
    );

    let proof_consumer = conversion.target_proof_consumer_evidence();
    assert_eq!(proof_consumer.status, WasmProofConsumerStatus::Rejected);
    assert!(!proof_consumer.target_semantics_consumed);
    for code in [
        "target-semantics-not-consumed",
        "missing-binary-provenance",
        "missing-checked-proof-certificate",
        "missing-proof-replay-metadata",
    ] {
        assert!(
            proof_consumer.blockers.iter().any(|blocker| blocker.code == code),
            "missing proof-consumer blocker `{code}`"
        );
    }
}

#[test]
fn unsupported_ledger_blocks_proof_grade_shape() {
    let mut conversion = proof_grade_shaped_scalar_conversion("unsupported_grade");
    conversion.unsupported = UnsupportedLedger {
        records: vec![UnsupportedRecord {
            stage: "trust-wasm-bridge".to_string(),
            architecture: Some("wasm32".to_string()),
            origin: None,
            opcode: Some("trust_symbolic.formula".to_string()),
            operand: Some("unsupported_grade::bb0::stmt0".to_string()),
            feature: "symbolic formula requires proof-grade Wasm semantics: fixture".to_string(),
        }],
    };

    assert!(
        !conversion.is_accepted(),
        "unsupported ledger entries must block even proof-grade-shaped conversions"
    );
    let proof_consumer = conversion.target_proof_consumer_evidence();
    assert_eq!(proof_consumer.status, WasmProofConsumerStatus::Rejected);
    assert!(proof_consumer.blockers.iter().any(|blocker| {
        blocker.code == "unsupported-ledger-not-empty"
            && blocker.detail.contains("1 unsupported ledger")
            && blocker.detail.contains("symbolic formula requires proof-grade Wasm semantics")
    }));
    assert!(proof_consumer.binding.blockers.iter().any(|blocker| {
        blocker.code == "unsupported-ledger-not-empty"
            && blocker
                .detail
                .contains("proof-grade acceptance requires unsupported-ledger elimination")
    }));
}

#[test]
fn accepts_unit_return_as_no_result_wat_without_proof_grade() {
    let function = VerifiableFunction {
        name: "ret_only".to_string(),
        def_path: "binary::ret_only".to_string(),
        span: SourceSpan::binary_address(0x1000),
        body: VerifiableBody {
            locals: vec![LocalDecl { index: 0, ty: Ty::Unit, name: None }],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(1),
                    rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(0x1004, 64))),
                    span: SourceSpan::binary_address(0x1000),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 0,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let conversion = convert_function_to_wat(&function);

    assert!(!conversion.is_accepted());
    assert!(conversion.is_inspectable());
    assert_eq!(conversion.validation, ReconstructionValidationStatus::Validated);
    assert_eq!(conversion.trust_level, TrustLevel::Rejected);
    assert!(conversion.unsupported.is_empty());
    let wat = conversion.wat.expect("accepted WAT");
    assert!(wat.contains("(func $ret_only)"));
    assert!(!wat.contains("(result"));
    assert!(wat.contains("(export \"ret_only\" (func $ret_only))"));
}

#[test]
fn accepts_simple_copy_of_integer_constant() {
    let mut function = constant_return_function("copy_const", 0, Ty::i64());
    function.body.locals.push(LocalDecl { index: 1, ty: Ty::i64(), name: None });
    function.body.blocks[0].stmts = vec![
        Statement::Assign {
            place: Place::local(1),
            rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(-7))),
            span: SourceSpan::binary_address(0x1000),
        },
        Statement::Assign {
            place: Place::local(0),
            rvalue: Rvalue::Use(Operand::Copy(Place::local(1))),
            span: SourceSpan::binary_address(0x1001),
        },
    ];

    let conversion = convert_function_to_wat(&function);

    assert!(!conversion.is_accepted());
    assert!(conversion.is_inspectable());
    assert!(conversion.wat.expect("accepted WAT").contains("i64.const -7"));
}

#[test]
fn accepts_simple_copy_of_integer_parameter() {
    let mut function = constant_return_function("identity", 0, Ty::i32());
    function.body.locals.push(LocalDecl { index: 1, ty: Ty::i32(), name: Some("x".into()) });
    function.body.arg_count = 1;
    function.body.blocks[0].stmts = vec![Statement::Assign {
        place: Place::local(0),
        rvalue: Rvalue::Use(Operand::Copy(Place::local(1))),
        span: SourceSpan::binary_address(0x1000),
    }];

    let conversion = convert_function_to_wat(&function);

    assert!(!conversion.is_accepted());
    assert!(conversion.is_inspectable());
    let wat = conversion.wat.expect("accepted WAT");
    assert!(wat.contains("(func $identity (param $p1 i32) (result i32)"));
    assert!(wat.contains("local.get $p1"));
    assert!(!wat.contains("ProofGrade"));
}

#[test]
fn accepts_parameter_add_sub_integer_constants() {
    let mut function = constant_return_function("adjust", 0, Ty::i64());
    function.body.locals.extend([
        LocalDecl { index: 1, ty: Ty::i64(), name: Some("x".into()) },
        LocalDecl { index: 2, ty: Ty::i64(), name: None },
    ]);
    function.body.arg_count = 1;
    function.body.blocks[0].stmts = vec![
        Statement::Assign {
            place: Place::local(2),
            rvalue: Rvalue::BinaryOp(
                BinOp::Add,
                Operand::Copy(Place::local(1)),
                Operand::Constant(ConstValue::Int(5)),
            ),
            span: SourceSpan::binary_address(0x1000),
        },
        Statement::Assign {
            place: Place::local(0),
            rvalue: Rvalue::BinaryOp(
                BinOp::Sub,
                Operand::Copy(Place::local(2)),
                Operand::Constant(ConstValue::Int(2)),
            ),
            span: SourceSpan::binary_address(0x1001),
        },
    ];

    let conversion = convert_function_to_wat(&function);

    assert!(!conversion.is_accepted());
    assert!(conversion.is_inspectable());
    let wat = conversion.wat.expect("accepted WAT");
    assert!(wat.contains("(func $adjust (param $p1 i64) (result i64)"));
    assert!(wat.contains("local.get $p1\n    i64.const 5\n    i64.add"));
    assert!(wat.contains("i64.const 2\n    i64.sub"));
    assert_eq!(conversion.trust_level, TrustLevel::Rejected);
}

#[test]
fn rejects_unsupported_integer_binary_op_fail_closed() {
    let mut function = constant_return_function("multiply", 0, Ty::i32());
    function.body.locals.push(LocalDecl { index: 1, ty: Ty::i32(), name: Some("x".into()) });
    function.body.arg_count = 1;
    function.body.blocks[0].stmts = vec![Statement::Assign {
        place: Place::local(0),
        rvalue: Rvalue::BinaryOp(
            BinOp::Mul,
            Operand::Copy(Place::local(1)),
            Operand::Constant(ConstValue::Int(3)),
        ),
        span: SourceSpan::binary_address(0x1000),
    }];

    let conversion = convert_function_to_wat(&function);

    assert!(conversion.wat.is_none());
    assert_eq!(conversion.validation, ReconstructionValidationStatus::Failed);
    assert_eq!(conversion.wasm_validation, WasmTargetValidationStatus::Rejected);
    assert_eq!(conversion.trust_level, TrustLevel::Rejected);
    assert!(
        conversion
            .validation_blockers
            .iter()
            .any(|blocker| blocker.code == "unsupported-wasm-subset")
    );
    assert!(conversion.validation_blockers.iter().any(|blocker| {
        blocker.code == "missing-target-semantic-validation"
            && blocker.detail.contains("Wasm target semantics")
    }));
    assert!(conversion.unsupported.records[0].feature.contains("unsupported statement"));
}

#[test]
fn rejects_parameter_to_parameter_add_fail_closed() {
    let mut function = constant_return_function("add_params", 0, Ty::i32());
    function.body.locals.extend([
        LocalDecl { index: 1, ty: Ty::i32(), name: Some("a".into()) },
        LocalDecl { index: 2, ty: Ty::i32(), name: Some("b".into()) },
    ]);
    function.body.arg_count = 2;
    function.body.blocks[0].stmts = vec![Statement::Assign {
        place: Place::local(0),
        rvalue: Rvalue::BinaryOp(
            BinOp::Add,
            Operand::Copy(Place::local(1)),
            Operand::Copy(Place::local(2)),
        ),
        span: SourceSpan::binary_address(0x1000),
    }];

    let conversion = convert_function_to_wat(&function);

    assert!(conversion.wat.is_none());
    assert_eq!(conversion.validation, ReconstructionValidationStatus::Failed);
    assert_eq!(conversion.wasm_validation, WasmTargetValidationStatus::Rejected);
    assert_eq!(conversion.trust_level, TrustLevel::Rejected);
    assert!(
        conversion.unsupported.records[0]
            .feature
            .contains("requires at least one constant operand")
    );
}

#[test]
fn rejects_unsupported_control_flow_with_ledger() {
    let mut function = constant_return_function("branchy", 1, Ty::i32());
    function.body.blocks.push(BasicBlock {
        id: BlockId(1),
        stmts: vec![],
        terminator: Terminator::Return,
    });

    let conversion = convert_function_to_wat(&function);

    assert!(conversion.wat.is_none());
    assert_eq!(conversion.validation, ReconstructionValidationStatus::Failed);
    assert_eq!(conversion.wasm_validation, WasmTargetValidationStatus::Rejected);
    assert_eq!(conversion.trust_level, TrustLevel::Rejected);
    assert_ne!(conversion.trust_level, TrustLevel::ProofGrade);
    assert_eq!(conversion.unsupported.records.len(), 1);
    assert_eq!(conversion.unsupported.records[0].stage, "trust-wasm-bridge");
    assert!(conversion.unsupported.records[0].feature.contains("unsupported control flow"));
    assert_eq!(conversion.validation_records.len(), 1);
    assert_eq!(conversion.validation_records[0].trust_level, TrustLevel::Rejected);
}

#[test]
fn rejects_non_integer_return_without_proof_grade() {
    let function = constant_return_function("floaty", 1, Ty::f32_ty());

    let conversion = convert_function_to_wat(&function);

    assert!(conversion.wat.is_none());
    assert_eq!(conversion.validation, ReconstructionValidationStatus::Failed);
    assert_eq!(conversion.wasm_validation, WasmTargetValidationStatus::Rejected);
    assert_eq!(conversion.trust_level, TrustLevel::Rejected);
    assert_ne!(conversion.trust_level, TrustLevel::ProofGrade);
    assert!(conversion.unsupported.records[0].feature.contains("unsupported return type"));
}

#[test]
fn preserves_symbolic_formula_metadata_on_rejected_wasm_conversion() {
    let formula = Formula::Var("x0".to_string(), Sort::BitVec(32));
    let mut function = constant_return_function("symbolic", 0, Ty::i32());
    function.body.blocks[0].stmts[0] = Statement::Assign {
        place: Place::local(0),
        rvalue: Rvalue::Use(Operand::Symbolic(formula.clone())),
        span: SourceSpan::binary_address(0x1000),
    };

    let conversion = convert_function_to_wat(&function);

    assert!(conversion.wat.is_none());
    assert!(!conversion.is_inspectable());
    assert_eq!(conversion.wasm_validation, WasmTargetValidationStatus::Rejected);
    assert_eq!(conversion.trust_level, TrustLevel::Rejected);
    assert_ne!(conversion.trust_level, TrustLevel::ProofGrade);
    assert_eq!(conversion.symbolic_formulas.len(), 1);
    assert_eq!(conversion.symbolic_formulas[0].function, "symbolic");
    assert_eq!(conversion.symbolic_formulas[0].block, 0);
    assert_eq!(conversion.symbolic_formulas[0].statement_index, 0);
    assert_eq!(conversion.symbolic_formulas[0].operand, "use");
    assert_eq!(conversion.symbolic_formulas[0].formula, formula);
    assert_eq!(conversion.symbolic_formulas[0].sort, "(_ BitVec 32)");
    assert_eq!(conversion.symbolic_formulas[0].bit_width, Some(32));
    assert_eq!(conversion.provenance_evidence.len(), 2);
    assert!(
        conversion.validation_blockers.iter().any(|blocker| {
            blocker.code == "binary-provenance-not-consumed-by-target-semantics"
        })
    );
    let proof_consumer = conversion.target_proof_consumer_evidence();
    assert_eq!(proof_consumer.status, WasmProofConsumerStatus::Rejected);
    assert!(!proof_consumer.target_semantics_consumed);
    assert!(proof_consumer.records.iter().any(|record| {
        record.kind == "symbolic_formula"
            && record.identifier == "symbolic::bb0::stmt0::use"
            && !record.accepted
            && record.detail.contains("formula JSON/SMT-LIB/sort metadata is preserved")
    }));
    assert!(proof_consumer.blockers.iter().any(|blocker| {
        blocker.code == "symbolic-formula-not-consumed-by-target-semantics"
            && blocker.detail.contains("trust-wasm-bridge::target-semantic-consumption-gate")
            && blocker.detail.contains("smtlib=x0")
    }));
}

#[test]
fn canonical_trust_ir_symbolic_formula_surfaces_as_wasm_blocker_evidence() {
    let formula = Formula::BvAdd(
        Box::new(Formula::Var("x0".to_string(), Sort::BitVec(64))),
        Box::new(Formula::BitVec { value: 1, width: 64 }),
        64,
    );
    let mut function = constant_return_function("symbolic_canonical", 0, Ty::u64());
    function.body.blocks[0].stmts[0] = Statement::Assign {
        place: Place::local(0),
        rvalue: Rvalue::Use(Operand::Symbolic(formula.clone())),
        span: SourceSpan::binary_address(0x1000),
    };

    let module = lower_to_trust_ir(&function).expect("symbolic function lowers to TrustIr");
    let canonical = trust_ir::format::canonical(&module);
    assert!(canonical.contains("dialect_op trust_symbolic.formula"));
    assert!(canonical.contains(SYMBOLIC_FORMULA_ATTR_JSON));

    let reparsed = trust_ir::parser::parse_module(&canonical).expect("canonical TrustIr parses");
    let formula_ops = reparsed.functions[0].blocks[0]
        .body
        .iter()
        .filter(|node| {
            matches!(
                &node.inst,
                Inst::DialectOp(op)
                    if op.dialect == SYMBOLIC_FORMULA_DIALECT
                        && op.op == SYMBOLIC_FORMULA_OP
            )
        })
        .count();
    assert_eq!(formula_ops, 1);
    assert!(
        !reparsed.functions[0].blocks[0]
            .body
            .iter()
            .any(|node| matches!(node.inst, Inst::Undef { .. })),
        "canonical symbolic formula must remain a dialect op, not Undef"
    );

    let conversion = convert_canonical_trust_ir_to_wat(&canonical);

    assert!(conversion.wat.is_none());
    assert_eq!(conversion.validation, ReconstructionValidationStatus::Failed);
    assert_eq!(conversion.wasm_validation, WasmTargetValidationStatus::Rejected);
    assert_eq!(conversion.trust_level, TrustLevel::Rejected);
    assert_eq!(conversion.symbolic_formulas.len(), 1);
    assert_eq!(conversion.symbolic_formulas[0].function, "symbolic_canonical");
    assert_eq!(conversion.symbolic_formulas[0].block, 0);
    assert_eq!(conversion.symbolic_formulas[0].operand, "dialect_op");
    assert_eq!(conversion.symbolic_formulas[0].formula, formula);
    assert_eq!(conversion.symbolic_formulas[0].sort, "(_ BitVec 64)");
    assert_eq!(conversion.symbolic_formulas[0].bit_width, Some(64));
    let proof_consumer = conversion.target_proof_consumer_evidence();
    assert_eq!(proof_consumer.status, WasmProofConsumerStatus::Rejected);
    assert!(!proof_consumer.target_semantics_consumed);
    assert_eq!(proof_consumer.binding.target_output, "wat:blocked:no-emitted-module");
    assert!(proof_consumer.binding.inputs.iter().any(|input| {
        input.kind == "canonical_trust_ir_formula"
            && input.identifier == "symbolic_canonical::bb0::stmt0::dialect_op"
            && input.canonical_source == "trust_symbolic.formula"
            && input.target_output == "wat:blocked:no-emitted-module"
            && !input.consumed_by_target_semantics
    }));
    assert!(proof_consumer.binding.inputs.iter().any(|input| {
        input.kind == "proof_replay"
            && input.identifier == "missing"
            && input.canonical_source == "proof-replay"
            && !input.consumed_by_target_semantics
    }));
    assert!(proof_consumer.records.iter().any(|record| {
        record.kind == "symbolic_formula"
            && record.identifier == "symbolic_canonical::bb0::stmt0::dialect_op"
            && !record.accepted
            && record.detail.contains("target semantics have not consumed")
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
    assert!(proof_consumer.blockers.iter().any(|blocker| {
        blocker.code == "symbolic-formula-not-consumed-by-target-semantics"
            && blocker.detail.contains("1 symbolic formula")
            && blocker.detail.contains("trust-wasm-bridge::target-semantic-consumption-gate")
            && blocker.detail.contains("(bvadd x0 (_ bv1 64))")
    }));
    assert!(conversion.validation_blockers.iter().any(|blocker| {
        blocker.code == "preserved-symbolic-formula"
            && blocker.detail.contains("(bvadd x0 (_ bv1 64))")
            && blocker.detail.contains("Undef")
    }));
    assert!(conversion.validation_blockers.iter().any(|blocker| {
        blocker.code == "missing-binary-provenance"
            && blocker.detail.contains("machine instructions")
    }));
    assert!(conversion.validation_records.iter().any(|record| {
        record.evidence.iter().any(|evidence| {
            matches!(
                evidence,
                ReconstructionValidationEvidence::Other(kind)
                    if kind == "PreservedCanonicalTrustIrSymbolicFormula"
            )
        }) && record.evidence.iter().any(|evidence| {
            matches!(
                evidence,
                ReconstructionValidationEvidence::Other(detail)
                    if detail.contains("formula.smtlib2=(bvadd x0 (_ bv1 64))")
            )
        }) && record.evidence.iter().any(|evidence| {
            matches!(
                evidence,
                ReconstructionValidationEvidence::Other(detail)
                    if detail == "formula.inferred_sort=(_ BitVec 64)"
            )
        }) && record.evidence.iter().any(|evidence| {
            matches!(
                evidence,
                ReconstructionValidationEvidence::Other(detail)
                    if detail == "formula.bit_width=64"
            )
        }) && record.evidence.iter().any(|evidence| {
            matches!(
                evidence,
                ReconstructionValidationEvidence::Other(detail)
                    if detail == "NoProofReplayMetadata"
            )
        })
    }));
    assert!(conversion.diagnostics.iter().any(|diagnostic| {
        diagnostic.contains("symbolic formula dialect metadata preserved")
            && diagnostic.contains("undef")
    }));
    assert!(conversion.unsupported.records.iter().any(|record| {
        record.opcode.as_deref() == Some("trust_symbolic.formula")
            && record.feature.contains("symbolic formula requires proof-grade Wasm semantics")
    }));
}

#[test]
fn canonical_trust_ir_binary_provenance_is_wasm_blocker_evidence_until_consumed() {
    let canonical = canonical_binary_provenance_trust_ir(
        "canonical_provenance_binary",
        EXACT_CANONICAL_BINARY_PROVENANCE_ATTRS,
    );
    trust_ir::parser::parse_module(&canonical).expect("canonical TrustIr provenance fixture parses");

    let conversion = convert_canonical_trust_ir_to_wat(&canonical);

    assert!(conversion.wat.is_none());
    assert!(!conversion.is_accepted());
    assert_eq!(conversion.validation, ReconstructionValidationStatus::Failed);
    assert_eq!(conversion.wasm_validation, WasmTargetValidationStatus::Rejected);
    assert_eq!(conversion.trust_level, TrustLevel::Rejected);
    assert_ne!(conversion.trust_level, TrustLevel::ProofGrade);
    assert!(conversion.symbolic_formulas.is_empty());
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
        "trust-wasm-bridge::target-semantic-consumption-gate"
    );
    assert_eq!(provenance.target_semantic_consumption.code, "no-wasm-target-semantic-consumer");
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
    assert_eq!(proof_consumer.status, WasmProofConsumerStatus::Rejected);
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
        diagnostic
            .contains("binary_provenance.source=canonical-trust_ir.trust_binary.provenance:unit-test")
            && diagnostic.contains("binary_provenance.instruction_bytes=1f2003d5")
            && diagnostic.contains("binary_provenance.target_semantics_consumed=false")
    }));
}

#[test]
fn canonical_trust_ir_malformed_binary_provenance_row_stays_missing_for_wasm() {
    let malformed_attrs = r#"[schema=str:"trust-types.BinaryProvenance@1"] [source=str:"malformed"] [binary_path=str:"fixture.bin"] [function_entry=str:"0x401000"] [instruction_address=str:"0x401004"] [instruction_size=str:"4"] [encoding=str:"0xd503201f"] [instruction_bytes=str:"not-hex"] [target_semantics_consumed=str:"true"]"#;
    let canonical =
        canonical_binary_provenance_trust_ir("canonical_malformed_provenance", malformed_attrs);
    trust_ir::parser::parse_module(&canonical).expect("malformed provenance row stays valid TrustIr");

    let conversion = convert_canonical_trust_ir_to_wat(&canonical);

    assert!(conversion.wat.is_none());
    assert_eq!(conversion.wasm_validation, WasmTargetValidationStatus::Rejected);
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
    assert_eq!(proof_consumer.status, WasmProofConsumerStatus::Rejected);
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
fn canonical_trust_ir_forged_consumed_binary_provenance_stays_rejected_for_wasm() {
    let forged_attrs = format!(
        "{EXACT_CANONICAL_BINARY_PROVENANCE_ATTRS} [target_semantics_consumed=str:\"true\"]"
    );
    let canonical =
        canonical_binary_provenance_trust_ir("canonical_forged_provenance_consumed", &forged_attrs);
    trust_ir::parser::parse_module(&canonical).expect("forged consumed-state row stays valid TrustIr");

    let conversion = convert_canonical_trust_ir_to_wat(&canonical);

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
        "trust-wasm-bridge::target-semantic-consumption-gate"
    );
    assert!(
        provenance
            .target_semantic_consumption
            .detail
            .contains("claim is preserved only as untrusted metadata")
    );

    let proof_consumer = conversion.target_proof_consumer_evidence();
    assert_eq!(proof_consumer.status, WasmProofConsumerStatus::Rejected);
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
                .contains("binary_provenance.consumption.code=no-wasm-target-semantic-consumer")
    }));
}

#[test]
fn canonical_trust_ir_checked_certificate_and_replay_are_bound_but_not_proof_grade() {
    let certificate_sha = "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";
    let replay_sha = "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb";
    let canonical = format!(
        r#"; TrustIr text format v1
module "canonical_proof_metadata"

fn @canonical_proof_metadata(functy.0) {{
bb0(%0: i32):
        %1 = dialect_op trust_binary.provenance() -> i32 {EXACT_CANONICAL_BINARY_PROVENANCE_ATTRS}
        %2 = dialect_op trust_proof.checked_certificate() -> i32 [schema=str:"trust-types.CheckedCertificate@1"] [source=str:"unit-test-cert"] [checker=str:"ay-cert-check"] [format=str:"lfsc"] [sha256=str:"{certificate_sha}"] [certificate_checked=str:"true"] [target_semantics_consumed=str:"true"]
        %3 = dialect_op trust_proof.proof_replay() -> i32 [schema=str:"trust-types.ProofReplay@1"] [source=str:"unit-test-replay"] [replay_status=str:"replayed"] [artifact_sha256=str:"{replay_sha}"] [exact_replay_checked=str:"true"] [target_semantics_consumed=str:"true"]
        ret %0
}}
"#
    );
    trust_ir::parser::parse_module(&canonical).expect("canonical proof metadata fixture parses");

    let conversion = convert_canonical_trust_ir_to_wat(&canonical);

    assert!(conversion.wat.is_none());
    assert!(!conversion.is_accepted());
    assert_eq!(conversion.trust_level, TrustLevel::Rejected);
    assert_eq!(conversion.checked_certificate_evidence.len(), 1);
    assert_eq!(conversion.proof_replay_evidence.len(), 1);
    let certificate = &conversion.checked_certificate_evidence[0];
    assert_eq!(certificate.function, "canonical_proof_metadata");
    assert_eq!(certificate.source, "canonical-trust_ir.trust_proof.checked_certificate:unit-test-cert");
    assert_eq!(certificate.block, Some(0));
    assert_eq!(certificate.statement_index, Some(1));
    assert_eq!(
        certificate.certificate,
        ProofCertificateStatus::Checked {
            checker: "ay-cert-check".to_string(),
            format: "lfsc".to_string(),
            sha256: Some(certificate_sha.to_string()),
        }
    );
    assert_eq!(
        certificate.target_semantic_consumption.input_claimed_target_semantics_consumed,
        Some(true)
    );
    assert!(!certificate.target_semantics_consumed);
    assert!(!certificate.target_semantic_consumption.target_semantics_consumed);

    let replay = &conversion.proof_replay_evidence[0];
    assert_eq!(replay.function, "canonical_proof_metadata");
    assert_eq!(replay.source, "canonical-trust_ir.trust_proof.proof_replay:unit-test-replay");
    assert_eq!(replay.block, Some(0));
    assert_eq!(replay.statement_index, Some(2));
    assert_eq!(replay.replay, ReplayStatus::Replayed);
    assert_eq!(replay.artifact_sha256.as_deref(), Some(replay_sha));
    assert!(replay.exact_replay_checked);
    assert_eq!(
        replay.target_semantic_consumption.input_claimed_target_semantics_consumed,
        Some(true)
    );
    assert!(!replay.target_semantics_consumed);

    assert!(
        !conversion
            .validation_blockers
            .iter()
            .any(|blocker| blocker.code == "missing-checked-proof-certificate"),
        "recognized checked certificate metadata must replace the missing-certificate blocker"
    );
    assert!(
        !conversion
            .validation_blockers
            .iter()
            .any(|blocker| blocker.code == "missing-proof-replay-metadata"),
        "recognized replay metadata must replace the missing-replay blocker"
    );
    assert!(conversion.validation_blockers.iter().any(|blocker| {
        blocker.code == "checked-certificate-not-consumed-by-target-semantics"
            && blocker.detail.contains("bridge-owned")
    }));
    assert!(conversion.validation_blockers.iter().any(|blocker| {
        blocker.code == "proof-replay-not-consumed-by-target-semantics"
            && blocker.detail.contains("bridge-owned")
    }));

    let proof_consumer = conversion.target_proof_consumer_evidence();
    assert_eq!(proof_consumer.status, WasmProofConsumerStatus::Rejected);
    assert!(!proof_consumer.target_semantics_consumed);
    assert!(proof_consumer.records.iter().any(|record| {
        record.kind == "checked_certificate"
            && record.identifier.contains("canonical_proof_metadata::bb0::stmt1")
            && record.identifier.contains(certificate_sha)
            && !record.accepted
            && record.detail.contains("target semantics have not consumed")
    }));
    assert!(proof_consumer.records.iter().any(|record| {
        record.kind == "proof_replay"
            && record.identifier.contains("canonical_proof_metadata::bb0::stmt2")
            && record.identifier.contains(replay_sha)
            && !record.accepted
            && record.detail.contains("target semantics have not consumed")
    }));
    assert!(proof_consumer.binding.inputs.iter().any(|input| {
        input.kind == "checked_certificate"
            && input.canonical_source == "trust_proof.checked_certificate"
            && input.identifier.contains(certificate_sha)
            && !input.consumed_by_target_semantics
    }));
    assert!(proof_consumer.binding.inputs.iter().any(|input| {
        input.kind == "proof_replay"
            && input.canonical_source == "trust_proof.proof_replay"
            && input.identifier.contains(replay_sha)
            && !input.consumed_by_target_semantics
    }));
    assert!(conversion.validation_records.iter().any(|record| {
        record.trust_level == TrustLevel::Rejected
            && record.evidence.contains(&ReconstructionValidationEvidence::Other(
                "CheckedProofCertificateMetadataPreserved:1".to_string(),
            ))
            && record.evidence.contains(&ReconstructionValidationEvidence::Other(
                "ProofReplayMetadataPreserved:1".to_string(),
            ))
            && record.evidence.iter().any(|evidence| {
                matches!(
                    evidence,
                    ReconstructionValidationEvidence::Other(detail)
                        if detail.contains("checked_certificate.target_semantics_consumed=false")
                )
            })
            && record.evidence.iter().any(|evidence| {
                matches!(
                    evidence,
                    ReconstructionValidationEvidence::Other(detail)
                        if detail.contains("proof_replay.target_semantics_consumed=false")
                )
            })
    }));
    assert!(conversion.diagnostics.iter().any(|diagnostic| {
        diagnostic.contains("checked_certificate.input_claim.target_semantics_consumed=true")
            && diagnostic
                .contains("checked_certificate.consumption.target_semantics_consumed=false")
    }));
    assert!(conversion.diagnostics.iter().any(|diagnostic| {
        diagnostic.contains("proof_replay.input_claim.target_semantics_consumed=true")
            && diagnostic.contains("proof_replay.consumption.target_semantics_consumed=false")
    }));
}

#[test]
fn canonical_empty_noop_slice_is_consumed_by_bounded_wasm_proof_consumer() {
    let certificate_sha = "eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee";
    let replay_sha = "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff";
    let certificate_attrs = format!(
        r#"[schema=str:"trust-types.CheckedCertificate@1"] [source=str:"bounded-empty-cert"] [checker=str:"trust-wasm-cert-check"] [format=str:"lfsc"] [sha256=str:"{certificate_sha}"] [certificate_checked=str:"true"] [target_semantics_consumed=str:"false"]"#
    );
    let replay_attrs = format!(
        r#"[schema=str:"trust-types.ProofReplay@1"] [source=str:"bounded-empty-replay"] [replay_status=str:"replayed"] [artifact_sha256=str:"{replay_sha}"] [exact_replay_checked=str:"true"] [target_semantics_consumed=str:"false"]"#
    );
    let canonical = canonical_bounded_empty_consumer_trust_ir(
        "canonical_empty_noop_consumer",
        &Formula::Bool(true),
        EXACT_CANONICAL_BINARY_PROVENANCE_ATTRS,
        &certificate_attrs,
        &replay_attrs,
        EXACT_CANONICAL_UNSUPPORTED_LEDGER_ATTRS,
    );
    trust_ir::parser::parse_module(&canonical).expect("bounded empty fixture parses");

    let conversion = convert_canonical_trust_ir_to_wat(&canonical);

    assert!(conversion.wat.is_none());
    assert_eq!(conversion.validation, ReconstructionValidationStatus::Failed);
    assert_eq!(conversion.wasm_validation, WasmTargetValidationStatus::Rejected);
    assert_eq!(conversion.trust_level, TrustLevel::Rejected);
    assert_eq!(conversion.symbolic_formulas.len(), 1);
    assert_eq!(conversion.symbolic_formulas[0].formula, Formula::Bool(true));
    assert_eq!(conversion.provenance_evidence.len(), 1);
    assert_eq!(conversion.checked_certificate_evidence.len(), 1);
    assert_eq!(conversion.proof_replay_evidence.len(), 1);
    assert_eq!(conversion.unsupported_ledger_evidence.len(), 1);
    assert!(conversion.provenance_evidence[0].target_semantics_consumed);
    assert_eq!(
        conversion.provenance_evidence[0].target_semantic_consumption.code,
        "bounded-empty-wasm-target-consumed"
    );
    assert!(conversion.checked_certificate_evidence[0].target_semantics_consumed);
    assert!(conversion.proof_replay_evidence[0].target_semantics_consumed);
    assert!(conversion.unsupported_ledger_evidence[0].target_semantics_consumed);
    assert!(conversion.unsupported_ledger_evidence[0].unsupported_ledger_eliminated);
    assert!(
        !conversion.validation_blockers.iter().any(|blocker| {
            matches!(
                blocker.code.as_str(),
                "binary-provenance-not-consumed-by-target-semantics"
                    | "checked-certificate-not-consumed-by-target-semantics"
                    | "proof-replay-not-consumed-by-target-semantics"
                    | "unsupported-ledger-not-consumed-by-target-semantics"
            )
        }),
        "bounded slice should not report consumed metadata as unconsumed"
    );
    assert!(
        conversion.validation_blockers.iter().any(|blocker| {
            blocker.code == "preserved-symbolic-formula"
                && blocker.detail.contains("formula JSON/SMT-LIB")
        }),
        "target proof-consumer acceptance for the bounded slice must not erase the conversion-level formula preservation blocker"
    );
    assert!(
        conversion
            .validation_blockers
            .iter()
            .any(|blocker| blocker.code == "unsupported-ledger-not-empty"),
        "unsupported symbolic-formula ledger entries must remain conversion blockers"
    );

    let proof_consumer = conversion.target_proof_consumer_evidence();
    assert_eq!(proof_consumer.status, WasmProofConsumerStatus::Rejected);
    assert!(proof_consumer.target_semantics_consumed);
    assert!(proof_consumer.blockers.iter().any(|blocker| {
        blocker.code == "unsupported-ledger-not-empty"
            && blocker.detail.contains("1 unsupported ledger")
            && blocker.detail.contains("symbolic formula requires proof-grade Wasm semantics")
    }));
    assert_eq!(proof_consumer.binding.target_output, "wat:blocked:no-emitted-module");
    assert_eq!(proof_consumer.binding.status, WasmProofConsumerStatus::Rejected);
    assert!(proof_consumer.binding.target_semantics_consumed);
    assert!(proof_consumer.records.iter().all(|record| record.accepted));
    assert!(proof_consumer.binding.inputs.iter().all(|input| {
        input.target_output == "wat:blocked:no-emitted-module" && input.consumed_by_target_semantics
    }));
    assert!(proof_consumer.proof_grade_blockers.is_empty());
    assert_eq!(proof_consumer.refinement_metadata_evidence.len(), 1);
    assert_eq!(
        proof_consumer.refinement_metadata_evidence[0].code,
        "bounded-empty-noop-wasm-refinement-consumed"
    );
    assert!(proof_consumer.records.iter().any(|record| {
        record.kind == "target_refinement"
            && record.identifier.contains("bounded-empty-noop")
            && record.accepted
    }));
    assert!(proof_consumer.records.iter().any(|record| {
        record.kind == "target_semantics" && record.detail.contains("bounded empty/no-op slice")
    }));
    assert!(conversion.diagnostics.iter().any(|diagnostic| {
        diagnostic.contains("binary_provenance.consumption.code=bounded-empty-wasm-target-consumed")
            && diagnostic.contains("binary_provenance.consumption.target_semantics_consumed=true")
    }));
    assert!(conversion.diagnostics.iter().any(|diagnostic| {
        diagnostic
            .contains("checked_certificate.consumption.code=bounded-empty-wasm-target-consumed")
            && diagnostic.contains(certificate_sha)
    }));
    assert!(conversion.diagnostics.iter().any(|diagnostic| {
        diagnostic.contains("proof_replay.consumption.code=bounded-empty-wasm-target-consumed")
            && diagnostic.contains(replay_sha)
    }));
    assert!(conversion.diagnostics.iter().any(|diagnostic| {
        diagnostic.contains("unsupported_ledger.source=canonical-trust_ir.trust_proof.unsupported_ledger:bounded-empty-unsupported-ledger")
            && diagnostic.contains("unsupported_ledger.eliminated=true")
            && diagnostic.contains("unsupported_ledger.consumption.target_semantics_consumed=true")
    }));
}

#[test]
fn canonical_empty_noop_wasm_consumer_rejects_replayed_trust_cg_target_evidence() {
    let certificate_sha = "eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee";
    let replay_sha = "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff";
    let certificate_attrs = format!(
        r#"[schema=str:"trust-types.CheckedCertificate@1"] [source=str:"bounded-empty-cert"] [checker=str:"trust-wasm-cert-check"] [format=str:"lfsc"] [sha256=str:"{certificate_sha}"] [certificate_checked=str:"true"] [target_semantics_consumed=str:"false"]"#
    );
    let replay_attrs = format!(
        r#"[schema=str:"trust-types.ProofReplay@1"] [source=str:"bounded-empty-replay"] [replay_status=str:"replayed"] [artifact_sha256=str:"{replay_sha}"] [exact_replay_checked=str:"true"] [target_semantics_consumed=str:"false"]"#
    );
    let canonical = canonical_bounded_empty_consumer_trust_ir(
        "canonical_empty_noop_consumer",
        &Formula::Bool(true),
        EXACT_CANONICAL_BINARY_PROVENANCE_ATTRS,
        &certificate_attrs,
        &replay_attrs,
        EXACT_CANONICAL_UNSUPPORTED_LEDGER_ATTRS,
    );
    let mut conversion = convert_canonical_trust_ir_to_wat(&canonical);
    let replayed_trust_cg_consumption = replayed_trust_cg_consumption_for_wasm();
    for provenance in &mut conversion.provenance_evidence {
        provenance.target_semantic_consumption = replayed_trust_cg_consumption.clone();
        provenance.target_semantics_consumed = true;
    }
    for certificate in &mut conversion.checked_certificate_evidence {
        certificate.target_semantic_consumption = replayed_trust_cg_consumption.clone();
        certificate.target_semantics_consumed = true;
    }
    for replay in &mut conversion.proof_replay_evidence {
        replay.target_semantic_consumption = replayed_trust_cg_consumption.clone();
        replay.target_semantics_consumed = true;
    }
    for unsupported_ledger in &mut conversion.unsupported_ledger_evidence {
        unsupported_ledger.target_semantic_consumption = replayed_trust_cg_consumption.clone();
        unsupported_ledger.target_semantics_consumed = true;
    }

    let proof_consumer = conversion.target_proof_consumer_evidence();

    assert_eq!(proof_consumer.status, WasmProofConsumerStatus::Rejected);
    assert!(proof_consumer.is_rejected());
    assert!(!proof_consumer.target_semantics_consumed);
    assert!(proof_consumer.blockers.iter().any(|blocker| {
        blocker.code == "bounded-empty-slice-not-bridge-consumed"
            && blocker.detail.contains("target-specific")
            && blocker.detail.contains("Wasm")
    }));
    assert!(proof_consumer.records.iter().any(|record| {
        record.kind == "binary_provenance"
            && !record.accepted
            && record.detail.contains("trust-cg-bridge::target-semantic-consumption-gate")
    }));
    assert!(proof_consumer.binding.inputs.iter().all(|input| {
        input.target_output == "wat:blocked:no-emitted-module"
            && !input.consumed_by_target_semantics
    }));
    assert_eq!(conversion.trust_level, TrustLevel::Rejected);
    assert_ne!(conversion.trust_level, TrustLevel::ProofGrade);
}

#[test]
fn canonical_empty_slice_with_nontrivial_formula_stays_rejected_for_wasm() {
    let formula = Formula::BvAdd(
        Box::new(Formula::Var("x0".to_string(), Sort::BitVec(32))),
        Box::new(Formula::BitVec { value: 1, width: 32 }),
        32,
    );
    let certificate_sha = "abababababababababababababababababababababababababababababababab";
    let replay_sha = "cdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcd";
    let certificate_attrs = format!(
        r#"[schema=str:"trust-types.CheckedCertificate@1"] [source=str:"nontrivial-cert"] [checker=str:"trust-wasm-cert-check"] [format=str:"lfsc"] [sha256=str:"{certificate_sha}"] [certificate_checked=str:"true"]"#
    );
    let replay_attrs = format!(
        r#"[schema=str:"trust-types.ProofReplay@1"] [source=str:"nontrivial-replay"] [replay_status=str:"replayed"] [artifact_sha256=str:"{replay_sha}"] [exact_replay_checked=str:"true"]"#
    );
    let canonical = canonical_bounded_empty_consumer_trust_ir(
        "canonical_empty_nontrivial_consumer",
        &formula,
        EXACT_CANONICAL_BINARY_PROVENANCE_ATTRS,
        &certificate_attrs,
        &replay_attrs,
        EXACT_CANONICAL_UNSUPPORTED_LEDGER_ATTRS,
    );

    let conversion = convert_canonical_trust_ir_to_wat(&canonical);

    assert!(!conversion.provenance_evidence[0].target_semantics_consumed);
    let proof_consumer = conversion.target_proof_consumer_evidence();
    assert_eq!(proof_consumer.status, WasmProofConsumerStatus::Rejected);
    assert!(!proof_consumer.target_semantics_consumed);
    assert!(proof_consumer.blockers.iter().any(|blocker| {
        blocker.code == "bounded-empty-slice-nontrivial-formula"
            && blocker.detail.contains("rejects nontrivial")
    }));
    assert!(
        proof_consumer
            .records
            .iter()
            .any(|record| { record.kind == "symbolic_formula" && !record.accepted })
    );
}

#[test]
fn canonical_empty_slice_with_extra_nonmetadata_op_stays_rejected_for_wasm() {
    let certificate_sha = "1212121212121212121212121212121212121212121212121212121212121212";
    let replay_sha = "3434343434343434343434343434343434343434343434343434343434343434";
    let certificate_attrs = format!(
        r#"[schema=str:"trust-types.CheckedCertificate@1"] [source=str:"extra-op-cert"] [checker=str:"trust-wasm-cert-check"] [format=str:"lfsc"] [sha256=str:"{certificate_sha}"] [certificate_checked=str:"true"]"#
    );
    let replay_attrs = format!(
        r#"[schema=str:"trust-types.ProofReplay@1"] [source=str:"extra-op-replay"] [replay_status=str:"replayed"] [artifact_sha256=str:"{replay_sha}"] [exact_replay_checked=str:"true"]"#
    );
    let canonical = canonical_bounded_empty_consumer_trust_ir(
        "canonical_empty_extra_op_consumer",
        &Formula::Bool(true),
        EXACT_CANONICAL_BINARY_PROVENANCE_ATTRS,
        &certificate_attrs,
        &replay_attrs,
        EXACT_CANONICAL_UNSUPPORTED_LEDGER_ATTRS,
    )
    .replace(
        "        ret %0",
        "        %6 = dialect_op trust_exec.not_empty() -> i32\n        ret %0",
    );
    trust_ir::parser::parse_module(&canonical).expect("extra op fixture parses");

    let conversion = convert_canonical_trust_ir_to_wat(&canonical);

    assert!(!conversion.provenance_evidence[0].target_semantics_consumed);
    let proof_consumer = conversion.target_proof_consumer_evidence();
    assert_eq!(proof_consumer.status, WasmProofConsumerStatus::Rejected);
    assert!(proof_consumer.blockers.iter().any(|blocker| {
        blocker.code == "bounded-empty-slice-not-bridge-consumed"
            && blocker.detail.contains("source-shape validation")
    }));
}

#[test]
fn canonical_trust_ir_symbolic_formula_schema_mismatch_is_fail_closed() {
    let formula = Formula::BvAdd(
        Box::new(Formula::Var("x0".to_string(), Sort::BitVec(64))),
        Box::new(Formula::BitVec { value: 1, width: 64 }),
        64,
    );
    let mut function = constant_return_function("symbolic_schema_mismatch", 0, Ty::u64());
    function.body.blocks[0].stmts[0] = Statement::Assign {
        place: Place::local(0),
        rvalue: Rvalue::Use(Operand::Symbolic(formula)),
        span: SourceSpan::binary_address(0x1000),
    };

    let module = lower_to_trust_ir(&function).expect("symbolic function lowers to TrustIr");
    let canonical = trust_ir::format::canonical(&module);
    assert!(
        canonical
            .contains(&format!("[{SYMBOLIC_FORMULA_ATTR_SCHEMA}=str:\"trust-types.Formula@1\"]"))
    );
    assert!(
        canonical
            .contains(&format!("[{SYMBOLIC_FORMULA_ATTR_SMTLIB}=str:\"(bvadd x0 (_ bv1 64))\"]"))
    );
    let sort_attr = format!("[{SYMBOLIC_FORMULA_ATTR_SORT}=str:\"(_ BitVec 64)\"]");
    let corrupted = canonical
        .replace(&sort_attr, &format!("[{SYMBOLIC_FORMULA_ATTR_SORT}=str:\"(_ BitVec 32)\"]"));
    assert_ne!(corrupted, canonical, "test must corrupt the formula sort attribute");

    let conversion = convert_canonical_trust_ir_to_wat(&corrupted);

    assert!(conversion.wat.is_none());
    assert!(!conversion.is_accepted());
    assert_eq!(conversion.wasm_validation, WasmTargetValidationStatus::Rejected);
    assert_eq!(conversion.trust_level, TrustLevel::Rejected);
    assert_eq!(conversion.symbolic_formulas.len(), 1);
    assert_eq!(conversion.symbolic_formulas[0].sort, "(_ BitVec 64)");
    assert_eq!(conversion.symbolic_formulas[0].bit_width, Some(64));
    assert!(conversion.validation_blockers.iter().any(|blocker| {
        blocker.code == "invalid-symbolic-formula-schema"
            && blocker.detail.contains("(_ BitVec 32)")
            && blocker.detail.contains("(_ BitVec 64)")
    }));
    assert!(conversion.validation_blockers.iter().any(|blocker| {
        blocker.code == "missing-proof-replay-metadata"
            && blocker.detail.contains("replay metadata")
    }));
    assert!(conversion.validation_records.iter().any(|record| {
        record.trust_level == TrustLevel::Rejected
            && record.evidence.contains(&ReconstructionValidationEvidence::Other(
                "formula.inferred_sort=(_ BitVec 64)".to_string(),
            ))
            && record.evidence.contains(&ReconstructionValidationEvidence::Other(
                "formula.bit_width=64".to_string(),
            ))
            && record.evidence.iter().any(|evidence| {
                matches!(
                    evidence,
                    ReconstructionValidationEvidence::Other(detail)
                        if detail.contains("formula.schema_error=")
                            && detail.contains("(_ BitVec 32)")
                            && detail.contains("(_ BitVec 64)")
                )
            })
    }));
}

#[test]
fn symbolic_formula_metadata_remains_proof_consumer_blocker_not_proof_grade() {
    let formula = Formula::Eq(
        Box::new(Formula::Var("guard".to_string(), Sort::Bool)),
        Box::new(Formula::Bool(true)),
    );
    let mut function = constant_return_function("formula_blocker", 0, Ty::Bool);
    function.body.blocks[0].stmts[0] = Statement::Assign {
        place: Place::local(0),
        rvalue: Rvalue::Use(Operand::Symbolic(formula.clone())),
        span: SourceSpan::binary_address(0x1000),
    };

    let module = lower_to_trust_ir(&function).expect("symbolic function lowers to TrustIr");
    let canonical = trust_ir::format::canonical(&module);
    let reparsed = trust_ir::parser::parse_module(&canonical).expect("canonical TrustIr parses");
    assert!(
        !reparsed.functions[0].blocks[0]
            .body
            .iter()
            .any(|node| matches!(node.inst, Inst::Undef { .. })),
        "proof-consumer formula metadata must not be replaced with Undef"
    );

    let conversion = convert_canonical_trust_ir_to_wat(&canonical);

    assert!(conversion.wat.is_none());
    assert!(!conversion.is_accepted());
    assert_eq!(conversion.trust_level, TrustLevel::Rejected);
    assert_ne!(conversion.trust_level, TrustLevel::ProofGrade);
    assert_eq!(conversion.symbolic_formulas.len(), 1);
    assert_eq!(conversion.symbolic_formulas[0].formula, formula);
    assert_eq!(conversion.symbolic_formulas[0].sort, "Bool");
    assert_eq!(conversion.symbolic_formulas[0].bit_width, None);
    assert!(conversion.validation_blockers.iter().any(|blocker| {
        blocker.code == "preserved-symbolic-formula"
            && blocker.detail.contains("consume formula JSON/SMT-LIB")
            && blocker.detail.contains("Undef")
    }));
    assert!(conversion.validation_records.iter().any(|record| {
        record.trust_level == TrustLevel::Rejected
            && record.evidence.contains(&ReconstructionValidationEvidence::Other(
                "PreservedCanonicalTrustIrSymbolicFormula".to_string(),
            ))
            && record
                .evidence
                .contains(&ReconstructionValidationEvidence::NoCheckedProofCertificate)
            && record.evidence.contains(&ReconstructionValidationEvidence::Other(
                "NoProofReplayMetadata".to_string(),
            ))
            && record.evidence.contains(&ReconstructionValidationEvidence::NoBinaryProofObligation)
            && record.diagnostics.iter().any(|diagnostic| diagnostic.contains("blocker/evidence"))
    }));

    let proof_consumer = conversion.target_proof_consumer_evidence();
    assert_eq!(proof_consumer.status, WasmProofConsumerStatus::Rejected);
    assert_eq!(proof_consumer.binding.target_output, "wat:blocked:no-emitted-module");
    assert!(proof_consumer.blockers.iter().any(|blocker| {
        blocker.code == "no-emitted-scalar-wasm-target-op-binding"
            && blocker.detail.contains("emitted no WAT target operation")
            && blocker.detail.contains("bounded empty/no-op")
    }));
    assert!(proof_consumer.blockers.iter().any(|blocker| {
        blocker.code == "symbolic-formula-not-consumed-by-target-semantics"
            && blocker.detail.contains("trust-wasm-bridge::target-semantic-consumption-gate")
            && blocker.detail.contains("(= guard true)")
    }));
}
