#![cfg(feature = "trust-mc-native-trust-ir-bundle")]
use std::time::{Duration, Instant};

use trust_bmc::TrustMcVerifierApiAdapter;
use trust_ir::proof::{ClauseBinding, ClausePlace, ClauseSort};
use trust_ir_bridge::native_verification_bundle_from_module;
use trust_verifier_api::*;

fn rebuild(
    public: &TrustContractBundle,
    mut module: trust_ir::Module,
) -> trust_ir::NativeVerificationBundle {
    let digest =
        public.canonical_obligation_semantic_digest_sha256(&public.obligations[0]).unwrap();
    module.proof_obligations[0].source.as_mut().unwrap().public.as_mut().unwrap().semantic_digest =
        trust_ir::ProofDigest::sha256(std::array::from_fn(|i| {
            u8::from_str_radix(&digest[2 * i..2 * i + 2], 16).unwrap()
        }));
    native_verification_bundle_from_module(
        module,
        trust_ir::ProofDigest::sha256([1; 32]),
        trust_ir::FuncId::new(0),
    )
    .unwrap()
}

fn fixture() -> (TrustContractBundle, trust_ir::NativeVerificationBundle) {
    let id = "trust_ir-native-trust-mc-request-0-proof-0".to_owned();
    let mut formula =
        trust_ir::ProofFormula::new("trust-wp.pure-expr.v1", "(r : bool) == (x : bool)");
    formula.bindings = vec![
        (
            "x".into(),
            ClauseBinding { sort: ClauseSort::Bool, place: ClausePlace::Param { index: 0 } },
        ),
        (
            "r".into(),
            ClauseBinding { sort: ClauseSort::Bool, place: ClausePlace::ResultSlot { index: 0 } },
        ),
    ];
    let mut public = TrustContractBundle::empty(
        "raw-post",
        BundleSubject::Function { crate_name: "test".into(), path: "identity".into() },
    );
    public.contracts.push(TrustContract {
        contract_id: id.clone(),
        kind: ContractKind::Ensures,
        predicate: ContractPredicate::CanonicalJson {
            schema: formula.schema.clone(),
            value: formula.payload.clone().into(),
        },
        source: SourceLocation::default(),
        metadata: vec![MetadataEntry {
            key: TRUST_IR_CLAUSE_BINDINGS_METADATA_KEY.into(),
            value: serde_json::to_string(&formula.bindings).unwrap(),
        }],
    });
    public.obligations.push(TrustObligation {
        obligation_id: id.clone(),
        kind: ObligationKind::Postcondition,
        contract_id: Some(id.clone()),
        proof_item_id: None,
        source: SourceLocation {
            file: Some("raw-post.rs".into()),
            line: Some(1),
            column: Some(9),
            end_line: Some(1),
            end_column: Some(19),
        },
        description: "identity".into(),
        required_strength: None,
        summary_facts: vec![],
        metadata: vec![
            MetadataEntry {
                key: "trust.trust_ir.native.verifier_suite".into(),
                value: "trust-mc".into(),
            },
            MetadataEntry { key: "trust.trust_ir.native.request_id".into(), value: "0".into() },
            MetadataEntry {
                key: "trust.trust_ir.native.proof_obligation_id".into(),
                value: "0".into(),
            },
        ],
    });
    let mut module = trust_ir::Module::new("raw-post");
    let file = module.intern_file("raw-post.rs").unwrap();
    let sig = module
        .add_func_type(trust_ir::FuncTy {
            params: vec![trust_ir::Ty::Bool],
            returns: vec![trust_ir::Ty::Bool],
            is_vararg: false,
            abi: None,
        })
        .unwrap();
    let bid = trust_ir::BlockId::new(0);
    let arg = trust_ir::ValueId::new(0);
    let mut block = trust_ir::Block::new(bid).with_param(arg, trust_ir::Ty::Bool);
    block.body.push(trust_ir::InstrNode::new(trust_ir::Inst::Return { values: vec![arg] }));
    let mut function = trust_ir::Function::new(trust_ir::FuncId::new(0), "identity", sig, bid)
        .with_producer(trust_ir::Producer::TrustIr);
    function.blocks.push(block);
    function.proofs.push(trust_ir::ProofAnnotation::Pure);
    module.try_add_function(function).unwrap();
    module.proof_obligations.push(
        trust_ir::ProofObligation::new(
            trust_ir::ProofId::new(0),
            trust_ir::ObligationKind::Postcondition,
            trust_ir::ProofStatus::Pending,
            "identity",
        )
        .with_function(trust_ir::FuncId::new(0))
        .with_formula(formula)
        .with_source(
            trust_ir::ProofObligationSourceIdentity::new(
                id.clone(),
                format!("trust-assertion:{id}"),
            )
            .with_range(trust_ir::ProofObligationSourceRange {
                file,
                start_line: 1,
                start_col: 9,
                end_line: 1,
                end_col: 19,
            })
            .with_public(trust_ir::PublicObligationIdentity {
                obligation_id: id,
                semantic_digest: trust_ir::ProofDigest::sha256([1; 32]),
            }),
        ),
    );
    let native = rebuild(&public, module);
    (public, native)
}

fn evidence(
    public: &TrustContractBundle,
    native: &trust_ir::NativeVerificationBundle,
) -> ObligationEvidence {
    TrustMcVerifierApiAdapter::default()
        .evidence_from_native_trust_ir_bundle(public, &public.obligations, native)
        .remove(0)
}

#[test]
fn exact_raw_postcondition_is_only_a_capability_decline() {
    let (public, native) = fixture();
    let row = evidence(&public, &native);
    assert_eq!(row.status, EvidenceStatus::Unsupported, "{row:#?}");
    assert_eq!(row.decline, Some(DeclineClass::Capability));
    assert!(row.proof_strength.is_none());
    assert!(row.artifacts.is_empty());
}

#[test]
fn mismatched_formula_source_and_public_bindings_are_terminal() {
    for mode in 0..3 {
        let (mut public, mut native) = fixture();
        match mode {
            0 => {
                native.module.proof_obligations[0].formula.as_mut().unwrap().payload =
                    "(r : bool) != (x : bool)".into()
            }
            1 => {
                native.module.proof_obligations[0].source.as_mut().unwrap().source_id =
                    "other-source".into()
            }
            _ => public.contracts[0].metadata[0].value = "[]".into(),
        }
        let native = rebuild(&public, native.module);
        let row = evidence(&public, &native);
        assert_eq!(row.status, EvidenceStatus::Unsupported, "mutation {mode}: {row:#?}");
        assert_eq!(row.decline, None, "mutation {mode}: {row:#?}");
    }
}

#[test]
fn body_vc_metadata_and_malformed_raw_markers_are_not_capability_gaps() {
    for (key, value) in
        [("trust.vc.formula.schema", "body-vc"), ("trust.ir.raw-source-postcondition.v1", "forged")]
    {
        let (mut public, native) = fixture();
        public.obligations[0].metadata.push(MetadataEntry { key: key.into(), value: value.into() });
        let native = rebuild(&public, native.module);
        let row = evidence(&public, &native);
        assert_eq!(row.status, EvidenceStatus::Unsupported, "{row:#?}");
        assert_eq!(row.decline, None, "{row:#?}");
    }
}

#[test]
fn expired_budget_is_terminal_before_raw_capability_dispatch() {
    let (public, native) = fixture();
    let row = TrustMcVerifierApiAdapter::default()
        .evidence_from_native_trust_ir_bundle_with_deadline(
            &public,
            &public.obligations,
            &native,
            Some(Instant::now() - Duration::from_secs(1)),
        )
        .remove(0);
    assert_ne!(row.status, EvidenceStatus::Proved);
    assert_eq!(row.decline, None, "{row:#?}");
}

#[test]
fn an_assumption_body_does_not_become_a_retryable_raw_claim() {
    let (public, native) = fixture();
    let mut module = native.module;
    module.functions[0].blocks[0].body.insert(
        0,
        trust_ir::InstrNode::new(trust_ir::Inst::Assume { cond: trust_ir::ValueId::new(0) }),
    );
    let candidate = native_verification_bundle_from_module(
        module,
        trust_ir::ProofDigest::sha256([1; 32]),
        trust_ir::FuncId::new(0),
    );
    let native = candidate.expect("the typed native producer can represent an Assume body");
    let row = evidence(&public, &native);
    assert_eq!(row.status, EvidenceStatus::Unsupported);
    assert_eq!(row.decline, None, "{row:#?}");
    assert!(
        row.diagnostics.iter().any(|message| message.contains("native body assumptions")),
        "{row:#?}"
    );
}

#[test]
fn typed_mc_contract_without_vc_metadata_keeps_its_existing_terminal_path() {
    let (mut public, native) = fixture();
    public.contracts[0].predicate = ContractPredicate::CanonicalJson {
        schema: "trust-mc.typed-chc-obligation.v1".into(),
        value: serde_json::json!({}),
    };
    let native = rebuild(&public, native.module);
    let row = evidence(&public, &native);
    assert_eq!(row.status, EvidenceStatus::Unsupported);
    assert_eq!(row.decline, None);
    assert!(
        row.diagnostics.iter().any(|message| message.contains("has no public formula metadata")),
        "{row:#?}"
    );
}

#[test]
fn duplicate_binding_names_do_not_receive_raw_capability() {
    let (mut public, mut native) = fixture();
    let formula = native.module.proof_obligations[0].formula.as_mut().unwrap();
    formula.bindings.push(formula.bindings[0].clone());
    public.contracts[0].metadata[0].value = serde_json::to_string(&formula.bindings).unwrap();
    let native = rebuild(&public, native.module);
    let row = evidence(&public, &native);
    assert_eq!(row.status, EvidenceStatus::Unsupported, "{row:#?}");
    assert_eq!(row.decline, None, "{row:#?}");
}

#[test]
fn an_unrelated_function_assumption_does_not_block_the_selected_raw_claim() {
    let (public, native) = fixture();
    let mut module = native.module;
    let mut unrelated = module.functions[0].clone();
    unrelated.id = trust_ir::FuncId::new(1);
    unrelated.name = "unrelated".into();
    unrelated.blocks[0].body.insert(
        0,
        trust_ir::InstrNode::new(trust_ir::Inst::Assume { cond: trust_ir::ValueId::new(0) }),
    );
    module.try_add_function(unrelated).unwrap();
    let native = rebuild(&public, module);
    let row = evidence(&public, &native);
    assert_eq!(row.status, EvidenceStatus::Unsupported, "{row:#?}");
    assert_eq!(row.decline, Some(DeclineClass::Capability), "{row:#?}");
}
