//! Retained real THIR body; captured query rows remain candidate inputs.

use trust_ir::proof::{ClauseBinding, ClausePlace, ClauseSort};
use trust_ir::{
    FunctionSummary, ObligationKind as IrKind, ProofFormula, ProofObligation,
    ProofObligationSourceIdentity, ProofStatus,
};
use trust_verifier_api::{
    BundleSubject, MetadataEntry, SourceLocation, TrustContract, TrustObligation, TrustSpecExpr,
};
use trust_wp_lib::trust_ir_body::{replay_trust_ir_body_contracts, verify_trust_ir_body_contracts};

use super::*;

fn fixture() -> (Module, TrustContractBundle, Vec<DirectContractShadowQuestion>) {
    let mut module = trust_ir::binary::deserialize_module(include_bytes!(
        "../tests/data/direct-shift-mask/module.trust-ir.bin"
    ))
    .unwrap();
    assert!(module.proof_obligations.is_empty());
    assert_eq!(module.functions.len(), 1);
    assert_eq!(module.functions[0].producer, Some(trust_ir::Producer::TRust));
    let report: serde_json::Value =
        serde_json::from_str(include_str!("../tests/data/direct-shift-mask/staged-query.json"))
            .unwrap();
    assert_eq!(report["outcome"]["rows_installed"], 2);
    assert_eq!(report["live_tier_refuses"], true);
    let original: TrustContractBundle = serde_json::from_str(include_str!(
        "../../trust-bmc/testdata/widthconv-shift-mask/public.json"
    ))
    .unwrap();
    let mut public = TrustContractBundle::empty(
        "direct-shift-mask",
        BundleSubject::Crate { name: "trust_widthconv".into() },
    );
    let mut questions = Vec::new();
    let mut summary = FunctionSummary::new();
    summary.params = vec!["target_width".into()];
    for index in 0..2 {
        let captured = &report["rows"][index];
        let mut carried = ProofFormula::new(
            "trust.contract-clause@1",
            captured["formula"]["payload"].as_str().unwrap(),
        );
        carried.smtlib = Some(captured["formula"]["smtlib"].as_str().unwrap().into());
        carried.bindings.push((
            "_0".into(),
            ClauseBinding {
                sort: ClauseSort::BitVec(32),
                place: ClausePlace::ResultSlot { index: 0 },
            },
        ));
        if index == 1 {
            carried.bindings.push((
                "target_width".into(),
                ClauseBinding {
                    sort: ClauseSort::BitVec(32),
                    place: ClausePlace::Param { index: 0 },
                },
            ));
        }
        assert_eq!(
            captured["formula"]["bindings"].as_array().unwrap().len(),
            carried.bindings.len()
        );
        let assertion = captured["assertion_id"].as_str().unwrap().to_string();
        assert_eq!(assertion, format!("trust_widthconv::shift_mask#ensures#c{index}"));
        let id = ProofId::new(index as u32);
        module.proof_obligations.push(
            ProofObligation::new(
                id,
                IrKind::Postcondition,
                ProofStatus::Pending,
                format!("captured authored postcondition {index}"),
            )
            .with_function(module.functions[0].id)
            .with_source(ProofObligationSourceIdentity::new(
                "trust-thir-lower/contract@1",
                &assertion,
            ))
            .with_formula(carried.clone()),
        );
        summary.ensures.push(carried.clone());
        let contract = original
            .contracts
            .iter()
            .find(|contract| {
                contract.contract_id
                    == format!("trust-contract:trust_widthconv::shift_mask:ensures:{index}")
            })
            .unwrap();
        let public_id = format!("direct:shift-mask:{index}");
        let contract_id = format!("direct:shift-mask:ensures:{index}");
        let source = SourceLocation {
            file: Some(module.files[0].clone()),
            line: Some(3 + index as u32),
            column: Some(0),
            end_line: Some(3 + index as u32),
            end_column: Some(40),
        };
        public.contracts.push(TrustContract {
            contract_id: contract_id.clone(),
            kind: ContractKind::Ensures,
            predicate: contract.predicate.clone(),
            source: source.clone(),
            metadata: vec![MetadataEntry {
                key: TRUST_IR_CLAUSE_BINDINGS_METADATA_KEY.into(),
                value: serde_json::to_string(&carried.bindings).unwrap(),
            }],
        });
        public.obligations.push(TrustObligation {
            obligation_id: public_id.clone(),
            kind: ObligationKind::Postcondition,
            contract_id: Some(contract_id),
            proof_item_id: None,
            source,
            description: "original authored width-conversion clause".into(),
            required_strength: None,
            summary_facts: vec![],
            metadata: vec![],
        });
        questions.push(DirectContractShadowQuestion {
            proof_id: id,
            public_obligation_id: public_id,
            assertion_id: assertion,
            carried_clause: carried,
            public_semantic_digest: String::new(),
        });
    }
    module.functions[0].summary = Some(summary);
    for (question, obligation) in questions.iter_mut().zip(&public.obligations) {
        question.public_semantic_digest =
            public.canonical_obligation_semantic_digest_sha256(obligation).unwrap();
    }
    assert!(trust_ir_build::validate_module(&module).is_empty());
    (module, public, questions)
}

#[test]
fn direct_contract_shadow_real_thir_postconditions_verify_and_replay_without_authority() {
    let (module, public, questions) = fixture();
    let original = module.clone();
    let shadow =
        direct_contract_shadow_verification_bundle(module.clone(), &public, &questions).unwrap();
    assert_eq!(shadow.disclosure.pristine_module_digest, module.stable_digest());
    assert_eq!(shadow.bundle().source_digest(), None);
    assert!(matches!(shadow.bundle().input, trust_ir::NativeAdapterInput::TrustIrModule));
    assert_eq!(shadow.bundle().producer, trust_ir::NativeBundleProducer::TRust);
    assert!(
        shadow
            .bundle()
            .module
            .proof_obligations
            .iter()
            .all(|row| row.status == ProofStatus::Pending)
    );
    let results = verify_trust_ir_body_contracts(shadow.bundle()).unwrap();
    assert_eq!(results.len(), 2);
    assert!(
        results.iter().all(|row| row.status == trust_wp_lib::VerifyBundleStatus::Verified),
        "{results:#?}"
    );
    replay_trust_ir_body_contracts(shadow.bundle(), &results).unwrap();
    assert_eq!(module, original);
}

#[test]
fn direct_contract_shadow_rejects_changed_question_or_installed_clause() {
    for mutation in ["predicate", "swap", "payload", "assertion", "file", "omission", "status"] {
        let (mut module, mut public, mut questions) = fixture();
        match mutation {
            "predicate" => {
                public.contracts[0].predicate =
                    TrustSpecPredicate::new(TrustSpecExpr::bool_literal(false), Vec::new())
                        .into_contract_predicate()
                        .unwrap();
                public.validate().expect("the changed public question remains well formed");
            }
            "swap" => {
                let id = questions[0].public_obligation_id.clone();
                questions[0].public_obligation_id = questions[1].public_obligation_id.clone();
                questions[1].public_obligation_id = id;
            }
            "payload" => {
                module.proof_obligations[0].formula.as_mut().unwrap().payload.push_str(" forged")
            }
            "assertion" => module.proof_obligations[0]
                .source
                .as_mut()
                .unwrap()
                .assertion_id
                .push_str("foreign"),
            "file" => public.obligations[0].source.file = Some("foreign.rs".into()),
            "omission" => {
                questions.pop();
            }
            "status" => module.proof_obligations[0].status = ProofStatus::Discharged,
            _ => unreachable!(),
        }
        assert!(
            direct_contract_shadow_verification_bundle(module, &public, &questions).is_err(),
            "{mutation}"
        );
    }
}

#[test]
fn direct_contract_shadow_changed_body_cannot_reuse_the_body_wp() {
    let (mut module, public, questions) = fixture();
    let old =
        direct_contract_shadow_verification_bundle(module.clone(), &public, &questions).unwrap();
    let proof = verify_trust_ir_body_contracts(old.bundle()).unwrap();
    let return_value = module.functions[0]
        .blocks
        .iter()
        .flat_map(|block| &block.body)
        .find_map(|node| {
            if let trust_ir::Inst::Return { values } = &node.inst {
                values.first().copied()
            } else {
                None
            }
        })
        .unwrap();
    let constant = module.functions[0]
        .blocks
        .iter_mut()
        .flat_map(|block| &mut block.body)
        .find(|node| node.results.contains(&return_value))
        .unwrap();
    let trust_ir::Inst::Const { value, .. } = &mut constant.inst else {
        panic!("captured literal return")
    };
    *value = trust_ir::Constant::Int(999);
    let changed = direct_contract_shadow_verification_bundle(module, &public, &questions).unwrap();
    assert!(replay_trust_ir_body_contracts(changed.bundle(), &proof).is_err());
    assert!(
        verify_trust_ir_body_contracts(changed.bundle())
            .unwrap()
            .iter()
            .all(|row| row.status != trust_wp_lib::VerifyBundleStatus::Verified)
    );
}

#[test]
fn direct_contract_shadow_false_assume_proves_no_authored_postcondition() {
    let (mut module, public, questions) = fixture();
    let original =
        direct_contract_shadow_verification_bundle(module.clone(), &public, &questions).unwrap();
    let old_results = verify_trust_ir_body_contracts(original.bundle()).unwrap();
    let function = &mut module.functions[0];
    let false_value = function.fresh_value_ids().peek().unwrap();
    let entry = function.blocks.iter_mut().find(|block| block.id == function.entry).unwrap();
    entry.body.splice(
        0..0,
        [
            trust_ir::InstrNode::new(trust_ir::Inst::Const {
                ty: trust_ir::Ty::Bool,
                value: trust_ir::Constant::Bool(false),
            })
            .with_result(false_value),
            trust_ir::InstrNode::new(trust_ir::Inst::Assume { cond: false_value }),
        ],
    );
    assert!(trust_ir_build::validate_module(&module).is_empty());
    let changed = direct_contract_shadow_verification_bundle(module, &public, &questions).unwrap();
    assert!(replay_trust_ir_body_contracts(changed.bundle(), &old_results).is_err());
    let results = verify_trust_ir_body_contracts(changed.bundle()).unwrap();
    assert_eq!(results.len(), 2, "the authored denominator must stay intact");
    assert!(results.iter().all(|row| row.status != trust_wp_lib::VerifyBundleStatus::Verified));
}

#[test]
fn direct_contract_shadow_malformed_ssa_refuses_before_requests() {
    let (mut module, public, questions) = fixture();
    let return_node = module.functions[0]
        .blocks
        .iter_mut()
        .flat_map(|block| &mut block.body)
        .find(|node| matches!(node.inst, trust_ir::Inst::Return { .. }))
        .unwrap();
    return_node.inst = trust_ir::Inst::Return { values: vec![trust_ir::ValueId::new(u32::MAX)] };
    assert!(!trust_ir_build::validate_module(&module).is_empty());
    assert!(direct_contract_shadow_verification_bundle(module, &public, &questions).is_err());
}

#[test]
fn direct_contract_shadow_rejects_ineligible_contract_owners() {
    for mutation in ["clean", "bodyless", "missing", "unscoped"] {
        let (mut module, public, questions) = fixture();
        match mutation {
            "clean" => module.functions[0].producer = Some(trust_ir::Producer::Clean),
            "bodyless" => {
                let original = &module.functions[0];
                let mut declaration = trust_ir::Function::new(
                    original.id,
                    original.name.clone(),
                    original.ty,
                    original.entry,
                )
                .with_producer(trust_ir::Producer::TRust);
                declaration.summary = original.summary.clone();
                module.functions[0] = declaration;
            }
            "missing" => module.proof_obligations[0].function = Some(trust_ir::FuncId::new(99)),
            "unscoped" => module.proof_obligations[0].function = None,
            _ => unreachable!(),
        }
        assert_eq!(module.proof_obligations.len(), 2);
        if matches!(mutation, "clean" | "bodyless") {
            let errors = trust_ir_build::validate_module(&module);
            assert!(errors.is_empty(), "{mutation}: {errors:?}");
        }
        let error = direct_contract_shadow_verification_bundle(module, &public, &questions)
            .expect_err("authored contract rows must retain a bodied direct owner");
        if matches!(mutation, "clean" | "bodyless") {
            assert!(error.contains("not direct-eligible"), "{mutation}: {error}");
        }
    }
}
