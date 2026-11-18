#![cfg(feature = "native-trust-ir-claims")]

use trust_ir::proof::{ClauseBinding, ClausePlace, ClauseSort};
use trust_ir::request::*;
use trust_ir::{
    Block, BlockId, FuncId, FuncTy, Function, Inst, InstrNode, Module, Producer, ProofDigest,
    ProofFormula, ProofId, ProofLineageId, ProofLineageManifest, ProofLineageNode, ProofObligation,
    ProofObligationSourceIdentity, ProofObligationSourceRange, ProofReplayIdentity, ProofStatus,
    ProofTransform, ProofTransformStage, PublicObligationIdentity, SourceSpan, Ty, ValueId,
};
use trust_verifier_api::native_public_question::{NativePublicProofScope, NativePublicQuestion};
use trust_verifier_api::*;

// Synthetic correspondence inputs, not compiler provenance or proof evidence.
// Unlike a private unchecked question constructor, every positive below goes
// through canonical native admission and the public sealed API.
fn fixture(kind: ContractKind) -> (TrustContractBundle, NativeVerificationBundle) {
    let mut public = TrustContractBundle::empty(
        "entry-question",
        BundleSubject::Function { crate_name: "test".into(), path: "identity".into() },
    );
    let mut module = Module::new("entry-question");
    let file = module.intern_file("identity.rs").unwrap();
    let signature = module
        .add_func_type(FuncTy {
            params: vec![Ty::Bool],
            returns: vec![Ty::Bool],
            is_vararg: false,
            abi: None,
        })
        .unwrap();
    let mut function = Function::new(FuncId::new(0), "identity", signature, BlockId::new(0))
        .with_producer(Producer::TrustIr);
    let mut block = Block::new(BlockId::new(0)).with_param(ValueId::new(0), Ty::Bool);
    block.body.push(InstrNode::new(Inst::Return { values: vec![ValueId::new(0)] }));
    function.blocks.push(block);
    module.try_add_function(function).unwrap();
    let param = (
        "x".into(),
        ClauseBinding { sort: ClauseSort::Bool, place: ClausePlace::Param { index: 0 } },
    );
    for (index, contract_id, role, payload, bindings) in [
        (
            0,
            "post",
            ContractKind::Ensures,
            "(r : bool) == (x : bool)",
            vec![
                param.clone(),
                (
                    "r".into(),
                    ClauseBinding {
                        sort: ClauseSort::Bool,
                        place: ClausePlace::ResultSlot { index: 0 },
                    },
                ),
            ],
        ),
        (1, "entry", kind, "(x : bool) == true", vec![param]),
    ] {
        let mut formula = ProofFormula::new("trust-wp.pure-expr.v1", payload);
        formula.bindings = bindings;
        let source = SourceLocation {
            file: Some("identity.rs".into()),
            line: Some(index + 1),
            column: Some(1),
            end_line: Some(index + 1),
            end_column: Some(2),
        };
        public.contracts.push(TrustContract {
            contract_id: contract_id.into(),
            kind: role,
            predicate: ContractPredicate::CanonicalJson {
                schema: formula.schema.clone(),
                value: formula.payload.clone().into(),
            },
            source: source.clone(),
            metadata: vec![MetadataEntry {
                key: TRUST_IR_CLAUSE_BINDINGS_METADATA_KEY.into(),
                value: serde_json::to_string(&formula.bindings).unwrap(),
            }],
        });
        let context = ObligationContext::new(
            ObligationProducer::Compatibility,
            ObligationOrigin::Contract {
                contract_id: contract_id.into(),
                contract_kind: role,
                contract_index: index as usize,
                predicate_schema: Some(formula.schema.clone()),
            },
        )
        .with_function(FunctionContext { crate_name: "test".into(), path: "identity".into() });
        public.obligations.push(TrustObligation {
            obligation_id: format!("obligation:{contract_id}"),
            kind: if index == 0 {
                ObligationKind::Postcondition
            } else {
                ObligationKind::Precondition
            },
            contract_id: Some(contract_id.into()),
            proof_item_id: None,
            source,
            description: format!("original {contract_id}"),
            required_strength: None,
            summary_facts: vec![],
            metadata: vec![context.to_metadata_entry().unwrap()],
        });
        module.proof_obligations.push(
            ProofObligation::new(
                ProofId::new(index),
                if index == 0 {
                    trust_ir::ObligationKind::Postcondition
                } else {
                    trust_ir::ObligationKind::Precondition
                },
                ProofStatus::Pending,
                format!("original {contract_id}"),
            )
            .with_function(FuncId::new(0))
            .with_formula(formula)
            .with_source(
                ProofObligationSourceIdentity::new(
                    contract_id,
                    format!("trust-assertion:{contract_id}"),
                )
                .with_range(ProofObligationSourceRange {
                    file,
                    start_line: index + 1,
                    start_col: 1,
                    end_line: index + 1,
                    end_col: 2,
                }),
            ),
        );
    }
    let mut native = NativeVerificationBundle::new(
        NativeBundleProducer::TrustIr,
        NativeAdapterInput::TrustIrModule,
        module.stable_digest(),
        module,
        ProofLineageManifest::new(),
    );
    native.provenance.source_language = NativeSourceLanguage::TrustIr;
    native.provenance.source_languages =
        std::collections::BTreeSet::from([NativeSourceLanguage::TrustIr]);
    let replay = ProofReplayIdentity::new("trust_wp", "correspondence-only")
        .with_transcript_digest(ProofDigest::sha256([9; 32]));
    let mut node = ProofLineageNode::new(
        ProofLineageId::new(0),
        ProofTransform::new(ProofTransformStage::TrustIrLowering, "identity", "test", "1"),
        native.trust_ir_module_digest,
        native.trust_ir_module_digest,
    );
    node.obligations = vec![ProofId::new(0), ProofId::new(1)];
    node.replay = Some(replay.clone());
    native.lineage.nodes.push(node);
    native.lineage.roots.push(ProofLineageId::new(0));
    for index in 0..2 {
        native.compiler_facts.obligation_sources.push(NativeObligationSource {
            obligation: ProofId::new(index),
            public_obligation_id: public.obligations[index as usize].obligation_id.clone(),
            function: Some(FuncId::new(0)),
            span: Some(SourceSpan { file, line: index + 1, col: 1 }),
            assertion_id: Some(NativeAssertionId::new(index)),
            cause: if index == 0 {
                NativeObligationCause::Postcondition
            } else {
                NativeObligationCause::Precondition
            },
            monomorphization: None,
            facts: vec![],
        });
    }
    native.requests.push(NativeVerificationRequest::TrustWp(TrustWpNativeRequest {
        id: NativeRequestId::new(0),
        mode: TrustWpVerificationMode::WeakestPrecondition,
        function: FuncId::new(0),
        obligations: vec![ProofId::new(0)],
        lineage_roots: vec![ProofLineageId::new(0)],
        options: TrustWpRequestOptions::default(),
        diagnostics: NativeDiagnosticsPolicy::default(),
        provenance: NativeRequestProvenance::trust_wp(NativeToolIdentity::new("trust_wp"))
            .with_solver(NativeToolIdentity::new("ay"))
            .with_replay(replay),
    }));
    refresh(&public, &mut native);
    (public, native)
}

fn refresh(public: &TrustContractBundle, native: &mut NativeVerificationBundle) {
    for proof in &mut native.module.proof_obligations {
        let source = proof.source.as_mut().unwrap();
        let original = public.obligations.iter().find(|obligation| {
            obligation.contract_id.as_deref() == Some(source.source_id.as_str())
        });
        if let Some(original) = original {
            let digest = public.canonical_obligation_semantic_digest_sha256(original).unwrap();
            source.public = Some(PublicObligationIdentity {
                obligation_id: original.obligation_id.clone(),
                semantic_digest: ProofDigest::sha256(std::array::from_fn(|i| {
                    u8::from_str_radix(&digest[2 * i..2 * i + 2], 16).unwrap()
                })),
            });
        }
    }
    native.trust_ir_module_digest = native.module.stable_digest();
    for node in &mut native.lineage.nodes {
        node.source_module = native.trust_ir_module_digest;
        node.target_module = native.trust_ir_module_digest;
    }
}

fn seal(public: &TrustContractBundle, native: &NativeVerificationBundle) -> Result<String, String> {
    let admitted = trust_ir::ValidatedNativeBundle::new(native)
        .expect("every correspondence control must first pass canonical structural admission");
    let question = NativePublicQuestion::new(public, &admitted, "obligation:post")?;
    assert_eq!(question.entry_preconditions(FuncId::new(0)).count(), 1);
    Ok(question.digest_sha256().into())
}

#[test]
fn exact_requires_and_assumes_seal_original_formulas_without_mutating_inputs() {
    for kind in [ContractKind::Requires, ContractKind::Assumes] {
        let (public, native) = fixture(kind);
        let before = (public.clone(), native.stable_digest());
        assert_eq!(seal(&public, &native).unwrap().len(), 64);
        assert_eq!(public, before.0);
        assert_eq!(native.stable_digest(), before.1);
    }
}

#[test]
fn typed_source_precondition_uses_the_existing_canonical_formula_owner() {
    let (mut public, mut native) = fixture(ContractKind::Requires);
    let predicate = TrustSpecPredicate::new(
        TrustSpecExpr::variable("x", TrustSpecSort::Bool),
        vec![TrustSpecVariable {
            name: "x".into(),
            sort: TrustSpecSort::Bool,
            origin: TrustSpecVariableOrigin::Local { index: 0 },
        }],
    );
    public.contracts[1].predicate = predicate.clone().into_contract_predicate().unwrap();
    let formula = native.module.proof_obligations[1].formula.as_mut().unwrap();
    formula.schema = trust_types::trust_formula_v1::TRUST_WP_TRUST_FORMULA_SCHEMA_VERSION.into();
    formula.payload = trust_verifier_api::trust_spec_native_formula::trust_spec_predicate_to_trust_formula_payload(&predicate).unwrap();
    refresh(&public, &mut native);
    seal(&public, &native).unwrap();
}

#[test]
fn public_only_changed_or_removed_premise_cannot_reuse_the_old_question() {
    let (public, native) = fixture(ContractKind::Requires);
    seal(&public, &native).unwrap();
    let mut changed = public.clone();
    changed.contracts[1].predicate = ContractPredicate::CanonicalJson {
        schema: "trust-wp.pure-expr.v1".into(),
        value: "(x : bool) == false".into(),
    };
    assert!(seal(&changed, &native).is_err());
    let mut removed = public;
    removed.contracts.pop();
    removed.obligations.pop();
    assert!(seal(&removed, &native).unwrap_err().contains("no exact public declaration"));
}

#[test]
fn coherently_changed_premise_has_a_different_complete_question_identity() {
    let (mut public, mut native) = fixture(ContractKind::Requires);
    let original = seal(&public, &native).unwrap();
    public.contracts[1].predicate = ContractPredicate::CanonicalJson {
        schema: "trust-wp.pure-expr.v1".into(),
        value: "(x : bool) == false".into(),
    };
    native.module.proof_obligations[1].formula.as_mut().unwrap().payload =
        "(x : bool) == false".into();
    refresh(&public, &mut native);
    assert_ne!(seal(&public, &native).unwrap(), original);
}

#[test]
fn forged_function_context_or_contract_role_is_not_an_entry_domain() {
    for change in 0..3 {
        let (mut public, mut native) = fixture(ContractKind::Requires);
        let entry = &mut public.obligations[1].metadata[0];
        let mut context = ObligationContext::from_metadata_entry(entry).unwrap().unwrap();
        match change {
            0 => context.function.as_mut().unwrap().path = "other_function".into(),
            1 => {
                context.origin = ObligationOrigin::Contract {
                    contract_id: "entry".into(),
                    contract_kind: ContractKind::Ensures,
                    contract_index: 1,
                    predicate_schema: None,
                }
            }
            _ => context.function = None,
        }
        *entry = context.to_metadata_entry().unwrap();
        refresh(&public, &mut native);
        assert!(seal(&public, &native).is_err(), "forgery {change}");
    }
}

#[test]
fn rehashed_native_formula_or_nonparameter_binding_does_not_override_public_source() {
    for change in 0..3 {
        let (mut public, mut native) = fixture(ContractKind::Requires);
        let formula = native.module.proof_obligations[1].formula.as_mut().unwrap();
        match change {
            0 => formula.payload = "true".into(),
            1 => formula.bindings[0].1.place = ClausePlace::ResultSlot { index: 0 },
            _ => formula.bindings[0].1.place = ClausePlace::Param { index: 9 },
        }
        if change != 0 {
            // Even a coherently forged public map cannot name a result or a
            // nonexistent original parameter as an entry input.
            public.contracts[1].metadata[0].value =
                serde_json::to_string(&formula.bindings).unwrap();
        }
        refresh(&public, &mut native);
        assert!(seal(&public, &native).is_err(), "forgery {change}");
    }
}

#[test]
fn native_precondition_metadata_without_its_original_public_contract_refuses() {
    let (mut public, mut native) = fixture(ContractKind::Requires);
    public.contracts[1].kind = ContractKind::Asserts;
    refresh(&public, &mut native);
    assert!(seal(&public, &native).unwrap_err().contains("no exact public declaration"));
}

#[test]
fn replay_assumption_atoms_cannot_mint_or_replace_declared_entry_preconditions() {
    let (public, mut native) = fixture(ContractKind::Requires);
    let NativeVerificationRequest::TrustWp(request) = &mut native.requests[0] else {
        unreachable!();
    };
    request.provenance.replay_context.atoms.push(
        NativeReplayAtom::assumption(
            NativeReplayAtomId::new(0),
            ProofFormula::smtlib2("false", "Bool"),
        )
        .with_obligation(ProofId::new(0)),
    );
    let admitted = trust_ir::ValidatedNativeBundle::new(&native).unwrap();
    let question = NativePublicQuestion::new(&public, &admitted, "obligation:post").unwrap();
    let entries: Vec<_> = question.entry_preconditions(FuncId::new(0)).collect();
    assert_eq!(entries.len(), 1);
    assert_eq!(entries[0].proof().formula.as_ref().unwrap().payload, "(x : bool) == true");
    // Selected engine admission still owes its existing replay-context
    // refusal. The core correspondence token grants no atom authority.
}

#[test]
fn unconditional_question_remains_unconditional_without_an_entry_carrier() {
    let (mut public, mut native) = fixture(ContractKind::Requires);
    public.contracts.pop();
    public.obligations.pop();
    native.module.proof_obligations.pop();
    native.compiler_facts.obligation_sources.pop();
    native.lineage.nodes[0].obligations.pop();
    refresh(&public, &mut native);
    let admitted = trust_ir::ValidatedNativeBundle::new(&native).unwrap();
    let question = NativePublicQuestion::new(&public, &admitted, "obligation:post").unwrap();
    assert!(!question.has_entry_preconditions());
    assert_eq!(question.entry_preconditions(FuncId::new(0)).count(), 0);
}

fn entry_on_callee(
    public: &mut TrustContractBundle,
    native: &mut NativeVerificationBundle,
    foreign: bool,
) {
    let mut callee = native.module.functions[0].clone();
    callee.id = FuncId::new(1);
    callee.name = "callee".into();
    callee.display_path = Some(if foreign { "dependency::callee" } else { "test::callee" }.into());
    native.module.try_add_function(callee).unwrap();
    native.module.proof_obligations[1].function = Some(FuncId::new(1));
    native.compiler_facts.obligation_sources[1].function = Some(FuncId::new(1));
    let entry = &mut public.obligations[1].metadata[0];
    let mut context = ObligationContext::from_metadata_entry(entry).unwrap().unwrap();
    context.function = Some(FunctionContext {
        crate_name: if foreign { "dependency" } else { "test" }.into(),
        path: if foreign { "dependency::callee" } else { "test::callee" }.into(),
    });
    *entry = context.to_metadata_entry().unwrap();
    refresh(public, native);
}

#[test]
fn unconditional_scope_retains_original_non_root_entry_obligations() {
    let (mut public, mut native) = fixture(ContractKind::Requires);
    entry_on_callee(&mut public, &mut native, false);
    let original = native.clone();
    let admitted = trust_ir::ValidatedNativeBundle::new(&native).unwrap();
    for scope in [NativePublicProofScope::Unconditional, NativePublicProofScope::DeclaredEntry] {
        let question =
            NativePublicQuestion::for_derivation(&public, &admitted, "obligation:post", scope)
                .unwrap();
        assert_eq!(question.entry_preconditions(FuncId::new(0)).count(), 0);
        assert_eq!(question.entry_preconditions(FuncId::new(1)).count(), 1);
        assert_eq!(
            question.entry_preconditions(FuncId::new(1)).next().unwrap().proof().id,
            ProofId::new(1)
        );
    }
    assert_eq!(native, original);
    let entry = &mut public.obligations[1].metadata[0];
    let mut forged = ObligationContext::from_metadata_entry(entry).unwrap().unwrap();
    forged.function.as_mut().unwrap().path = "identity".into();
    *entry = forged.to_metadata_entry().unwrap();
    refresh(&public, &mut native);
    let admitted = trust_ir::ValidatedNativeBundle::new(&native).unwrap();
    assert!(
        NativePublicQuestion::for_derivation(
            &public,
            &admitted,
            "obligation:post",
            NativePublicProofScope::Unconditional
        )
        .is_err(),
        "a forged root context must not hide the original callee carrier"
    );
}

#[test]
fn unconditional_scope_refuses_a_missing_original_callee_entry_carrier() {
    let (mut public, mut native) = fixture(ContractKind::Requires);
    entry_on_callee(&mut public, &mut native, false);
    let admitted = trust_ir::ValidatedNativeBundle::new(&native).unwrap();
    NativePublicQuestion::for_derivation(
        &public,
        &admitted,
        "obligation:post",
        NativePublicProofScope::Unconditional,
    )
    .unwrap();
    native.module.proof_obligations.pop();
    native.compiler_facts.obligation_sources.pop();
    native.lineage.nodes[0].obligations.pop();
    refresh(&public, &mut native);
    let admitted = trust_ir::ValidatedNativeBundle::new(&native).unwrap();
    assert!(
        NativePublicQuestion::for_derivation(
            &public,
            &admitted,
            "obligation:post",
            NativePublicProofScope::Unconditional
        )
        .is_err()
    );
}

#[test]
fn a_caller_owned_callsite_precondition_is_not_an_omittable_root_entry() {
    let (public, mut native) = fixture(ContractKind::Requires);
    let mut callee = native.module.functions[0].clone();
    callee.id = FuncId::new(1);
    callee.name = "callee".into();
    callee.display_path = Some("test::callee".into());
    native.module.try_add_function(callee).unwrap();
    native.module.functions[0].blocks[0].body.insert(
        0,
        InstrNode::new(Inst::Call { callee: FuncId::new(1), args: vec![ValueId::new(0)] })
            .with_result(ValueId::new(1)),
    );
    native.module.proof_obligations[1].site =
        Some(trust_ir::proof::ObligationSite::new(FuncId::new(0), BlockId::new(0), 0));
    refresh(&public, &mut native);
    let admitted = trust_ir::ValidatedNativeBundle::new(&native)
        .expect("original typed call-site carrier is structurally admitted");
    assert!(
        matches!(&native.module.functions[0].blocks[0].body[0].inst,Inst::Call { callee,.. } if *callee == FuncId::new(1))
    );
    for scope in [NativePublicProofScope::Unconditional, NativePublicProofScope::DeclaredEntry] {
        assert!(
            NativePublicQuestion::for_derivation(&public, &admitted, "obligation:post", scope)
                .is_err(),
            "a call-site condition is owed, never an omitted root declaration: {scope:?}"
        );
    }
}

#[test]
fn unsupported_root_declaration_does_not_erase_an_independently_matched_callee_entry() {
    let (mut public, mut native) = fixture(ContractKind::Requires);
    let mut root_contract = public.contracts[1].clone();
    let mut root_obligation = public.obligations[1].clone();
    entry_on_callee(&mut public, &mut native, false);
    root_contract.contract_id = "unsupported-root".into();
    root_contract.predicate = ContractPredicate::CanonicalJson {
        schema: "unsupported.root.v1".into(),
        value: "original unsupported root declaration".into(),
    };
    root_obligation.obligation_id = "obligation:unsupported-root".into();
    root_obligation.contract_id = Some(root_contract.contract_id.clone());
    let mut context =
        ObligationContext::from_metadata_entry(&root_obligation.metadata[0]).unwrap().unwrap();
    if let ObligationOrigin::Contract { contract_id, contract_index, .. } = &mut context.origin {
        *contract_id = root_contract.contract_id.clone();
        *contract_index = 2;
    } else {
        unreachable!()
    }
    root_obligation.metadata[0] = context.to_metadata_entry().unwrap();
    public.contracts.push(root_contract);
    public.obligations.push(root_obligation);
    let admitted = trust_ir::ValidatedNativeBundle::new(&native).unwrap();
    let bare = NativePublicQuestion::for_derivation(
        &public,
        &admitted,
        "obligation:post",
        NativePublicProofScope::Unconditional,
    )
    .unwrap();
    assert_eq!(bare.entry_preconditions(FuncId::new(0)).count(), 0);
    assert_eq!(bare.entry_preconditions(FuncId::new(1)).count(), 1);
    assert!(NativePublicQuestion::new(&public, &admitted, "obligation:post").is_err());
}

#[test]
fn callee_only_domain_does_not_allow_a_forged_selected_post_owner() {
    let (mut public, mut native) = fixture(ContractKind::Requires);
    entry_on_callee(&mut public, &mut native, false);
    let admitted = trust_ir::ValidatedNativeBundle::new(&native).unwrap();
    let question = NativePublicQuestion::new(&public, &admitted, "obligation:post").unwrap();
    assert_eq!(question.entry_preconditions(FuncId::new(0)).count(), 0);
    assert_eq!(question.entry_preconditions(FuncId::new(1)).count(), 1);
    let entry = &mut public.obligations[0].metadata[0];
    let mut context = ObligationContext::from_metadata_entry(entry).unwrap().unwrap();
    context.function.as_mut().unwrap().path = "callee".into();
    *entry = context.to_metadata_entry().unwrap();
    refresh(&public, &mut native);
    let admitted = trust_ir::ValidatedNativeBundle::new(&native).unwrap();
    assert!(NativePublicQuestion::new(&public, &admitted, "obligation:post").is_err());
}

#[test]
fn coherent_foreign_crate_relabeling_does_not_override_the_original_subject() {
    let (mut public, mut native) = fixture(ContractKind::Requires);
    for obligation in &mut public.obligations {
        let entry = &mut obligation.metadata[0];
        let mut context = ObligationContext::from_metadata_entry(entry).unwrap().unwrap();
        context.function.as_mut().unwrap().crate_name = "foreign".into();
        *entry = context.to_metadata_entry().unwrap();
    }
    refresh(&public, &mut native);
    assert!(seal(&public, &native).unwrap_err().contains("original public subject"));
}

#[test]
fn a_qualified_original_cross_crate_callee_keeps_its_own_entry_domain() {
    let (mut public, mut native) = fixture(ContractKind::Requires);
    entry_on_callee(&mut public, &mut native, true);
    let admitted = trust_ir::ValidatedNativeBundle::new(&native).unwrap();
    let question = NativePublicQuestion::new(&public, &admitted, "obligation:post").unwrap();
    assert_eq!(question.entry_preconditions(FuncId::new(0)).count(), 0);
    assert_eq!(question.entry_preconditions(FuncId::new(1)).count(), 1);
}

#[test]
fn unrelated_whole_crate_declaration_does_not_need_a_proof_in_this_native_unit() {
    let (mut public, native) = fixture(ContractKind::Requires);
    let original = seal(&public, &native).unwrap();
    let mut contract = public.contracts[1].clone();
    contract.contract_id = "unrelated-entry".into();
    public.contracts.push(contract);
    let mut obligation = public.obligations[1].clone();
    obligation.obligation_id = "obligation:unrelated-entry".into();
    obligation.contract_id = Some("unrelated-entry".into());
    let mut context =
        ObligationContext::from_metadata_entry(&obligation.metadata[0]).unwrap().unwrap();
    context.function.as_mut().unwrap().path = "unrelated".into();
    context.origin = ObligationOrigin::Contract {
        contract_id: "unrelated-entry".into(),
        contract_kind: ContractKind::Requires,
        contract_index: 2,
        predicate_schema: Some("trust-wp.pure-expr.v1".into()),
    };
    obligation.metadata[0] = context.to_metadata_entry().unwrap();
    public.obligations.push(obligation);
    // The irrelevant declaration does not narrow admission. Complete public
    // identity intentionally changes, without supplying another premise.
    assert_ne!(seal(&public, &native).unwrap(), original);
}

#[test]
fn same_crate_same_basename_does_not_relabel_an_original_callee() {
    let (mut public, mut native) = fixture(ContractKind::Requires);
    entry_on_callee(&mut public, &mut native, false);
    native.module.functions[1].display_path = Some("test::m1::callee".into());
    let entry = &mut public.obligations[1].metadata[0];
    let mut context = ObligationContext::from_metadata_entry(entry).unwrap().unwrap();
    context.function.as_mut().unwrap().path = "test::m1::callee".into();
    *entry = context.to_metadata_entry().unwrap();
    refresh(&public, &mut native);
    let admitted = trust_ir::ValidatedNativeBundle::new(&native).unwrap();
    NativePublicQuestion::new(&public, &admitted, "obligation:post").unwrap();
    let entry = &mut public.obligations[1].metadata[0];
    context.function.as_mut().unwrap().path = "test::m2::callee".into();
    *entry = context.to_metadata_entry().unwrap();
    refresh(&public, &mut native);
    let admitted = trust_ir::ValidatedNativeBundle::new(&native).unwrap();
    assert!(NativePublicQuestion::new(&public, &admitted, "obligation:post").is_err());
}

#[test]
fn original_selected_unit_identity_does_not_depend_on_a_bare_root_symbol() {
    let (mut public, mut native) = fixture(ContractKind::Requires);
    public.subject =
        BundleSubject::Function { crate_name: "test".into(), path: "test::identity".into() };
    native.module.name = "test::identity".into();
    for obligation in &mut public.obligations {
        let entry = &mut obligation.metadata[0];
        let mut context = ObligationContext::from_metadata_entry(entry).unwrap().unwrap();
        context.function.as_mut().unwrap().path = "test::identity".into();
        *entry = context.to_metadata_entry().unwrap();
    }
    refresh(&public, &mut native);
    seal(&public, &native).unwrap();
}

#[test]
fn repeated_qualified_path_does_not_select_or_conflate_monomorphized_instances() {
    let (mut public, mut native) = fixture(ContractKind::Requires);
    entry_on_callee(&mut public, &mut native, false);
    let mut other = native.module.functions[1].clone();
    other.id = FuncId::new(2);
    other.name = "other_monomorphization".into();
    native.module.try_add_function(other).unwrap();
    refresh(&public, &mut native);
    let admitted = trust_ir::ValidatedNativeBundle::new(&native).unwrap();
    let question = NativePublicQuestion::new(&public, &admitted, "obligation:post").unwrap();
    assert_eq!(question.entry_preconditions(FuncId::new(1)).count(), 1);
    assert_eq!(question.entry_preconditions(FuncId::new(2)).count(), 0);
    assert_eq!(
        question.entry_preconditions(FuncId::new(1)).next().unwrap().proof().function,
        Some(FuncId::new(1))
    );
}

#[test]
fn both_derivation_scopes_bind_one_question_and_only_conditioned_scope_exposes_premises() {
    let (public, native) = fixture(ContractKind::Requires);
    let admitted = trust_ir::ValidatedNativeBundle::new(&native).unwrap();
    let conditioned = NativePublicQuestion::new(&public, &admitted, "obligation:post").unwrap();
    let bare = NativePublicQuestion::for_derivation(
        &public,
        &admitted,
        "obligation:post",
        NativePublicProofScope::Unconditional,
    )
    .unwrap();
    assert_eq!(bare.digest_sha256(), conditioned.digest_sha256());
    assert_eq!(bare.proof_scope(), NativePublicProofScope::Unconditional);
    assert_eq!(bare.entry_preconditions(FuncId::new(0)).count(), 0);
    assert_eq!(conditioned.entry_preconditions(FuncId::new(0)).count(), 1);
}

#[test]
fn unsupported_requires_does_not_prevent_a_premise_free_question() {
    let (mut public, mut native) = fixture(ContractKind::Requires);
    public.contracts[1].predicate = ContractPredicate::CanonicalJson {
        schema: "unsupported.entry.codec.v1".into(),
        value: "arbitrary unsupported declaration".into(),
    };
    native.module.proof_obligations[1].formula.as_mut().unwrap().schema =
        "unsupported.entry.codec.v1".into();
    refresh(&public, &mut native);
    let admitted = trust_ir::ValidatedNativeBundle::new(&native).unwrap();
    assert!(NativePublicQuestion::new(&public, &admitted, "obligation:post").is_err());
    let bare = NativePublicQuestion::for_derivation(
        &public,
        &admitted,
        "obligation:post",
        NativePublicProofScope::Unconditional,
    )
    .unwrap();
    assert!(!bare.has_entry_preconditions());
    let old_digest = bare.digest_sha256().to_owned();
    public.contracts[1].predicate = ContractPredicate::CanonicalJson {
        schema: "unsupported.entry.codec.v1".into(),
        value: "changed unsupported declaration".into(),
    };
    let bare = NativePublicQuestion::for_derivation(
        &public,
        &admitted,
        "obligation:post",
        NativePublicProofScope::Unconditional,
    )
    .unwrap();
    assert_ne!(bare.digest_sha256(), old_digest);
}

#[test]
fn strategy_transport_annotations_are_not_an_alternate_entry_domain() {
    let (mut public, native) = fixture(ContractKind::Requires);
    let original = seal(&public, &native).unwrap();
    for obligation in &mut public.obligations {
        obligation.metadata.push(MetadataEntry {
            key: "trust.trust_ir.native.request_id".into(),
            value: "42".into(),
        });
    }
    assert_eq!(seal(&public, &native).unwrap(), original);
}

#[test]
fn an_unconditional_question_needs_no_usable_native_entry_carrier() {
    let (mut public, mut native) = fixture(ContractKind::Requires);
    public.obligations.pop();
    native.module.proof_obligations.pop();
    native.compiler_facts.obligation_sources.pop();
    native.lineage.nodes[0].obligations.pop();
    refresh(&public, &mut native);
    let admitted = trust_ir::ValidatedNativeBundle::new(&native).unwrap();
    assert!(NativePublicQuestion::new(&public, &admitted, "obligation:post").is_err());
    let bare = NativePublicQuestion::for_derivation(
        &public,
        &admitted,
        "obligation:post",
        NativePublicProofScope::Unconditional,
    )
    .unwrap();
    assert_eq!(bare.proof_scope(), NativePublicProofScope::Unconditional);
    assert!(!bare.has_entry_preconditions());
}

#[test]
fn missing_precondition_on_a_bare_callee_is_not_silently_classified_outside() {
    let (mut public, mut native) = fixture(ContractKind::Requires);
    let mut callee = native.module.functions[0].clone();
    callee.id = FuncId::new(1);
    callee.name = "callee".into();
    native.module.try_add_function(callee).unwrap();
    native.module.proof_obligations.pop();
    native.compiler_facts.obligation_sources.pop();
    native.lineage.nodes[0].obligations.pop();
    let entry = &mut public.obligations[1].metadata[0];
    let mut context = ObligationContext::from_metadata_entry(entry).unwrap().unwrap();
    context.function.as_mut().unwrap().path = "test::callee".into();
    *entry = context.to_metadata_entry().unwrap();
    refresh(&public, &mut native);
    let admitted = trust_ir::ValidatedNativeBundle::new(&native).unwrap();
    let error = NativePublicQuestion::new(&public, &admitted, "obligation:post").unwrap_err();
    assert!(error.contains("unidentified native function"), "{error}");
    let error = NativePublicQuestion::for_derivation(
        &public,
        &admitted,
        "obligation:post",
        NativePublicProofScope::Unconditional,
    )
    .unwrap_err();
    assert!(error.contains("unidentified native function"), "{error}");
}

#[test]
fn absent_post_context_cannot_exempt_an_unidentified_selected_root() {
    let (mut public, mut native) = fixture(ContractKind::Requires);
    public.obligations[0].metadata.clear();
    native.module.proof_obligations.pop();
    native.compiler_facts.obligation_sources.pop();
    native.lineage.nodes[0].obligations.pop();
    let entry = &mut public.obligations[1].metadata[0];
    let mut context = ObligationContext::from_metadata_entry(entry).unwrap().unwrap();
    context.function.as_mut().unwrap().path = "test::identity".into();
    *entry = context.to_metadata_entry().unwrap();
    refresh(&public, &mut native);
    let admitted = trust_ir::ValidatedNativeBundle::new(&native).unwrap();
    let error = NativePublicQuestion::new(&public, &admitted, "obligation:post").unwrap_err();
    assert!(error.contains("unidentified native function"), "{error}");
    let bare = NativePublicQuestion::for_derivation(
        &public,
        &admitted,
        "obligation:post",
        NativePublicProofScope::Unconditional,
    )
    .unwrap();
    assert!(!bare.has_entry_preconditions());
    // A genuinely empty domain needs no invented context or premise.
    public.contracts.pop();
    public.obligations.pop();
    refresh(&public, &mut native);
    let admitted = trust_ir::ValidatedNativeBundle::new(&native).unwrap();
    let empty = NativePublicQuestion::new(&public, &admitted, "obligation:post").unwrap();
    assert!(!empty.has_entry_preconditions());
}
