//! Integration checks run the real body-WP engine behind an inconclusive primary.

use super::*;

#[path = "native_wp_tests/archived_envelopes.rs"]
mod archived_envelopes;
use archived_envelopes::{assert_archived_schema8_input, derived_current_native_input};

fn fixture(negate: bool) -> (TrustContractBundle, NativeVerificationBundle) {
    fixture_with_requirement(negate, None)
}

fn fixture_with_requirement(
    negate: bool,
    required: Option<ProofStrength>,
) -> (TrustContractBundle, NativeVerificationBundle) {
    use trust_ir::proof::{ClauseBinding, ClausePlace, ClauseSort};
    const CLAIM: &str = "(r : bool) == (x : bool)";
    let bindings = vec![
        (
            "x".into(),
            ClauseBinding { sort: ClauseSort::Bool, place: ClausePlace::Param { index: 0 } },
        ),
        (
            "r".into(),
            ClauseBinding { sort: ClauseSort::Bool, place: ClausePlace::ResultSlot { index: 0 } },
        ),
    ];
    let mut obligation =
        native_trust_ir_obligation("trust-mc", 0, 0, ObligationKind::Postcondition, required);
    obligation.contract_id = Some("boolean-contract".into());
    obligation.source = SourceLocation {
        file: Some("body-wp.rs".into()),
        line: Some(1),
        column: Some(9),
        end_line: Some(1),
        end_column: Some(19),
    };
    let mut public = TrustContractBundle::empty(
        "body-wp",
        BundleSubject::Function { crate_name: "test".into(), path: "identity".into() },
    );
    public.contracts.push(TrustContract {
        contract_id: "boolean-contract".into(),
        kind: ContractKind::Ensures,
        predicate: ContractPredicate::CanonicalJson {
            schema: "trust-wp.pure-expr.v1".into(),
            value: serde_json::Value::String(CLAIM.into()),
        },
        source: SourceLocation::default(),
        metadata: vec![MetadataEntry {
            key: trust_verifier_api::TRUST_IR_CLAUSE_BINDINGS_METADATA_KEY.into(),
            value: serde_json::to_string(&bindings).unwrap(),
        }],
    });
    public.obligations.push(obligation.clone());
    let digest = public.canonical_obligation_semantic_digest_sha256(&obligation).unwrap();
    let digest = trust_ir::ProofDigest::sha256(std::array::from_fn(|i| {
        u8::from_str_radix(&digest[2 * i..2 * i + 2], 16).unwrap()
    }));
    let mut module = trust_ir::Module::new("body-wp");
    let file = module.intern_file("body-wp.rs").unwrap();
    let function_id = trust_ir::FuncId::new(0);
    let signature = module
        .add_func_type(trust_ir::FuncTy {
            params: vec![trust_ir::Ty::Bool],
            returns: vec![trust_ir::Ty::Bool],
            is_vararg: false,
            abi: None,
        })
        .unwrap();
    let block_id = trust_ir::BlockId::new(0);
    let argument = trust_ir::ValueId::new(0);
    let returned = trust_ir::ValueId::new(3);
    let mut block = trust_ir::Block::new(block_id).with_param(argument, trust_ir::Ty::Bool);
    if negate {
        for (id, value) in [(1, false), (2, true)] {
            block.body.push(
                trust_ir::InstrNode::new(trust_ir::Inst::Const {
                    ty: trust_ir::Ty::Bool,
                    value: trust_ir::Constant::Bool(value),
                })
                .with_result(trust_ir::ValueId::new(id)),
            );
        }
    }
    block.body.push(
        trust_ir::InstrNode::new(if negate {
            trust_ir::Inst::Select {
                ty: trust_ir::Ty::Bool,
                cond: argument,
                then_val: trust_ir::ValueId::new(1),
                else_val: trust_ir::ValueId::new(2),
            }
        } else {
            trust_ir::Inst::Copy { ty: trust_ir::Ty::Bool, operand: argument }
        })
        .with_result(returned),
    );
    block.body.push(trust_ir::InstrNode::new(trust_ir::Inst::Return { values: vec![returned] }));
    let mut function = trust_ir::Function::new(function_id, "identity", signature, block_id)
        .with_producer(trust_ir::Producer::TrustIr);
    function.blocks.push(block);
    module.try_add_function(function).unwrap();
    let mut formula = trust_ir::ProofFormula::new("trust-wp.pure-expr.v1", CLAIM);
    formula.bindings = bindings;
    module.proof_obligations.push(
        trust_ir::ProofObligation::new(
            trust_ir::ProofId::new(0),
            trust_ir::ObligationKind::Postcondition,
            trust_ir::ProofStatus::Pending,
            "returns its Boolean argument",
        )
        .with_function(function_id)
        .with_formula(formula)
        .with_source(router_native_obligation_source_identity(
            trust_ir::ProofId::new(0),
            &obligation.obligation_id,
            file,
            1,
            digest,
        )),
    );
    let source = module.proof_obligations[0].source.as_mut().unwrap();
    source.source_id = obligation.contract_id.clone().unwrap();
    source.assertion_id = format!("trust-assertion:{}", source.source_id);
    let native =
        native_verification_bundle_from_module(module, native_trust_ir_digest(1), function_id)
            .unwrap();
    (public, native)
}

fn configured_engines(
    primary_status: EvidenceStatus,
) -> Vec<Box<dyn VerificationEngine + Send + Sync>> {
    let mut engines = required_native_engines();
    let index = engines.iter().position(|engine| engine.manifest().name == "trust-mc").unwrap();
    engines[index] = Box::new(UnitEngine::new(
        "trust-mc",
        EngineKind::Reachability,
        ObligationKind::Postcondition,
        SupportLevel::Supported,
        UnitEvidenceMode::Evidence {
            status: primary_status,
            proof_strength: None,
            artifacts: vec![],
            diagnostics: vec!["controlled primary outcome".into()],
        },
    ));
    engines
}

fn engine(primary_status: EvidenceStatus) -> FullVerificationEngine {
    FullVerificationEngine::new(
        configured_engines(primary_status),
        FullVerificationPolicy::default(),
    )
}

#[test]
fn native_body_wp_discharges_unknown_primary_with_bound_replayed_evidence() {
    let (public, native) = fixture(false);
    let result = engine(EvidenceStatus::Unknown).verify_obligations_with_native_trust_ir_bundle(
        &public,
        &public.obligations,
        &native,
        &VerifierExecutionContext::new("native-body-wp"),
    );
    assert_eq!(result.summary.proved, 1, "{result:#?}");
    assert!(result.evidence[0].satisfies_proof_artifact_policy(), "{result:#?}");
    assert_eq!(result.evidence[0].proof_strength, Some(ProofStrength::deductive()));
    assert!(result.evidence[0].diagnostics.iter().any(|text| text.contains("deductive fallback")));
    assert!(
        result.evidence[0]
            .artifacts
            .iter()
            .any(|artifact| artifact.kind == EvidenceArtifactKind::ProofCertificate)
    );
}

#[test]
fn native_body_wp_checked_fact_is_reusable_only_for_its_exact_inputs() {
    let (public, native) = fixture(false);
    let live = engine(EvidenceStatus::Unknown)
        .verify_obligations_with_native_trust_ir_bundle_and_fresh_receipts(
            &public,
            &public.obligations,
            &native,
            &VerifierExecutionContext::new("checked-wp-fact"),
        );
    assert_eq!(live.checked_native_wp_proofs().len(), 1);
    let (result, mut receipts) = live.into_parts();
    let facts = receipts.take_checked_native_wp_proofs();
    assert!(receipts.checked_native_wp_proofs().is_empty());
    let fact = facts[&public.obligations[0].obligation_id].clone();
    let obligation = &public.obligations[0];
    let evidence = &result.evidence[0];
    assert_eq!(fact.proof_strength(), ProofStrength::deductive());
    let selected = native
        .requests
        .iter()
        .find_map(|request| match request {
            trust_ir::NativeVerificationRequest::TrustWp(request)
                if request.id.index() == fact.native_request_id() =>
            {
                Some(request)
            }
            _ => None,
        })
        .expect("checked fact names the actual WP request");
    assert_eq!(selected.obligations, [trust_ir::ProofId::new(fact.native_proof_id())]);
    assert!(fact.matches(&public, &native, obligation, evidence));
    assert!(fact.clone().matches(&public.clone(), &native.clone(), obligation, evidence));

    let mut changed_native = native.clone();
    changed_native.module.functions[0].name.push_str("_changed");
    assert!(!fact.matches(&public, &changed_native, obligation, evidence));
    let mut changed_public = public.clone();
    changed_public.bundle_id.push_str("_changed");
    assert!(!fact.matches(&changed_public, &native, obligation, evidence));
    let mut changed_row = evidence.clone();
    changed_row.evidence_id.push_str("_changed");
    assert!(!fact.matches(&public, &native, obligation, &changed_row));
    let mut changed_contract = public.clone();
    changed_contract.contracts[0].metadata[0].value = "[]".into();
    assert!(!fact.matches(&changed_contract, &native, obligation, evidence));
}

#[test]
fn native_body_wp_false_or_cancelled_work_mints_no_checked_fact() {
    for cancelled in [false, true] {
        let (public, native) = fixture(!cancelled);
        let context = VerifierExecutionContext::new("no-checked-wp-fact");
        if cancelled {
            context.cancellation.cancel(trust_verifier_api::CancellationReason::UserRequested);
        }
        let live = engine(EvidenceStatus::Unknown)
            .verify_obligations_with_native_trust_ir_bundle_and_fresh_receipts(
                &public,
                &public.obligations,
                &native,
                &context,
            );
        assert_eq!(live.result().summary.proved, 0);
        assert!(live.checked_native_wp_proofs().is_empty());
    }
}

#[test]
fn native_body_wp_real_primary_can_use_body_proof_without_a_chc_payload() {
    for negate in [false, true] {
        let (public, native) = fixture(negate);
        let mut module = native.module;
        // The compiler records this annotation on the real Boolean sources.
        // Body semantics, not the annotation, must justify either verdict.
        module.functions[0].proofs.push(trust_ir::ProofAnnotation::Pure);
        let digest =
            public.canonical_obligation_semantic_digest_sha256(&public.obligations[0]).unwrap();
        module.proof_obligations[0]
            .source
            .as_mut()
            .unwrap()
            .public
            .as_mut()
            .unwrap()
            .semantic_digest = trust_ir::ProofDigest::sha256(std::array::from_fn(|i| {
            u8::from_str_radix(&digest[2 * i..2 * i + 2], 16).unwrap()
        }));
        let native = native_verification_bundle_from_module(
            module,
            native_trust_ir_digest(1),
            trust_ir::FuncId::new(0),
        )
        .unwrap();
        let live = FullVerificationEngine::with_required_native_engines_timeout_ms(5_000)
            .verify_obligations_with_native_trust_ir_bundle_and_fresh_receipts(
                &public,
                &public.obligations,
                &native,
                &VerifierExecutionContext::new("native-primary-body-wp"),
            );
        assert_eq!(live.result().summary.proved, usize::from(!negate), "{:#?}", live.result());
        assert_eq!(live.checked_native_wp_proofs().len(), usize::from(!negate));
        if negate {
            assert_eq!(
                live.result().evidence[0].status,
                EvidenceStatus::Failed,
                "{:#?}",
                live.result()
            );
        }
    }
}

#[test]
fn native_body_wp_real_primary_checks_unsigned_select_with_the_original_boolean_question() {
    for (ty, maximum) in [
        (trust_ir::Ty::U8, u64::from(u8::MAX)),
        (trust_ir::Ty::U32, u64::from(u32::MAX)),
        (trust_ir::Ty::U64, u64::MAX),
    ] {
        for swapped in [false, true] {
            let (public, original) = fixture(false);
            let original_formula = original.module.proof_obligations[0].formula.clone();
            let mut module = original.module;
            // Match the compiler's producer record; WP still checks the body.
            module.functions[0].proofs.push(trust_ir::ProofAnnotation::Pure);
            let block = &mut module.functions[0].blocks[0];
            block.body = vec![
                trust_ir::InstrNode::new(trust_ir::Inst::Const {
                    ty: ty.clone(),
                    value: trust_ir::Constant::Int(0),
                })
                .with_result(trust_ir::ValueId::new(1)),
                trust_ir::InstrNode::new(trust_ir::Inst::Const {
                    ty: ty.clone(),
                    value: trust_ir::Constant::Int(i128::from(maximum)),
                })
                .with_result(trust_ir::ValueId::new(2)),
                trust_ir::InstrNode::new(trust_ir::Inst::Select {
                    ty: ty.clone(),
                    cond: trust_ir::ValueId::new(0),
                    then_val: trust_ir::ValueId::new(if swapped { 2 } else { 1 }),
                    else_val: trust_ir::ValueId::new(if swapped { 1 } else { 2 }),
                })
                .with_result(trust_ir::ValueId::new(3)),
                trust_ir::InstrNode::new(trust_ir::Inst::ICmp {
                    op: trust_ir::ICmpOp::Eq,
                    ty: ty.clone(),
                    lhs: trust_ir::ValueId::new(3),
                    rhs: trust_ir::ValueId::new(1),
                })
                .with_result(trust_ir::ValueId::new(4)),
                trust_ir::InstrNode::new(trust_ir::Inst::Return {
                    values: vec![trust_ir::ValueId::new(4)],
                }),
            ];
            assert_eq!(module.proof_obligations[0].formula, original_formula);
            let native = native_verification_bundle_from_module(
                module,
                native_trust_ir_digest(1),
                trust_ir::FuncId::new(0),
            )
            .unwrap();
            native.validate().unwrap();
            let live = FullVerificationEngine::with_required_native_engines_timeout_ms(5_000)
                .verify_obligations_with_native_trust_ir_bundle_and_fresh_receipts(
                    &public,
                    &public.obligations,
                    &native,
                    &VerifierExecutionContext::new("native-primary-unsigned-select"),
                );
            assert_eq!(
                live.result().summary.proved,
                usize::from(!swapped),
                "type={ty:?}, swapped={swapped}: {:#?}",
                live.result()
            );
            assert_eq!(live.checked_native_wp_proofs().len(), usize::from(!swapped));
            let obligation = &public.obligations[0];
            let evidence = &live.result().evidence[0];
            if swapped {
                assert_eq!(evidence.status, EvidenceStatus::Failed, "{:#?}", live.result());
            } else {
                assert!(evidence.satisfies_proof_artifact_policy(), "{evidence:#?}");
                assert_eq!(evidence.proof_strength, Some(ProofStrength::deductive()));
                let fact = &live.checked_native_wp_proofs()[&obligation.obligation_id];
                let request = native.requests.iter().find_map(|request| match request {
                    trust_ir::NativeVerificationRequest::TrustWp(request)
                        if request.id.index() == fact.native_request_id() =>
                    {
                        Some(request)
                    }
                    _ => None,
                });
                assert_eq!(
                    request.expect("checked fact names the actual WP request").obligations,
                    [trust_ir::ProofId::new(fact.native_proof_id())]
                );
                assert!(fact.matches(&public, &native, obligation, evidence));
            }
        }
    }
}

#[test]
fn native_body_wp_checks_original_public_typed_specification() {
    use trust_verifier_api::{
        TrustSpecBinaryOp, TrustSpecExpr, TrustSpecPredicate, TrustSpecSort, TrustSpecVariable,
        TrustSpecVariableOrigin,
    };
    for negate in [false, true] {
        let (mut public, mut native) = fixture(negate);
        let predicate = TrustSpecPredicate::new(
            TrustSpecExpr::binary(
                TrustSpecBinaryOp::Eq,
                TrustSpecExpr::result(TrustSpecSort::Bool),
                TrustSpecExpr::variable("x", TrustSpecSort::Bool),
            ),
            vec![TrustSpecVariable {
                name: "x".into(),
                sort: TrustSpecSort::Bool,
                origin: TrustSpecVariableOrigin::Local { index: 1 },
            }],
        );
        public.contracts[0].predicate = predicate.clone().into_contract_predicate().unwrap();
        let original = public.contracts[0].predicate.clone();
        let mut formula = trust_wp::trust_wp_native_formula_from_trust_spec(&predicate).unwrap();
        formula.bindings =
            native.module.proof_obligations[0].formula.as_ref().unwrap().bindings.clone();
        formula.bindings.iter_mut().find(|(name, _)| name == "r").unwrap().0 = "result".into();
        public.contracts[0].metadata[0].value = serde_json::to_string(&formula.bindings).unwrap();
        native.module.proof_obligations[0].formula = Some(formula);
        let digest =
            public.canonical_obligation_semantic_digest_sha256(&public.obligations[0]).unwrap();
        native.module.proof_obligations[0]
            .source
            .as_mut()
            .unwrap()
            .public
            .as_mut()
            .unwrap()
            .semantic_digest = trust_ir::ProofDigest::sha256(std::array::from_fn(|i| {
            u8::from_str_radix(&digest[2 * i..2 * i + 2], 16).unwrap()
        }));
        rebind_native_bundle_module_digest(&mut native);
        let live = engine(EvidenceStatus::Unknown)
            .verify_obligations_with_native_trust_ir_bundle_and_fresh_receipts(
                &public,
                &public.obligations,
                &native,
                &VerifierExecutionContext::new("public-typed-spec"),
            );
        assert_eq!(public.contracts[0].predicate, original);
        assert_eq!(live.result().summary.proved, usize::from(!negate), "{:#?}", live.result());
        assert_eq!(live.checked_native_wp_proofs().len(), usize::from(!negate));
    }
}

#[test]
fn native_body_wp_preserves_false_contract_and_definitive_primary() {
    let (public, native) = fixture(true);
    let result = engine(EvidenceStatus::Unknown).verify_obligations_with_native_trust_ir_bundle(
        &public,
        &public.obligations,
        &native,
        &VerifierExecutionContext::new("native-body-wp-false"),
    );
    assert_eq!(result.summary.proved, 0, "{result:#?}");
    assert_eq!(result.evidence[0].status, EvidenceStatus::Failed, "{result:#?}");
    let (public, native) = fixture(false);
    for status in [
        EvidenceStatus::Proved,
        EvidenceStatus::Failed,
        EvidenceStatus::Timeout,
        EvidenceStatus::Canceled,
        EvidenceStatus::Unsupported,
    ] {
        let result = engine(status).verify_obligations_with_native_trust_ir_bundle(
            &public,
            &public.obligations,
            &native,
            &VerifierExecutionContext::new("native-body-wp-terminal"),
        );
        assert_eq!(result.summary.proved, 0, "{result:#?}");
        assert!(!result.diagnostics.iter().any(|text| text.contains("engine=trust-wp")));
    }
}

/// Regression (2026-11-15): the body question is the bare postcondition. With
/// unsigned Select on the body path, `fn rmax(a, b) requires b <= a ensures
/// result <= a { if a < b { b } else { a } }` came back `[postcond] FAILED`
/// from a state the precondition excludes (ui `e9_requires_hypothesis_*`,
/// `call_dest_bounding_contract_held`). A function with a precondition keeps a
/// body proof and loses only the body refutation.
#[test]
fn native_body_wp_withholds_a_counterexample_found_without_the_precondition() {
    let requires = |kind| TrustContract {
        contract_id: "boolean-precondition".into(),
        kind,
        predicate: ContractPredicate::CanonicalJson {
            schema: "trust-wp.pure-expr.v1".into(),
            value: serde_json::Value::String("(x : bool)".into()),
        },
        source: SourceLocation::default(),
        metadata: Vec::new(),
    };
    for kind in [ContractKind::Requires, ContractKind::Assumes] {
        // The false contract: refuted without a precondition (the control
        // above), withheld with one.
        let (mut public, native) = fixture(true);
        public.contracts.push(requires(kind.clone()));
        let result = engine(EvidenceStatus::Unknown)
            .verify_obligations_with_native_trust_ir_bundle(
                &public,
                &public.obligations,
                &native,
                &VerifierExecutionContext::new("native-body-wp-conditional-false"),
            );
        assert_eq!(result.summary.proved, 0, "{result:#?}");
        assert_eq!(result.summary.failed, 0, "{result:#?}");
        assert!(
            result.evidence.iter().all(|row| row.status != EvidenceStatus::Failed),
            "{result:#?}"
        );
        assert!(
            format!("{result:?}").contains("body-aware WP counterexample withheld"),
            "the withheld counterexample must be the stated reason: {result:#?}"
        );

        // The true contract still proves: a proof of the bare clause proves
        // the conditional one.
        let (mut public, native) = fixture(false);
        public.contracts.push(requires(kind));
        let result = engine(EvidenceStatus::Unknown)
            .verify_obligations_with_native_trust_ir_bundle(
                &public,
                &public.obligations,
                &native,
                &VerifierExecutionContext::new("native-body-wp-conditional-true"),
            );
        assert_eq!(result.summary.proved, 1, "{result:#?}");
    }
}

#[test]
fn native_body_wp_rejects_swapped_public_request_identity() {
    let (mut public, native) = fixture(false);
    public.obligations[0].metadata = native_trust_ir_metadata("trust-mc", 91, 0);
    let result = engine(EvidenceStatus::Unknown).verify_obligations_with_native_trust_ir_bundle(
        &public,
        &public.obligations,
        &native,
        &VerifierExecutionContext::new("native-body-wp-wrong-id"),
    );
    assert_eq!(result.summary.proved, 0, "{result:#?}");
}

#[test]
fn native_body_wp_rejects_changed_public_contract_even_with_rehashed_identity() {
    let (mut public, native) = fixture(false);
    let NativeVerificationRequest::TrustWp(request) = native
        .requests
        .iter()
        .find(|request| matches!(request, NativeVerificationRequest::TrustWp(_)))
        .unwrap()
    else {
        unreachable!()
    };
    let valid_proof = super::super::engines::NativeTrustWpTrustIrEngine::new()
        .verify_obligation_with_native_trust_ir_request(
            &public,
            &public.obligations[0],
            &native,
            request,
            trust_ir::ProofId::new(0),
        );
    assert_eq!(valid_proof.status, EvidenceStatus::Proved);
    public.contracts[0].predicate = ContractPredicate::CanonicalJson {
        schema: "trust-wp.pure-expr.v1".into(),
        value: serde_json::Value::String("(r : bool) != (x : bool)".into()),
    };
    let digest =
        public.canonical_obligation_semantic_digest_sha256(&public.obligations[0]).unwrap();
    let mut rebound = native.clone();
    rebound.module.proof_obligations[0]
        .source
        .as_mut()
        .unwrap()
        .public
        .as_mut()
        .unwrap()
        .semantic_digest = trust_ir::ProofDigest::sha256(std::array::from_fn(|i| {
        u8::from_str_radix(&digest[2 * i..2 * i + 2], 16).unwrap()
    }));
    rebind_native_bundle_module_digest(&mut rebound);
    rebound
        .validate()
        .expect("forged identity is structurally valid but is not the claimed formula");
    for native in [native, rebound] {
        let result = engine(EvidenceStatus::Unknown)
            .verify_obligations_with_native_trust_ir_bundle(
                &public,
                &public.obligations,
                &native,
                &VerifierExecutionContext::new("changed-public-contract"),
            );
        assert_eq!(result.summary.proved, 0, "{result:#?}");
        for require_proof_artifacts in [false, true] {
            let mut engines = configured_engines(EvidenceStatus::Unknown);
            let slot =
                engines.iter().position(|engine| engine.manifest().name == "trust-wp").unwrap();
            let mut manifest = valid_proof.engine.clone();
            manifest.repository = Some("stale-proof-control".into());
            engines[slot] = Box::new(ReplayedProof { manifest, proof: valid_proof.clone() });
            let policy = FullVerificationPolicy {
                require_proof_artifacts,
                ..FullVerificationPolicy::default()
            };
            let result = FullVerificationEngine::new(engines, policy)
                .verify_obligations_with_native_trust_ir_bundle(
                    &public,
                    &public.obligations,
                    &native,
                    &VerifierExecutionContext::new("replayed-other-contract"),
                );
            assert_eq!(
                result.summary.proved, 0,
                "a certificate for a different contract was accepted: {result:#?}"
            );
        }
    }
}

struct ReplayedProof {
    manifest: EngineManifest,
    proof: ObligationEvidence,
}

impl VerificationEngine for ReplayedProof {
    fn manifest(&self) -> &EngineManifest {
        &self.manifest
    }
    fn supports(&self, _: &TrustObligation) -> SupportLevel {
        SupportLevel::Supported
    }
    fn verify_validated(&self, _: ValidatedVerificationRequest<'_>) -> Vec<ObligationEvidence> {
        vec![self.proof.clone()]
    }
}

#[test]
fn native_body_wp_cannot_relabel_another_claims_proof_in_the_same_bundle() {
    let (mut public, initial) = fixture(false);
    let mut false_obligation =
        native_trust_ir_obligation("trust-mc", 1, 1, ObligationKind::Postcondition, None);
    false_obligation.contract_id = Some("false-contract".into());
    false_obligation.source = SourceLocation {
        file: Some("other-claim.rs".into()),
        line: Some(2),
        column: Some(9),
        end_line: Some(2),
        end_column: Some(19),
    };
    let mut false_contract = public.contracts[0].clone();
    false_contract.contract_id = "false-contract".into();
    false_contract.predicate = ContractPredicate::CanonicalJson {
        schema: "trust-wp.pure-expr.v1".into(),
        value: serde_json::Value::String("(r : bool) != (x : bool)".into()),
    };
    public.contracts.push(false_contract);
    public.obligations.push(false_obligation);
    let mut module = initial.module;
    let mut false_proof = module.proof_obligations[0].clone();
    false_proof.id = trust_ir::ProofId::new(1);
    false_proof.formula.as_mut().unwrap().payload = "(r : bool) != (x : bool)".into();
    let file = module.intern_file("other-claim.rs").unwrap();
    false_proof.source = Some(router_native_obligation_source_identity(
        false_proof.id,
        &public.obligations[1].obligation_id,
        file,
        2,
        native_trust_ir_digest(1),
    ));
    false_proof.source.as_mut().unwrap().source_id = "false-contract".into();
    false_proof.source.as_mut().unwrap().assertion_id = "trust-assertion:false-contract".into();
    module.proof_obligations.push(false_proof);
    for (proof, obligation) in module.proof_obligations.iter_mut().zip(&public.obligations) {
        let digest = public.canonical_obligation_semantic_digest_sha256(obligation).unwrap();
        proof.source.as_mut().unwrap().public.as_mut().unwrap().semantic_digest =
            trust_ir::ProofDigest::sha256(std::array::from_fn(|i| {
                u8::from_str_radix(&digest[2 * i..2 * i + 2], 16).unwrap()
            }));
    }
    let native = native_verification_bundle_from_module(
        module,
        native_trust_ir_digest(1),
        trust_ir::FuncId::new(0),
    )
    .unwrap();
    let request = native
        .requests
        .iter()
        .find_map(|request| match request {
            NativeVerificationRequest::TrustWp(request)
                if request.obligations == [trust_ir::ProofId::new(0)] =>
            {
                Some(request)
            }
            _ => None,
        })
        .unwrap();
    let mut forged = super::super::engines::NativeTrustWpTrustIrEngine::new()
        .verify_obligation_with_native_trust_ir_request(
            &public,
            &public.obligations[0],
            &native,
            request,
            trust_ir::ProofId::new(0),
        );
    assert_eq!(forged.status, EvidenceStatus::Proved, "the other claim must have a genuine proof");
    let target = &public.obligations[1];
    let artifact = &mut forged.artifacts[0];
    let payload = artifact
        .materialization
        .as_ref()
        .unwrap()
        .bound_payload_bytes(artifact.kind, &forged.obligation_id)
        .unwrap();
    let mut payload: serde_json::Value = serde_json::from_slice(payload).unwrap();
    payload["statement"]["obligation_id"] = target.obligation_id.clone().into();
    let (materialization, hash) = EvidenceArtifactMaterialization::new_bound(
        artifact.kind,
        &serde_json::to_vec(&payload).unwrap(),
        "forged-other-claim",
        &target.obligation_id,
        Vec::new(),
    )
    .unwrap();
    artifact.uri = format!("trust-wp-body://forged/{}", hash.value);
    artifact.hash = hash;
    artifact.materialization = Some(materialization);
    forged.obligation_id = target.obligation_id.clone();
    forged.evidence_id = "relabelled-genuine-proof".into();
    assert!(forged.satisfies_proof_artifact_policy(), "the attack is structurally well formed");
    let mut engines = configured_engines(EvidenceStatus::Unknown);
    let slot = engines.iter().position(|engine| engine.manifest().name == "trust-wp").unwrap();
    let mut manifest = forged.engine.clone();
    manifest.repository = Some("other-claim-control".into());
    engines[slot] = Box::new(ReplayedProof { manifest, proof: forged });
    let result = FullVerificationEngine::new(engines, FullVerificationPolicy::default())
        .verify_obligations_with_native_trust_ir_bundle(
            &public,
            std::slice::from_ref(target),
            &native,
            &VerifierExecutionContext::new("other-claim-proof"),
        );
    assert_eq!(result.summary.proved, 0, "{result:#?}");
}

#[test]
fn native_body_wp_rejects_new_proof_of_a_differently_bound_contract() {
    let (public, mut native) = fixture(true);
    let formula = native.module.proof_obligations[0].formula.as_mut().unwrap();
    for (name, binding) in &mut formula.bindings {
        if name == "r" {
            binding.place = trust_ir::proof::ClausePlace::Param { index: 0 };
        }
    }
    rebind_native_bundle_module_digest(&mut native);
    let mut scoped = native.clone();
    scoped.requests.retain(|request| matches!(request, NativeVerificationRequest::TrustWp(_)));
    let proof = trust_wp_lib::trust_ir_body::verify_trust_ir_body_contracts(&scoped).unwrap();
    assert_eq!(
        proof[0].status,
        trust_wp_lib::VerifyBundleStatus::Verified,
        "the altered native bindings produce a genuine tautology, not the public result contract"
    );
    let result = engine(EvidenceStatus::Unknown).verify_obligations_with_native_trust_ir_bundle(
        &public,
        &public.obligations,
        &native,
        &VerifierExecutionContext::new("changed-bindings"),
    );
    assert_eq!(result.summary.proved, 0, "{result:#?}");
}

#[test]
fn native_body_wp_native_replay_cannot_be_promoted_to_certified() {
    for required in [None, Some(ProofStrength::certified(ReasoningKind::Deductive))] {
        let (public, native) = fixture_with_requirement(false, required);
        let request = native
            .requests
            .iter()
            .find_map(|request| match request {
                NativeVerificationRequest::TrustWp(request) => Some(request),
                _ => None,
            })
            .unwrap();
        let mut proof = super::super::engines::NativeTrustWpTrustIrEngine::new()
            .verify_obligation_with_native_trust_ir_request(
                &public,
                &public.obligations[0],
                &native,
                request,
                trust_ir::ProofId::new(0),
            );
        assert_eq!(proof.status, EvidenceStatus::Proved);
        proof.proof_strength = Some(ProofStrength::certified(ReasoningKind::Deductive));
        for require_proof_artifacts in [false, true] {
            let mut engines = configured_engines(EvidenceStatus::Unknown);
            let slot =
                engines.iter().position(|engine| engine.manifest().name == "trust-wp").unwrap();
            let mut manifest = proof.engine.clone();
            manifest.repository = Some("grade-promotion-control".into());
            engines[slot] = Box::new(ReplayedProof { manifest, proof: proof.clone() });
            let policy = FullVerificationPolicy {
                require_proof_artifacts,
                ..FullVerificationPolicy::default()
            };
            let result = FullVerificationEngine::new(engines, policy)
                .verify_obligations_with_native_trust_ir_bundle(
                    &public,
                    &public.obligations,
                    &native,
                    &VerifierExecutionContext::new("promoted-native-replay"),
                );
            assert_eq!(result.summary.proved, 0, "{result:#?}");
        }
    }
}

#[test]
fn native_body_wp_respects_zero_per_obligation_budget() {
    let (public, native) = fixture(false);
    let NativeVerificationRequest::TrustWp(request) = native
        .requests
        .iter()
        .find(|request| matches!(request, NativeVerificationRequest::TrustWp(_)))
        .unwrap()
    else {
        unreachable!()
    };
    let adapter = super::super::engines::NativeTrustWpTrustIrEngine::with_timeout_ms(0);
    let evidence = adapter.verify_obligation_with_native_trust_ir_request(
        &public,
        &public.obligations[0],
        &native,
        request,
        trust_ir::ProofId::new(0),
    );
    assert_eq!(evidence.status, EvidenceStatus::Timeout);
    assert!(evidence.proof_strength.is_none());
    assert!(evidence.artifacts.is_empty());
}

struct StopAfterProof {
    manifest: EngineManifest,
    native: NativeVerificationBundle,
    cancellation: trust_verifier_api::CancellationToken,
    deadline: Option<Instant>,
    completed: Arc<AtomicUsize>,
}

impl VerificationEngine for StopAfterProof {
    fn manifest(&self) -> &EngineManifest {
        &self.manifest
    }
    fn supports(&self, _: &TrustObligation) -> SupportLevel {
        SupportLevel::Supported
    }
    fn verify_validated(
        &self,
        request: ValidatedVerificationRequest<'_>,
    ) -> Vec<ObligationEvidence> {
        let (bundle, obligations) = request.into_parts();
        let NativeVerificationRequest::TrustWp(native_request) = self
            .native
            .requests
            .iter()
            .find(|request| matches!(request, NativeVerificationRequest::TrustWp(_)))
            .unwrap()
        else {
            unreachable!()
        };
        let adapter = super::super::engines::NativeTrustWpTrustIrEngine::new();
        let row = adapter.verify_obligation_with_native_trust_ir_request(
            bundle,
            &obligations[0],
            &self.native,
            native_request,
            trust_ir::ProofId::new(0),
        );
        assert_eq!(row.status, EvidenceStatus::Proved, "control must produce a real proof");
        self.completed.fetch_add(1, Ordering::SeqCst);
        if let Some(deadline) = self.deadline {
            std::thread::sleep(
                deadline.saturating_duration_since(Instant::now()) + Duration::from_millis(1),
            );
        } else {
            self.cancellation.cancel(trust_verifier_api::CancellationReason::UserRequested);
        }
        vec![row]
    }
}

#[test]
fn native_body_wp_cancellation_during_proof_prevents_publication() {
    let (public, native) = fixture(false);
    let context = VerifierExecutionContext::new("cancel-during-wp");
    let mut engines = configured_engines(EvidenceStatus::Unknown);
    let slot = engines.iter().position(|engine| engine.manifest().name == "trust-wp").unwrap();
    let mut manifest = engines[slot].manifest().clone();
    // Dispatch this test double through the generic engine path; it invokes
    // the genuine native proof before signaling cancellation.
    manifest.repository = Some("cancellation-control".into());
    let completed = Arc::new(AtomicUsize::new(0));
    engines[slot] = Box::new(StopAfterProof {
        manifest,
        native: native.clone(),
        cancellation: context.cancellation.clone(),
        deadline: None,
        completed: completed.clone(),
    });
    let configured = FullVerificationEngine::new(engines, FullVerificationPolicy::default());
    let result = configured.verify_obligations_with_native_trust_ir_bundle(
        &public,
        &public.obligations,
        &native,
        &context,
    );
    assert_eq!(result.summary.proved, 0, "{result:#?}");
    assert_eq!(completed.load(Ordering::SeqCst), 1);
    assert_eq!(result.evidence[0].status, EvidenceStatus::Canceled, "{result:#?}");
}

#[test]
fn native_body_wp_deadline_during_proof_prevents_publication() {
    let (public, native) = fixture(false);
    let deadline = Instant::now() + Duration::from_secs(1);
    let context = VerifierExecutionContext::new("deadline-during-wp").with_deadline(deadline);
    let mut engines = configured_engines(EvidenceStatus::Unknown);
    let slot = engines.iter().position(|engine| engine.manifest().name == "trust-wp").unwrap();
    let mut manifest = engines[slot].manifest().clone();
    manifest.repository = Some("deadline-control".into());
    let completed = Arc::new(AtomicUsize::new(0));
    engines[slot] = Box::new(StopAfterProof {
        manifest,
        native: native.clone(),
        cancellation: context.cancellation.clone(),
        deadline: Some(deadline),
        completed: completed.clone(),
    });
    let configured = FullVerificationEngine::new(engines, FullVerificationPolicy::default());
    let result = configured.verify_obligations_with_native_trust_ir_bundle(
        &public,
        &public.obligations,
        &native,
        &context,
    );
    assert_eq!(completed.load(Ordering::SeqCst), 1, "deadline control must execute a real proof");
    assert_eq!(result.summary.proved, 0, "{result:#?}");
    assert_eq!(result.evidence[0].status, EvidenceStatus::Timeout, "{result:#?}");
}

#[test]
fn native_body_wp_refuses_mismatched_public_source_projection() {
    fn bound_fixture() -> (TrustContractBundle, NativeVerificationBundle) {
        let (mut public, native) = fixture(false);
        public.obligations[0].source = SourceLocation {
            file: Some("body-wp.rs".into()),
            line: Some(1),
            column: Some(9),
            end_line: Some(1),
            end_column: Some(19),
        };
        let mut module = native.module;
        let source = module.proof_obligations[0].source.as_mut().unwrap();
        source.source_id = public.obligations[0].contract_id.clone().unwrap();
        source.assertion_id = format!("trust-assertion:{}", source.source_id);
        let digest =
            public.canonical_obligation_semantic_digest_sha256(&public.obligations[0]).unwrap();
        source.public.as_mut().unwrap().semantic_digest =
            proof_digest_from_canonical_sha256(&digest);
        let native = native_verification_bundle_from_module(
            module,
            native_trust_ir_digest(1),
            trust_ir::FuncId::new(0),
        )
        .unwrap();
        (public, native)
    }
    let (public, native) = bound_fixture();
    let positive = engine(EvidenceStatus::Unknown)
        .verify_obligations_with_native_trust_ir_bundle_and_fresh_receipts(
            &public,
            &public.obligations,
            &native,
            &VerifierExecutionContext::new("bound-source-positive"),
        );
    assert_eq!(positive.result().summary.proved, 1);
    let mut accepted = Vec::new();
    for mutation in 0..4 {
        let (mut public, native) = bound_fixture();
        let mut module = native.module;
        let source = module.proof_obligations[0].source.as_mut().unwrap();
        match mutation {
            0 => public.obligations[0].source.line = Some(2),
            1 => source.source_id.push_str("-other"),
            2 => source.assertion_id.push_str("-other"),
            3 => source.range.as_mut().unwrap().end_col += 1,
            _ => unreachable!(),
        }
        let digest =
            public.canonical_obligation_semantic_digest_sha256(&public.obligations[0]).unwrap();
        source.public.as_mut().unwrap().semantic_digest =
            proof_digest_from_canonical_sha256(&digest);
        let native = native_verification_bundle_from_module(
            module,
            native_trust_ir_digest(1),
            trust_ir::FuncId::new(0),
        )
        .unwrap();
        native.validate().expect("the native bundle is internally coherent");
        if let Some(root) = std::env::var_os("TRUST_SOURCE_BINDING_REPRO_DIR") {
            let root = std::path::PathBuf::from(root);
            std::fs::create_dir_all(&root).unwrap();
            std::fs::write(
                root.join(format!("mutation-{mutation}.json")),
                serde_json::to_vec_pretty(&serde_json::json!({"public":public,"native":native}))
                    .unwrap(),
            )
            .unwrap();
        }
        let result = engine(EvidenceStatus::Unknown)
            .verify_obligations_with_native_trust_ir_bundle_and_fresh_receipts(
                &public,
                &public.obligations,
                &native,
                &VerifierExecutionContext::new("mismatched-source"),
            );
        if result.result().summary.proved != 0 || !result.checked_native_wp_proofs().is_empty() {
            accepted.push(mutation);
        }
    }
    assert!(
        accepted.is_empty(),
        "mismatched public source projections minted proofs: {accepted:?}"
    );
}

#[test]
fn native_body_wp_cached_replay_still_binds_the_public_source() {
    let (public, native) = fixture(false);
    let live = engine(EvidenceStatus::Unknown)
        .verify_obligations_with_native_trust_ir_bundle_and_fresh_receipts(
            &public,
            &public.obligations,
            &native,
            &VerifierExecutionContext::new("warm-source-binding"),
        );
    assert_eq!(live.result().summary.proved, 1);
    let evidence = &live.result().evidence[0];
    let request = native
        .requests
        .iter()
        .find_map(|request| match request {
            NativeVerificationRequest::TrustWp(request) => Some(request),
            _ => None,
        })
        .unwrap();
    let index = super::native_trust_ir::NativeTrustIrEvidenceIndex::from_bundle(&native);
    for _ in 0..2 {
        assert!(index.accepts_wp_certificate(
            &public,
            &public.obligations[0],
            evidence,
            request.id.index(),
            0,
        ));
    }
    let mut changed = public.clone();
    changed.obligations[0].source.line = Some(2);
    for _ in 0..2 {
        assert!(!index.accepts_wp_certificate(
            &changed,
            &changed.obligations[0],
            evidence,
            request.id.index(),
            0,
        ));
    }
    assert!(index.accepts_wp_certificate(
        &public,
        &public.obligations[0],
        evidence,
        request.id.index(),
        0,
    ));
}

fn fixture_with_original_program_binding() -> (TrustContractBundle, NativeVerificationBundle) {
    let (mut public, native) = fixture(false);
    let contract_id = public.obligations[0].contract_id.clone().unwrap();
    public.obligations[0].metadata.push(
        trust_verifier_api::ObligationContext::new(
            trust_verifier_api::ObligationProducer::CompilerMirExtract,
            trust_verifier_api::ObligationOrigin::Contract {
                contract_id,
                contract_kind: ContractKind::Ensures,
                contract_index: 0,
                predicate_schema: Some("trust-wp.pure-expr.v1".into()),
            },
        )
        .to_metadata_entry()
        .unwrap(),
    );
    let semantic =
        public.canonical_obligation_semantic_digest_sha256(&public.obligations[0]).unwrap();
    let mut module = native.module.clone();
    module.proof_obligations[0].source.as_mut().unwrap().public.as_mut().unwrap().semantic_digest =
        trust_ir::ProofDigest::sha256(std::array::from_fn(|i| {
            u8::from_str_radix(&semantic[2 * i..2 * i + 2], 16).unwrap()
        }));
    let native = native_verification_bundle_from_module(
        module,
        native.provenance.source_digest.unwrap(),
        trust_ir::FuncId::new(0),
    )
    .unwrap();
    let digest = native.trust_ir_module_digest.to_string();
    let hex = digest.strip_prefix("sha256:").unwrap();
    let public_id = public.obligations[0].obligation_id.clone();
    public.obligations[0].metadata.extend([
        MetadataEntry {
            key: "trust.trust_ir.native.trust_ir_module_digest".into(),
            value: hex.into(),
        },
        MetadataEntry {
            key: "trust.trust_ir.native.proof_unit.v1".into(),
            value: serde_json::json!({
                "schema_version":"trust.trust_ir.native-proof-unit.v1",
                "public_obligation_id":public_id,
                "proof_obligation_id":0,
                "trust_ir_module_digest":{"algorithm":"sha256","value":hex},
            })
            .to_string(),
        },
    ]);
    assert_eq!(
        public.canonical_obligation_semantic_digest_sha256(&public.obligations[0]).unwrap(),
        semantic
    );
    (public, native)
}

#[test]
fn native_body_wp_warm_replay_and_cloned_fact_check_original_program_bindings() {
    const MODULE_KEY: &str = "trust.trust_ir.native.trust_ir_module_digest";
    const UNIT_KEY: &str = "trust.trust_ir.native.proof_unit.v1";
    let (public, native) = fixture_with_original_program_binding();
    let live = engine(EvidenceStatus::Unknown)
        .verify_obligations_with_native_trust_ir_bundle_and_fresh_receipts(
            &public,
            &public.obligations,
            &native,
            &VerifierExecutionContext::new("warm-program-binding"),
        );
    assert_eq!(live.result().summary.proved, 1, "{:#?}", live.result());
    let evidence = &live.result().evidence[0];
    let fact = live.checked_native_wp_proofs()[&public.obligations[0].obligation_id].clone();
    let request = native
        .requests
        .iter()
        .find_map(|request| match request {
            NativeVerificationRequest::TrustWp(request) => Some(request),
            _ => None,
        })
        .unwrap();
    let index = super::native_trust_ir::NativeTrustIrEvidenceIndex::from_bundle(&native);
    let digest =
        public.canonical_obligation_semantic_digest_sha256(&public.obligations[0]).unwrap();
    for _ in 0..2 {
        assert!(index.accepts_wp_certificate(
            &public,
            &public.obligations[0],
            evidence,
            request.id.index(),
            0
        ));
        assert!(fact.clone().matches(&public, &native, &public.obligations[0], evidence));
    }
    for mutation in 0..9 {
        let mut changed = public.clone();
        let entries = &mut changed.obligations[0].metadata;
        match mutation {
            0 => {
                entries.iter_mut().find(|entry| entry.key == MODULE_KEY).unwrap().value =
                    "0".repeat(64)
            }
            1 => {
                let encoded =
                    &mut entries.iter_mut().find(|entry| entry.key == UNIT_KEY).unwrap().value;
                let mut unit: serde_json::Value = serde_json::from_str(encoded).unwrap();
                unit["trust_ir_module_digest"]["value"] = "0".repeat(64).into();
                *encoded = unit.to_string();
            }
            2 => entries.retain(|entry| entry.key != MODULE_KEY && entry.key != UNIT_KEY),
            3 => entries.retain(|entry| entry.key != MODULE_KEY),
            4 => entries.retain(|entry| entry.key != UNIT_KEY),
            5 | 6 => {
                let key = if mutation == 5 { MODULE_KEY } else { UNIT_KEY };
                let duplicate = entries.iter().find(|entry| entry.key == key).unwrap().clone();
                entries.push(duplicate);
            }
            _ => {
                if mutation == 7 {
                    entries
                        .iter_mut()
                        .find(|entry| entry.key == "trust.trust_ir.native.proof_obligation_id")
                        .unwrap()
                        .value = "1".into();
                }
                let encoded =
                    &mut entries.iter_mut().find(|entry| entry.key == UNIT_KEY).unwrap().value;
                let mut unit: serde_json::Value = serde_json::from_str(encoded).unwrap();
                if mutation == 7 {
                    unit["proof_obligation_id"] = 1.into();
                } else {
                    unit["public_obligation_id"] = "another-public-obligation".into();
                }
                *encoded = unit.to_string();
            }
        }
        let changed_digest =
            changed.canonical_obligation_semantic_digest_sha256(&changed.obligations[0]);
        if matches!(mutation, 5 | 6) {
            assert!(changed_digest.is_err(), "duplicate metadata must also refuse canonically");
        } else {
            assert_eq!(changed_digest.unwrap(), digest);
        }
        for _ in 0..2 {
            assert!(
                !index.accepts_wp_certificate(
                    &changed,
                    &changed.obligations[0],
                    evidence,
                    request.id.index(),
                    0
                ),
                "warm mutation {mutation}"
            );
            assert!(
                !fact.clone().matches(&changed, &native, &changed.obligations[0], evidence),
                "cloned fact mutation {mutation}"
            );
        }
    }
    assert!(index.accepts_wp_certificate(
        &public,
        &public.obligations[0],
        evidence,
        request.id.index(),
        0
    ));
    assert!(fact.matches(&public, &native, &public.obligations[0], evidence));
}

#[path = "input_capture_tests.rs"]
mod input_capture_tests;

/// A trust-mc primary with a fixed answer that, when told to, answers only once
/// the native solve cutoff has passed, or cancels the run while it answers.
struct LatePrimary {
    inner: UnitEngine,
    answers_after: Option<Instant>,
    cancels: Option<trust_verifier_api::CancellationToken>,
}

impl VerificationEngine for LatePrimary {
    fn manifest(&self) -> &EngineManifest {
        self.inner.manifest()
    }
    fn supports(&self, obligation: &TrustObligation) -> SupportLevel {
        self.inner.supports(obligation)
    }
    fn verify_validated(
        &self,
        request: ValidatedVerificationRequest<'_>,
    ) -> Vec<ObligationEvidence> {
        if let Some(at) = self.answers_after {
            std::thread::sleep(
                at.saturating_duration_since(Instant::now()) + Duration::from_millis(1),
            );
        }
        if let Some(token) = &self.cancels {
            token.cancel(trust_verifier_api::CancellationReason::UserRequested);
        }
        self.inner.verify_validated(request)
    }
}

/// HARDENED-PROFILE-UNMEASURED-1: a postcondition the primary leaves undecided
/// after the native solve cutoff has passed (the function's own deadline far
/// off) is published as the clock stop it is: the deductive fallback that could
/// decide it was refused by that clock alone. Before, the row stayed the
/// primary's `unknown`, which names no clock. A run cancelled while the primary
/// answers is published as cancelled the same way. Controls: the same primary
/// inside the cutoff is discharged by the fallback; a definitive primary that
/// answers late keeps its verdict, and so does a row no rule lets the fallback
/// take (a terminal refusal, or no fallback engine): the clock decided nothing
/// there.
#[test]
fn a_fallback_refused_by_the_clock_alone_publishes_the_clock_stop() {
    #[derive(Clone, Copy, PartialEq)]
    enum Stop {
        None,
        Late,
        Cancelled,
    }
    let run = |status: EvidenceStatus, stop: Stop, with_fallback: bool| {
        let (public, native) = fixture(false);
        let late = stop == Stop::Late;
        let cutoff = Instant::now()
            + if late { Duration::from_millis(300) } else { Duration::from_secs(3600) };
        let context = VerifierExecutionContext::new("fallback-clock")
            .with_deadline(Instant::now() + Duration::from_secs(7200))
            .with_native_solve_cutoff(Some(cutoff));
        let mut engines = configured_engines(status);
        if !with_fallback {
            engines.retain(|engine| engine.manifest().name != "trust-wp");
        }
        let slot = engines.iter().position(|engine| engine.manifest().name == "trust-mc").unwrap();
        engines[slot] = Box::new(LatePrimary {
            inner: UnitEngine::new(
                "trust-mc",
                EngineKind::Reachability,
                ObligationKind::Postcondition,
                SupportLevel::Supported,
                UnitEvidenceMode::Evidence {
                    status,
                    proof_strength: None,
                    artifacts: vec![],
                    diagnostics: vec!["controlled primary outcome".into()],
                },
            ),
            answers_after: late.then_some(cutoff),
            cancels: (stop == Stop::Cancelled).then(|| context.cancellation.clone()),
        });
        let configured = FullVerificationEngine::new(engines, FullVerificationPolicy::default());
        let result = configured.verify_obligations_with_native_trust_ir_bundle(
            &public,
            &public.obligations,
            &native,
            &context,
        );
        assert!(!context.budget_exceeded(), "the function's own deadline never passes here");
        result
    };
    let names_the_refused_fallback = |result: &VerificationRunResult, why: &str| {
        result.evidence[0].diagnostics.iter().any(|text| {
            text.contains(&format!("deductive fallback not attempted: {why}"))
                && text.contains("controlled primary outcome")
        })
    };
    let names_no_refused_fallback = |result: &VerificationRunResult| {
        !result
            .evidence
            .iter()
            .flat_map(|evidence| &evidence.diagnostics)
            .any(|text| text.contains("deductive fallback not attempted"))
    };
    const CLOCK: &str = "the verification clock had run out";
    const CANCEL: &str = "the run was cancelled";

    let late = run(EvidenceStatus::Unknown, Stop::Late, true);
    assert_eq!(late.evidence[0].status, EvidenceStatus::Timeout, "{late:#?}");
    assert_eq!(late.summary.proved, 0, "{late:#?}");
    assert!(
        names_the_refused_fallback(&late, CLOCK),
        "the clock is named and the primary's own diagnostics are kept: {late:#?}"
    );

    let cancelled = run(EvidenceStatus::Unknown, Stop::Cancelled, true);
    assert_eq!(cancelled.evidence[0].status, EvidenceStatus::Canceled, "{cancelled:#?}");
    assert_eq!(cancelled.summary.proved, 0, "{cancelled:#?}");
    assert!(
        names_the_refused_fallback(&cancelled, CANCEL),
        "the cancellation is named, not a clock: {cancelled:#?}"
    );

    let in_time = run(EvidenceStatus::Unknown, Stop::None, true);
    assert_eq!(
        in_time.summary.proved, 1,
        "control: inside the cutoff the fallback decides: {in_time:#?}"
    );

    let definitive = run(EvidenceStatus::Failed, Stop::Late, true);
    assert_eq!(definitive.evidence[0].status, EvidenceStatus::Failed, "{definitive:#?}");
    assert!(names_no_refused_fallback(&definitive), "{definitive:#?}");

    // Rows the fallback is refused for a reason other than the clock keep the
    // primary's answer under an expired cutoff: a refusal with no stated decline
    // is terminal, and with no trust-wp engine there is no fallback to refuse.
    let terminal = run(EvidenceStatus::Unsupported, Stop::Late, true);
    assert_eq!(terminal.evidence[0].status, EvidenceStatus::Unsupported, "{terminal:#?}");
    assert!(names_no_refused_fallback(&terminal), "{terminal:#?}");

    let no_fallback = run(EvidenceStatus::Unknown, Stop::Late, false);
    assert_eq!(no_fallback.evidence[0].status, EvidenceStatus::Unknown, "{no_fallback:#?}");
    assert!(names_no_refused_fallback(&no_fallback), "{no_fallback:#?}");
}

#[path = "native_wp_input_tests.rs"]
mod input_identity;

#[path = "native_wp_captured_tests.rs"]
mod captured_native;

#[cfg(feature = "native-wp-mathematics")]
#[path = "native_wp_execution_tests.rs"]
mod execution_mathematics;

#[cfg(feature = "native-wp-mathematics")]
#[path = "native_wp_translation_tests.rs"]
mod translation_mathematics;

#[path = "native_wp_tests/selected_boundary.rs"]
mod selected_boundary;

#[path = "native_wp_tests/current_self_use.rs"]
mod current_self_use;

#[path = "native_wp_tests/solver_budget_self_use.rs"]
mod solver_budget_self_use;

#[path = "native_wp_tests/budget_division_self_use.rs"]
mod budget_division_self_use;

#[path = "native_wp_tests/eager_definedness.rs"]
mod eager_definedness;
