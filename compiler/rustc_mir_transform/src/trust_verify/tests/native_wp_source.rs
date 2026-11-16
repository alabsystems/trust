use super::*;

fn boolean_source(
    wrong_body: bool,
) -> (
    trust_types::VerifiableFunction,
    trust_types::CompilerContractBundle,
    super::super::native_wp_source::CapturedSource,
) {
    use rustc_middle::mir::trust_contract::{
        TrustContractPredicateKind, TrustContractProposition as P,
        TrustContractPropositionDomain as D,
    };
    use trust_thir_lower::contract_carry::{
        CarryClause, CarryParam, ClauseRole, ContractBodyRecord, ParamReference,
    };
    // These JSON files are immutable 6c9 compiler exports of source.rs.txt,
    // not synthetic bodies. The separate query record below models the source
    // query/HIR input; production obtains it through capture_contract_body.
    let json = if wrong_body {
        include_str!("fixtures/native_wp_query/wrong_mir.json")
    } else {
        include_str!("fixtures/native_wp_query/identity_mir.json")
    };
    let function: trust_types::VerifiableFunction = serde_json::from_str(json).unwrap();
    assert_eq!(function.body.return_ty, trust_types::Ty::Bool);
    assert_eq!(function.body.arg_count, 1);
    let contract = &function.contracts[0];
    let contracts = trust_types::CompilerContractBundle::new(function.contracts.clone())
        .with_typed_propositions(vec![trust_types::CompilerContractProposition {
            source_contract_index: 0,
            kind: contract.kind,
            body: contract.body.clone(),
            formula: function.postconditions[0].clone(),
            variable_domains: ["_0", "x"]
                .into_iter()
                .map(|name| trust_types::CompilerContractVariableDomain {
                    name: name.into(),
                    domain: trust_types::CompilerContractValueDomain::Bool,
                })
                .collect(),
        }]);
    let body = ContractBodyRecord {
        def_index: 0,
        // The shared query carry deliberately records a crate-relative path.
        def_path: if wrong_body { "wrong" } else { "identity" }.into(),
        ir_param_count: Some(1),
        params: vec![CarryParam {
            ir_index: 0,
            name: "x".into(),
            hir_local_id: 10,
            mutable: false,
            reference: ParamReference::ByValue,
        }],
        binding_refusal: None,
        clauses: vec![CarryClause {
            role: ClauseRole::Ensures,
            ordinal: 0,
            loop_key: None,
            predicate: TrustContractPredicateKind::Typed {
                text: rustc_span::Symbol::intern(&function.contracts[0].body),
                proposition: P::Eq(
                    Box::new(P::Var { name: rustc_span::Symbol::intern("_0"), domain: D::Bool }),
                    Box::new(P::Var { name: rustc_span::Symbol::intern("x"), domain: D::Bool }),
                ),
            },
            place_bindings: None,
        }],
        loop_headers: vec![],
        refusal: None,
    };
    let source = super::super::native_wp_source::CapturedSource {
        function_path: function.def_path.clone(),
        body,
    };
    (function, contracts, source)
}

#[test]
#[allow(deprecated)]
fn query_bound_catalog_keeps_raw_postcondition_and_real_body_vcs() {
    rustc_span::create_default_session_globals_then(|| {
        for wrong_body in [false, true] {
            let (function, contracts, source) = boolean_source(wrong_body);
            assert_eq!(source.body.def_path, if wrong_body { "wrong" } else { "identity" });
            assert_eq!(source.function_path, function.def_path);
            assert_ne!(source.body.def_path, source.function_path);
            let (vcs, _) =
                trust_vcgen::regenerate_postcondition_production_variants(&function).unwrap();
            let reference =
                trust_mir_extract::contract_bundle_to_verifier_api(&function, &contracts);
            let marker_id = reference.obligations[0].obligation_id.clone();
            let original_predicate = reference.contracts[0].predicate.clone();
            let mut public =
                trust_mir_extract::function_to_verifier_api_bundle(&function, &contracts, &vcs);
            assert_eq!(
                bind_exact_source_clause_native_formulas(
                    &function,
                    &contracts,
                    &vcs,
                    &reference,
                    &mut public,
                    None,
                ),
                1
            );
            let body_claims = public
                .obligations
                .iter()
                .filter(|row| row.obligation_id != marker_id)
                .map(|row| {
                    (
                        row.obligation_id.clone(),
                        api_obligation_metadata_value(row, TRUST_VC_FORMULA_PAYLOAD_METADATA_KEY)
                            .map(str::to_owned),
                    )
                })
                .collect::<Vec<_>>();
            assert!(!body_claims.is_empty(), "actual vcgen must emit a body check");
            let native = build_native_trust_ir_bundle_for_test_verifier_api_with_source(
                &function,
                &mut public,
                &vcs,
                Some(&source),
            )
            .unwrap()
            .unwrap();
            // Trust: the genuine current compiler-unit input uses the shared
            // lossless transport codec, including compressed replay formulas.
            // Its typed and request-scoped identities must survive transport.
            let encoded =
                trust_ir::request::transport::native_bundle_transport_payload(&native).unwrap();
            assert!(
                encoded["bundle"]["requests"]
                    .as_array()
                    .unwrap()
                    .iter()
                    .flat_map(|request| request.as_object().unwrap().values())
                    .flat_map(|request| {
                        request["provenance"]["replay_context"]["atoms"]
                            .as_array()
                            .into_iter()
                            .flatten()
                    })
                    .any(|atom| atom.get("formula_ref").is_some())
            );
            let restored =
                trust_ir::request::transport::rehydrate_native_bundle_transport_payload(&encoded)
                    .unwrap();
            assert_eq!(restored, native);
            assert_eq!(restored.stable_digest(), native.stable_digest());
            assert_eq!(
                trust_ir::request::transport::native_bundle_transport_payload(&restored).unwrap(),
                encoded
            );
            for request in &native.requests {
                if let trust_ir::NativeVerificationRequest::TrustWp(wp) = request {
                    let select = |bundle: &trust_ir::NativeVerificationBundle| {
                        let mut scoped = bundle.clone();
                        scoped.requests.retain(|candidate| {
                            matches!(candidate, trust_ir::NativeVerificationRequest::TrustWp(selected)
                                if selected.id == wp.id)
                        });
                        assert_eq!(scoped.requests.len(), 1);
                        scoped.stable_digest()
                    };
                    assert_eq!(select(&restored), select(&native));
                }
            }
            let marker =
                public.obligations.iter().find(|row| row.obligation_id == marker_id).unwrap();
            assert_eq!(
                native_trust_ir_route_for_api_obligation(marker),
                Some(("trust-mc", trust_ir::ObligationKind::Postcondition))
            );
            let contract = public
                .contracts
                .iter()
                .find(|contract| Some(&contract.contract_id) == marker.contract_id.as_ref())
                .unwrap();
            assert_eq!(
                contract.predicate, original_predicate,
                "query binding must not rewrite source meaning"
            );
            let bindings: Vec<(String, trust_ir::proof::ClauseBinding)> = serde_json::from_str(
                exactly_one_metadata_value(
                    &contract.metadata,
                    trust_verifier_api::TRUST_IR_CLAUSE_BINDINGS_METADATA_KEY,
                )
                .unwrap(),
            )
            .unwrap();
            assert_eq!(bindings.len(), 2);
            assert!(bindings.iter().any(|(name, binding)| name == "_0"
                && matches!(binding.place, trust_ir::proof::ClausePlace::ResultSlot { index: 0 })));
            assert!(bindings.iter().any(|(name, binding)| name == "x"
                && matches!(binding.place, trust_ir::proof::ClausePlace::Param { index: 0 })));
            for (id, payload) in &body_claims {
                let row = public.obligations.iter().find(|row| &row.obligation_id == id).unwrap();
                assert_eq!(
                    api_obligation_metadata_value(row, TRUST_VC_FORMULA_PAYLOAD_METADATA_KEY),
                    payload.as_deref()
                );
                if exactly_one_metadata_value(
                    &row.metadata,
                    TRUST_VC_SOURCE_CONTRACT_INDEX_METADATA_KEY,
                )
                .is_some()
                {
                    assert!(
                        vcs.iter().any(|vc| source_clause_body_link(&public, row, vc).is_some()),
                        "raw source preservation must retain the exact body proof-group link"
                    );
                }
            }
            let proof = native
                .module
                .proof_obligations
                .iter()
                .find(|proof| {
                    proof
                        .source
                        .as_ref()
                        .and_then(|source| source.public.as_ref())
                        .is_some_and(|source| source.obligation_id == marker_id)
                })
                .unwrap();
            assert_eq!(proof.kind, trust_ir::ObligationKind::Postcondition);
            assert_eq!(proof.formula.as_ref().unwrap().bindings, bindings);
            assert!(native.requests.iter().any(|request| {
                matches!(request, trust_ir::NativeVerificationRequest::TrustWp(wp) if wp.obligations == [proof.id])
            }));
            let checked = trust_router::FullVerificationEngine::with_required_native_engines()
                .verify_obligations_with_native_trust_ir_bundle_and_fresh_receipts(
                    &public,
                    &public.obligations,
                    &native,
                    &trust_router::VerifierExecutionContext::new("query-bound-source"),
                );
            let (result, receipts) = checked.into_parts();
            let source_evidence = result
                .evidence
                .iter()
                .find(|evidence| evidence.obligation_id == marker_id)
                .expect("source postcondition evidence");
            assert_eq!(
                source_evidence.status == trust_verifier_api::EvidenceStatus::Proved,
                !wrong_body,
                "source status {:?}: {:?}",
                source_evidence.status,
                source_evidence.diagnostics
            );
            let (mut rows, row_bindings) =
                full_verification_legacy_results_bound(&function, &public, &result);
            let mut authorities = vec![None; rows.len()];
            let applied = super::super::native_wp_source::apply_authorities(
                &public,
                Some(&native),
                &result,
                Some(receipts.checked_native_wp_proofs()),
                &mut rows,
                &row_bindings,
                &mut authorities,
            );
            assert_eq!(applied, usize::from(!wrong_body));
            if !wrong_body {
                assert!(authorities.iter().any(|authority| matches!(
                    authority,
                    Some(ResultProofAuthority::NativeWpSource { .. })
                )));
                let index = authorities.iter().position(Option::is_some).unwrap();
                // An existing same-grade composition does not suppress the
                // stronger publication binding supplied by this real fact.
                // This fixture exercises selection only; it does not mint a
                // new body proof or use the synthetic composition as evidence.
                authorities[index] = Some(ResultProofAuthority::ExactSourceClauseDischarge {
                    row: exact_result_row_identity(index, &rows[index].0).unwrap(),
                    binding: row_bindings[index].clone().unwrap(),
                    body_proofs: Vec::new(),
                    certificate: None,
                });
                assert_eq!(
                    super::super::native_wp_source::apply_authorities(
                        &public,
                        Some(&native),
                        &result,
                        Some(receipts.checked_native_wp_proofs()),
                        &mut rows,
                        &row_bindings,
                        &mut authorities,
                    ),
                    1
                );
                assert!(matches!(
                    authorities[index],
                    Some(ResultProofAuthority::NativeWpSource { .. })
                ));
                let authority = authorities[index].as_ref().unwrap();
                assert_eq!(
                    trust_disposition_for_authority(
                        Some(authority),
                        index,
                        &rows[index].0,
                        &rows[index].1,
                        row_bindings[index].as_ref(),
                    ),
                    Some((TrustStatus::Trusted, TrustProofStrength::Deductive)),
                );
                let wire = build_transport_results_with_runtime_checks_bound(
                    false,
                    None,
                    &rows,
                    Some(&result),
                    &vec![None; rows.len()],
                    &row_bindings,
                    &authorities,
                );
                if let Some(directory) = std::env::var_os("TRUST_WP_TEST_TRANSPORT_DIR") {
                    let directory = std::path::PathBuf::from(directory);
                    std::fs::create_dir_all(&directory).unwrap();
                    std::fs::write(
                        directory.join("actual-compiler-native-wp-transport.json"),
                        serde_json::to_vec_pretty(&wire).unwrap(),
                    )
                    .unwrap();
                }
                let transport = &wire[index];
                assert_eq!(transport.outcome, Outcome::Proved);
                let published =
                    transport.proof_evidence.as_ref().expect("publishable native proof");
                assert_eq!(published.status, TransportProofStatus::Proved);
                assert_eq!(published.suite, "trust-wp");
                let wp = native
                    .requests
                    .iter()
                    .find_map(|request| match request {
                        trust_ir::NativeVerificationRequest::TrustWp(wp)
                            if wp.obligations.contains(&proof.id) =>
                        {
                            Some(wp)
                        }
                        _ => None,
                    })
                    .unwrap();
                assert_eq!(
                    published.request_id.as_deref(),
                    Some(wp.id.index().to_string().as_str())
                );
                assert_eq!(
                    published.proof_id.as_deref(),
                    Some(proof.id.index().to_string().as_str())
                );
                assert_eq!(
                    published.native_id.as_deref(),
                    Some(
                        native_trust_ir_proof_unit_id("trust-wp", wp.id.index(), proof.id.index(),)
                            .as_str()
                    )
                );
                assert!(!published.artifacts.is_empty());
                let native_transport = transport.native_trust_ir.as_ref().unwrap();
                assert!(native_transport.present);
                assert_eq!(native_transport.suite, published.suite);
                assert_eq!(native_transport.request_id, published.request_id);
                assert_eq!(native_transport.native_id, published.native_id);
                assert!(trust_types::native_trust_ir_artifact_shape_is_publishable(
                    native_transport
                ));
                assert_eq!(
                    trust_types::transport_proof_artifact_topology_defect(
                        &published.suite,
                        &published.artifacts,
                        transport.obligation_id.as_deref(),
                    ),
                    None
                );
                assert_eq!(
                    trust_types::modern_body_wp_proof_defect(
                        &published.artifacts,
                        transport.obligation_id.as_deref(),
                        published.request_id.as_deref(),
                        published.proof_id.as_deref(),
                        published.strength.as_ref().unwrap(),
                        published.evidence.as_ref().unwrap(),
                        native_transport,
                        None,
                    ),
                    None
                );
                assert!(
                    trust_types::modern_body_wp_proof_defect(
                        &published.artifacts,
                        transport.obligation_id.as_deref(),
                        Some("999"),
                        published.proof_id.as_deref(),
                        published.strength.as_ref().unwrap(),
                        published.evidence.as_ref().unwrap(),
                        native_transport,
                        None,
                    )
                    .is_some()
                );
                let mut changed_result = rows[index].1.clone();
                if let VerificationResult::Proved { time_ms, .. } = &mut changed_result {
                    *time_ms = time_ms.saturating_add(1);
                }
                assert!(!authority.matches_compiler_result(&changed_result));
                assert_eq!(
                    trust_disposition_for_authority(
                        Some(authority),
                        index,
                        &rows[index].0,
                        &changed_result,
                        row_bindings[index].as_ref(),
                    ),
                    None,
                );
                // A previously accepted proof is not a persistent permission:
                // missing or replaced inputs revoke the old private token.
                assert_eq!(
                    super::super::native_wp_source::apply_authorities(
                        &public,
                        Some(&native),
                        &result,
                        None,
                        &mut rows,
                        &row_bindings,
                        &mut authorities,
                    ),
                    0
                );
                assert!(authorities.iter().all(Option::is_none));
                assert_eq!(
                    super::super::native_wp_source::apply_authorities(
                        &public,
                        Some(&native),
                        &result,
                        Some(receipts.checked_native_wp_proofs()),
                        &mut rows,
                        &row_bindings,
                        &mut authorities,
                    ),
                    1
                );
                let empty = BTreeMap::new();
                assert_eq!(
                    super::super::native_wp_source::apply_authorities(
                        &public,
                        Some(&native),
                        &result,
                        Some(&empty),
                        &mut rows,
                        &row_bindings,
                        &mut authorities,
                    ),
                    0
                );
                assert!(authorities.iter().all(Option::is_none));
                assert_eq!(
                    super::super::native_wp_source::apply_authorities(
                        &public,
                        Some(&native),
                        &result,
                        Some(receipts.checked_native_wp_proofs()),
                        &mut rows,
                        &row_bindings,
                        &mut authorities,
                    ),
                    1
                );
                let authorized_index = authorities
                    .iter()
                    .position(|authority| {
                        matches!(authority, Some(ResultProofAuthority::NativeWpSource { .. }))
                    })
                    .expect("fresh native source authority");
                rows[authorized_index].0.location = native_trust_ir_test_span(999);
                assert_eq!(
                    super::super::native_wp_source::apply_authorities(
                        &public,
                        Some(&native),
                        &result,
                        Some(receipts.checked_native_wp_proofs()),
                        &mut rows,
                        &row_bindings,
                        &mut authorities,
                    ),
                    0
                );
                assert!(authorities.iter().all(Option::is_none));
                rows[authorized_index].0 = legacy_vc_from_api_obligation(&function, marker);
                assert_eq!(
                    super::super::native_wp_source::apply_authorities(
                        &public,
                        Some(&native),
                        &result,
                        Some(receipts.checked_native_wp_proofs()),
                        &mut rows,
                        &row_bindings,
                        &mut authorities,
                    ),
                    1
                );
                let mut changed_native = native.clone();
                changed_native.module.functions[0].blocks[0].body[0].inst = trust_ir::Inst::Const {
                    ty: trust_ir::Ty::Bool,
                    value: trust_ir::Constant::Bool(false),
                };
                assert_eq!(
                    super::super::native_wp_source::apply_authorities(
                        &public,
                        Some(&changed_native),
                        &result,
                        Some(receipts.checked_native_wp_proofs()),
                        &mut rows,
                        &row_bindings,
                        &mut authorities,
                    ),
                    0
                );
                assert!(authorities.iter().all(Option::is_none));
            }
        }
    });
}

#[test]
fn query_bound_catalog_refuses_stale_source_identity_and_parameter_bindings() {
    rustc_span::create_default_session_globals_then(|| {
        for mutation in 0..10 {
            let (function, contracts, mut source) = boolean_source(false);
            match mutation {
                0 => source.function_path.push_str("::stale"),
                1 => source.body.ir_param_count = Some(2),
                2 => source.body.params[0].ir_index = 1,
                3 => source.body.clauses[0].ordinal = 1,
                4 => source.body.params[0].name = "unrelated".into(),
                5 => source.body.params[0].mutable = true,
                6 => {
                    let rustc_middle::mir::trust_contract::TrustContractPredicateKind::Typed {
                        proposition,
                        ..
                    } = &mut source.body.clauses[0].predicate
                    else {
                        unreachable!()
                    };
                    *proposition =
                        rustc_middle::mir::trust_contract::TrustContractProposition::Bool(false);
                }
                7 => {
                    let rustc_middle::mir::trust_contract::TrustContractPredicateKind::Typed {
                        text,
                        ..
                    } = &mut source.body.clauses[0].predicate
                    else {
                        unreachable!()
                    };
                    *text = rustc_span::Symbol::intern("__trust_lowered_compiler_contract__:false");
                }
                8 => {} // the public predicate is changed below, without updating its digest
                9 => source.function_path = source.body.def_path.clone(),
                _ => unreachable!(),
            }
            let (vcs, _) =
                trust_vcgen::regenerate_postcondition_production_variants(&function).unwrap();
            let mut public =
                trust_mir_extract::function_to_verifier_api_bundle(&function, &contracts, &vcs);
            if mutation == 8 {
                public.contracts[0].predicate = trust_verifier_api::TrustSpecPredicate::new(
                    trust_verifier_api::TrustSpecExpr::bool_literal(true),
                    Vec::new(),
                )
                .into_contract_predicate()
                .unwrap();
            }
            let native = build_native_trust_ir_bundle_for_test_verifier_api_with_source(
                &function,
                &mut public,
                &vcs,
                Some(&source),
            )
            .unwrap()
            .unwrap();
            assert!(
                public.obligations.iter().all(|obligation| {
                    exactly_one_metadata_value(
                        &obligation.metadata,
                        "trust.ir.raw-source-postcondition.v1",
                    )
                    .is_none()
                }),
                "mutation {mutation} acquired query authority"
            );
            assert!(
                public.contracts.iter().all(|contract| exactly_one_metadata_value(
                    &contract.metadata,
                    trust_verifier_api::TRUST_IR_CLAUSE_BINDINGS_METADATA_KEY,
                )
                .is_none()),
                "mutation {mutation} acquired query-bound clause bindings"
            );
            assert!(public.obligations.iter().all(|obligation| {
                super::super::native_wp_source::formula(&public.contracts, obligation)
                    .unwrap()
                    .is_none()
            }));
            assert!(!native.requests.is_empty(), "the legacy routes remain available");
        }
    });
}
