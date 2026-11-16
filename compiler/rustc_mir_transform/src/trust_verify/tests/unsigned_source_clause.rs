//! Producer controls over retained integer bodies. Reconstructed query sidecars
//! are explicitly test inputs; the real macro origin is not invented here.
use super::*;

fn input(
    name: &str,
) -> (
    trust_types::VerifiableFunction,
    trust_types::CompilerContractBundle,
    Vec<VerificationCondition>,
    Vec<trust_ir::ProofEvidence>,
) {
    let text = match name {
        "clamp_width" => include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../../crates/trust-source-contract/tests/fixtures/retained-clamp-width.json"
        )),
        "clamp_to_max" => include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../../crates/trust-source-contract/tests/fixtures/retained-clamp-to-max.json"
        )),
        _ => panic!("unknown fixture"),
    };
    let capture: serde_json::Value = serde_json::from_str(text).unwrap();
    let raw = capture["original_function_json"].as_str().unwrap();
    assert_eq!(trust_types::stable_sha256_hex(raw.as_bytes()), capture["function_sha256"]);
    let function: trust_types::VerifiableFunction = serde_json::from_str(raw).unwrap();
    let propositions = function
        .contracts
        .iter()
        .enumerate()
        .map(|(index, contract)| {
            let formula = function.postconditions[index].clone();
            // `free_variables` is a set; sorting makes the collected order
            // deterministic regardless of iteration order.
            #[allow(rustc::potential_query_instability)]
            let mut names = formula.free_variables().into_iter().collect::<Vec<_>>();
            names.sort();
            let domains = names
                .into_iter()
                .map(|name| {
                    let ty = if name == "_0" {
                        &function.body.return_ty
                    } else {
                        &function
                            .body
                            .locals
                            .iter()
                            .find(|decl| trust_vcgen::local_var_name(&function, decl) == name)
                            .unwrap()
                            .ty
                    };
                    let trust_types::Ty::Int { width, signed } = ty else { panic!("not scalar") };
                    trust_types::CompilerContractVariableDomain {
                        name,
                        domain: trust_types::CompilerContractValueDomain::MachineInt {
                            width: *width,
                            signed: *signed,
                        },
                    }
                })
                .collect();
            trust_types::CompilerContractProposition {
                source_contract_index: index,
                kind: contract.kind,
                body: contract.body.clone(),
                formula,
                variable_domains: domains,
            }
        })
        .collect();
    let contracts = trust_types::CompilerContractBundle::new(function.contracts.clone())
        .with_typed_propositions(propositions);
    let proof_capture: serde_json::Value = serde_json::from_str(include_str!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../crates/trust-certify/tests/fixtures/retained-clamp-body-proofs.json"
    )))
    .unwrap();
    let mut vcs = Vec::new();
    let mut proofs = Vec::new();
    for row in capture["body_vcs"].as_array().unwrap() {
        let raw = row["original_vc_json"].as_str().unwrap();
        assert_eq!(trust_types::stable_sha256_hex(raw.as_bytes()), row["payload_sha256"]);
        let proof = proof_capture["rows"]
            .as_array()
            .unwrap()
            .iter()
            .find(|p| p["obligation_id"] == row["obligation_id"])
            .unwrap();
        vcs.push(serde_json::from_str(raw).unwrap());
        proofs.push(serde_json::from_value(proof["evidence"].clone()).unwrap());
    }
    (function, contracts, vcs, proofs)
}

#[test]
fn unsigned_source_question_capture_is_complete_and_non_authoritative() {
    rustc_span::create_default_session_globals_then(|| {
        for name in ["clamp_width", "clamp_to_max"] {
            let (function, contracts, vcs, _) = input(name);
            let bundle =
                trust_mir_extract::function_to_verifier_api_bundle(&function, &contracts, &vcs);
            let captured = capture_source_clause_question(&contracts, &bundle).unwrap();
            assert_eq!(captured, bundle);
            for index in 0..2 {
                assert_eq!(
                    trust_source_contract::exact_ensures_body_group(
                        &function,
                        &contracts,
                        index,
                        &vcs,
                        Some(64),
                        None,
                    )
                    .unwrap()
                    .body_indices()
                    .len(),
                    2
                );
            }
            let mut routed = bundle.clone();
            routed.metadata.push(trust_verifier_api::MetadataEntry {
                key: "independent.route".into(),
                value: "retained".into(),
            });
            let mut extra = routed.obligations[0].clone();
            extra.obligation_id.push_str(":unrelated");
            routed.obligations.push(extra);
            assert_eq!(captured, bundle, "capture must precede all routing additions");
            assert_eq!(routed.obligations.len(), captured.obligations.len() + 1);
            let mut wrong_source = contracts.clone();
            wrong_source.contracts[0].body.push_str(" && true");
            assert!(
                trust_source_contract::exact_ensures_body_group(
                    &function,
                    &wrong_source,
                    0,
                    &vcs,
                    Some(64),
                    None,
                )
                .is_none(),
                "a changed query cannot borrow the original body's proofs"
            );
            let mut narrowed = function.clone();
            narrowed.preconditions.push(Formula::Bool(false));
            assert!(capture_source_clause_question(&contracts, &routed).is_some());
            assert!(
                trust_source_contract::exact_ensures_body_group(
                    &narrowed,
                    &contracts,
                    0,
                    &vcs,
                    Some(64),
                    None,
                )
                .is_none(),
                "retention must never imply admission"
            );
        }
    });
}

#[test]
fn unsigned_source_discharge_requires_actual_complete_body_authorities_and_keeps_rows() {
    rustc_span::create_default_session_globals_then(|| {
        let (function, contracts, vcs, proofs) = input("clamp_width");
        let mut bundle =
            trust_mir_extract::function_to_verifier_api_bundle(&function, &contracts, &vcs);
        let reference = trust_mir_extract::contract_bundle_to_verifier_api(&function, &contracts);
        let captured = capture_source_clause_question(&contracts, &bundle).unwrap();
        bind_exact_source_clause_native_formulas(
            &function,
            &contracts,
            &vcs,
            &reference,
            &mut bundle,
            Some(64),
        );
        let evidence = bundle.obligations.iter().map(unsupported_evidence_for).collect::<Vec<_>>();
        let run = trust_verifier_api::VerificationRunResult::from_evidence(
            trust_router::VerifierExecutionContext::new("unsigned-source-discharge").snapshot(),
            &bundle,
            evidence[0].engine.clone(),
            &bundle.obligations,
            evidence,
        );
        let snapshot = exact_fresh_vc_rekey_snapshot(
            &function,
            &contracts,
            &bundle,
            &vcs,
            run.context.clone(),
        );
        let (mut results, mut bindings) = full_verification_legacy_results_bound_with_fresh_vcs(
            &function, &bundle, &run, &vcs, &snapshot,
        );
        let mut kernel = vec![None; results.len()];
        for (vc, proof) in vcs.iter().zip(proofs) {
            assert!(trust_certify::replay_presented_vc_evidence(vc, &proof));
            let index = results
                .iter()
                .position(|(candidate, _)| RowKey::of(candidate) == RowKey::of(vc))
                .unwrap();
            results[index].1 = authority_test_proved();
            kernel[index] = Some(proof);
        }
        let mut unrelated = vcs[0].clone();
        unrelated.kind = VcKind::Assertion { message: "unrelated retained row".into() };
        unrelated.formula = Formula::Bool(true);
        results.push((
            unrelated,
            VerificationResult::Unknown {
                solver: "unrelated".into(),
                time_ms: 0,
                reason: "keep".into(),
            },
        ));
        bindings.push(None);
        kernel.push(None);
        let original = results.clone();
        let mut missing = build_result_proof_authorities(&results, &bindings, Some(&run), &kernel);
        let body = missing.iter().position(Option::is_some).unwrap();
        missing[body] = None;
        let mut partial = results.clone();
        assert!(
            apply_exact_source_clause_discharges(
                &bundle,
                &run,
                &vcs,
                &snapshot,
                &mut partial,
                &bindings,
                &mut missing
            ) < 2
        );
        let mut authorities =
            build_result_proof_authorities(&results, &bindings, Some(&run), &kernel);
        assert_eq!(
            apply_exact_source_clause_discharges(
                &bundle,
                &run,
                &vcs,
                &snapshot,
                &mut results,
                &bindings,
                &mut authorities
            ),
            2
        );
        assert_eq!(results.len(), original.len());
        for (index, (vc, _)) in original.iter().enumerate() {
            if vc.contract_metadata.is_some() || index == original.len() - 1 {
                assert_eq!(format!("{:?}", results[index]), format!("{:?}", original[index]));
            }
        }
        assert_eq!(
            captured.obligations.iter().filter(|row| !row.is_default_admission()).count() + 1,
            results.len(),
        );
        assert!(authorities.last().unwrap().is_none());
        // No attach() source capture ran in this test: a derived candidate is
        // not a published source certificate or invented macro authority.
        assert!(authorities.iter().filter_map(Option::as_ref).all(|authority| {
            !matches!(
                authority,
                ResultProofAuthority::ExactSourceClauseDischarge { certificate: Some(_), .. }
            )
        }));
    });
}
