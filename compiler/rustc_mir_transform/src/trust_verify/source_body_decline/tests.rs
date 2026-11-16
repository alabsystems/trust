//! Actual captured body, reconstructed canonical query sidecar, and explicit
//! unit-test run/placement inputs. These are not live execution receipts.
use trust_types::{
    CompilerContractBundle, CompilerContractProposition, CompilerContractValueDomain,
    CompilerContractVariableDomain, VerifiableFunction,
};

use super::*;

struct Input {
    function: VerifiableFunction,
    contracts: CompilerContractBundle,
    vcs: Vec<VerificationCondition>,
    bundle: trust_verifier_api::TrustContractBundle,
    authority: CompilerFunctionAuthority,
    context: trust_verifier_api::VerifierExecutionSnapshot,
}

fn input() -> Input {
    let function: VerifiableFunction = serde_json::from_str(include_str!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../crates/trust-vcgen/testdata/native-opaque-return-call-e560.json"
    )))
    .unwrap();
    let contract = &function.contracts[0];
    let contracts = CompilerContractBundle::new(function.contracts.clone())
        .with_typed_propositions(vec![CompilerContractProposition {
            source_contract_index: 0,
            kind: contract.kind,
            body: contract.body.clone(),
            formula: function.postconditions[0].clone(),
            variable_domains: ["_0", "x"]
                .into_iter()
                .map(|name| CompilerContractVariableDomain {
                    name: name.into(),
                    domain: CompilerContractValueDomain::MachineInt { width: 8, signed: false },
                })
                .collect(),
        }]);
    // Match the real compiler entry, including interval augmentation. Bare
    // generation missed the range wrapper that broke the live decline binding.
    let context = trust_vcgen::VcgenContext::for_function(function.def_path.clone());
    let mut rows = trust_types::vc_context::VcContext::new();
    let generation = trust_vcgen::generate_vcs_with_discharge_and_overflow_origins(
        &function,
        &trust_vcgen::SummaryDatabase::new(),
        false,
        &context,
        &FxHashSet::<(trust_types::BlockId, usize)>::default(),
        &mut rows,
    );
    assert!(generation.discharged.iter().all(|(vc, _)| vc.kind.declined_contract_body().is_none()));
    let mut vcs = generation.solver_vcs;
    // The compiler's all_vcs carrier includes preclassified rows too.
    vcs.extend(generation.discharged.into_iter().map(|(vc, _)| vc));
    let bundle = trust_mir_extract::function_to_verifier_api_bundle_with_compiler_identity(
        &function,
        &contracts,
        &vcs,
        "n4_runtime_blackbox_monitor",
        0x1234,
        Some(64),
    );
    let authority = CompilerFunctionAuthority::exact(
        trust_verifier_api::FunctionContext {
            crate_name: "n4_runtime_blackbox_monitor".into(),
            path: function.def_path.clone(),
        },
        0x1234,
    );
    let context =
        trust_router::VerifierExecutionContext::new("typed-decline-unit-control").snapshot();
    Input { function, contracts, vcs, bundle, authority, context }
}

fn snapshot(input: &Input) -> ExactFreshVcRekeySnapshot {
    exact_fresh_vc_rekey_snapshot_with_dispatched_obligations(
        &input.function,
        &input.contracts,
        &input.bundle,
        &input.bundle.obligations,
        &input.vcs,
        ExactDefinitionEntryMarkerSet::default(),
        &input.authority,
        input.context.clone(),
    )
}

// Trust: explicit unit-test query record for the captured u8 clause. Production
// gets this record from capture_contract_body; this is not live query authority.
fn opaque_query(input: &Input) -> native_wp_source::CapturedSource {
    use rustc_middle::mir::trust_contract::{
        TrustContractPredicateKind, TrustContractProposition as P,
        TrustContractPropositionDomain as D,
    };
    use trust_thir_lower::contract_carry::{
        CarryClause, CarryParam, ClauseRole, ContractBodyRecord, ParamReference,
    };
    let var = |name| P::Var {
        name: rustc_span::Symbol::intern(name),
        domain: D::MachineInt { width: 8, signed: false },
    };
    native_wp_source::CapturedSource {
        function_path: input.function.def_path.clone(),
        body: ContractBodyRecord {
            def_index: 0,
            def_path: input.function.name.clone(),
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
                    text: rustc_span::Symbol::intern(&input.function.contracts[0].body),
                    proposition: P::Gt(Box::new(var("_0")), Box::new(var("x"))),
                },
                place_bindings: None,
            }],
            loop_headers: vec![],
            refusal: None,
        },
    }
}

#[test]
fn native_body_decline_survives_actual_query_and_native_carrier_transition() {
    rustc_span::create_default_session_globals_then(|| {
        let mut input = input();
        assert_eq!(snapshot(&input).source_body_declines.len(), 1);
        let mut reference = MonitorReference::capture(
            &input.function,
            &input.contracts,
            &input.bundle,
            &input.vcs,
            &input.authority,
        )
        .unwrap();
        let query = opaque_query(&input);
        let native = build_native_trust_ir_bundle_for_test_verifier_api_with_source_and_reference(
            &input.function,
            &mut input.bundle,
            &input.vcs,
            Some(&query),
            Some(&mut reference),
        )
        .unwrap()
        .expect("the captured body must reach native construction");
        assert!(!native.requests.is_empty());
        assert!(input.bundle.contracts.iter().any(|contract| {
            contract
                .metadata
                .iter()
                .any(|entry| entry.key == trust_verifier_api::TRUST_IR_CLAUSE_BINDINGS_METADATA_KEY)
        }));
        let seal = |input: &Input| {
            exact_fresh_vc_rekey_snapshot_with_dispatched_obligations_and_source_reference(
                &input.function,
                &input.contracts,
                &input.bundle,
                &input.bundle.obligations,
                &input.vcs,
                ExactDefinitionEntryMarkerSet::default(),
                &input.authority,
                input.context.clone(),
                Some(&reference),
            )
        };
        let snapshot = seal(&input);
        assert!(snapshot.complete, "native rewriting must retain the whole fresh seal");
        assert_eq!(
            snapshot.source_body_declines.len(),
            1,
            "the real query-owned binding must retain the non-proving source association"
        );
        let native_bundle = input.bundle.clone();
        for mutation in ["changed", "missing", "duplicate", "unknown_contract", "unknown_row"] {
            input.bundle = native_bundle.clone();
            let contract = input
                .bundle
                .contracts
                .iter_mut()
                .find(|contract| {
                    contract.metadata.iter().any(|entry| {
                        entry.key == trust_verifier_api::TRUST_IR_CLAUSE_BINDINGS_METADATA_KEY
                    })
                })
                .unwrap();
            let binding = contract
                .metadata
                .iter()
                .find(|entry| {
                    entry.key == trust_verifier_api::TRUST_IR_CLAUSE_BINDINGS_METADATA_KEY
                })
                .unwrap()
                .clone();
            match mutation {
                "changed" => contract.metadata.iter_mut().find(|entry| entry.key == binding.key)
                    .unwrap().value = "[]".into(),
                "missing" => contract.metadata.retain(|entry| entry.key != binding.key),
                "duplicate" => contract.metadata.push(binding),
                "unknown_contract" => contract.metadata.push(trust_verifier_api::MetadataEntry {
                    key: "unit-control.unknown".into(), value: "unowned".into(),
                }),
                "unknown_row" => input.bundle.obligations.iter_mut().find(|row| {
                    matches!(&row.kind, trust_verifier_api::ObligationKind::Custom { namespace, name }
                        if namespace == "trust.vc" && name == "declined_contract_body")
                }).unwrap().metadata.push(trust_verifier_api::MetadataEntry {
                    key: "unit-control.unknown".into(), value: "unowned".into(),
                }),
                _ => unreachable!(),
            }
            assert!(seal(&input).source_body_declines.is_empty(), "{mutation}");
        }
    });
}

fn run(
    input: &Input,
    change: impl Fn(&mut trust_verifier_api::ObligationEvidence),
) -> trust_verifier_api::VerificationRunResult {
    let engine = trust_verifier_api::EngineManifest::new(
        "trust-full-verifier",
        trust_verifier_api::API_VERSION,
        trust_verifier_api::EngineKind::Composite,
    );
    let evidence = input
        .bundle
        .obligations
        .iter()
        .map(|obligation| {
            let mut row = trust_verifier_api::ObligationEvidence {
                evidence_id: format!("evidence:{}", obligation.obligation_id),
                obligation_id: obligation.obligation_id.clone(),
                engine: engine.clone(),
                status: trust_verifier_api::EvidenceStatus::Unsupported,
                decline: None,
                proof_strength: None,
                artifacts: vec![],
                counterexample: None,
                publication: Default::default(),
                diagnostics: vec![],
            };
            if source_clause_marker_identity(&input.bundle, obligation).is_some() {
                row.diagnostics.push(
                    trust_verifier_api::ROUTED_NATIVE_PRE_SOLVE_INPUT_REFUSAL_DIAGNOSTIC.into(),
                );
            }
            change(&mut row);
            row
        })
        .collect();
    trust_verifier_api::VerificationRunResult::from_evidence(
        input.context.clone(),
        &input.bundle,
        engine,
        &input.bundle.obligations,
        evidence,
    )
}

#[test]
fn native_body_decline_never_becomes_a_proof_and_explains_both_current_rows() {
    rustc_span::create_default_session_globals_then(|| {
        let input = input();
        let snapshot = snapshot(&input);
        assert!(snapshot.complete);
        assert_eq!(snapshot.source_body_declines.len(), 1);
        let run = run(&input, |_| {});
        assert!(run.validate_derived_state().is_ok());
        let (mut results, bindings) = full_verification_legacy_results_bound_with_fresh_vcs(
            &input.function,
            &input.bundle,
            &run,
            &input.vcs,
            &snapshot,
        );
        let mut authorities = vec![None; results.len()];
        apply_exact_source_clause_discharges(
            &input.bundle,
            &run,
            &input.vcs,
            &snapshot,
            &mut results,
            &bindings,
            &mut authorities,
        );
        assert!(
            exact_source_clause_discharge_plans(&input.bundle, &run, &input.vcs, &snapshot)
                .is_empty()
        );
        assert_eq!(
            apply(
                &input.bundle,
                &run,
                &run,
                &input.vcs,
                &snapshot,
                &mut results,
                &bindings,
                &authorities
            ),
            2
        );
        for (vc, result) in &results {
            assert!(matches!(result, VerificationResult::Unknown { .. }));
            assert_eq!(
                trust_types::determinism::StopCause::of_result(result),
                trust_types::determinism::StopCause::Unsupported
            );
            assert!(
                vc.kernel_authority_refusal().is_some()
                    || matches!(vc.formula, Formula::Bool(false))
            );
        }
        assert!(authorities.iter().all(Option::is_none));
    });
}

#[test]
fn native_body_decline_requires_the_entire_nonempty_current_run_and_carrier() {
    rustc_span::create_default_session_globals_then(|| {
        let input = input();
        let snapshot = snapshot(&input);
        let baseline = run(&input, |_| {});
        for alteration in [
            "empty",
            "unrelated_vc",
            "payload",
            "catalog",
            "dispatch",
            "context",
            "duplicate_result",
        ] {
            let mut vcs = input.vcs.clone();
            let mut bundle = input.bundle.clone();
            let mut run = baseline.clone();
            let (mut results, mut bindings) = full_verification_legacy_results_bound_with_fresh_vcs(
                &input.function,
                &input.bundle,
                &baseline,
                &input.vcs,
                &snapshot,
            );
            match alteration {
                "empty" => vcs.clear(),
                "unrelated_vc" => vcs.push(vcs[0].clone()),
                "payload" => vcs[0].formula = Formula::Bool(false),
                "catalog" => bundle.obligations.reverse(),
                "dispatch" => run.requested_obligations.reverse(),
                "context" => run.context.run_id.push_str("-foreign"),
                "duplicate_result" => {
                    results.push(results[0].clone());
                    bindings.push(bindings[0].clone());
                }
                _ => unreachable!(),
            }
            let authorities = vec![None; results.len()];
            assert_eq!(
                apply(
                    &bundle,
                    &baseline,
                    &run,
                    &vcs,
                    &snapshot,
                    &mut results,
                    &bindings,
                    &authorities
                ),
                0,
                "{alteration}"
            );
        }
    });
}

#[test]
fn native_body_decline_result_census_rejects_same_length_admission_substitution() {
    rustc_span::create_default_session_globals_then(|| {
        let input = input();
        let mut snapshot = snapshot(&input);
        let run = run(&input, |_| {});
        let (mut results, mut bindings) = full_verification_legacy_results_bound_with_fresh_vcs(
            &input.function,
            &input.bundle,
            &run,
            &input.vcs,
            &snapshot,
        );
        // Actual native constructor output, not an invented admission spelling.
        let admission = super::super::tests::native_test_default_admission();
        assert!(admission.is_default_admission());
        snapshot.catalog_obligations.push(admission.clone());
        assert_eq!(
            bound_result_rows(&snapshot, &results, &bindings).unwrap().len(),
            results.len(),
            "the synthetic catalog row is not part of the expected result population"
        );
        let vc = legacy_vc_from_api_obligation(&input.function, &admission);
        let binding = result_obligation_binding(0, &vc, &admission)
            .expect("the general binding constructor can represent a synthetic admission");
        assert!(binding.matches_row(0, &vc));
        results[0].0 = vc;
        bindings[0] = Some(binding);
        assert_eq!(
            results.len(),
            snapshot.catalog_obligations.iter().filter(|row| !row.is_default_admission()).count()
        );
        assert!(
            bound_result_rows(&snapshot, &results, &bindings).is_none(),
            "same-length distinct catalog membership cannot replace a required real result"
        );
    });
}

#[test]
fn native_body_decline_preserves_original_and_later_stops_and_failed_markers() {
    rustc_span::create_default_session_globals_then(|| {
        use trust_types::determinism::StopCause;
        let input = input();
        let snapshot = snapshot(&input);
        for cause in [
            StopCause::WallBackstop,
            StopCause::RssBackstop,
            StopCause::SolverFault,
            StopCause::AdmissionRefused,
            StopCause::Unclassified,
        ] {
            let run = run(&input, |row| row.diagnostics.push(cause.stamp("original work stopped")));
            let (mut results, bindings) = full_verification_legacy_results_bound_with_fresh_vcs(
                &input.function,
                &input.bundle,
                &run,
                &input.vcs,
                &snapshot,
            );
            let authorities = vec![None; results.len()];
            keep_exact_source_clause_markers_pending(&input.bundle, &mut results, &bindings);
            assert_eq!(
                apply(
                    &input.bundle,
                    &run,
                    &run,
                    &input.vcs,
                    &snapshot,
                    &mut results,
                    &bindings,
                    &authorities
                ),
                2
            );
            assert!(
                results.iter().all(|(_, result)| StopCause::of_result(result) == cause),
                "{cause}"
            );
        }
        let run = run(&input, |_| {});
        let (mut results, bindings) = full_verification_legacy_results_bound_with_fresh_vcs(
            &input.function,
            &input.bundle,
            &run,
            &input.vcs,
            &snapshot,
        );
        let authorities = vec![None; results.len()];
        let marker = bindings
            .iter()
            .position(|binding| {
                binding.as_ref().is_some_and(|binding| {
                    source_clause_marker_identity(&input.bundle, &binding.canonical_obligation)
                        .is_some()
                })
            })
            .unwrap();
        results[marker].1 = VerificationResult::Unknown {
            solver: "later-work".into(),
            time_ms: 0,
            reason: StopCause::RssBackstop.stamp("later resource stop"),
        };
        apply(
            &input.bundle,
            &run,
            &run,
            &input.vcs,
            &snapshot,
            &mut results,
            &bindings,
            &authorities,
        );
        assert_eq!(StopCause::of_result(&results[marker].1), StopCause::RssBackstop);
        results[marker].1 = VerificationResult::Unknown {
            solver: "trust-exact-source-clause-discharge".into(),
            time_ms: 0,
            reason: StopCause::WallBackstop.stamp("later stop retained the pending solver name"),
        };
        apply(
            &input.bundle,
            &run,
            &run,
            &input.vcs,
            &snapshot,
            &mut results,
            &bindings,
            &authorities,
        );
        assert_eq!(StopCause::of_result(&results[marker].1), StopCause::WallBackstop);
        let failed = VerificationResult::Failed {
            solver: "actual-refutation".into(),
            time_ms: 1,
            counterexample: Some(trust_types::Counterexample::new(vec![])),
        };
        results[marker].1 = failed.clone();
        apply(
            &input.bundle,
            &run,
            &run,
            &input.vcs,
            &snapshot,
            &mut results,
            &bindings,
            &authorities,
        );
        assert_eq!(
            serde_json::to_value(&results[marker].1).unwrap(),
            serde_json::to_value(&failed).unwrap()
        );
    });
}

#[test]
fn native_body_decline_preserves_distinct_current_run_stops() {
    rustc_span::create_default_session_globals_then(|| {
        use trust_types::determinism::StopCause;
        let input = input();
        let snapshot = snapshot(&input);
        let original = run(&input, |_| {});
        for (status, cause) in [
            (trust_verifier_api::EvidenceStatus::Timeout, StopCause::WallBackstop),
            (trust_verifier_api::EvidenceStatus::Canceled, StopCause::WallBackstop),
            (trust_verifier_api::EvidenceStatus::Unknown, StopCause::RssBackstop),
            (trust_verifier_api::EvidenceStatus::Unknown, StopCause::SolverFault),
            (trust_verifier_api::EvidenceStatus::Unknown, StopCause::AdmissionRefused),
            (trust_verifier_api::EvidenceStatus::Unknown, StopCause::Unclassified),
            (trust_verifier_api::EvidenceStatus::Unsupported, StopCause::RssBackstop),
        ] {
            let current = run(&input, |row| {
                row.status = status;
                row.diagnostics.push(cause.stamp("current work stopped after the original run"));
            });
            assert!(exact_fresh_vc_rekey_run_is_complete(
                &input.bundle,
                &current,
                &input.vcs,
                &snapshot
            ));
            let (mut results, bindings) = full_verification_legacy_results_bound_with_fresh_vcs(
                &input.function,
                &input.bundle,
                &original,
                &input.vcs,
                &snapshot,
            );
            let authorities = vec![None; results.len()];
            keep_exact_source_clause_markers_pending(&input.bundle, &mut results, &bindings);
            apply(
                &input.bundle,
                &original,
                &current,
                &input.vcs,
                &snapshot,
                &mut results,
                &bindings,
                &authorities,
            );
            assert!(
                results.iter().all(|(_, result)| StopCause::of_result(result) == cause),
                "distinct current {status:?} must retain {cause}"
            );
        }
    });
}

#[test]
fn native_body_decline_revokes_a_previous_classification_after_current_seal_changes() {
    rustc_span::create_default_session_globals_then(|| {
        use trust_types::determinism::StopCause;
        let input = input();
        let snapshot = snapshot(&input);
        let original = run(&input, |_| {});
        let (mut results, bindings) = full_verification_legacy_results_bound_with_fresh_vcs(
            &input.function,
            &input.bundle,
            &original,
            &input.vcs,
            &snapshot,
        );
        let authorities = vec![None; results.len()];
        assert_eq!(
            apply(
                &input.bundle,
                &original,
                &original,
                &input.vcs,
                &snapshot,
                &mut results,
                &bindings,
                &authorities
            ),
            2
        );
        assert!(
            results
                .iter()
                .all(|(_, result)| StopCause::of_result(result) == StopCause::Unsupported)
        );
        let mut stale = original.clone();
        stale.context.run_id.push_str("-changed");
        assert_eq!(
            apply(
                &input.bundle,
                &original,
                &stale,
                &input.vcs,
                &snapshot,
                &mut results,
                &bindings,
                &authorities
            ),
            0
        );
        assert!(
            results
                .iter()
                .all(|(_, result)| StopCause::of_result(result) == StopCause::Unclassified)
        );
    });
}

#[test]
fn native_body_decline_does_not_explain_unknown_or_proof_bearing_marker_evidence() {
    rustc_span::create_default_session_globals_then(|| {
        use trust_types::determinism::StopCause;
        let input = input();
        let snapshot = snapshot(&input);
        let marker = &snapshot.source_body_declines.values().next().unwrap().marker_id;
        let clean = run(&input, |_| {});
        let mut unbound_refusals = 0;
        let mut bound_refusals = 0;
        for distinct_current in [false, true] {
            for alteration in [
                "unknown",
                "unknown_wall",
                "proved",
                "strength",
                "artifact",
                "counterexample",
                "decline",
                "unqualified",
            ] {
                let run = run(&input, |row| {
                    if &row.obligation_id != marker {
                        return;
                    }
                    match alteration {
                        "unknown" => row.status = trust_verifier_api::EvidenceStatus::Unknown,
                        "unknown_wall" => {
                            row.status = trust_verifier_api::EvidenceStatus::Unknown;
                            row.diagnostics.push(
                                StopCause::WallBackstop.stamp("original native work stopped"),
                            );
                        }
                        "proved" => row.status = trust_verifier_api::EvidenceStatus::Proved,
                        "strength" => {
                            row.proof_strength =
                                Some(trust_verifier_api::ProofStrength::smt_unsat())
                        }
                        "artifact" => row.artifacts.push(trust_verifier_api::EvidenceArtifact {
                            kind: trust_verifier_api::EvidenceArtifactKind::SolverTranscript,
                            uri: "artifact://unit-control/provisional".into(),
                            hash: trust_verifier_api::ArtifactHash {
                                algorithm: "sha256".into(),
                                value: "a".repeat(64),
                            },
                            materialization: None,
                        }),
                        "counterexample" => {
                            row.counterexample = Some(trust_verifier_api::Counterexample {
                                format: "unit-control".into(),
                                data: serde_json::json!({}),
                            })
                        }
                        "decline" => {
                            row.decline = Some(trust_verifier_api::DeclineClass::Capability)
                        }
                        "unqualified" => row.diagnostics.clear(),
                        _ => unreachable!(),
                    }
                });
                let original = if distinct_current { &clean } else { &run };
                let (mut results, bindings) = full_verification_legacy_results_bound_with_fresh_vcs(
                    &input.function,
                    &input.bundle,
                    original,
                    &input.vcs,
                    &snapshot,
                );
                let marker_row = bindings.iter().position(|binding| {
                    binding.as_ref().is_some_and(|binding| &binding.public_obligation_id == marker)
                });
                let authorities = vec![None; results.len()];
                let Some(marker_row) = marker_row else {
                    // Some contradictory proof-bearing rows fail the native
                    // run's derived-state validation before a private binding
                    // can exist. Exercise that earlier refusal too; never
                    // invent a binding merely to reach this later phase.
                    assert!(original.validate_derived_state().is_err(), "{alteration}");
                    assert!(!results.is_empty());
                    assert!(bindings.iter().all(Option::is_none));
                    assert!(results.iter().all(|(_, result)| matches!(
                        result,
                        VerificationResult::Unknown { .. }
                    ) && StopCause::of_result(result)
                        == StopCause::Unclassified));
                    let before = serde_json::to_value(&results).unwrap();
                    assert_eq!(
                        apply(
                            &input.bundle,
                            original,
                            &run,
                            &input.vcs,
                            &snapshot,
                            &mut results,
                            &bindings,
                            &authorities,
                        ),
                        0
                    );
                    assert_eq!(serde_json::to_value(&results).unwrap(), before);
                    assert!(authorities.iter().all(Option::is_none));
                    unbound_refusals += 1;
                    continue;
                };
                apply(
                    &input.bundle,
                    original,
                    &run,
                    &input.vcs,
                    &snapshot,
                    &mut results,
                    &bindings,
                    &authorities,
                );
                assert_eq!(
                    StopCause::of_result(&results[marker_row].1),
                    if alteration == "unknown_wall" {
                        StopCause::WallBackstop
                    } else {
                        StopCause::Unclassified
                    },
                    "{alteration}, distinct current={distinct_current}"
                );
                assert!(authorities.iter().all(Option::is_none));
                bound_refusals += 1;
            }
        }
        assert!(unbound_refusals > 0, "the native integrity rejection must be exercised");
        assert!(bound_refusals > 0, "the bound evidence rejection must be exercised");
    });
}

fn monitor_record(input: &Input) -> ClauseMonitorRecord {
    let proposition = &input.contracts.typed_propositions[0];
    let certified = trust_spec_elab::certify_monitor_from_typed_scope(
        "result > x",
        &[("result", "u8"), ("x", "u8")],
    )
    .expect("actual scalar predicate kernel-certifies");
    let bound = bind_certified_monitor_to_static_formula(
        certified,
        StaticMonitorProposition {
            formula: proposition.formula.clone(),
            variable_domains: proposition.variable_domains.clone(),
        },
    )
    .expect("actual source proposition/evaluator agree");
    ClauseMonitorRecord {
        source_index: 0,
        kind: rustc_middle::mir::trust_contract::TrustContractKind::Ensures,
        subject: rustc_middle::mir::trust_contract::TrustContractSubject::Function,
        span: rustc_span::DUMMY_SP,
        predicate_digest: trust_types::typed_contract_proposition_digest(
            &bound.static_formula,
            &bound.variable_domains,
        ),
        typed_proposition_digest: Some(trust_types::typed_contract_proposition_digest(
            &bound.static_formula,
            &bound.variable_domains,
        )),
        // Explicit unit-test placement input. Production can construct this
        // state only after its existing exact MIR preflight succeeds.
        evidence: ClauseMonitorEvidence::Monitored(bound),
    }
}

#[test]
fn native_body_decline_monitor_uses_exact_constructor_and_live_kernel_record() {
    rustc_span::create_default_session_globals_then(|| {
        let input = input();
        let reference = MonitorReference::capture(
            &input.function,
            &input.contracts,
            &input.bundle,
            &input.vcs,
            &input.authority,
        )
        .unwrap();
        let record = monitor_record(&input);
        let id = reference.claims.keys().next().unwrap();
        let mut bundle = input.bundle.clone();
        stamp_monitors_from_records(
            std::slice::from_ref(&record),
            &input.authority,
            &reference,
            &mut bundle,
        );
        let row = bundle.obligations.iter().find(|row| &row.obligation_id == id).unwrap();
        assert_eq!(
            transport_monitor_evidence_from_metadata(&row.metadata).unwrap().status,
            TransportMonitorStatus::Monitored
        );
        for alteration in [
            "missing_record",
            "duplicate_record",
            "provisional",
            "unmonitored",
            "missing_lowering",
            "duplicate_lowering",
            "changed_lowering",
            "bad_digest",
            "duplicate_digest",
            "unknown_role",
            "duplicate_obligation",
            "predicate",
            "source",
            "claim",
            "context",
            "foreign_crate",
        ] {
            let mut bundle = input.bundle.clone();
            let mut records = vec![record.clone()];
            let row = bundle.obligations.iter_mut().find(|row| &row.obligation_id == id).unwrap();
            match alteration {
                "missing_record" => records.clear(),
                "duplicate_record" => records.push(record.clone()),
                "provisional" => {
                    let ClauseMonitorEvidence::Monitored(bound) = record.evidence.clone() else {
                        panic!()
                    };
                    records[0].evidence = ClauseMonitorEvidence::MonitorCertified(bound);
                }
                "unmonitored" => {
                    records[0].evidence =
                        ClauseMonitorEvidence::Unmonitored { reason: "placement refused".into() }
                }
                "missing_lowering" => {
                    row.metadata.retain(|entry| entry.key != "trust.contract.lowering")
                }
                "duplicate_lowering" => row.metadata.push(
                    row.metadata
                        .iter()
                        .find(|entry| entry.key == "trust.contract.lowering")
                        .unwrap()
                        .clone(),
                ),
                "changed_lowering" => row
                    .metadata
                    .iter_mut()
                    .find(|entry| entry.key == "trust.contract.lowering")
                    .unwrap()
                    .value
                    .push('x'),
                "bad_digest" => {
                    row.metadata
                        .iter_mut()
                        .find(|entry| entry.key == TRUST_CONTRACT_PREDICATE_DIGEST_METADATA_KEY)
                        .unwrap()
                        .value = "bad".into();
                    bundle.contracts[0]
                        .metadata
                        .iter_mut()
                        .find(|entry| entry.key == TRUST_CONTRACT_PREDICATE_DIGEST_METADATA_KEY)
                        .unwrap()
                        .value = "bad".into();
                }
                "duplicate_digest" => row.metadata.push(
                    row.metadata
                        .iter()
                        .find(|entry| entry.key == TRUST_CONTRACT_PREDICATE_DIGEST_METADATA_KEY)
                        .unwrap()
                        .clone(),
                ),
                "unknown_role" => row.metadata.push(trust_verifier_api::MetadataEntry {
                    key: "trust.vc.unknown.role".into(),
                    value: "allowed".into(),
                }),
                "duplicate_obligation" => {
                    let duplicate = row.clone();
                    bundle.obligations.push(duplicate);
                }
                "predicate" => {
                    bundle.contracts[0].predicate =
                        trust_verifier_api::ContractPredicate::TrustExpr { text: "true".into() }
                }
                "source" => row.source.line = Some(999),
                "claim" => row.contract_id.as_mut().unwrap().push('x'),
                "context" => row
                    .metadata
                    .iter_mut()
                    .find(|entry| entry.key == trust_verifier_api::OBLIGATION_CONTEXT_METADATA_KEY)
                    .unwrap()
                    .value
                    .push('x'),
                "foreign_crate" => bundle.bundle_id.push('x'),
                _ => unreachable!(),
            }
            stamp_monitors_from_records(&records, &input.authority, &reference, &mut bundle);
            let row = bundle.obligations.iter().find(|row| &row.obligation_id == id).unwrap();
            assert!(
                transport_monitor_evidence_from_metadata(&row.metadata)
                    .is_none_or(|monitor| monitor.status != TransportMonitorStatus::Monitored),
                "{alteration}"
            );
            if !["missing_record", "duplicate_record", "provisional", "unmonitored"]
                .contains(&alteration)
            {
                assert!(
                    MonitorReference::capture(
                        &input.function,
                        &input.contracts,
                        &bundle,
                        &input.vcs,
                        &input.authority
                    )
                    .is_none(),
                    "{alteration} cannot manufacture its own constructor reference"
                );
            }
        }
        // Re-evaluation revokes an earlier positive stamp; it cannot survive
        // loss of its live record merely because the row metadata was cached.
        stamp_monitors_from_records(&[], &input.authority, &reference, &mut bundle);
        let row = bundle.obligations.iter().find(|row| &row.obligation_id == id).unwrap();
        assert_eq!(
            transport_monitor_evidence_from_metadata(&row.metadata).unwrap().status,
            TransportMonitorStatus::Unmonitored
        );
    });
}
