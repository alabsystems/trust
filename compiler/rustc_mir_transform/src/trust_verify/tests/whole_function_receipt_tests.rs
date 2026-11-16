//! Actual native dispatch plus compiler result-binding controls. These use
//! compiler library fixtures, not a claim that rustc ingested a source file.

use trust_router::full_verification::{
    TRUST_TRUST_IR_NATIVE_PROOF_OBLIGATION_ID_METADATA_KEY,
    TRUST_TRUST_IR_NATIVE_REQUEST_ID_METADATA_KEY,
};

use super::*;

struct WholeFixture {
    function: trust_types::VerifiableFunction,
    native: trust_ir::NativeVerificationBundle,
    source: trust_ir::SourceGenerationAuthority,
    direct: FreshExactDirectCompilerFixture,
    aggregate_index: usize,
}

fn whole_fixture(panic_reachable: bool) -> WholeFixture {
    let function = native_trust_ir_panic_function(panic_reachable);
    let contracts = trust_types::CompilerContractBundle::new(Vec::new());
    let mut bundle =
        trust_mir_extract::function_to_verifier_api_bundle_with_loop_feedback_candidates(
            &function,
            &contracts,
            &[],
            &[],
        );
    ensure_default_trust_mc_function_obligation(&function, &mut bundle).unwrap();
    // The generic test builder intentionally has no Session/target. This
    // explicit fixture profile must enter the real builder BEFORE module,
    // lineage, public-row and live source bindings are computed.
    let mut native = build_native_trust_ir_bundle_from_verifiable_functions(
        &function,
        &mut bundle,
        vec![function.clone()],
        &BundledMemberSourceIdentityLedger::default(),
        &FxHashSet::default(),
        &FxHashSet::default(),
        &FxHashSet::default(),
        &FxHashSet::default(),
        &FxHashSet::default(),
        &FxHashSet::default(),
        &FxHashSet::default(),
        &FxHashSet::default(),
        &FxHashSet::default(), // bundled_destructor_members: none
        &trust_ir_bridge::CallReachWithdrawals::default(), // call_reach_open_callees: no withdrawals
        None,
        None, // borrow_reach_scope
        &trust_ir_bridge::InstanceHypothesisSites::default(),
        &trust_ir_bridge::CompilerAllocGrowPins::default(), // Trust: no grow pins
        None,
        &[],
        &[],
        Some(trust_ir::TargetInfo {
            triple: "aarch64-apple-darwin".into(),
            pointer_size: 8,
            endianness: trust_ir::Endianness::Little,
            abi: None,
            struct_passing: Default::default(),
        }),
        &mut None,
        &mut PanicFreedomFoldAttestation::default(), // not consumed on this seam
        &mut None,       // own-root Assert charges: published only by the live caller
        &mut Vec::new(), // runtime-checked std members: none in a one-body bundle
        false,
        None, // no query/HIR source carry on this fixture
        None, // no private query-bound source reference on this fixture
        &mut None, // no source reference side table on this fixture
    );
    let source = mint_source_generation_authority_for_live_native_bundle(&mut native)
        .expect("existing compiler source-generation seam")
        .expect("native source authority");
    let native = native.unwrap().unwrap();
    let dispatched = bundle.obligations.clone();
    let context = trust_router::VerifierExecutionContext::new("whole-compiler-fixture")
        .with_deadline(std::time::Instant::now() + std::time::Duration::from_secs(60));
    let LiveFullVerificationDispatch { result: final_run, live_receipts } =
        verify_full_bundle_with_live_receipts(
            &bundle,
            &dispatched,
            Some(&native),
            Some(&source),
            None, // no source reference facts
            &context,
            SESSION_DEFAULT_VC_TIMEOUT_MS,
        );
    let live_receipts = live_receipts.expect("actual router receipt package");
    let snapshot = exact_fresh_vc_rekey_snapshot(
        &function,
        &contracts,
        &bundle,
        &[],
        final_run.context.clone(),
    );
    let (results, bindings) = full_verification_legacy_results_bound_with_fresh_vcs(
        &function,
        &bundle,
        &final_run,
        &[],
        &snapshot,
    );
    let source_run = final_run.clone();
    // Preserve both actual rows; never silently discard default admission to
    // manufacture a singleton fixture. Bind mutations to the aggregate itself.
    assert_eq!(bundle.obligations.len(), 2);
    let aggregate_id = bundle
        .obligations
        .iter()
        .find(|row| obligation_is_synthesized_whole_function_panic_freedom(&function, None, row))
        .expect("compiler-generated whole-function aggregate")
        .obligation_id
        .clone();
    let aggregate_index = bindings
        .iter()
        .position(|binding| {
            binding.as_ref().is_some_and(|binding| binding.public_obligation_id == aggregate_id)
        })
        .expect("exact aggregate legacy row");
    WholeFixture {
        function,
        native,
        source,
        aggregate_index,
        direct: FreshExactDirectCompilerFixture {
            bundle,
            dispatched,
            context,
            source_run,
            final_run,
            live_receipts,
            results,
            bindings,
        },
    }
}

fn install_existing_direct(
    fixture: &mut WholeFixture,
    authorities: &mut [Option<ResultProofAuthority>],
) {
    let direct = &mut fixture.direct;
    let expected = direct.live_receipts.fresh_exact_direct_chc_pdr_receipts().len();
    let report = install_fresh_exact_direct_chc_pdr_authorities(
        &direct.bundle,
        &direct.dispatched,
        &direct.context,
        &direct.final_run,
        Some(&mut direct.live_receipts),
        &direct.results,
        &direct.bindings,
        authorities,
    );
    assert_eq!(report.minted, expected, "{:?}", report.rejected);
    assert!(report.rejected.is_empty());
}

fn install_whole(
    fixture: &mut WholeFixture,
    authorities: &mut [Option<ResultProofAuthority>],
) -> super::super::whole_function_receipt::FreshWholeFunctionChcPdrMintReport {
    let direct = &mut fixture.direct;
    install_fresh_whole_function_chc_pdr_authorities(
        &fixture.function,
        &direct.bundle,
        &direct.dispatched,
        Some(&fixture.native),
        Some(&fixture.source),
        &direct.context,
        &direct.final_run,
        Some(&mut direct.live_receipts),
        &direct.results,
        &direct.bindings,
        authorities,
    )
}

#[test]
fn whole_function_compiler_receipt_preserves_distinct_trusted_grade_and_transport() {
    let mut fixture = whole_fixture(false);
    assert_eq!(
        fixture.direct.live_receipts.fresh_whole_function_chc_pdr_receipts().len(),
        1,
        "{:#?}",
        fixture.direct.final_run
    );
    let mut authorities = vec![None; fixture.direct.results.len()];
    assert!(
        !native_proved_authority_validation_failures(
            Some(&fixture.direct.final_run),
            &fixture.direct.results,
            &fixture.direct.bindings,
            &authorities,
        )
        .is_empty(),
        "public Proved is not authority"
    );
    let report = install_whole(&mut fixture, &mut authorities);
    assert_eq!(report.minted, 1, "{:?}", report.rejected);
    assert!(report.rejected.is_empty());
    install_existing_direct(&mut fixture, &mut authorities);
    let direct = &fixture.direct;
    let index = fixture.aggregate_index;
    let authority = authorities[index].as_ref().unwrap();
    assert!(matches!(authority, ResultProofAuthority::FreshWholeFunctionChcPdr { .. }));
    let (vc, result) = &direct.results[index];
    assert_eq!(
        trust_disposition_for_authority(
            Some(authority),
            index,
            vc,
            result,
            direct.bindings[index].as_ref(),
        ),
        Some((TrustStatus::Trusted, TrustProofStrength::Inductive))
    );
    assert!(!authority.is_fresh_exact_direct_chc_pdr_for(
        index,
        vc,
        result,
        direct.bindings[index].as_ref()
    ));
    assert!(!authority.is_exact_source_clause_body_proof_for(
        index,
        vc,
        result,
        direct.bindings[index].as_ref()
    ));
    assert!(authority.kernel_evidence_for(index, vc, direct.bindings[index].as_ref()).is_none());
    assert!(
        native_proved_authority_validation_failures(
            Some(&direct.final_run),
            &direct.results,
            &direct.bindings,
            &authorities,
        )
        .is_empty()
    );
    let transport = build_transport_results_with_runtime_checks_bound(
        false,
        None,
        &direct.results,
        Some(&direct.final_run),
        &[],
        &direct.bindings,
        &authorities,
    );
    assert_eq!(transport[index].outcome, Outcome::Proved);
    assert!(transport[index].proof_evidence.is_some(), "real native artifact evidence retained");
    assert!(
        results_establish_unconditional_panic_freedom(
            &direct.results,
            &direct.bindings,
            &authorities,
        ),
        "actual all-input whole query, not sibling-only subsumption"
    );
    // Combining an actual whole-query receipt with definition-entry assumption
    // bookkeeping must not publish an unconditional callee theorem.
    let mut conditional_results = direct.results.clone();
    let mut conditional_bindings = direct.bindings.clone();
    let mut conditional_authorities = authorities.clone();
    let entry_index = conditional_results.len();
    let entry_vc = test_vc(2);
    let entry_binding = result_obligation_binding_with_compiler_assumptions(
        entry_index,
        &entry_vc,
        &authority_test_native_obligation("whole:entry-assumption", 72, 2),
        true,
        false,
    )
    .unwrap();
    conditional_authorities.push(Some(ResultProofAuthority::DefinitionEntryAssumption {
        row: exact_result_row_identity(entry_index, &entry_vc).unwrap(),
        binding: entry_binding.clone(),
    }));
    conditional_bindings.push(Some(entry_binding));
    conditional_results.push((
        entry_vc,
        VerificationResult::Proved {
            solver: trust_types::Symbol::intern(TRUST_ENTRY_ASSUMPTION_SOLVER),
            time_ms: 0,
            strength: trust_types::ProofStrength::deductive(),
            proof_certificate: None,
            solver_warnings: None,
            native_proof_envelope: None,
        },
    ));
    assert!(
        !results_establish_unconditional_panic_freedom(
            &conditional_results,
            &conditional_bindings,
            &conditional_authorities,
        ),
        "requires assumptions still block unconditional registry admission"
    );
    let again = install_whole(&mut fixture, &mut authorities);
    assert_eq!(again.minted, 0, "receipt consumed exactly once");
}

#[test]
fn whole_function_compiler_receipt_rejects_actual_reachable_panic() {
    let mut fixture = whole_fixture(true);
    assert!(fixture.direct.live_receipts.fresh_whole_function_chc_pdr_receipts().is_empty());
    assert_eq!(fixture.direct.final_run.summary.proved, 0, "{:#?}", fixture.direct.final_run);
    assert!(fixture.direct.results.iter().all(|(_, result)| !result.is_proved()));
    let aggregate_id =
        &fixture.direct.bindings[fixture.aggregate_index].as_ref().unwrap().public_obligation_id;
    let actual = fixture
        .direct
        .final_run
        .evidence
        .iter()
        .find(|row| &row.obligation_id == aggregate_id)
        .unwrap();
    // Public failure authority is independently gated: this whole-function
    // proof-only route does not yet carry the native refutation witness.
    assert_eq!(actual.status, trust_verifier_api::EvidenceStatus::Unsupported, "{actual:#?}");
    assert!(actual.counterexample.is_none());
    let digest = fixture.native.stable_digest();
    assert!(fixture.source.authorizes_bundle(&fixture.native));
    let runner = trust_mc_driver::NativeTrustIrChcPdrRunner::with_solve_options(
        trust_mc_core::ChcPdrSolveOptions::default()
            .with_timeout(std::time::Duration::from_secs(30)),
    );
    // Match the production native solve configuration: standalone certificate
    // export is not supported. This probe requires a real typed counterexample,
    // not proof publication and not a certificate-export refusal.
    assert!(!runner.solve_options().produce_proof_certificate);
    let native_outcome = runner
        .solve_bundle_native_proof_grade_with_source_authority(&fixture.native, &fixture.source)
        .expect("actual source-authorized solve of the identical native bundle");
    assert!(native_outcome.obligations.is_empty());
    let public = fixture
        .direct
        .bundle
        .obligations
        .iter()
        .find(|row| &row.obligation_id == aggregate_id)
        .unwrap();
    let request_id: u32 =
        unique_api_obligation_metadata_value(public, TRUST_TRUST_IR_NATIVE_REQUEST_ID_METADATA_KEY)
            .unwrap()
            .parse()
            .unwrap();
    let proof_id: u32 = unique_api_obligation_metadata_value(
        public,
        TRUST_TRUST_IR_NATIVE_PROOF_OBLIGATION_ID_METADATA_KEY,
    )
    .unwrap()
    .parse()
    .unwrap();
    let retained = native_outcome
        .not_proved
        .iter()
        .find(|row| {
            row.translated.request_id.index() == request_id
                && row.translated.obligations.iter().map(|id| id.index()).collect::<Vec<_>>()
                    == vec![proof_id]
        })
        .expect("exact aggregate request retained by the proof-only adapter");
    let fresh = runner.translate_obligations(&fixture.native).unwrap();
    let translated =
        fresh.iter().find(|row| row.request_id == retained.translated.request_id).unwrap();
    assert_eq!(translated.function, retained.translated.function);
    assert_eq!(translated.obligations, retained.translated.obligations);
    assert_eq!(translated.lineage_roots, retained.translated.lineage_roots);
    assert!(translated.diagnostics.is_empty());
    assert!(retained.translated.diagnostics.is_empty());
    assert_eq!(
        trust_mc_driver::normalized_typed_chc_pdr_input(&translated.obligation).unwrap(),
        trust_mc_driver::normalized_typed_chc_pdr_input(&retained.translated.obligation).unwrap(),
        "same full translated query, not just matching IDs",
    );
    assert_eq!(
        translated.obligation.native_metadata,
        retained.translated.obligation.native_metadata
    );
    let typed =
        trust_mc_driver::NativeTypedChcPdrRunner::with_options(runner.solve_options().clone())
            .solve_full_verification(translated.obligation.clone())
            .unwrap();
    assert_eq!(typed.outcome.obligation_id, translated.obligation.obligation_id);
    assert!(
        matches!(
            &typed.outcome.status,
            trust_mc_core::ChcPdrSolveStatus::Refuted { witness: Some(_) }
        ),
        "actual typed counterexample required; Unknown/unsupported text cannot pass: {typed:#?}"
    );
    assert_eq!(fixture.native.stable_digest(), digest);
    assert!(fixture.source.authorizes_bundle(&fixture.native));
    let mut authorities = vec![None; fixture.direct.results.len()];
    assert_eq!(install_whole(&mut fixture, &mut authorities).minted, 0);
    assert!(authorities.iter().all(Option::is_none));
}

#[test]
fn whole_function_compiler_receipt_refuses_pre_mint_mutations() {
    for mutation in 0..7 {
        let mut fixture = whole_fixture(false);
        assert_eq!(fixture.direct.live_receipts.fresh_whole_function_chc_pdr_receipts().len(), 1);
        let mut authorities = vec![None; fixture.direct.results.len()];
        let index = fixture.aggregate_index;
        let id = fixture.direct.bindings[index].as_ref().unwrap().public_obligation_id.clone();
        match mutation {
            0 => fixture.direct.results[index].0.formula = Formula::Bool(true),
            1 => fixture.direct.bindings[index] = None,
            2 => fixture
                .direct
                .bundle
                .obligations
                .iter_mut()
                .find(|row| row.obligation_id == id)
                .unwrap()
                .description
                .push_str(" changed"),
            3 => fixture.native = fixture.native.clone(), // equal content, erased live marker
            4 => fixture.function.def_path.push_str("_foreign"),
            5 => fixture
                .direct
                .final_run
                .evidence
                .iter_mut()
                .find(|row| row.obligation_id == id)
                .unwrap()
                .diagnostics
                .push("changed".into()),
            _ => {
                fixture.direct.context =
                    fixture.direct.context.clone().with_deadline(
                        std::time::Instant::now() - std::time::Duration::from_secs(1),
                    );
            }
        }
        let report = install_whole(&mut fixture, &mut authorities);
        assert_eq!(report.minted, 0, "mutation {mutation}");
        assert!(!report.rejected.is_empty(), "mutation {mutation}");
        assert!(authorities.iter().all(Option::is_none));
        assert!(fixture.direct.live_receipts.fresh_whole_function_chc_pdr_receipts().is_empty());
    }
}

#[test]
fn whole_function_compiler_receipt_refuses_post_mint_row_result_and_public_run_mutations() {
    let mut fixture = whole_fixture(false);
    let mut authorities = vec![None; fixture.direct.results.len()];
    assert_eq!(install_whole(&mut fixture, &mut authorities).minted, 1);
    install_existing_direct(&mut fixture, &mut authorities);
    assert!(
        native_proved_authority_validation_failures(
            Some(&fixture.direct.final_run),
            &fixture.direct.results,
            &fixture.direct.bindings,
            &authorities
        )
        .is_empty()
    );
    let index = fixture.aggregate_index;
    for mutation in 0..5 {
        let mut results = fixture.direct.results.clone();
        let mut bindings = fixture.direct.bindings.clone();
        let mut run = fixture.direct.final_run.clone();
        match mutation {
            0 => results[index].0.formula = Formula::Bool(true),
            1 => results[index].0.location.line_start += 1,
            2 => bindings[index] = None,
            3 => {
                let VerificationResult::Proved { solver_warnings, .. } = &mut results[index].1
                else {
                    panic!("actual Proved fixture");
                };
                *solver_warnings = Some(vec!["changed result".into()]);
            }
            _ => run.evidence[0].diagnostics.push("changed final run".into()),
        }
        assert!(
            !native_proved_authority_validation_failures(
                Some(&run),
                &results,
                &bindings,
                &authorities,
            )
            .is_empty(),
            "mutation {mutation}"
        );
    }
}

#[test]
fn whole_function_compiler_receipt_cannot_cross_live_dispatches_or_replace_authority() {
    let mut first = whole_fixture(false);
    let mut second = whole_fixture(false);
    std::mem::swap(&mut first.direct.live_receipts, &mut second.direct.live_receipts);
    let mut authorities = vec![None; first.direct.results.len()];
    let report = install_whole(&mut first, &mut authorities);
    assert_eq!(report.minted, 0);
    assert!(!report.rejected.is_empty());

    let mut fixture = whole_fixture(false);
    let index = fixture.aggregate_index;
    let vc = &fixture.direct.results[index].0;
    let prior = ResultProofAuthority::DefinitionEntryAssumption {
        row: exact_result_row_identity(index, vc).unwrap(),
        binding: fixture.direct.bindings[index].clone().unwrap(),
    };
    let mut authorities = vec![None; fixture.direct.results.len()];
    authorities[index] = Some(prior);
    assert_eq!(install_whole(&mut fixture, &mut authorities).minted, 0);
    assert!(matches!(
        authorities[index],
        Some(ResultProofAuthority::DefinitionEntryAssumption { .. })
    ));
}
