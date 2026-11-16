//! Trust: Eligibility to prepare a calculus alternative without losing native
//! or bundled-member debt. This is NOT a proof, checked selector, caller
//! capability, grade or serialized favorable flag. Original carriers are read
//! once while they still exist; the parent separately seals both prepared
//! alternatives and later requires fresh exact artifact/row-set replay.
//! The original independent hard-L0 escalation remains mandatory; this marker
//! cannot suppress its diagnostic or turn a refutation into report success.

use super::*;
/// Borrowed only through eager preparation and the committed paired save.
/// Keeping no cloned RowKey payload or full carrier allows compaction to drop
/// the originals. Only this module can construct the nonserialized marker.
/// The parent must also keep the ORIGINAL preparation stop scope through the
/// paired seal: even the original clock's thread check does not identify a
/// popped/replaced TLS stop scope.
pub(super) struct NativeDebtEligibility<'source> {
    rows: &'source [ExactResultRowIdentity],
    // A real shared borrow freezes the ACTUAL original carrier until paired
    // preparation/sealing ends. Borrowing only the row slice would permit the
    // carrier to change or drop while the marker still appeared usable.
    _original: &'source VerificationArtifacts,
    clock: &'source PendingClock,
}

impl<'source> NativeDebtEligibility<'source> {
    /// The SAME candidate inventory, while its original clock/stop still allows
    /// preparation. This does not mint a final checked-presentation token.
    pub(super) fn candidate_rows(&self) -> Option<&'source [ExactResultRowIdentity]> {
        preparation_allows(self.clock).then_some(self.rows)
    }
}

fn preparation_allows(clock: &PendingClock) -> bool {
    if trust_certify::calculus_row::base::preparation_stop().is_some() {
        return false;
    }
    // Use ONLY the actual original clock: its existing method checks the
    // creating thread and combines genuinely earned later-function credit
    // with fixed inherited/current hard limits. No new capture/mark/credit.
    let Ok(deadline) = clock.deadline() else { return false };
    super::report_deadline_allows(deadline)
}

pub(super) fn covers_native_debt<'source>(
    sess: &Session,
    artifacts: &'source VerificationArtifacts,
    exact_candidate_rows: &'source [ExactResultRowIdentity],
    clock: &'source PendingClock,
) -> Option<NativeDebtEligibility<'source>> {
    if !preparation_allows(clock) || !artifacts.runtime_checked_std_members.is_empty() {
        // Kept runtime checks are real member debt. No original private static
        // authority discharges them merely because a root candidate can replay.
        return None;
    }
    let input = artifacts.calculus_reporting.as_ref()?;
    if clock.deadline != input.deadline {
        // The parent captures this clock ONCE at the original publication
        // entry from these actual inputs, before effectful source facts can
        // earn other-function credit. An unrelated clock is not a substitute.
        return None;
    }
    let run = artifacts.full_verification.as_ref()?;
    let covered = original_carriers_cover_debt(
        run,
        &artifacts.results,
        &artifacts.result_bindings,
        &artifacts.proof_authorities,
        exact_candidate_rows,
        sess.overflow_checks(),
        |id| grounded_panic_freedom_row(sess, id),
        || preparation_allows(clock),
    );
    if !covered {
        return None;
    }
    Some(NativeDebtEligibility {
        rows: exact_candidate_rows, _original: artifacts, clock,
    })
}

/// Same original S4/private-transport predicates, extended to account for ALL
/// requested native members and compiler rows, not only public Proved labels.
/// An Unknown native row can retain an ORIGINAL compiler-private Proved row;
/// Unknown itself grants nothing. Tests inject an explicit grounding lookup
/// without manufacturing a Session or a private proof capability.
fn original_carriers_cover_debt(
    run: &trust_verifier_api::VerificationRunResult,
    results: &[(VerificationCondition, VerificationResult)],
    bindings: &[Option<ResultObligationBinding>],
    authorities: &[Option<ResultProofAuthority>],
    candidates: &[ExactResultRowIdentity],
    overflow_checks: bool,
    grounded_row: impl Fn(&str) -> Option<ExactResultRowIdentity>,
    mut may_continue: impl FnMut() -> bool,
) -> bool {
    if !may_continue()
        || candidates.is_empty()
        || results.len() != bindings.len()
        || results.len() != authorities.len()
        || !run.skipped.is_empty()
        || run.context.cancellation.requested
        || !matches!(
            run.status,
            trust_verifier_api::VerificationRunStatus::Proved
                | trust_verifier_api::VerificationRunStatus::Inconclusive
        )
    {
        return false;
    }
    // Keep the ACTUAL typed run and every derived-state validator unchanged.
    // These existing helpers have no stop callback; fence their entry/exit,
    // and poll every input-sized loop authored below. No new clock or credit.
    if run.validate_derived_state().is_err()
        || !may_continue()
        || native_run_trust_ir_lowering_failed(run)
    {
        return false;
    }
    let binding_rows = build_exact_result_binding_row_index(results, bindings);
    if !may_continue() || !binding_rows.ambiguous_ids.is_empty() {
        return false;
    }
    let evidence_index = build_full_verification_evidence_index(run);
    if !may_continue() || !evidence_index.ambiguous_requested_ids.is_empty() {
        return false;
    }
    let live_run_validation = build_live_authority_run_validation_cache(authorities, run);
    if !may_continue() {
        return false;
    }

    let mut candidate_indices = FxHashSet::default();
    for candidate in candidates {
        if !may_continue() || !candidate_indices.insert(candidate.index) {
            return false;
        }
        let Some((vc, result)) = results.get(candidate.index) else { return false };
        let Some(binding) = bindings[candidate.index].as_ref() else { return false };
        if exact_result_row_identity(candidate.index, vc).as_ref() != Some(candidate)
            || !binding.matches_row(candidate.index, vc)
            || !native_identity_is_complete_and_canonical(&binding.native_identity)
            || !calculus_row_covers(vc, overflow_checks)
            || authorities[candidate.index].is_some()
            || !matches!(result, VerificationResult::Unknown { .. } | VerificationResult::Proved { .. })
        {
            return false;
        }
    }

    let mut original_private_proved = vec![false; results.len()];
    for (row, (vc, result)) in results.iter().enumerate() {
        if !may_continue()
            || matches!(vc.kind, VcKind::UnsupportedMir { .. })
            || result_is_held_assert_refutation(result)
            || !matches!(result, VerificationResult::Unknown { .. } | VerificationResult::Proved { .. })
        {
            return false;
        }
        if let Some(binding) = bindings[row].as_ref() {
            let Some(obligation) = evidence_index.requested_by_id
                .get(binding.public_obligation_id.as_str()).copied()
            else {
                return false;
            };
            // Full canonical equality includes native proof-unit/source facts,
            // context and instance metadata. Same numeric IDs or symbols alone
            // cannot donate a current compiler row to a different request.
            if !binding.matches_row(row, vc) || !binding.matches_public_obligation(obligation) {
                return false;
            }
        }
        if candidate_indices.contains(&row) {
            continue;
        }
        let Some(authority) = authorities[row].as_ref() else { return false };
        if !matches!(result, VerificationResult::Proved { .. })
            || !authority.permits_static_proved_transport_for(row, vc, result, bindings[row].as_ref())
            || !live_authority_run_is_valid(authority, Some(&live_run_validation))
        {
            return false;
        }
        original_private_proved[row] = true;
    }

    for evidence in &run.evidence {
        if !may_continue()
            || !matches!(
                evidence.status,
                trust_verifier_api::EvidenceStatus::Proved | trust_verifier_api::EvidenceStatus::Unknown
            )
            || evidence.counterexample.is_some()
        {
            return false;
        }
        let Some(obligation) = evidence_index.requested_by_id
            .get(evidence.obligation_id.as_str()).copied()
        else {
            return false;
        };
        if obligation.is_default_admission() {
            // Preserve the API's exact synthetic-sentinel exclusion; it is not
            // a safety obligation and pays for no candidate/member debt.
            continue;
        }
        if evidence.status == trust_verifier_api::EvidenceStatus::Proved
            && evidence_index.strict_accepted_by_obligation_id
                .get(evidence.obligation_id.as_str()).copied() != Some(evidence)
        {
            // Exactly the original conflict-free accepted-evidence/lineage
            // bar. A favorable public label is not an accepted private proof.
            return false;
        }
    }

    let mut covered_candidates = FxHashSet::default();
    for obligation in &run.requested_obligations {
        if !may_continue() {
            return false;
        }
        if obligation.is_default_admission() {
            continue;
        }
        let id = obligation.obligation_id.as_str();
        if !evidence_index.evidence_by_obligation_id.contains_key(id) {
            // No unique diagnostic row or exact accepted evidence selected by
            // the original index: absent/ambiguous/unattempted debt remains.
            return false;
        }
        if let Some(grounded) = grounded_row(id) {
            let Some((vc, _)) = results.get(grounded.index) else { return false };
            // The ORIGINAL compiler grounding may retire its public binding.
            // Keep exactly its row seal and private static proof bar. A fresh
            // candidate cannot use that retirement as a made-up binding.
            if exact_result_row_identity(grounded.index, vc).as_ref() != Some(&grounded)
                || candidate_indices.contains(&grounded.index)
                || !original_private_proved[grounded.index]
            {
                return false;
            }
            continue;
        }
        let Some(row) = binding_rows.unique_rows.get(id).copied() else { return false };
        if !bindings[row].as_ref().is_some_and(|binding| binding.matches_public_obligation(obligation)) {
            return false;
        }
        if candidate_indices.contains(&row) {
            if !covered_candidates.insert(row) {
                return false;
            }
        } else if !original_private_proved[row] {
            return false;
        }
    }
    for candidate in candidates {
        if !may_continue() || !covered_candidates.contains(&candidate.index) {
            return false;
        }
    }
    may_continue()
}

#[cfg(test)]
mod tests {
    //! Pure carrier controls, AUTHORED/UNEXECUTED. These are deliberately not
    //! compiler-produced artifacts or VF5/kernel positives. The one positive
    //! ORIGINAL private member authority must be produced by the unchanged
    //! real certification path when the controls actually run, never a hand
    //! constructed KernelCertified or a favorable public label.

    use super::*;

    struct Fixture {
        run: trust_verifier_api::VerificationRunResult,
        results: Vec<(VerificationCondition, VerificationResult)>,
        bindings: Vec<Option<ResultObligationBinding>>,
        authorities: Vec<Option<ResultProofAuthority>>,
        candidates: Vec<ExactResultRowIdentity>,
        certified: Vec<Option<trust_ir::ProofEvidence>>,
    }

    fn obligation(index: u32) -> trust_verifier_api::TrustObligation {
        use trust_verifier_api::{MetadataEntry, ObligationKind, SourceLocation, TrustObligation};
        TrustObligation {
            obligation_id: format!("native-debt:data:{index}"),
            kind: ObligationKind::ArithmeticSafety,
            contract_id: None,
            proof_item_id: None,
            source: SourceLocation {
                file: Some("native-debt-data.rs".into()),
                line: Some(index + 1),
                column: Some(1),
                end_line: Some(index + 1),
                end_column: Some(2),
                ..SourceLocation::default()
            },
            description: "unproved carrier DATA, not compiler evidence".into(),
            required_strength: None,
            summary_facts: Vec::new(),
            metadata: vec![
                MetadataEntry {
                    key: trust_router::full_verification::TRUST_TRUST_IR_NATIVE_VERIFIER_SUITE_METADATA_KEY.into(),
                    value: "trust-mc".into(),
                },
                MetadataEntry {
                    key: trust_router::full_verification::TRUST_TRUST_IR_NATIVE_REQUEST_ID_METADATA_KEY.into(),
                    value: "7".into(),
                },
                MetadataEntry {
                    key: trust_router::full_verification::TRUST_TRUST_IR_NATIVE_PROOF_OBLIGATION_ID_METADATA_KEY.into(),
                    value: index.to_string(),
                },
                MetadataEntry {
                    key: TRUST_TRUST_IR_NATIVE_OBLIGATION_SOURCE_DIGEST_METADATA_KEY.into(),
                    value: "a".repeat(64),
                },
            ],
        }
    }

    fn data_run(
        requested: Vec<trust_verifier_api::TrustObligation>,
        evidence: Option<Vec<trust_verifier_api::ObligationEvidence>>,
    ) -> trust_verifier_api::VerificationRunResult {
        use trust_verifier_api::{
            BundleSubject, EngineKind, EngineManifest, EvidencePublicationMetadata,
            EvidenceStatus, ObligationEvidence, TrustContractBundle, VerificationRunResult,
        };
        let engine = EngineManifest::new("native-debt-data", "unit-control", EngineKind::Reachability);
        let evidence = evidence.unwrap_or_else(|| requested.iter().map(|obligation| {
            ObligationEvidence {
                evidence_id: format!("data:{}", obligation.obligation_id),
                obligation_id: obligation.obligation_id.clone(),
                engine: engine.clone(),
                status: EvidenceStatus::Unknown,
                decline: None,
                proof_strength: None,
                artifacts: Vec::new(),
                counterexample: None,
                publication: EvidencePublicationMetadata::default(),
                diagnostics: Vec::new(),
            }
        }).collect());
        let mut bundle = TrustContractBundle::empty(
            "native-debt-data-bundle",
            BundleSubject::Function {
                crate_name: "native_debt_data".into(), path: "native_debt_data::root".into(),
            },
        );
        bundle.obligations = requested.clone();
        VerificationRunResult::from_evidence(
            trust_router::VerifierExecutionContext::new("native-debt-data-run").snapshot(),
            &bundle, engine, &requested, evidence,
        )
    }

    fn vc(index: u32) -> VerificationCondition {
        VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: trust_types::Symbol::intern(if index == 0 { "data::root" } else { "data::member" }),
            location: trust_types::SourceSpan {
                file: "native-debt-data.rs".into(), line_start: index + 1,
                col_start: 1, line_end: index + 1, col_end: 2,
            },
            // A genuinely false violation, used only for a real certification
            // of the ORIGINAL member row below, not a fake kernel capability.
            formula: trust_types::Formula::Eq(
                Box::new(trust_types::Formula::Int(0)), Box::new(trust_types::Formula::Int(1)),
            ),
            contract_metadata: None,
            obligation: None,
        }
    }

    impl Fixture {
        fn new(with_member: bool) -> Self {
            let mut results = vec![(vc(0), VerificationResult::Unknown {
                solver: "unit-DATA".into(), time_ms: 0, reason: "unproved candidate".into(),
            })];
            let mut requested = vec![obligation(0)];
            if with_member {
                requested.push(obligation(1));
                results.push((vc(1), VerificationResult::Proved {
                    solver: "public-label-alone-is-not-authority".into(),
                    time_ms: 0,
                    strength: ProofStrength::smt_unsat_strict_checked(),
                    proof_certificate: None,
                    solver_warnings: None,
                    native_proof_envelope: None,
                }));
            }
            let bindings = results.iter().zip(&requested).enumerate()
                .map(|(row, ((vc, _), obligation))| result_obligation_binding(row, vc, obligation))
                .collect::<Vec<_>>();
            // This is the existing actual kernel certification + private
            // authority constructor, not an injected/fabricated authority.
            let certified = certify_all(&results, None);
            let authorities = build_result_proof_authorities(&results, &bindings, None, &certified);
            assert!(authorities[0].is_none(), "the Unknown candidate earned no authority");
            if with_member {
                assert!(certified[1].is_some(), "the real kernel must certify the member baseline");
                assert!(matches!(authorities[1], Some(ResultProofAuthority::KernelCertified { .. })));
            }
            Self {
                run: data_run(requested, None),
                candidates: vec![exact_result_row_identity(0, &results[0].0).unwrap()],
                results, bindings, authorities, certified,
            }
        }

        fn covered(&self) -> bool {
            self.covered_with(|_| None, || true)
        }

        fn covered_with(
            &self,
            grounded: impl Fn(&str) -> Option<ExactResultRowIdentity>,
            may_continue: impl FnMut() -> bool,
        ) -> bool {
            original_carriers_cover_debt(
                &self.run, &self.results, &self.bindings, &self.authorities,
                &self.candidates, true, grounded, may_continue,
            )
        }
    }

    #[test]
    fn candidate_and_genuine_original_member_authority_cover_the_full_native_inventory() {
        let fixture = Fixture::new(true);
        fixture.run.validate_derived_state().expect("canonical typed DATA run");
        assert!(fixture.run.evidence.iter().all(|row| row.status == trust_verifier_api::EvidenceStatus::Unknown));
        let before = serde_json::to_value(&fixture.run).unwrap();
        assert!(fixture.covered(), "original private member proof survives native Unknown");
        assert_eq!(serde_json::to_value(&fixture.run).unwrap(), before, "no run/summary rewrite");
    }

    #[test]
    fn genuine_member_population_does_not_cover_added_publisher_debt_or_proved_labels() {
        use super::super::publication_identity::OwedInventory;
        use super::super::proposal::published_complement_is_covered;
        let fixture = Fixture::new(true);
        assert!(fixture.covered(), "actual original kernel member authority is required");
        let expected = build_transport_results_with_runtime_checks_bound(
            true, None, &fixture.results, Some(&fixture.run), &fixture.certified,
            &fixture.bindings, &fixture.authorities,
        );
        assert_eq!(expected.len(), 2);
        assert_eq!(expected[1].outcome, Outcome::Proved,
            "the original transport builder must admit the genuine member proof");
        let candidates = FxHashSet::from_iter([0usize]);
        let candidate_published = FxHashSet::from_iter([0usize]);
        let covers = |actual: &[TransportObligationResult]| {
            let owed = OwedInventory::capture(actual, PublishedRowTally::of(actual, None), || true).unwrap();
            let index = owed.row_index(|| true).unwrap();
            published_complement_is_covered(
                &expected, &candidates, &candidate_published, &owed, &index, || true,
            ).is_some()
        };
        assert!(covers(&expected), "same complete original population joins exactly");
        for outcome in [Outcome::Unknown, Outcome::RuntimeChecked, Outcome::Skipped, Outcome::Proved] {
            let mut actual = expected.clone();
            let mut extra = expected[1].clone();
            extra.obligation_id = Some("publisher-added:debt".into());
            extra.description = "added policy/premise DATA, not original member authority".into();
            extra.outcome = outcome;
            extra.proof_evidence = None;
            extra.grade = None;
            actual.push(extra);
            assert!(!covers(&actual), "added {outcome:?} row is not paid by the root candidate");
        }
        let mut assumed = expected.clone();
        assumed[1].kind = trust_types::assumption::INSTANCE_HYPOTHESIS_DISCHARGE_ROW_KIND.into();
        assumed[1].solver = trust_types::assumption::INSTANCE_HYPOTHESIS_ROW_SOLVER.into();
        let owed = OwedInventory::capture(&assumed, PublishedRowTally::of(&assumed, None), || true).unwrap();
        let index = owed.row_index(|| true).unwrap();
        assert!(published_complement_is_covered(
            &assumed, &candidates, &candidate_published, &owed, &index, || true,
        ).is_none(), "an assumed instance discharge is never an independent static proof");
        let mut missing = expected.clone();
        missing.pop();
        assert!(!covers(&missing), "a missing privately proved member still owes its exact publication");
        let owed = OwedInventory::capture(&expected, PublishedRowTally::of(&expected, None), || true).unwrap();
        let index = owed.row_index(|| true).unwrap();
        assert!(published_complement_is_covered(
            &expected, &candidates, &candidate_published, &owed, &index, || false,
        ).is_none(), "stopped relation work cannot approve a partial denominator");
        // This is a carrier/publication regression with real original member
        // certification, not a compiler-produced module or VF5-positive claim.
    }

    #[test]
    fn noncandidate_member_debt_cannot_be_paid_by_a_root_or_public_proved_label() {
        let mut fixture = Fixture::new(true);
        assert!(fixture.covered());
        fixture.authorities[1] = None;
        assert!(!fixture.covered(), "the member's public Proved label is no authority");

        let mut missing = Fixture::new(true);
        missing.results.truncate(1);
        missing.bindings.truncate(1);
        missing.authorities.truncate(1);
        assert!(!missing.covered(), "the unchanged requested member still owes a real compiler row");
    }

    #[test]
    fn canonical_native_source_and_row_mutations_cannot_donate_candidate_identity() {
        let mut fixture = Fixture::new(false);
        assert!(fixture.covered(), "nonempty native Unknown candidate baseline");
        let mut requested = fixture.run.requested_obligations.clone();
        let identity = native_transport_identity(&requested[0]);
        requested[0].metadata.iter_mut().find(|entry| {
            entry.key == TRUST_TRUST_IR_NATIVE_OBLIGATION_SOURCE_DIGEST_METADATA_KEY
        }).unwrap().value = "b".repeat(64);
        assert_eq!(native_transport_identity(&requested[0]), identity, "numeric native IDs unchanged");
        fixture.run = data_run(requested, None);
        fixture.run.validate_derived_state().unwrap();
        assert!(!fixture.covered(), "full canonical source/instance metadata must still match");

        let mut row = Fixture::new(false);
        row.results[0].0.function = trust_types::Symbol::intern("data::another_instance");
        row.candidates[0] = exact_result_row_identity(0, &row.results[0].0).unwrap();
        assert!(!row.covered(), "recomputed public candidate cannot move the private row binding");
    }

    #[test]
    fn moved_duplicate_or_missing_private_bindings_never_cover_native_debt() {
        let mut swapped = Fixture::new(true);
        assert!(swapped.covered());
        swapped.bindings.swap(0, 1);
        assert!(!swapped.covered());
        let mut duplicate = Fixture::new(false);
        duplicate.candidates.push(duplicate.candidates[0].clone());
        assert!(!duplicate.covered());
        let mut missing = Fixture::new(false);
        missing.bindings[0] = None;
        assert!(!missing.covered());
        let mut collision = Fixture::new(true);
        collision.bindings[1] = result_obligation_binding(
            1, &collision.results[1].0, &collision.run.requested_obligations[0],
        );
        assert!(collision.bindings[1].as_ref().unwrap().matches_row(1, &collision.results[1].0));
        assert!(!collision.covered(), "two current private rows cannot claim one public obligation");
        let mut ambiguous = Fixture::new(false);
        ambiguous.run.requested_obligations.push(ambiguous.run.requested_obligations[0].clone());
        assert!(ambiguous.run.validate_derived_state().is_err());
        assert!(!ambiguous.covered());
        let mut evidence = Fixture::new(false);
        let mut rows = evidence.run.evidence.clone();
        let mut second = rows[0].clone();
        second.evidence_id.push_str(":duplicate-obligation");
        rows.push(second);
        evidence.run = data_run(evidence.run.requested_obligations.clone(), Some(rows));
        evidence.run.validate_derived_state().unwrap();
        assert!(!evidence.covered(), "ambiguous native Unknown evidence is still debt");
    }

    #[test]
    fn skipped_failed_and_incomplete_native_identity_remain_uncovered() {
        let mut fixture = Fixture::new(false);
        assert!(fixture.covered());
        let mut evidence = fixture.run.evidence.clone();
        evidence[0].status = trust_verifier_api::EvidenceStatus::Failed;
        fixture.run = data_run(fixture.run.requested_obligations.clone(), Some(evidence));
        fixture.run.validate_derived_state().unwrap();
        assert!(!fixture.covered(), "a real refutation cannot be hidden by eligibility");
        let mut skipped = Fixture::new(false);
        skipped.run = data_run(skipped.run.requested_obligations.clone(), Some(Vec::new()));
        skipped.run.validate_derived_state().unwrap();
        assert!(!skipped.run.skipped.is_empty());
        assert!(!skipped.covered());

        let mut absent = Fixture::new(false);
        let mut requested = absent.run.requested_obligations.clone();
        requested[0].metadata.retain(|entry| entry.key !=
            trust_router::full_verification::TRUST_TRUST_IR_NATIVE_PROOF_OBLIGATION_ID_METADATA_KEY);
        absent.bindings[0] = result_obligation_binding(0, &absent.results[0].0, &requested[0]);
        absent.run = data_run(requested, None);
        absent.run.validate_derived_state().unwrap();
        assert!(!absent.covered(), "even a matching private row cannot invent an absent native proof ID");
    }

    #[test]
    fn held_refutations_cannot_enter_as_ordinary_unknown_candidates() {
        for reason in [
            TRUST_HELD_ASSERT_REFUTATION_REASON.to_string(),
            format!("{} retained original witness", trust_vcgen::GENERIC_REFUTATION_HELD_PREFIX),
        ] {
            let mut fixture = Fixture::new(false);
            assert!(fixture.covered(), "paired ordinary Unknown carrier baseline");
            fixture.results[0].1 = VerificationResult::Unknown {
                solver: "unit-DATA-held-witness".into(), time_ms: 0, reason: reason.into(),
            };
            assert!(result_is_held_assert_refutation(&fixture.results[0].1));
            assert!(!fixture.covered(),
                "the original held witness cannot become a proposed proof in JSON-only mode");
        }
    }

    #[test]
    fn only_the_exact_original_grounded_member_can_retain_its_private_proof() {
        let mut fixture = Fixture::new(true);
        assert!(fixture.covered());
        let member_id = fixture.run.requested_obligations[1].obligation_id.clone();
        let grounded = exact_result_row_identity(1, &fixture.results[1].0).unwrap();
        fixture.bindings[1] = None; // The ORIGINAL grounding retired this binding.
        assert!(fixture.covered_with(
            |id| (id == member_id).then(|| grounded.clone()), || true,
        ));
        assert!(!fixture.covered(), "no grounding lookup means the retired binding pays nothing");
        let mut wrong = grounded.clone();
        wrong.index = 0;
        assert!(!fixture.covered_with(|id| (id == member_id).then(|| wrong.clone()), || true));
        fixture.results[1].0.formula = trust_types::Formula::Bool(true);
        assert!(!fixture.covered_with(
            |id| (id == member_id).then(|| grounded.clone()), || true,
        ), "the recorded row and original kernel proof cannot follow a changed formula");
    }

    #[test]
    fn every_observed_preparation_checkpoint_can_refuse_without_a_marker() {
        let fixture = Fixture::new(true);
        let mut total = 0;
        assert!(fixture.covered_with(|_| None, || { total += 1; true }));
        assert!(total > 1);
        for cutoff in 0..total {
            let mut seen = 0;
            assert!(!fixture.covered_with(|_| None, || {
                let allowed = seen < cutoff;
                seen += 1;
                allowed
            }), "stopping at checkpoint {cutoff} must retain ordinary debt");
        }
    }
}
