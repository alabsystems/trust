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
mod tests;
