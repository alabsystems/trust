//! Original-carrier eligibility for a proposed DATA delta. This is neither
//! proof nor a selected verdict: only a later fresh opaque current-artifact
//! judgment may authorize its narrow final policy/presentation patch.

use super::*;
use super::super::publication_failure::CandidateRowDebt;
use native_debt::NativeDebtEligibility;
use prepared::PreparedCollection;
use publication_identity::{OwedInventory, RowIndex, row_identity};
use trust_types::determinism::StopCause;

#[derive(serde::Serialize, serde::Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub(super) struct RowOverlay {
    pub(super) vc: usize,
    pub(super) published: usize,
    pub(super) identity: [u8; 32],
}

/// Both borrows remain LIVE in the same original preparation scope until the
/// writer seals Original and Proposed roles. No eligibility is deserialized,
/// cloned or retained with the full source/native carriers after that point.
pub(super) struct PreparedProposal<'native, 'prepared> {
    native: NativeDebtEligibility<'native>,
    _original_failure: Option<CandidateRowDebt<'prepared>>,
    pub(super) overlays: Vec<RowOverlay>,
    pub(super) drop_actions: Vec<usize>,
    pub(super) human_tally: Option<PublishedRowTally>,
    pub(super) owed: &'prepared OwedInventory,
}

/// Small live provenance for the EXACT delta sealed under the original
/// borrows. This is not proof and cannot choose a favorable verdict without
/// a fresh checked current-artifact token. It is never deserialized/cloned.
pub(super) struct SourceApproval {
    overlays: Vec<RowOverlay>,
    drop_actions: Vec<usize>,
    human_tally: Option<PublishedRowTally>,
    owed: [u8; 32],
}

impl SourceApproval {
    pub(super) fn matches(
        &self,
        overlays: &[RowOverlay],
        drop_actions: &[usize],
        human_tally: Option<PublishedRowTally>,
        owed: &OwedInventory,
    ) -> bool {
        self.overlays == overlays && self.drop_actions == drop_actions
            && self.human_tally == human_tally && self.owed == owed.digest()
    }
}

impl PreparedProposal<'_, '_> {
    pub(super) fn still_current(&self) -> bool {
        self.native.candidate_rows().is_some_and(|rows| {
            rows.len() == self.overlays.len()
                && rows.iter().zip(&self.overlays).all(|(row, overlay)| row.index == overlay.vc)
        })
    }

    /// The storage owner calls this only AFTER both accepted-write role
    /// records sealed and still_current rechecked in the SAME original scope.
    /// No original private carrier is retained by this small source approval.
    pub(super) fn into_source_approval(self) -> SourceApproval {
        SourceApproval {
            overlays: self.overlays, drop_actions: self.drop_actions,
            human_tally: self.human_tally, owed: self.owed.digest(),
        }
    }
}

fn amendable_outcome(owed: &OwedInventory, index: usize) -> bool {
    matches!(owed.outcome(index), Some(Outcome::Unknown | Outcome::RuntimeChecked | Outcome::Proved))
        && matches!(owed.stop(index), Some(StopCause::Solved | StopCause::SolverIncomplete | StopCause::Unclassified))
}

pub(super) fn prepare<'native, 'prepared>(
    sess: &Session,
    original: &'prepared PreparedCollection,
    artifacts: &'native VerificationArtifacts,
    rows: &'native [ExactResultRowIdentity],
    clock: &'native PendingClock,
) -> Option<PreparedProposal<'native, 'prepared>> {
    let mut original_failure = None;
    let mut drop_actions = Vec::new();
    drop_actions.try_reserve(original.actions.len()).ok()?;
    for (index, action) in original.actions.iter().enumerate() {
        match action {
            PreparedAction::Diagnostic(diagnostic) if diagnostic.diagnostic.aborting => return None,
            PreparedAction::FullFailure { failure, .. } => {
                if original_failure.is_some() { return None; }
                // Every original source/canonical/nonrow floor is retained.
                // A native coverage marker alone cannot erase its diagnostic.
                original_failure = Some(failure.candidate_row_debt()?);
                drop_actions.push(index);
            }
            PreparedAction::LevelZeroRowFailure(_) => drop_actions.push(index),
            _ => {}
        }
    }
    let native = native_debt::covers_native_debt(sess, artifacts, rows, clock)?;
    let owed = original.owed.as_ref()?;
    // Refutations/timeouts anywhere remain independent original body debt.
    // Added assumptions/premises remain in BOTH plans and in the denominator.
    for index in 0..owed.total() {
        native.candidate_rows()?;
        if matches!(owed.outcome(index), Some(Outcome::Failed | Outcome::Timeout)) {
            return None;
        }
    }
    let published = owed.row_index(|| native.candidate_rows().is_some()).ok()?;
    let mut overlays = Vec::new();
    overlays.try_reserve(rows.len()).ok()?;
    let mut used = FxHashSet::default();
    used.try_reserve(rows.len()).ok()?;
    for row in native.candidate_rows()? {
        let (vc, result) = artifacts.results.get(row.index)?;
        let binding = artifacts.result_bindings.get(row.index)?.as_ref()?;
        let expected = artifacts.transport_results.get(row.index)?;
        if !binding.matches_row(row.index, vc)
            || expected.obligation_id.as_deref() != Some(binding.public_obligation_id.as_str())
            || result_is_held_assert_refutation(result)
        {
            return None;
        }
        let identity = row_identity(expected).ok()?;
        let at = published.unique_row(&identity)?;
        if !used.insert(at) || !amendable_outcome(owed, at) { return None; }
        overlays.push(RowOverlay { vc: row.index, published: at, identity });
    }
    // The marker validated ORIGINAL private static authority for every
    // noncandidate compiler row. Join that exact population to the actual
    // post-prefix publication; a bare extra Proved DATA row is not authority.
    if artifacts.transport_results.len() != artifacts.results.len() { return None; }
    let mut candidate_vcs = FxHashSet::default();
    candidate_vcs.try_reserve(overlays.len()).ok()?;
    candidate_vcs.extend(overlays.iter().map(|row| row.vc));
    published_complement_is_covered(
        &artifacts.transport_results, &candidate_vcs, &used, owed, &published,
        || native.candidate_rows().is_some(),
    )?;
    if let Some(transport) = &original.transport {
        // Only the original row-debt diagnostics follow this boundary. A
        // future reordering must not accidentally erase a prefix/source floor.
        if drop_actions.iter().any(|index| *index < transport.action) { return None; }
    }
    let human_tally = if let Some(human) = &original.human {
        let mut tally = human.original_tally;
        if tally.total() != owed.total() { return None; }
        for overlay in &overlays {
            match owed.outcome(overlay.published)? {
                Outcome::Unknown => tally.unknown = tally.unknown.checked_sub(1)?,
                Outcome::RuntimeChecked => tally.runtime_checked = tally.runtime_checked.checked_sub(1)?,
                Outcome::Proved => continue,
                _ => return None,
            }
            tally.proved = tally.proved.checked_add(1)?;
        }
        let indices = overlays.iter().map(|row| row.vc).collect::<Vec<_>>();
        // Pure validation of the proposed renderer; this creates no proof and
        // does not repeat any authority/source query or infer a certified tier.
        human.facts.render(tally, &indices)?;
        Some(tally)
    } else {
        None
    };
    let prepared = PreparedProposal {
        native, _original_failure: original_failure, overlays,
        drop_actions, human_tally, owed,
    };
    prepared.still_current().then_some(prepared)
}

/// DATA correspondence only. The caller has already validated the actual
/// ORIGINAL private authority for every noncandidate native/compiler row.
/// This relation cannot manufacture that authority from Proved labels.
pub(super) fn published_complement_is_covered(
    expected_rows: &[TransportObligationResult],
    candidate_vcs: &FxHashSet<usize>,
    candidate_published: &FxHashSet<usize>,
    owed: &OwedInventory,
    published: &RowIndex,
    mut may_continue: impl FnMut() -> bool,
) -> Option<()> {
    if !may_continue() { return None; }
    let mut original_proved = FxHashSet::default();
    original_proved.try_reserve(expected_rows.len()).ok()?;
    for (index, expected) in expected_rows.iter().enumerate() {
        if !may_continue() { return None; }
        if candidate_vcs.contains(&index) { continue; }
        if expected.outcome != Outcome::Proved { return None; }
        let at = published.unique_row(&row_identity(expected).ok()?)?;
        if !owed.independently_proved(at) || !original_proved.insert(at) { return None; }
    }
    for index in 0..owed.total() {
        if !may_continue() { return None; }
        if !candidate_published.contains(&index) && !original_proved.contains(&index) {
            // Native coverage accounts its actual typed carrier, not extra
            // publisher rows. Their unrelated debt cannot disappear with the
            // full-failure diagnostic in either JSON-only or human mode.
            return None;
        }
    }
    may_continue().then_some(())
}
