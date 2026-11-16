//! The single late selection point. Stored DATA and source eligibility alone
//! select nothing. A fresh kernel token for the actual final published module,
//! exact original row correspondence and the original clock are all required.
//! Every conversion finishes before original policy output is changed.

use super::*;
use prepared::PreparedCollection;
use publication_identity::row_identity;
use stored::RestoredDelta;
use super::super::publication_calculus_transport;
use super::super::publication_transport::FittedFunctionTransport;
use trust_certify::calculus_row::{CalculusRowClaim, hints::CheckedPresentation};

/// Success is consumed immediately by the ordinary final publisher. No new
/// registry/cached result/ResultProofAuthority/caller or optimizer fact is
/// created, and no deserialized grade or Boolean can construct this value.
pub(super) fn apply(
    original: &mut PreparedCollection,
    delta: RestoredDelta,
    checked: &CheckedPresentation,
    claim: &CalculusRowClaim,
    mut still_current: impl FnMut() -> bool,
) -> Option<FittedFunctionTransport> {
    if !still_current() || !checked.matches_claim(claim) || delta.overlays.is_empty() {
        return None;
    }
    let transport = original.transport.as_ref()?;
    let owed = original.owed.as_ref()?;
    if transport.data.result().results.len() != owed.total() { return None; }
    let mut published_indices = Vec::new();
    let mut vc_indices = Vec::new();
    published_indices.try_reserve(delta.overlays.len()).ok()?;
    vc_indices.try_reserve(delta.overlays.len()).ok()?;
    for overlay in &delta.overlays {
        if !still_current() { return None; }
        let row = transport.data.result().results.get(overlay.published)?;
        if row_identity(row).ok()? != overlay.identity { return None; }
        published_indices.push(overlay.published);
        vc_indices.push(overlay.vc);
    }
    // The actual token supplies all mathematical fields and provenance. Its
    // claim is independent of the saved report and the original native/member
    // coverage was sealed while those genuine private carriers were borrowed.
    let checked_rows = publication_calculus_transport::prepare(
        checked, claim, &transport.data.result().results,
        &published_indices, &mut still_current,
    )?;
    let fitted = transport.data.prepare_calculus_selection(checked_rows, &mut still_current)?;
    let human = match delta.human {
        Some(human) => {
            if !still_current() { return None; }
            let mut report = human.facts.render(human.tally, &vc_indices)?;
            report.notes.try_reserve(1).ok()?;
            report.note(format!(
            "VF5 kernel checked the current artifact {:02x?}, function {} / symbol {:02x?}; \
             reference environment {:02x?}, statement {:02x?}. Calculus/model proof retains \
             SemR translation, target kappa and closed-world entry premises; no source-VC \
             encoding, caller propagation or check-elision authority is added",
            checked.artifact_sha256(), checked.fid(), checked.symbol(),
            checked.environment_sha256(), checked.statement_sha256(),
            ));
            Some((human.action, PreparedAction::Note(PreparedLocatedNote {
                span: human.span, report,
            })))
        }
        None => None,
    };
    // Every field/index was authenticated before construction of RestoredDelta.
    // Check the actual destination shapes again before this final, infallible
    // commit. A failure above or here leaves the COMPLETE original unchanged.
    if let Some((index, _)) = &human {
        if !matches!(original.actions.get(*index), Some(PreparedAction::Note(_))) {
            return None;
        }
    }
    for &index in &delta.drop_actions {
        if !still_current() || index < transport.action
            || !matches!(original.actions.get(index), Some(PreparedAction::Diagnostic(_)))
        {
            return None;
        }
    }
    // Linearization point: math replay, all DATA restoration/rendering, exact
    // transport fitting and every hard/inherited stop check have completed.
    // No later query, codec, fitter or proof conversion is needed to emit.
    if !binding_finishes_current(&mut still_current, || checked.matches_claim(claim)) {
        return None;
    }
    if let Some((index, action)) = human {
        original.actions[index] = action;
    }
    let mut index = 0;
    original.actions.retain(|_| {
        let keep = !delta.drop_actions.contains(&index);
        index += 1;
        keep
    });
    Some(fitted)
}

/// Binding hashes the actual input-sized artifact. Currentness must bracket
/// that work; a successful hash cannot carry a pre-hash deadline observation
/// straight into policy/output mutation.
fn binding_finishes_current(
    mut still_current: impl FnMut() -> bool,
    matches_claim: impl FnOnce() -> bool,
) -> bool {
    still_current() && matches_claim() && still_current()
}

#[cfg(test)]
mod tests;
