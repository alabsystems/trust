//! Actual maintained kernel replay for each freshly regenerated current row.
//! The compiler's serialized status/evidence/snapshot remains DATA. The
//! enclosing native command/session owner supplies its live origin; only this
//! invocation's real kernel API can return the retained AuditedProof values.
use super::{KernelPreparation, census::Census};
use crate::util::CargoResult;
use anyhow::Context as _;
use std::time::Instant;
use trust_certify::proof_artifacts::{AuditedProof, ProofReplayVcIdentity};
use trust_proof_session::VerificationSession;
use trust_types::{
    FunctionTransportResult, Outcome, TransportObligationResult, VerificationCondition,
    determinism::StopCause,
};

pub(super) struct Row {
    pub function: String,
    pub obligation: Option<String>,
    pub claim: Option<String>,
    // Retain actual replay-entry DATA; only regression diagnostics consume it.
    _replay_entered: bool,
    // All original rows, including refusals, occupy one slot. No favorable
    // subset can shrink the original compiler census or satisfy this node.
    proof: Option<AuditedProof>,
    identity: Option<ProofReplayVcIdentity>,
    vc: Option<Box<VerificationCondition>>,
    pub stop: Option<StopCause>,
    pub failure: Option<anyhow::Error>,
}
pub(super) struct CheckedRows {
    pub rows: Vec<Row>,
    pub input_failures: Vec<anyhow::Error>,
}
impl CheckedRows {
    fn record_session_bookend(&mut self, session: &VerificationSession) {
        if let Err(error) = session.check_current() {
            // Keep the actual error, including native IO/errno, beside every
            // actual proof owner. Restoring names cannot erase this refusal.
            self.input_failures.push(error.into());
        }
    }
    /// Actual per-call observations only; no engine-search counter is inferred.
    #[cfg(test)]
    pub(super) fn observed_work(&self) -> (usize, usize, Option<(usize, usize)>) {
        let entered = self.rows.iter().filter(|row| row._replay_entered).count();
        let proofs = self.rows.iter().filter_map(|row| row.proof.as_ref());
        let mut returned = 0;
        let mut rechecks = 0;
        let mut references = 0;
        let mut complete_kinds = true;
        for proof in proofs {
            returned += 1;
            match proof.audit().map(|audit| audit.kind()) {
                Some(trust_certify::proof_artifacts::ReplayKind::CurrentKernelRecheck) => {
                    rechecks += 1
                }
                Some(trust_certify::proof_artifacts::ReplayKind::CurrentProcessReference) => {
                    references += 1
                }
                None => complete_kinds = false,
            }
        }
        (
            entered,
            returned,
            complete_kinds.then_some((rechecks, references)),
        )
    }
    pub(super) fn require_complete(&self, census: &Census) -> CargoResult<()> {
        anyhow::ensure!(
            self.input_failures.is_empty(),
            "native kernel input post-bookend failed: {}",
            self.input_failures
                .iter()
                .map(super::bounded_reason)
                .collect::<Vec<_>>()
                .join("; ")
        );
        anyhow::ensure!(
            !self.rows.is_empty() && self.rows.len() == census.terminal.total_obligations,
            "native verification kernel result omitted the complete nonzero current population"
        );
        anyhow::ensure!(
            census.coverage.is_complete(),
            "native kernel lost complete current coverage"
        );
        let originals = census.functions.iter().flat_map(|function| {
            function
                .results
                .iter()
                .map(move |original| (function, original))
        });
        for (row, (function, original)) in self.rows.iter().zip(originals) {
            anyhow::ensure!(
                row.function == function.function
                    && row.obligation == original.obligation_id
                    && row.claim == original.claim_digest_sha256,
                "native kernel row was donated from another current function/claim"
            );
            anyhow::ensure!(
                row.failure.is_none() && row.stop.is_none(),
                "native current row {} has no accepted kernel proof: {}",
                row.function,
                row.failure
                    .as_ref()
                    .map(super::bounded_reason)
                    .unwrap_or_else(|| "original kernel budget stopped".into())
            );
            let proof = row
                .proof
                .as_ref()
                .context("native current row omitted its actual kernel proof owner")?;
            let vc = row
                .vc
                .as_ref()
                .context("native kernel row omitted its regenerated current VC")?;
            let expected = original
                .original_vc_snapshot
                .as_ref()
                .context("current compiler row lost its complete original VC snapshot")?
                .decode_for_row(
                    original
                        .obligation_id
                        .as_deref()
                        .context("current obligation is absent")?,
                    original
                        .claim_digest_sha256
                        .as_deref()
                        .context("current claim is absent")?,
                )
                .map_err(anyhow::Error::msg)?;
            anyhow::ensure!(
                row.identity.as_ref() == ProofReplayVcIdentity::of(vc).as_ref()
                    && row.identity.as_ref() == ProofReplayVcIdentity::of(&expected).as_ref(),
                "native kernel proof belongs to another complete current VC"
            );
            // Audit diagnostics do not grant authority. When available they
            // must remain bound to the same actual returned proof and VC.
            if let Some(audit) = proof.audit() {
                anyhow::ensure!(
                    audit.matches(vc, proof.evidence()),
                    "native kernel observation was donated from another proof/VC"
                );
            }
        }
        Ok(())
    }
}

pub(super) fn check(
    census: &Census,
    session: &VerificationSession,
    preparation: &KernelPreparation,
    deadline: Instant,
) -> CargoResult<CheckedRows> {
    preparation.require_current()?;
    session.check_current()?;
    let mut rows = Vec::new();
    rows.try_reserve_exact(census.terminal.total_obligations)?;
    for function in &census.functions {
        for original in &function.results {
            let mut row = Row {
                function: function.function.clone(),
                obligation: original.obligation_id.clone(),
                claim: original.claim_digest_sha256.clone(),
                _replay_entered: false,
                proof: None,
                identity: None,
                vc: None,
                stop: None,
                failure: None,
            };
            let checked = (|| -> CargoResult<()> {
                preparation.require_current()?;
                session.check_current()?;
                replay_current_row(function, original, session, deadline, &mut row)?;
                preparation.require_current()?;
                session.check_current()?;
                anyhow::ensure!(
                    Instant::now() < deadline && row.stop.is_none(),
                    "current native kernel replay stopped at the original deadline/budget"
                );
                anyhow::ensure!(
                    row.proof.is_some(),
                    "current-kernel artifact replay is unavailable for this original row"
                );
                Ok(())
            })();
            if let Err(error) = checked {
                row.failure = Some(error);
            }
            rows.push(row);
        }
    }
    let mut checked = CheckedRows {
        rows,
        input_failures: Vec::new(),
    };
    if let Err(error) = preparation.require_current() {
        checked.input_failures.push(error);
    }
    checked.record_session_bookend(session);
    Ok(checked)
}

/// Mathematical replay only. This private helper never issues a completed
/// native node or supplies source/command/session origin. The production call
/// above always brackets it with the SAME actual paid local preparation.
fn replay_current_row(
    function: &FunctionTransportResult,
    original: &TransportObligationResult,
    session: &VerificationSession,
    deadline: Instant,
    row: &mut Row,
) -> CargoResult<()> {
    anyhow::ensure!(
        Instant::now() < deadline,
        "original native verification node expired"
    );
    anyhow::ensure!(
        original.outcome == Outcome::Proved
            && original.assumes.is_empty()
            && function.modeled_facts.is_empty()
            && !trust_types::assumption::is_instance_hypothesis_discharge_row(
                &original.kind,
                &original.solver
            ),
        "current compiler row is unproved, conditional or a callee assumption"
    );
    let obligation = original
        .obligation_id
        .as_deref()
        .context("current row has no exact obligation identity")?;
    let claim = original
        .claim_digest_sha256
        .as_deref()
        .context("current row has no exact claim binding")?;
    let snapshot = original
        .original_vc_snapshot
        .as_ref()
        .context("current row has no complete regenerated VC snapshot")?;
    let vc = snapshot
        .decode_for_row(obligation, claim)
        .map_err(anyhow::Error::msg)?;
    anyhow::ensure!(
        vc.function.as_str() == function.function
            && original.typed_kind.as_deref() == Some(&vc.kind),
        "current VC snapshot differs from its original function/typed row"
    );
    let identity = ProofReplayVcIdentity::of(&vc)
        .context("current VC exceeds canonical kernel identity bounds")?;
    if let Some(reason) = vc.kernel_authority_refusal() {
        anyhow::bail!("current VC cannot acquire kernel authority: {reason}");
    }
    row._replay_entered = true;
    let (proof, stop) =
        trust_certify::proof_artifacts::replay_vc_with_artifacts_reporting_stop_and_audit_until(
            &vc,
            session.artifact_root(),
            Some(deadline),
        );
    // Save actual returned owners BEFORE any fallible final bookend.
    row.proof = proof;
    row.stop = stop;
    row.identity = Some(identity);
    row.vc = Some(Box::new(vc));
    anyhow::ensure!(
        row.proof.is_some() && row.stop.is_none(),
        "current kernel could not replay this original row within its original budget"
    );
    Ok(())
}

#[cfg(test)]
mod tests;
