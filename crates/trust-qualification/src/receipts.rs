//! The second paired-runner stage: native receipt checks under the original
//! input owner. Consistent self-reported lineage is not build authentication.

use serde::Serialize;
use trust_stage_receipt::{CheckedReceipt, StageReceipt};

use crate::pair::{InspectedPair, Request, Snapshot};
use crate::{Git, Result, refusal};

pub const PENDING_STAGES: &[&str] = crate::pair::PENDING_STAGES.split_at(1).1;
const CLAIM_SCOPE: &str = "checked receipt vocabulary, listed executable bytes and self-reported completed candidate consistency only; no execution, proof, build authentication, candidate qualification or publication authority";

/// A later native stage consumes this owner. There is deliberately no
/// deserializer or constructor from a saved report, and no execution grant.
#[derive(Debug)]
pub struct ReceiptCheckedPair {
    pair: InspectedPair,
    candidate: StageReceipt,
    control: StageReceipt,
    declared_candidate_source_closure_sha256: String,
}

#[derive(Serialize)]
pub struct ReceiptObservation<'a> {
    pub state: &'static str,
    pub raw_sha256: Option<&'a str>,
    pub listed_files_verified: usize,
    pub provenance_lines: Vec<String>,
    pub llvm_identity_unstated_reason: String,
}

#[derive(Serialize)]
pub struct ReceiptReport<'a> {
    pub schema: &'static str,
    pub stage: &'static str,
    pub status: &'static str,
    pub claim_scope: &'static str,
    pub pending_stages: &'static [&'static str],
    pub inputs: &'a Snapshot,
    pub requested_inputs: &'a Request,
    pub candidate_receipt: ReceiptObservation<'a>,
    pub control_receipt: ReceiptObservation<'a>,
    pub declared_candidate_source_closure_sha256: &'a str,
}

fn observation(receipt: &StageReceipt) -> ReceiptObservation<'_> {
    ReceiptObservation {
        state: if receipt.checked().is_some() { "checked" } else { "absent" },
        raw_sha256: receipt.checked().map(CheckedReceipt::raw_sha256),
        listed_files_verified: receipt.checked().map_or(0, CheckedReceipt::files_verified),
        provenance_lines: receipt.provenance_lines(),
        llvm_identity_unstated_reason: receipt.llvm_identity_unstated(),
    }
}

impl InspectedPair {
    /// Validate the candidate before any later compiler/workload activity.
    /// Exact receipt bytes must match those retained by the first stage, and
    /// the complete original source/toolchain/config snapshot is rebound both
    /// before and after reading receipts and their listed executable files.
    pub fn check_receipts(self, git: &impl Git) -> Result<ReceiptCheckedPair> {
        self.check_unchanged(git)?;
        let inputs = self.snapshot();
        let candidate =
            trust_stage_receipt::inspect(&inputs.candidate.path, &inputs.candidate.reported_commit)
                .map_err(|error| refusal(format!("candidate stage receipt: {error}")))?;
        let checked_candidate =
            candidate.checked().ok_or_else(|| refusal("candidate stage receipt is absent"))?;
        if checked_candidate.raw_sha256() != inputs.candidate_receipt.sha256 {
            return Err(refusal("candidate receipt differs from original inspected bytes"));
        }
        let declared_candidate_source_closure_sha256 = checked_candidate
            .completed_candidate(&inputs.candidate.reported_commit)
            .map_err(|error| refusal(format!("completed candidate receipt: {error}")))?
            .declared_source_closure_sha256()
            .to_owned();
        let control =
            trust_stage_receipt::inspect(&inputs.control.path, &inputs.control.reported_commit)
                .map_err(|error| refusal(format!("control stage receipt: {error}")))?;
        self.check_unchanged(git)?;
        Ok(ReceiptCheckedPair {
            pair: self,
            candidate,
            control,
            declared_candidate_source_closure_sha256,
        })
    }
}

impl ReceiptCheckedPair {
    pub fn report(&self) -> ReceiptReport<'_> {
        let mut candidate_receipt = observation(&self.candidate);
        candidate_receipt.state = "completed-candidate-checked";
        ReceiptReport {
            schema: "trust.paired-qualification.v1",
            stage: "stage-receipt-validation",
            status: "receipts-checked",
            claim_scope: CLAIM_SCOPE,
            pending_stages: PENDING_STAGES,
            inputs: self.pair.snapshot(),
            requested_inputs: self.pair.report().requested_inputs,
            candidate_receipt,
            control_receipt: observation(&self.control),
            declared_candidate_source_closure_sha256: &self
                .declared_candidate_source_closure_sha256,
        }
    }

    /// Saved receipt checks never replace rebinding the complete original
    /// inputs before a later stage consumes this live owner.
    pub fn check_unchanged(&self, git: &impl Git) -> Result<()> {
        self.pair.check_unchanged(git)
    }

    pub fn snapshot(&self) -> &Snapshot {
        self.pair.snapshot()
    }
}
