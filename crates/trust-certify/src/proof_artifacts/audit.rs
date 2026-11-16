//! Observations of proof-artifact replay, never stored acceptance or row authority.

use super::*;

/// Which actual replay path supplied the returned evidence. This is not a
/// count of the kernel's internal inferences or a statement about solver work.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum ReplayKind {
    CurrentKernelRecheck,
    CurrentProcessReference,
}

/// A non-authority observation minted only for an admitted artifact replay.
/// It cannot deserialize a saved verdict, mint a certificate or permit a row.
/// Publication must additionally check its final exact-row and grade gates.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ReplayAudit {
    schema: u32,
    kind: ReplayKind,
    function: String,
    full_vc_sha256: String,
    proof_evidence_sha256: String,
    lineage_sha256: String,
}

impl ReplayAudit {
    pub(super) fn new(
        vc: &VerificationCondition,
        evidence: &ProofEvidence,
        kind: ReplayKind,
    ) -> Option<Self> {
        let max_depth = super::super::vc_max_depth_within_gate(vc)?;
        if max_depth <= super::super::SHALLOW_CALLER_STACK_MAX_DEPTH
            || super::super::ON_CERTIFY_STACK.with(std::cell::Cell::get)
        {
            let out = Self::encode_on_stack(vc, evidence, kind);
            if let Some(cause) = trust_types::verify_budget::exhaustion_cause() {
                super::super::note_certify_stop(cause);
            }
            return out;
        }
        super::super::on_certify_stack(|| Self::encode_on_stack(vc, evidence, kind))
    }

    fn encode_on_stack(
        vc: &VerificationCondition,
        evidence: &ProofEvidence,
        kind: ReplayKind,
    ) -> Option<Self> {
        let identity = super::super::ObligationIdentity::from_vc(vc)?;
        let ProofEvidence::CleanCic { lineage, .. } = evidence else {
            return None;
        };
        let lineage = bincode::serialize(lineage).ok()?;
        let encoded_evidence = bincode::serialize(evidence).ok()?;
        let mut proof = Sha256::new();
        proof.update(b"trust.proof-artifact.replay-audit.v1\0");
        proof.update((encoded_evidence.len() as u64).to_le_bytes());
        proof.update(encoded_evidence);
        Some(Self {
            schema: 1,
            kind,
            function: vc.function.to_string(),
            full_vc_sha256: digest(&identity.encoded),
            proof_evidence_sha256: format!("{:x}", proof.finalize()),
            lineage_sha256: digest(&lineage),
        })
    }

    #[must_use]
    pub fn kind(&self) -> ReplayKind {
        self.kind
    }

    /// Exact observation binding only. A match confers no proof authority and
    /// must never replace the final row's own certificate/admission checks.
    #[must_use]
    pub fn matches(&self, vc: &VerificationCondition, evidence: &ProofEvidence) -> bool {
        Self::new(vc, evidence, self.kind).as_ref() == Some(self)
    }

    /// Compare serialized diagnostic data with a newly computed observation.
    /// This neither deserializes an admitted audit nor checks/accepts a proof;
    /// the caller must retain its independent current-row and proof authority.
    /// Unknown fields, versions, kinds and changed bindings do not match.
    #[must_use]
    pub fn matches_serialized_observation(
        observation: &serde_json::Value,
        vc: &VerificationCondition,
        evidence: &ProofEvidence,
    ) -> bool {
        [ReplayKind::CurrentKernelRecheck, ReplayKind::CurrentProcessReference].into_iter().any(
            |kind| {
                Self::new(vc, evidence, kind)
                    .and_then(|audit| serde_json::to_value(audit).ok())
                    .as_ref()
                    == Some(observation)
            },
        )
    }
}

/// Carries the observation with the exact proof returned by this invocation.
/// `None` means no artifact-replay observation, never "fresh search" or zero.
#[derive(Debug)]
#[must_use]
pub struct AuditedProof {
    evidence: ProofEvidence,
    audit: Option<ReplayAudit>,
}

impl AuditedProof {
    pub(super) fn new(evidence: ProofEvidence, audit: Option<ReplayAudit>) -> Self {
        Self { evidence, audit }
    }

    #[must_use]
    pub fn evidence(&self) -> &ProofEvidence {
        &self.evidence
    }

    #[must_use]
    pub fn audit(&self) -> Option<&ReplayAudit> {
        self.audit.as_ref()
    }

    #[must_use]
    pub fn into_parts(self) -> (ProofEvidence, Option<ReplayAudit>) {
        (self.evidence, self.audit)
    }
}
