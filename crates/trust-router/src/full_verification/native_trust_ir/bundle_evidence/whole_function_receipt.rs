//! Publication-bound whole-function receipts, separate from formula receipts.

use super::*;

/// Affine live safety proof for one canonical compiler panic aggregate.
/// Public evidence, including an identical serialized run, cannot mint or
/// recreate this value. It is intentionally neither Clone nor serializable.
#[derive(Debug)]
pub struct FreshWholeFunctionChcPdrReceipt {
    #[cfg(feature = "trust-build")]
    inner: trust_bmc::FreshWholeFunctionChcPdrReceipt,
    accepted_evidence: Option<ObligationEvidence>,
    published_run: Option<Arc<LiveVerificationPublishedRun>>,
    #[cfg(not(feature = "trust-build"))]
    unavailable: std::convert::Infallible,
}

impl FreshWholeFunctionChcPdrReceipt {
    #[cfg(feature = "trust-build")]
    pub(super) fn from_native(inner: trust_bmc::FreshWholeFunctionChcPdrReceipt) -> Self {
        Self { inner, accepted_evidence: None, published_run: None }
    }

    #[cfg(feature = "trust-build")]
    #[must_use]
    pub fn public_obligation_id(&self) -> &str {
        self.inner.public_obligation_id()
    }

    #[cfg(feature = "trust-build")]
    #[must_use]
    pub fn dispatch_deadline(&self) -> Option<Instant> {
        self.inner.dispatch_deadline()
    }

    #[cfg(feature = "trust-build")]
    pub(crate) fn exact_bundles_match(
        &self,
        public: &TrustContractBundle,
        native: &NativeVerificationBundle,
    ) -> bool {
        self.inner.bundle_seal().matches_bundles(public, native)
    }

    #[cfg(feature = "trust-build")]
    pub(crate) fn shares_exact_bundles(&self, other: &Self) -> bool {
        self.inner.shares_bundle_seal(&other.inner.bundle_seal())
    }

    #[cfg(feature = "trust-build")]
    pub(crate) fn still_authorizes_sealed_obligation(
        &self,
        obligation: &TrustObligation,
    ) -> Result<trust_verifier_api::ProofStrength, String> {
        self.inner.still_authorizes_under_exact_bundle_seal(&self.inner.bundle_seal(), obligation)
    }

    pub(crate) fn bind_to_accepted_evidence(
        mut self,
        evidence: &ObligationEvidence,
    ) -> Option<Self> {
        if self.accepted_evidence.is_some()
            || evidence.status != EvidenceStatus::Proved
            || evidence.proof_strength.is_none()
        {
            return None;
        }
        self.accepted_evidence = Some(evidence.clone());
        Some(self)
    }

    pub(crate) fn matches_accepted_evidence(&self, evidence: &ObligationEvidence) -> bool {
        accepted_evidence_binding_matches(self.accepted_evidence.as_ref(), evidence)
    }

    pub(crate) fn bind_to_published_run(
        mut self,
        seal: &LiveVerificationDispatchSeal,
    ) -> Option<Self> {
        if self.published_run.is_some()
            || !published_run_contains_exact_evidence(
                &seal.published_run,
                self.accepted_evidence.as_ref()?,
            )
        {
            return None;
        }
        self.published_run = Some(Arc::clone(seal.published_run()));
        Some(self)
    }

    #[cfg(feature = "trust-build")]
    pub(crate) fn authorizes_accepted_evidence(
        &self,
        obligation: &TrustObligation,
        evidence: &ObligationEvidence,
        seal: &LiveVerificationDispatchSeal,
    ) -> Result<trust_verifier_api::ProofStrength, String> {
        if !seal.is_live() || self.dispatch_deadline() != seal.deadline() {
            return Err("whole-function receipt is late, cancelled, or deadline-mismatched".into());
        }
        if evidence.obligation_id != obligation.obligation_id
            || !self.matches_accepted_evidence(evidence)
            || !published_run_binding_matches(self.published_run.as_ref(), seal, evidence)
        {
            return Err(
                "whole-function receipt differs from its exact published dispatch/row".into()
            );
        }
        let strength = self.still_authorizes_sealed_obligation(obligation)?;
        if evidence.proof_strength.as_ref() != Some(&strength) {
            return Err("whole-function receipt differs from the accepted proof grade".into());
        }
        if !seal.is_live() {
            return Err("whole-function receipt expired during replay".into());
        }
        Ok(strength)
    }
}
