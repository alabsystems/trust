//! Typed TrustIr native verification bundle indexing and per-suite evidence
//! helpers for the full verifier.

mod bundle_evidence;
mod index;

pub use bundle_evidence::{
    DirectTrustVcProofReceipt, FreshExactDirectChcPdrReceipt,
    trust_wp_native_replay_metadata_entries_for_request,
};
pub(crate) use bundle_evidence::{
    LiveVerificationDispatchSeal, is_native_trust_ir_engine, native_trust_ir_bundle_evidence,
    native_trust_ir_bundle_evidence_is_incomplete,
};
pub(crate) use index::{
    NativeTrustIrEvidenceIndex, NativeTrustIrObligationIdentity, native_trust_ir_artifact_match,
};

use trust_ir_bridge::NativeVerificationBundle;
use trust_verifier_api::{EvidenceArtifact, TrustObligation};

/// Public typed-TrustIr binding-artifact index over a compiler-held
/// `NativeVerificationBundle`.
///
/// This exposes exactly the artifact triple the in-process full-verifier
/// engines attach to a proved obligation's evidence — the bundle, request, and
/// proof-obligation `trust_ir-native://` artifacts, each content-addressed by the
/// bundle/request stable digest computed from the bundle bytes the caller
/// actually holds. The compiler's v1/ay bridge lane uses it to bind its own
/// proof evidence to the same native TrustIr identity that the obligation's
/// `trust.trust_ir.native.*` metadata declares; the digests can only come from a
/// real bundle, never from row text.
#[derive(Debug, Clone)]
pub struct NativeTrustIrBindingIndex {
    index: NativeTrustIrEvidenceIndex,
}

impl NativeTrustIrBindingIndex {
    /// Index the bundle once; per-obligation lookups are cheap.
    #[must_use]
    pub fn from_bundle(bundle: &NativeVerificationBundle) -> Self {
        Self { index: NativeTrustIrEvidenceIndex::from_bundle(bundle) }
    }

    /// The bundle/request/proof `trust_ir-native://` artifact triple binding
    /// `obligation` to its typed native TrustIr request.
    ///
    /// Returns `Ok(None)` when the obligation's kind does not route to a
    /// native-TrustIr suite, and `Err` when the obligation declares a native
    /// identity the bundle does not actually contain (fail-closed: the caller
    /// must not attach binding artifacts it cannot back with bundle bytes).
    pub fn binding_artifacts_for_obligation(
        &self,
        obligation: &TrustObligation,
    ) -> Result<Option<Vec<EvidenceArtifact>>, String> {
        let Some(route) = super::routing::obligation_route(obligation) else {
            return Ok(None);
        };
        self.index
            .artifact_match(route, obligation)
            .map(|matched| matched.map(|matched| matched.artifacts))
    }
}
