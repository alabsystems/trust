//! Reusable evidence that the native body checker accepted one exact claim.

use std::sync::Arc;

use sha2::{Digest, Sha256};
use trust_ir::NativeVerificationBundle;
use trust_verifier_api::{ObligationEvidence, ProofStrength, TrustContractBundle, TrustObligation};

/// A checked body-WP fact, bound to its program, public claim and accepted row.
///
/// Only the native certificate checker can create this value. Cloning it
/// shares the checked immutable inputs; checking its bindings does not run a
/// solver or rederive the proof. It carries Sound/Deductive evidence, never
/// Clean-kernel certification or source-generation authority.
#[derive(Debug, Clone)]
pub struct CheckedNativeWpProof {
    native: Arc<NativeVerificationBundle>,
    public_semantic_digest: String,
    accepted_evidence_digest: [u8; 32],
    native_request_id: u32,
    native_proof_id: u32,
    #[cfg(feature = "trust-build")]
    translation_witness: Option<trust_wp_lib::trust_ir_body::NativeBodyWpTranslationWitness>,
}

impl CheckedNativeWpProof {
    #[cfg(feature = "trust-build")]
    pub(super) fn new(
        native: Arc<NativeVerificationBundle>,
        public_semantic_digest: String,
        accepted_evidence: &ObligationEvidence,
        native_request_id: u32,
        native_proof_id: u32,
        translation_witness: Option<trust_wp_lib::trust_ir_body::NativeBodyWpTranslationWitness>,
    ) -> Option<Self> {
        Some(Self {
            native,
            public_semantic_digest,
            accepted_evidence_digest: evidence_digest(accepted_evidence)?,
            native_request_id,
            native_proof_id,
            translation_witness,
        })
    }

    /// Match all semantic inputs and the complete accepted evidence row.
    /// Unrelated public catalog entries need not invalidate this fact; the
    /// canonical digest covers the referenced contract and its full context.
    #[must_use]
    pub fn matches(
        &self,
        public: &TrustContractBundle,
        native: &NativeVerificationBundle,
        obligation: &TrustObligation,
        accepted_evidence: &ObligationEvidence,
    ) -> bool {
        evidence_digest(accepted_evidence) == Some(self.accepted_evidence_digest)
            && obligation.obligation_id == accepted_evidence.obligation_id
            && native == self.native.as_ref()
            && self.matches_original_program_binding(obligation)
            && public
                .canonical_obligation_semantic_digest_sha256(obligation)
                .is_ok_and(|digest| digest == self.public_semantic_digest)
    }

    fn matches_original_program_binding(&self, obligation: &TrustObligation) -> bool {
        #[cfg(feature = "trust-build")]
        {
            self.native.module.proof_obligations.iter()
                .find(|proof| proof.id.index() == self.native_proof_id)
                .is_some_and(|proof| {
                    trust_verifier_api::native_contract_claim::validate_native_public_module_binding(
                        &self.native.module, proof, obligation,
                    ).is_ok()
                })
        }
        #[cfg(not(feature = "trust-build"))]
        {
            let _ = obligation;
            false
        }
    }

    #[must_use]
    pub fn proof_strength(&self) -> ProofStrength {
        ProofStrength::deductive()
    }

    /// The native WP request whose certificate was replayed, which can differ
    /// from the public obligation's original primary-engine request.
    #[must_use]
    pub fn native_request_id(&self) -> u32 {
        self.native_request_id
    }

    /// The native proof obligation selected by the replayed WP request.
    #[must_use]
    pub fn native_proof_id(&self) -> u32 {
        self.native_proof_id
    }

    /// Diagnostic translation data checked against this fact's exact native
    /// input and accepted certificate. A present witness is correspondence,
    /// not a translation theorem, source authority or stronger proof grade.
    /// Native-only certificates may have no witness.
    #[cfg(feature = "trust-build")]
    #[must_use]
    pub fn translation_witness(
        &self,
    ) -> Option<&trust_wp_lib::trust_ir_body::NativeBodyWpTranslationWitness> {
        self.translation_witness.as_ref()
    }
}

// Bind every row field without retaining another copy of its potentially
// large materialized native bundle. This is input identity, not proof replay.
fn evidence_digest(evidence: &ObligationEvidence) -> Option<[u8; 32]> {
    Some(Sha256::digest(serde_json::to_vec(evidence).ok()?).into())
}
