//! Execution policy for the full verifier and shared metadata-key constants.

/// Public obligation metadata key that binds a verifier-api obligation to a
/// TrustIr `ProofId` inside a typed native verification request bundle.
pub const TRUST_TRUST_IR_NATIVE_PROOF_OBLIGATION_ID_METADATA_KEY: &str =
    "trust.trust_ir.native.proof_obligation_id";
/// Optional public obligation metadata key for the TrustIr native request id.
pub const TRUST_TRUST_IR_NATIVE_REQUEST_ID_METADATA_KEY: &str = "trust.trust_ir.native.request_id";
/// Optional public obligation metadata key for the expected native verifier suite.
pub const TRUST_TRUST_IR_NATIVE_VERIFIER_SUITE_METADATA_KEY: &str =
    "trust.trust_ir.native.verifier_suite";

pub(crate) const TRUST_VC_HARDENED_NAMESPACE: &str = "trust.vc.hardened";
pub(crate) const TRUST_VC_HARDENED_WILDCARD: &str = "*";

/// Full-verification execution policy.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FullVerificationPolicy {
    /// Require proof-grade evidence for every requested obligation.
    pub fail_on_any_unproved: bool,
    /// Treat ordinary bounded BMC evidence as diagnostic-only.
    pub reject_bounded_proofs: bool,
    /// Require accepted proof-grade evidence to carry replay/check artifacts or
    /// solver-backed transcript artifacts.
    pub require_proof_artifacts: bool,
    /// Require native trust-wp, trust-vc, trust-mc, and TY lanes to be present in the
    /// engine set. The default adapters are fail-closed placeholders until
    /// those repos expose real native APIs.
    pub require_all_required_engines: bool,
}

impl Default for FullVerificationPolicy {
    fn default() -> Self {
        Self {
            fail_on_any_unproved: true,
            reject_bounded_proofs: true,
            require_proof_artifacts: true,
            require_all_required_engines: true,
        }
    }
}
