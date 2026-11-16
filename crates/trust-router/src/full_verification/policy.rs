//! Execution policy for the full verifier and shared metadata-key constants.

/// Public obligation metadata key that binds a verifier-api obligation to a
/// TrustIr `ProofId` inside a typed native verification request bundle.
pub const TRUST_TRUST_IR_NATIVE_PROOF_OBLIGATION_ID_METADATA_KEY: &str =
    trust_verifier_api::native_routing_identity::PROOF_KEY;
/// Optional public obligation metadata key for the TrustIr native request id.
pub const TRUST_TRUST_IR_NATIVE_REQUEST_ID_METADATA_KEY: &str =
    trust_verifier_api::native_routing_identity::REQUEST_KEY;
/// Optional public obligation metadata key for the expected native verifier suite.
pub const TRUST_TRUST_IR_NATIVE_VERIFIER_SUITE_METADATA_KEY: &str =
    trust_verifier_api::native_routing_identity::SUITE_KEY;

// The privileged namespace is ALIASED from the crate that owns the vocabulary,
// never re-declared: a local spelling could drift from the admitted list and
// silently split the hardened lane in two.
pub(crate) use trust_verifier_api::TRUST_VC_HARDENED_OBLIGATION_NAMESPACE as TRUST_VC_HARDENED_NAMESPACE;
// Allocation-capacity namespace, aliased for the same no-drift reason. Routable
// ONLY to the trust-vc certificate-import lane (see `obligation_route_for_kind`),
// never to the whole-function CHC — the mapping that false-proved unbounded
// allocations (the recorded P0 at trust-verifier-api's namespace constant).
pub(crate) use trust_verifier_api::TRUST_VC_UNBOUNDED_ALLOCATION_OBLIGATION_NAMESPACE as TRUST_VC_UNBOUNDED_ALLOCATION_NAMESPACE;
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
    /// Require the active native trust-vc, trust-mc, and TY lanes to be present
    /// in the engine set. Historical TrustWP wire evidence stays readable, but
    /// TrustWP is not required while it advertises zero routed capabilities.
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
