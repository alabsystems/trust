//! Fail-closed orchestration for native Trust full verification.
//!
//! This module is intentionally stricter than the legacy VC router. It consumes
//! the public `trust-verifier-api` contract bundle shape, requests evidence for
//! every obligation, and lets `VerificationRunResult` decide whether the run is
//! actually proved. Missing native engine integrations become explicit
//! `Unsupported` evidence; they are never upgraded into proof.

mod capabilities;
mod engine;
mod engines;
mod evidence_policy;
mod native_trust_ir;
mod policy;
mod routing;
mod run_result_ext;
mod util;

// --- Public surface re-exports preserving `trust_router::full_verification::*` ---
pub use engine::{
    FullVerificationEngine, FullVerificationRunWithFreshReceipts, LiveVerificationReceiptBatch,
};
pub use engines::{NativeTrustMcTrustIrEngine, NativeTyEngine, required_native_engines};
pub use native_trust_ir::{
    DirectTrustVcProofReceipt, FreshExactDirectChcPdrReceipt, NativeTrustIrBindingIndex,
    trust_wp_native_replay_metadata_entries_for_request,
};
pub use policy::{
    FullVerificationPolicy, TRUST_TRUST_IR_NATIVE_PROOF_OBLIGATION_ID_METADATA_KEY,
    TRUST_TRUST_IR_NATIVE_REQUEST_ID_METADATA_KEY,
    TRUST_TRUST_IR_NATIVE_VERIFIER_SUITE_METADATA_KEY,
};
pub use run_result_ext::{
    FullVerificationEvidenceBlocker, FullVerificationEvidenceDecision,
    FullVerificationNativeTrustIrEvidence, FullVerificationObligationEvidence,
    FullVerificationRunResultExt,
};

// Re-export the typed trust_wp metadata-key constants and helpers used by both
// the public API and the in-tree integration tests.
pub use trust_wp::{
    TRUST_TRUST_WP_CLAIM_DIGEST_METADATA_KEY, TRUST_TRUST_WP_NATIVE_ORIGIN_METADATA_KEY,
    TRUST_TRUST_WP_NATIVE_REPLAY_METADATA_KEY, TRUST_TRUST_WP_NATIVE_REPLAY_REQUIRED_METADATA_KEYS,
    TRUST_TRUST_WP_NATIVE_SOLVER_METADATA_KEY, TRUST_TRUST_WP_NATIVE_SUMMARY_FACT_METADATA_KEY,
    TRUST_TRUST_WP_NATIVE_VERIFIER_METADATA_KEY, TRUST_TRUST_WP_PROOF_CONTEXT_METADATA_KEY,
    TRUST_TRUST_WP_TRUST_IR_OBLIGATION_SOURCE_METADATA_KEY,
    TRUST_TRUST_WP_TRUST_IR_SOURCE_SPAN_METADATA_KEY,
};

// Make `TRUST_VC_HARDENED_NAMESPACE` / `_WILDCARD` reachable from the tests
// module via `use super::*;` without changing the module's public surface.
#[cfg(test)]
pub(crate) use policy::{TRUST_VC_HARDENED_NAMESPACE, TRUST_VC_HARDENED_WILDCARD};

#[cfg(test)]
mod tests;
