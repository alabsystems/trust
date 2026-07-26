//! Internal batch result and routed-obligation types for the engine.

use std::collections::BTreeMap;

use trust_verifier_api::{
    EngineManifest, ObligationEvidence, TrustObligation, VerifierExecutionContext,
};

use super::super::native_trust_ir::{DirectTrustVcProofReceipt, FreshExactDirectChcPdrReceipt};
use super::super::routing::ObligationRoute;
use super::super::util::worker_threads;

pub(super) struct FullVerificationBatchResult {
    pub(super) evidence: Vec<ObligationEvidence>,
    pub(super) diagnostics: Vec<String>,
    pub(super) direct_trust_vc_receipts: BTreeMap<String, DirectTrustVcProofReceipt>,
    pub(super) fresh_exact_direct_chc_pdr_receipts: BTreeMap<String, FreshExactDirectChcPdrReceipt>,
}

impl FullVerificationBatchResult {
    pub(super) fn ordinary(evidence: Vec<ObligationEvidence>, diagnostics: Vec<String>) -> Self {
        Self {
            evidence,
            diagnostics,
            direct_trust_vc_receipts: BTreeMap::new(),
            fresh_exact_direct_chc_pdr_receipts: BTreeMap::new(),
        }
    }
}

pub(super) struct EngineBatch {
    pub(super) engine_index: usize,
    pub(super) batch: Vec<RoutedObligation>,
}

pub(super) struct CompletedEngineBatch {
    pub(super) batch: Vec<RoutedObligation>,
    pub(super) evidence: Vec<ObligationEvidence>,
    pub(super) manifest: EngineManifest,
    pub(super) elapsed_ms: u128,
    pub(super) direct_trust_vc_receipts: BTreeMap<String, DirectTrustVcProofReceipt>,
    pub(super) fresh_exact_direct_chc_pdr_receipts: BTreeMap<String, FreshExactDirectChcPdrReceipt>,
}

pub(super) struct RoutedObligation {
    pub(super) index: usize,
    pub(super) obligation: TrustObligation,
    pub(super) route: ObligationRoute,
}

pub(super) fn engine_batch_diagnostic(
    completed: &CompletedEngineBatch,
    context: Option<&VerifierExecutionContext>,
) -> String {
    let worker_threads = worker_threads(context)
        .map(|limit| limit.to_string())
        .unwrap_or_else(|| "unbounded".to_string());
    format!(
        "full-verification engine batch: engine={}@{} obligations={} elapsed_ms={} worker_threads={}",
        completed.manifest.name,
        completed.manifest.version,
        completed.batch.len(),
        completed.elapsed_ms,
        worker_threads
    )
}
