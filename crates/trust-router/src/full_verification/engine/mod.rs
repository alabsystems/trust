//! `FullVerificationEngine` orchestration and per-batch dispatch.

mod batch;

use std::{
    collections::{BTreeMap, HashMap},
    time::Instant,
};

use rayon::prelude::*;
use trust_ir_bridge::NativeVerificationBundle;
use trust_verifier_api::{
    API_VERSION, Counterexample, EngineKind, EngineManifest, EvidencePublicationMetadata,
    EvidenceStatus, ObligationEvidence, ProofStrength, ReasoningKind, SupportLevel,
    TrustContractBundle, TrustObligation, ValidatedVerificationRequest, VerificationEngine,
    VerificationRunResult, VerifierExecutionContext,
};

use self::batch::{
    CompletedEngineBatch, EngineBatch, FullVerificationBatchResult, RoutedObligation,
    engine_batch_diagnostic,
};
use super::capabilities::{all_full_verification_capabilities, obligation_kinds_owned_by};
use super::evidence_policy::{
    direct_trust_vc_evidence_is_privately_authorized, evidence_has_proved_failed_conflict,
    evidence_satisfies_full_artifact_policy, evidence_uses_reserved_direct_trust_vc_namespace,
    missing_primary_evidence_reason, rejected_primary_evidence, rejected_primary_evidence_reason,
    select_evidence,
};
use super::native_trust_ir::{
    DirectTrustVcProofReceipt, FreshExactDirectChcPdrReceipt, LiveVerificationDispatchSeal,
    NativeTrustIrEvidenceIndex, is_native_trust_ir_engine, native_trust_ir_artifact_match,
    native_trust_ir_bundle_evidence, native_trust_ir_bundle_evidence_is_incomplete,
};
use super::policy::FullVerificationPolicy;
use super::routing::{ObligationRoute, PrimaryEngine, REQUIRED_PRIMARY_ENGINES, obligation_route};
use super::util::{append_unique_artifacts, status_label, support_description, worker_threads};

/// A live full-verification result and its affine native proof sidecars.
///
/// This type is intentionally not cloneable or serializable. The ordinary
/// full-verifier entry points discard the sidecars; only the explicit live API
/// can move them into a compiler-owned final authority boundary.
#[derive(Debug)]
pub struct FullVerificationRunWithFreshReceipts {
    result: VerificationRunResult,
    live_receipts: LiveVerificationReceiptBatch,
}

/// Opaque, affine receipt package for one exact live verifier dispatch.
///
/// The private dispatch seal, source run, and both receipt maps remain coupled
/// inside this non-cloneable, non-serializable value. Callers may move receipts
/// out for compiler consumption, but can authorize them only through the same
/// package; there is no independent seal/source argument that can be swapped
/// with a byte-identical result from another dispatch.
#[derive(Debug)]
pub struct LiveVerificationReceiptBatch {
    // `None` is the ordinary, zero-authority case. Avoid minting the seal in
    // that case: minting snapshots the complete source run, so doing it for
    // every result would impose an unnecessary O(run-size) clone on callers
    // that never produced a live receipt.
    dispatch_seal: Option<LiveVerificationDispatchSeal>,
    direct_trust_vc_receipts: BTreeMap<String, DirectTrustVcProofReceipt>,
    fresh_exact_direct_chc_pdr_receipts: BTreeMap<String, FreshExactDirectChcPdrReceipt>,
}

impl LiveVerificationReceiptBatch {
    /// Exact router source run privately bound to every receipt in this batch.
    #[must_use]
    pub fn source_run(&self) -> Option<&VerificationRunResult> {
        self.dispatch_seal.as_ref().map(LiveVerificationDispatchSeal::source_run)
    }

    /// Compare a caller's complete current bundle with the immutable bundle
    /// that produced this dispatch. Consumers perform this linear check once
    /// for the affine batch, never once per receipt.
    #[must_use]
    pub fn matches_bundle(&self, bundle: &TrustContractBundle) -> bool {
        self.dispatch_seal
            .as_ref()
            .is_some_and(|dispatch_seal| dispatch_seal.matches_bundle(bundle))
    }

    /// Borrow the unconsumed direct receipt inventory without transferring
    /// authority.
    #[must_use]
    pub fn direct_trust_vc_receipts(&self) -> &BTreeMap<String, DirectTrustVcProofReceipt> {
        &self.direct_trust_vc_receipts
    }

    /// Borrow the unconsumed FreshExact receipt inventory without
    /// transferring authority.
    #[must_use]
    pub fn fresh_exact_direct_chc_pdr_receipts(
        &self,
    ) -> &BTreeMap<String, FreshExactDirectChcPdrReceipt> {
        &self.fresh_exact_direct_chc_pdr_receipts
    }

    /// Move the direct TrustVC receipts out exactly once.
    pub fn take_direct_trust_vc_receipts(&mut self) -> BTreeMap<String, DirectTrustVcProofReceipt> {
        std::mem::take(&mut self.direct_trust_vc_receipts)
    }

    /// Split one direct receipt into its own still-coupled affine package.
    pub fn take_direct_trust_vc_receipt_batch(&mut self, obligation_id: &str) -> Option<Self> {
        let dispatch_seal = self.dispatch_seal.as_ref()?.fork();
        let receipt = self.direct_trust_vc_receipts.remove(obligation_id)?;
        Some(Self {
            dispatch_seal: Some(dispatch_seal),
            direct_trust_vc_receipts: std::iter::once((obligation_id.to_string(), receipt))
                .collect(),
            fresh_exact_direct_chc_pdr_receipts: BTreeMap::new(),
        })
    }

    /// Move the fresh exact CHC/PDR receipts out exactly once.
    pub fn take_fresh_exact_direct_chc_pdr_receipts(
        &mut self,
    ) -> BTreeMap<String, FreshExactDirectChcPdrReceipt> {
        std::mem::take(&mut self.fresh_exact_direct_chc_pdr_receipts)
    }

    /// Split one FreshExact receipt into its own still-coupled affine package.
    pub fn take_fresh_exact_direct_chc_pdr_receipt_batch(
        &mut self,
        obligation_id: &str,
    ) -> Option<Self> {
        let dispatch_seal = self.dispatch_seal.as_ref()?.fork();
        let receipt = self.fresh_exact_direct_chc_pdr_receipts.remove(obligation_id)?;
        Some(Self {
            dispatch_seal: Some(dispatch_seal),
            direct_trust_vc_receipts: BTreeMap::new(),
            fresh_exact_direct_chc_pdr_receipts: std::iter::once((
                obligation_id.to_string(),
                receipt,
            ))
            .collect(),
        })
    }

    /// Revalidate a detached direct receipt against this package's immutable
    /// source dispatch and one exact accepted row.
    pub fn authorizes_direct_trust_vc_receipt(
        &self,
        receipt: &DirectTrustVcProofReceipt,
        obligation: &TrustObligation,
        evidence: &ObligationEvidence,
    ) -> Result<ProofStrength, String> {
        let Some(dispatch_seal) = self.dispatch_seal.as_ref() else {
            return Err("live receipt batch has no dispatch authority".to_string());
        };
        if !dispatch_seal.is_live() || receipt.dispatch_deadline() != dispatch_seal.deadline() {
            return Err("live receipt batch is late, cancelled, or deadline-mismatched".to_string());
        }
        let authorization =
            receipt.authorizes_accepted_evidence(obligation, evidence, dispatch_seal);
        if !dispatch_seal.is_live() || receipt.dispatch_deadline() != dispatch_seal.deadline() {
            return Err(
                "live receipt batch became late, cancelled, or deadline-mismatched".to_string()
            );
        }
        authorization
    }

    /// Revalidate a detached FreshExact receipt against this package's
    /// immutable source dispatch and one exact accepted row.
    #[cfg(feature = "trust-build")]
    pub fn authorizes_fresh_exact_direct_chc_pdr_receipt(
        &self,
        receipt: &FreshExactDirectChcPdrReceipt,
        obligation: &TrustObligation,
        evidence: &ObligationEvidence,
    ) -> Result<ProofStrength, String> {
        let Some(dispatch_seal) = self.dispatch_seal.as_ref() else {
            return Err("live receipt batch has no dispatch authority".to_string());
        };
        if !dispatch_seal.is_live() || receipt.dispatch_deadline() != dispatch_seal.deadline() {
            return Err("live receipt batch is late, cancelled, or deadline-mismatched".to_string());
        }
        let authorization =
            receipt.authorizes_accepted_evidence(obligation, evidence, dispatch_seal);
        if !dispatch_seal.is_live() || receipt.dispatch_deadline() != dispatch_seal.deadline() {
            return Err(
                "live receipt batch became late, cancelled, or deadline-mismatched".to_string()
            );
        }
        authorization
    }
}

impl FullVerificationRunWithFreshReceipts {
    /// Borrow the ordinary public run result.
    #[must_use]
    pub fn result(&self) -> &VerificationRunResult {
        &self.result
    }

    /// Borrow the live direct TrustVC receipt map without transferring
    /// authority.
    #[must_use]
    pub fn direct_trust_vc_receipts(&self) -> &BTreeMap<String, DirectTrustVcProofReceipt> {
        &self.live_receipts.direct_trust_vc_receipts
    }

    /// Borrow the live receipt map without transferring authority.
    #[must_use]
    pub fn fresh_exact_direct_chc_pdr_receipts(
        &self,
    ) -> &BTreeMap<String, FreshExactDirectChcPdrReceipt> {
        &self.live_receipts.fresh_exact_direct_chc_pdr_receipts
    }

    /// Move the public result and its still-coupled affine receipt package into
    /// the caller's final authority boundary.
    #[must_use]
    pub fn into_parts(self) -> (VerificationRunResult, LiveVerificationReceiptBatch) {
        (self.result, self.live_receipts)
    }

    fn into_result(self) -> VerificationRunResult {
        let result =
            discard_live_receipt_sidecars(self.result, self.live_receipts.direct_trust_vc_receipts);
        discard_live_receipt_sidecars(
            result,
            self.live_receipts.fresh_exact_direct_chc_pdr_receipts,
        )
    }
}

struct FinishedPrimaryEvidence {
    evidence: ObligationEvidence,
    accepted: bool,
}

/// Composite full-verification engine over native backend engines.
pub struct FullVerificationEngine {
    manifest: EngineManifest,
    policy: FullVerificationPolicy,
    engines: Vec<Box<dyn VerificationEngine + Send + Sync>>,
    invalid_engine_manifests: Vec<String>,
    duplicate_primary_engines: Vec<&'static str>,
    missing_required_engines: Vec<&'static str>,
}

impl FullVerificationEngine {
    /// Build a full verifier from explicit engines.
    #[must_use]
    pub fn new(
        engines: Vec<Box<dyn VerificationEngine + Send + Sync>>,
        policy: FullVerificationPolicy,
    ) -> Self {
        let mut manifest =
            EngineManifest::new("trust-full-verifier", API_VERSION, EngineKind::Composite);
        manifest.capabilities = all_full_verification_capabilities();
        manifest.proof_modes = vec![
            ReasoningKind::Deductive,
            ReasoningKind::OwnershipAnalysis,
            ReasoningKind::Chc,
            ReasoningKind::Pdr,
            ReasoningKind::TemporalModelCheck,
            ReasoningKind::ExplicitStateModel,
        ];
        let mut verifier = Self {
            manifest,
            policy,
            engines,
            invalid_engine_manifests: Vec::new(),
            duplicate_primary_engines: Vec::new(),
            missing_required_engines: Vec::new(),
        };
        // Engine manifests and registrations are immutable after construction.
        // Audit them once instead of rescanning every capability for every
        // obligation in a large bundle.
        verifier.invalid_engine_manifests = verifier.collect_invalid_engine_manifest_diagnostics();
        verifier.duplicate_primary_engines = verifier.collect_duplicate_primary_engine_names();
        verifier.missing_required_engines = verifier.collect_missing_required_engine_names();
        verifier
    }

    /// Build a verifier with the required native trust-wp/trust-vc/trust-mc/TY engines.
    #[must_use]
    pub fn with_required_native_engines() -> Self {
        Self::new(super::engines::required_native_engines(), FullVerificationPolicy::default())
    }

    /// Run full verification and return the fail-closed run envelope.
    #[must_use]
    pub fn verify_bundle(
        &self,
        bundle: &TrustContractBundle,
        context: &VerifierExecutionContext,
    ) -> VerificationRunResult {
        self.verify_with_context(bundle, &bundle.obligations, context)
    }

    /// Run full verification with a typed TrustIr native request bundle.
    ///
    /// The native bundle is not treated as proof by itself. It is an identity
    /// and replay boundary for trust-vc, trust-mc, and trust_wp evidence: proof-grade
    /// child evidence on those routes must be bound to a matching typed native
    /// request/proof obligation artifact before the composite verifier accepts
    /// it.
    #[must_use]
    pub fn verify_bundle_with_native_trust_ir_bundle(
        &self,
        bundle: &TrustContractBundle,
        native_bundle: &NativeVerificationBundle,
        context: &VerifierExecutionContext,
    ) -> VerificationRunResult {
        self.verify_with_context_and_native_trust_ir_bundle_with_fresh_receipts(
            bundle,
            &bundle.obligations,
            context,
            Some(native_bundle),
        )
        .into_result()
    }

    /// Run full verification while retaining live direct TrustVC and
    /// exact-direct CHC/PDR receipts from the same native solves that produced
    /// the public result.
    #[must_use]
    pub fn verify_bundle_with_native_trust_ir_bundle_and_fresh_receipts(
        &self,
        bundle: &TrustContractBundle,
        native_bundle: &NativeVerificationBundle,
        context: &VerifierExecutionContext,
    ) -> FullVerificationRunWithFreshReceipts {
        self.verify_with_context_and_native_trust_ir_bundle_with_fresh_receipts(
            bundle,
            &bundle.obligations,
            context,
            Some(native_bundle),
        )
    }

    /// Run full verification for an exact canonical subset of a bundle while
    /// retaining the typed TrustIr replay boundary.
    ///
    /// This is used by compiler-owned lanes whose public bundle intentionally
    /// retains catalog rows that are not proof requests (for example a
    /// definition-site precondition, which is an entry assumption and whose
    /// proof obligation belongs to each caller). The ordinary canonical-subset
    /// validation still runs before dispatch; an ID-preserving rewrite or a row
    /// not present in `bundle` therefore fails closed.
    #[must_use]
    pub fn verify_obligations_with_native_trust_ir_bundle(
        &self,
        bundle: &TrustContractBundle,
        obligations: &[TrustObligation],
        native_bundle: &NativeVerificationBundle,
        context: &VerifierExecutionContext,
    ) -> VerificationRunResult {
        self.verify_with_context_and_native_trust_ir_bundle_with_fresh_receipts(
            bundle,
            obligations,
            context,
            Some(native_bundle),
        )
        .into_result()
    }

    /// Verify an exact canonical subset while retaining affine proof receipts
    /// from the same native solves. Receipt-less or rejected rows remain only
    /// ordinary public evidence and cannot acquire authority through this API.
    #[must_use]
    pub fn verify_obligations_with_native_trust_ir_bundle_and_fresh_receipts(
        &self,
        bundle: &TrustContractBundle,
        obligations: &[TrustObligation],
        native_bundle: &NativeVerificationBundle,
        context: &VerifierExecutionContext,
    ) -> FullVerificationRunWithFreshReceipts {
        self.verify_obligations_with_optional_native_trust_ir_bundle_and_live_receipts(
            bundle,
            obligations,
            Some(native_bundle),
            context,
        )
    }

    /// Verify an exact canonical subset while retaining every affine native
    /// proof receipt from the same live dispatch.
    ///
    /// The optional native bundle is deliberately independent of the receipt
    /// boundary: the dedicated direct TrustVC MIR-memory lane is valid only
    /// when no native request/source claims the obligation, so it can mint a
    /// receipt while `native_bundle` is `None`. Public result-only entry points
    /// continue to discard all receipt sidecars.
    #[must_use]
    pub fn verify_obligations_with_optional_native_trust_ir_bundle_and_live_receipts(
        &self,
        bundle: &TrustContractBundle,
        obligations: &[TrustObligation],
        native_bundle: Option<&NativeVerificationBundle>,
        context: &VerifierExecutionContext,
    ) -> FullVerificationRunWithFreshReceipts {
        self.verify_with_context_and_native_trust_ir_bundle_with_fresh_receipts(
            bundle,
            obligations,
            context,
            native_bundle,
        )
    }

    fn verify_batch_with_context_details(
        &self,
        bundle: &TrustContractBundle,
        obligations: &[TrustObligation],
        context: Option<&VerifierExecutionContext>,
        native_trust_ir: Option<&NativeTrustIrEvidenceIndex>,
        native_bundle: Option<&NativeVerificationBundle>,
    ) -> FullVerificationBatchResult {
        let mut results = vec![None; obligations.len()];
        if let Err(error) = bundle.validate_requested_obligations(obligations) {
            let diagnostic = format!(
                "full-verification rejected invalid bundle/request before dispatch: {error}"
            );
            let evidence = obligations
                .iter()
                .map(|obligation| self.policy_unsupported(obligation, diagnostic.clone()))
                .collect();
            return FullVerificationBatchResult::ordinary(evidence, vec![diagnostic]);
        }
        if context.is_some_and(|context| context.budget_exceeded()) {
            let evidence = obligations
                .iter()
                .map(|obligation| {
                    self.timed_out(
                        obligation,
                        "full-verification wall-clock budget exceeded before dispatch",
                    )
                })
                .collect();
            return FullVerificationBatchResult::ordinary(
                evidence,
                vec!["full-verification wall-clock budget exceeded before dispatch".to_string()],
            );
        }
        if let Some(limit) = exceeded_obligation_limit(context, obligations.len()) {
            let diagnostic = format!(
                "full-verification obligation limit exceeded before dispatch: requested_obligations={} limit={limit}",
                obligations.len()
            );
            let evidence = obligations
                .iter()
                .map(|obligation| self.timed_out(obligation, diagnostic.clone()))
                .collect();
            return FullVerificationBatchResult::ordinary(evidence, vec![diagnostic]);
        }

        let invalid_manifests = &self.invalid_engine_manifests;
        if !invalid_manifests.is_empty() {
            let diagnostic = format!(
                "full-verification configuration contains invalid engine manifests: {}",
                invalid_manifests.join("; ")
            );
            let evidence = obligations
                .iter()
                .map(|obligation| self.policy_unsupported(obligation, diagnostic.clone()))
                .collect();
            return FullVerificationBatchResult::ordinary(evidence, vec![diagnostic]);
        }

        let duplicate_primaries = &self.duplicate_primary_engines;
        if !duplicate_primaries.is_empty() {
            let diagnostic = format!(
                "full-verification configuration has ambiguous duplicate primary engines: {}",
                duplicate_primaries.join(", ")
            );
            let evidence = obligations
                .iter()
                .map(|obligation| self.policy_unsupported(obligation, diagnostic.clone()))
                .collect();
            return FullVerificationBatchResult::ordinary(evidence, vec![diagnostic]);
        }

        if self.policy.require_all_required_engines {
            let missing = &self.missing_required_engines;
            if !missing.is_empty() {
                let reason = format!(
                    "full verification requires native trust-wp, trust-vc, trust-mc, and TY engines; missing: {}",
                    missing.join(", ")
                );
                let evidence = obligations
                    .iter()
                    .map(|obligation| self.policy_unsupported(obligation, reason.clone()))
                    .collect();
                return FullVerificationBatchResult::ordinary(evidence, Vec::new());
            }
        }

        let mut batches = self.empty_engine_batches();
        let mut batch_order = Vec::new();
        for (index, obligation) in obligations.iter().enumerate() {
            let Some(route) = obligation_route(obligation) else {
                // Trust (R1 corpus, root-cause surfacing): an unroutable kind is
                // dominated by the compiler's honest `Custom{trust.vc,
                // unsupported_mir}` fatal-assumption obligations, whose
                // DESCRIPTION names the actual unloweable construct
                // ("unsupported MIR `X`: detail"). Carry it in the reason so the
                // per-obligation report names the root construct instead of only
                // this generic ownership message (94 cascade-noise rows on the
                // first corpus sweep).
                results[index] = Some(self.policy_unsupported(
                    obligation,
                    format!(
                        "no full-verification primary owner is defined for obligation kind {:?}; obligation: {}",
                        obligation.kind, obligation.description
                    ),
                ));
                continue;
            };

            if self.policy.reject_bounded_proofs
                && obligation.required_strength.as_ref().is_some_and(ProofStrength::is_bounded)
            {
                results[index] = Some(self.policy_unsupported(
                    obligation,
                    "full verification requires unbounded or exhaustive proof strength; bounded BMC is diagnostic only",
                ));
                continue;
            }

            let Some(engine_index) = self.primary_engine_index(route.primary) else {
                results[index] = Some(self.not_attempted(
                    obligation,
                    format!(
                        "primary owner {} is required for {:?} obligations; configured engines: {}",
                        route.primary.name(),
                        obligation.kind,
                        self.configured_engine_list()
                    ),
                ));
                continue;
            };

            let primary = self.engines[engine_index].as_ref();
            if context.is_some_and(|context| context.budget_exceeded()) {
                results[index] = Some(self.timed_out(
                    obligation,
                    "full-verification wall-clock budget exceeded before scheduling obligation",
                ));
                continue;
            }
            let support = primary.supports(obligation);
            if !support.is_supported() {
                results[index] = Some(self.policy_unsupported(
                    obligation,
                    format!(
                        "primary owner {}@{} rejected {:?}: {}",
                        primary.manifest().name,
                        primary.manifest().version,
                        obligation.kind,
                        support_description(&support)
                    ),
                ));
                continue;
            }

            if batches[engine_index].is_empty() {
                batch_order.push(engine_index);
            }
            batches[engine_index].push(RoutedObligation {
                index,
                route,
                obligation: obligation.clone(),
            });
        }

        let engine_batches = batch_order
            .into_iter()
            .filter_map(|engine_index| {
                let batch = std::mem::take(&mut batches[engine_index]);
                if batch.is_empty() { None } else { Some(EngineBatch { engine_index, batch }) }
            })
            .collect::<Vec<_>>();

        let mut diagnostics = Vec::new();
        let mut direct_trust_vc_receipts = BTreeMap::new();
        let mut fresh_exact_direct_chc_pdr_receipts = BTreeMap::new();
        for completed in self.execute_engine_batches(bundle, engine_batches, context, native_bundle)
        {
            diagnostics.push(engine_batch_diagnostic(&completed, context));
            let CompletedEngineBatch {
                batch,
                evidence: child_evidence,
                manifest,
                elapsed_ms: _,
                direct_trust_vc_receipts: mut batch_direct_receipts,
                fresh_exact_direct_chc_pdr_receipts: mut batch_fresh_receipts,
            } = completed;
            // Every direct receipt in a native batch must share the same exact
            // immutable bundle snapshot. Perform the one deep comparison here
            // before any row can use receipt-exclusive evidence; later row
            // checks are intentionally receipt-local and O(1).
            if !direct_receipt_bundle_is_coherent(&batch_direct_receipts, bundle) {
                batch_direct_receipts.clear();
            }
            if !fresh_receipt_bundle_is_coherent(&batch_fresh_receipts, bundle) {
                batch_fresh_receipts.clear();
            }
            // Build the obligation join once. Primary selection, hard-conflict
            // detection, rejection priority, and receipt binding then inspect
            // only the rows for the current public identity instead of
            // rescanning the complete child result for every routed obligation.
            let child_evidence_index = PrimaryEvidenceRowIndex::new(&child_evidence);
            for item in batch {
                let child_rows = child_evidence_index.rows(item.obligation.obligation_id.as_str());
                let unique_child_row =
                    child_evidence_index.unique_row(item.obligation.obligation_id.as_str());
                let direct_receipt = batch_direct_receipts.remove(&item.obligation.obligation_id);
                let finished = if context.is_some_and(|context| context.budget_exceeded()) {
                    FinishedPrimaryEvidence {
                        evidence: self.timed_out(
                            &item.obligation,
                            "full-verification wall-clock budget exceeded before accepting primary evidence",
                        ),
                        accepted: false,
                    }
                } else {
                    self.finish_primary_evidence(
                        bundle,
                        &item.obligation,
                        item.route,
                        child_rows,
                        &manifest,
                        native_trust_ir,
                        direct_receipt.as_ref(),
                    )
                };
                if let Some(receipt) = direct_receipt
                    && direct_receipt_authorizes_final_evidence(
                        &receipt,
                        bundle,
                        &item.obligation,
                        unique_child_row,
                        &finished,
                        context,
                    )
                    && let Some(receipt) = receipt.bind_to_accepted_evidence(&finished.evidence)
                    && direct_trust_vc_receipts
                        .insert(item.obligation.obligation_id.clone(), receipt)
                        .is_some()
                {
                    // One public identity cannot carry two independent live
                    // capabilities. Drop both rather than selecting by batch
                    // order.
                    direct_trust_vc_receipts.remove(&item.obligation.obligation_id);
                }
                if let Some(receipt) = batch_fresh_receipts.remove(&item.obligation.obligation_id)
                    && fresh_receipt_authorizes_final_evidence(
                        &receipt,
                        bundle,
                        &item.obligation,
                        unique_child_row,
                        &finished,
                        context,
                    )
                    && let Some(receipt) = receipt.bind_to_accepted_evidence(&finished.evidence)
                    && fresh_exact_direct_chc_pdr_receipts
                        .insert(item.obligation.obligation_id.clone(), receipt)
                        .is_some()
                {
                    // Two routed batches claiming live authority for one public
                    // identity are structurally ambiguous. Drop both receipts;
                    // ordinary evidence remains available for diagnostics only.
                    fresh_exact_direct_chc_pdr_receipts.remove(&item.obligation.obligation_id);
                }
                results[item.index] = Some(finished.evidence);
            }
        }

        let evidence = results
            .into_iter()
            .enumerate()
            .map(|(index, evidence)| {
                evidence.unwrap_or_else(|| {
                    self.policy_unsupported(
                        &obligations[index],
                        "internal full-verification batching error: obligation was not completed",
                    )
                })
            })
            .collect();
        FullVerificationBatchResult {
            evidence,
            diagnostics,
            direct_trust_vc_receipts,
            fresh_exact_direct_chc_pdr_receipts,
        }
    }

    fn execute_engine_batches(
        &self,
        bundle: &TrustContractBundle,
        engine_batches: Vec<EngineBatch>,
        context: Option<&VerifierExecutionContext>,
        native_bundle: Option<&NativeVerificationBundle>,
    ) -> Vec<CompletedEngineBatch> {
        if engine_batches.len() <= 1 || worker_threads(context).is_some_and(|limit| limit <= 1) {
            return self.execute_engine_batches_serial(
                bundle,
                engine_batches,
                context,
                native_bundle,
            );
        }

        if let Some(limit) = worker_threads(context) {
            let thread_count = limit.min(engine_batches.len());
            if let Ok(pool) = rayon::ThreadPoolBuilder::new().num_threads(thread_count).build() {
                return pool.install(|| {
                    self.execute_engine_batches_parallel(
                        bundle,
                        engine_batches,
                        context,
                        native_bundle,
                    )
                });
            }
            return self.execute_engine_batches_serial(
                bundle,
                engine_batches,
                context,
                native_bundle,
            );
        }

        self.execute_engine_batches_parallel(bundle, engine_batches, context, native_bundle)
    }

    fn execute_engine_batches_serial(
        &self,
        bundle: &TrustContractBundle,
        engine_batches: Vec<EngineBatch>,
        context: Option<&VerifierExecutionContext>,
        native_bundle: Option<&NativeVerificationBundle>,
    ) -> Vec<CompletedEngineBatch> {
        engine_batches
            .into_iter()
            .map(|engine_batch| {
                self.execute_engine_batch(bundle, engine_batch, context, native_bundle)
            })
            .collect()
    }

    fn execute_engine_batches_parallel(
        &self,
        bundle: &TrustContractBundle,
        engine_batches: Vec<EngineBatch>,
        context: Option<&VerifierExecutionContext>,
        native_bundle: Option<&NativeVerificationBundle>,
    ) -> Vec<CompletedEngineBatch> {
        engine_batches
            .into_par_iter()
            .map(|engine_batch| {
                self.execute_engine_batch(bundle, engine_batch, context, native_bundle)
            })
            .collect()
    }

    fn execute_engine_batch(
        &self,
        bundle: &TrustContractBundle,
        engine_batch: EngineBatch,
        context: Option<&VerifierExecutionContext>,
        native_bundle: Option<&NativeVerificationBundle>,
    ) -> CompletedEngineBatch {
        let primary = self.engines[engine_batch.engine_index].as_ref();
        let requested =
            engine_batch.batch.iter().map(|item| item.obligation.clone()).collect::<Vec<_>>();
        let started = Instant::now();
        // Trust: a per-function wall-clock deadline carried on the
        // execution context bounds in-process full verification. When it
        // elapses, the engines below degrade remaining obligations to
        // `Timeout` (sound: never `Proved`) rather than solving unbounded.
        let deadline = context.and_then(|ctx| ctx.deadline());
        // PANIC FIREWALL: a panic inside the native trust-ir / trust-mc CHC
        // translation (e.g. an `Expr::ite` branch-sort-mismatch ICE deep in a
        // call-summary combiner) must NEVER abort the compile. Catch it and
        // degrade to "no native evidence" (None): the obligations then flow
        // through the standard incomplete-evidence fallback below to the primary
        // engine, which can only yield Unknown/Unsupported here — never Proved.
        // This is defense-in-depth; the combiner itself is also hardened to
        // decline (havoc) on a sort mismatch rather than panic.
        let native_evidence = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            native_trust_ir_bundle_evidence(
                primary.manifest(),
                bundle,
                &requested,
                native_bundle,
                deadline,
            )
        }))
        .unwrap_or(None);
        let (mut evidence, mut direct_trust_vc_receipts, mut fresh_exact_direct_chc_pdr_receipts) =
            match native_evidence {
                Some(native_evidence) => (
                    Some(native_evidence.evidence),
                    native_evidence.direct_trust_vc_receipts,
                    native_evidence.fresh_exact_direct_chc_pdr_receipts,
                ),
                None => (None, BTreeMap::new(), BTreeMap::new()),
            };
        let native_trust_ir_bundle_is_authoritative =
            evidence.is_some() && is_native_trust_ir_engine(primary.manifest());
        if !native_trust_ir_bundle_is_authoritative
            && native_trust_ir_bundle_evidence_is_incomplete(&requested, evidence.as_deref())
        {
            // A sidecar is meaningful only for the exact native evidence batch
            // that produced it. Never carry it across a generic-primary
            // fallback or a merged evidence inventory.
            direct_trust_vc_receipts.clear();
            fresh_exact_direct_chc_pdr_receipts.clear();
            let mut primary_evidence = if let Some(context) = context {
                primary.verify_with_context(bundle, &requested, context).evidence
            } else {
                primary.verify(bundle, &requested)
            };
            if let Some(native_evidence) = evidence.as_mut() {
                native_evidence.append(&mut primary_evidence);
            } else {
                evidence = Some(primary_evidence);
            }
        }
        let evidence = evidence.unwrap_or_default();
        let elapsed_ms = started.elapsed().as_millis();
        let manifest = primary.manifest().clone();
        CompletedEngineBatch {
            batch: engine_batch.batch,
            evidence,
            manifest,
            elapsed_ms,
            direct_trust_vc_receipts,
            fresh_exact_direct_chc_pdr_receipts,
        }
    }

    fn finish_primary_evidence(
        &self,
        bundle: &TrustContractBundle,
        obligation: &TrustObligation,
        route: ObligationRoute,
        evidence: &[&ObligationEvidence],
        manifest: &EngineManifest,
        native_trust_ir: Option<&NativeTrustIrEvidenceIndex>,
        direct_trust_vc_receipt: Option<&DirectTrustVcProofReceipt>,
    ) -> FinishedPrimaryEvidence {
        if let Some(best) = select_evidence(
            obligation,
            bundle,
            route,
            evidence,
            self.policy,
            native_trust_ir,
            direct_trust_vc_receipt,
        ) {
            return FinishedPrimaryEvidence {
                evidence: self.wrap_accepted_child_evidence(
                    best,
                    obligation,
                    route,
                    native_trust_ir,
                ),
                accepted: true,
            };
        }

        if let Some(rejected) = rejected_primary_evidence(obligation, evidence) {
            let reason = if evidence_has_proved_failed_conflict(obligation, evidence) {
                "primary engine produced conflicting Proved and Failed evidence for the same obligation; failed closed on the Failed row"
                    .to_string()
            } else {
                rejected_primary_evidence_reason(
                    obligation,
                    bundle,
                    route,
                    &rejected,
                    native_trust_ir,
                    direct_trust_vc_receipt,
                )
            };
            return FinishedPrimaryEvidence {
                evidence: self.wrap_rejected_child_evidence(
                    rejected,
                    bundle,
                    obligation,
                    route,
                    native_trust_ir,
                    direct_trust_vc_receipt,
                    reason,
                ),
                accepted: false,
            };
        }

        FinishedPrimaryEvidence {
            evidence: self
                .not_attempted(obligation, missing_primary_evidence_reason(manifest, obligation)),
            accepted: false,
        }
    }

    fn empty_engine_batches(&self) -> Vec<Vec<RoutedObligation>> {
        (0..self.engines.len()).map(|_| Vec::new()).collect()
    }

    fn policy_unsupported(
        &self,
        obligation: &TrustObligation,
        reason: impl Into<String>,
    ) -> ObligationEvidence {
        self.base_evidence(obligation, EvidenceStatus::Unsupported, None, vec![reason.into()])
    }

    fn not_attempted(
        &self,
        obligation: &TrustObligation,
        reason: impl Into<String>,
    ) -> ObligationEvidence {
        self.base_evidence(obligation, EvidenceStatus::Unsupported, None, vec![reason.into()])
    }

    fn timed_out(
        &self,
        obligation: &TrustObligation,
        reason: impl Into<String>,
    ) -> ObligationEvidence {
        self.base_evidence(obligation, EvidenceStatus::Timeout, None, vec![reason.into()])
    }

    fn wrap_accepted_child_evidence(
        &self,
        mut evidence: ObligationEvidence,
        obligation: &TrustObligation,
        route: ObligationRoute,
        native_trust_ir: Option<&NativeTrustIrEvidenceIndex>,
    ) -> ObligationEvidence {
        let child = evidence.engine.clone();
        if let Ok(Some(native_match)) =
            native_trust_ir_artifact_match(native_trust_ir, route, obligation)
        {
            append_unique_artifacts(&mut evidence.artifacts, native_match.artifacts);
            evidence.diagnostics.push(native_match.diagnostic);
        }
        evidence.engine = self.manifest.clone();
        evidence.diagnostics.push(format!(
            "primary owner {}@{} produced accepted evidence {} for {:?}; route requires {}",
            child.name,
            child.version,
            evidence.evidence_id,
            route.obligation_kind,
            route.required_strength_description()
        ));
        evidence
    }

    fn wrap_rejected_child_evidence(
        &self,
        mut evidence: ObligationEvidence,
        bundle: &TrustContractBundle,
        obligation: &TrustObligation,
        route: ObligationRoute,
        native_trust_ir: Option<&NativeTrustIrEvidenceIndex>,
        direct_trust_vc_receipt: Option<&DirectTrustVcProofReceipt>,
        reason: String,
    ) -> ObligationEvidence {
        let child = evidence.engine.clone();
        let unauthorized_reserved_direct =
            evidence_uses_reserved_direct_trust_vc_namespace(&evidence)
                && !direct_trust_vc_evidence_is_privately_authorized(
                    route,
                    bundle,
                    obligation,
                    &evidence,
                    direct_trust_vc_receipt,
                );
        if evidence.status == EvidenceStatus::Proved
            && (unauthorized_reserved_direct
                || (self.policy.require_proof_artifacts
                    && !evidence_satisfies_full_artifact_policy(
                        route,
                        &evidence,
                        bundle,
                        obligation,
                        native_trust_ir,
                        direct_trust_vc_receipt,
                    )))
        {
            // A rejected `Proved` row is retained for diagnostics.  Strip its
            // publication-bearing artifacts so generic run aggregation cannot
            // mistake an unauthorized reserved-direct lookalike for an
            // accepted proof, including when ordinary artifact checks were
            // disabled by policy.
            evidence.artifacts.clear();
        }
        evidence.engine = self.manifest.clone();
        evidence.diagnostics.push(format!(
            "primary owner {}@{} produced rejected evidence {} for {:?}: {}",
            child.name, child.version, evidence.evidence_id, route.obligation_kind, reason
        ));
        evidence
    }

    fn primary_engine(
        &self,
        primary: PrimaryEngine,
    ) -> Option<&(dyn VerificationEngine + Send + Sync)> {
        self.primary_engine_index(primary).map(|index| self.engines[index].as_ref())
    }

    fn primary_engine_index(&self, primary: PrimaryEngine) -> Option<usize> {
        self.engines.iter().position(|engine| primary.matches_manifest(engine.manifest()))
    }

    fn configured_engine_list(&self) -> String {
        if self.engines.is_empty() {
            return "none".to_string();
        }
        self.engines
            .iter()
            .map(|engine| {
                let manifest = engine.manifest();
                format!("{}@{}", manifest.name, manifest.version)
            })
            .collect::<Vec<_>>()
            .join(", ")
    }

    fn collect_duplicate_primary_engine_names(&self) -> Vec<&'static str> {
        REQUIRED_PRIMARY_ENGINES
            .iter()
            .copied()
            .filter(|primary| {
                self.engines
                    .iter()
                    .filter(|engine| primary.matches_manifest(engine.manifest()))
                    .take(2)
                    .count()
                    > 1
            })
            .map(PrimaryEngine::name)
            .collect()
    }

    fn collect_invalid_engine_manifest_diagnostics(&self) -> Vec<String> {
        self.engines
            .iter()
            .enumerate()
            .filter_map(|(index, engine)| {
                engine.manifest().validate().err().map(|error| {
                    format!("engine[{index}] `{}` rejected: {error}", engine.manifest().name)
                })
            })
            .collect()
    }

    fn collect_missing_required_engine_names(&self) -> Vec<&'static str> {
        REQUIRED_PRIMARY_ENGINES
            .iter()
            .copied()
            .filter(|primary| !self.required_engine_is_native_ready(*primary))
            .map(PrimaryEngine::name)
            .collect()
    }

    fn required_engine_is_native_ready(&self, primary: PrimaryEngine) -> bool {
        let Some(engine) = self.primary_engine(primary) else {
            return false;
        };
        let owned_kinds = obligation_kinds_owned_by(primary);
        engine.manifest().capabilities.iter().any(|capability| {
            owned_kinds.contains(&capability.obligation_kind)
                && matches!(capability.support, SupportLevel::Supported | SupportLevel::Preferred)
        })
    }

    fn base_evidence(
        &self,
        obligation: &TrustObligation,
        status: EvidenceStatus,
        proof_strength: Option<ProofStrength>,
        diagnostics: Vec<String>,
    ) -> ObligationEvidence {
        ObligationEvidence {
            evidence_id: format!(
                "trust-full-verifier:{}:{}",
                status_label(status),
                obligation.obligation_id
            ),
            obligation_id: obligation.obligation_id.clone(),
            engine: self.manifest.clone(),
            status,
            proof_strength,
            artifacts: Vec::new(),
            counterexample: None::<Counterexample>,
            publication: EvidencePublicationMetadata::default(),
            diagnostics,
        }
    }

    fn verify_with_context_and_native_trust_ir_bundle_with_fresh_receipts(
        &self,
        bundle: &TrustContractBundle,
        obligations: &[TrustObligation],
        context: &VerifierExecutionContext,
        native_bundle: Option<&NativeVerificationBundle>,
    ) -> FullVerificationRunWithFreshReceipts {
        let effective_context = context_with_wall_time_deadline(context);
        let context = &effective_context;
        let native_trust_ir = native_bundle.map(NativeTrustIrEvidenceIndex::from_bundle);
        let native_trust_ir_diagnostics =
            native_trust_ir.as_ref().map_or_else(Vec::new, |index| index.diagnostics.clone());
        let batch_result = if context.is_cancelled() {
            FullVerificationBatchResult::ordinary(Vec::new(), Vec::new())
        } else {
            self.verify_batch_with_context_details(
                bundle,
                obligations,
                Some(context),
                native_trust_ir.as_ref(),
                native_bundle,
            )
        };

        let FullVerificationBatchResult {
            evidence,
            diagnostics,
            direct_trust_vc_receipts,
            fresh_exact_direct_chc_pdr_receipts,
        } = batch_result;
        let mut result = VerificationRunResult::from_evidence(
            context.snapshot(),
            bundle,
            self.manifest().clone(),
            obligations,
            evidence,
        );
        result.diagnostics.extend(native_trust_ir_diagnostics);
        result.diagnostics.extend(diagnostics);
        let (dispatch_seal, direct_trust_vc_receipts, fresh_exact_direct_chc_pdr_receipts) =
            if direct_trust_vc_receipts.is_empty() && fresh_exact_direct_chc_pdr_receipts.is_empty()
                || !publication_boundary_is_live(&result, bundle, obligations, context)
            {
                // The overwhelmingly common result-only path must not clone
                // the complete publication carrier merely to retain an empty
                // authority package.
                (None, BTreeMap::new(), BTreeMap::new())
            } else {
                let dispatch_seal = LiveVerificationDispatchSeal::mint(&result, bundle, context);
                let direct_trust_vc_receipts = finalize_direct_receipts_at_publication_boundary(
                    direct_trust_vc_receipts,
                    &result,
                    bundle,
                    obligations,
                    context,
                    &dispatch_seal,
                );
                let fresh_exact_direct_chc_pdr_receipts =
                    finalize_fresh_receipts_at_publication_boundary(
                        fresh_exact_direct_chc_pdr_receipts,
                        &result,
                        bundle,
                        obligations,
                        context,
                        &dispatch_seal,
                    );
                if !dispatch_seal.is_live()
                    || direct_trust_vc_receipts.is_empty()
                        && fresh_exact_direct_chc_pdr_receipts.is_empty()
                {
                    (None, BTreeMap::new(), BTreeMap::new())
                } else {
                    (
                        Some(dispatch_seal),
                        direct_trust_vc_receipts,
                        fresh_exact_direct_chc_pdr_receipts,
                    )
                }
            };
        FullVerificationRunWithFreshReceipts {
            result,
            live_receipts: LiveVerificationReceiptBatch {
                dispatch_seal,
                direct_trust_vc_receipts,
                fresh_exact_direct_chc_pdr_receipts,
            },
        }
    }
}

/// Ordered per-obligation view over one child engine batch.
///
/// The outer hash join is built once in O(N). Each vector retains the child's
/// original row order, which is observable when rejection priority chooses the
/// first row of a given status. Duplicate identities remain explicit groups;
/// they are never collapsed into an arbitrary authority row.
struct PrimaryEvidenceRowIndex<'a> {
    rows_by_obligation: HashMap<&'a str, Vec<&'a ObligationEvidence>>,
}

impl<'a> PrimaryEvidenceRowIndex<'a> {
    fn new(evidence: &'a [ObligationEvidence]) -> Self {
        let mut rows_by_obligation = HashMap::<&str, Vec<&ObligationEvidence>>::new();
        for row in evidence {
            rows_by_obligation.entry(row.obligation_id.as_str()).or_default().push(row);
        }
        Self { rows_by_obligation }
    }

    fn rows(&self, obligation_id: &str) -> &[&'a ObligationEvidence] {
        self.rows_by_obligation.get(obligation_id).map_or(&[], Vec::as_slice)
    }

    fn unique_row(&self, obligation_id: &str) -> Option<&'a ObligationEvidence> {
        let [row] = self.rows(obligation_id) else { return None };
        Some(*row)
    }

    #[cfg(test)]
    fn indexed_row_count(&self) -> usize {
        self.rows_by_obligation.values().map(Vec::len).sum()
    }
}

fn direct_receipt_authorizes_final_evidence(
    receipt: &DirectTrustVcProofReceipt,
    bundle: &TrustContractBundle,
    obligation: &TrustObligation,
    child_row: Option<&ObligationEvidence>,
    finished: &FinishedPrimaryEvidence,
    context: Option<&VerifierExecutionContext>,
) -> bool {
    let Some(child_row) = child_row else { return false };
    if !final_evidence_matches_accepted_proved_row(&obligation.obligation_id, child_row, finished)
        || receipt.public_obligation_id() != obligation.obligation_id
        || !live_receipt_context_is_live(receipt.dispatch_deadline(), context)
    {
        return false;
    }

    receipt.matches(bundle, obligation, child_row)
        && child_row.proof_strength == finished.evidence.proof_strength
        && live_receipt_context_is_live(receipt.dispatch_deadline(), context)
}

fn fresh_receipt_authorizes_final_evidence(
    receipt: &FreshExactDirectChcPdrReceipt,
    _bundle: &TrustContractBundle,
    obligation: &TrustObligation,
    child_row: Option<&ObligationEvidence>,
    finished: &FinishedPrimaryEvidence,
    context: Option<&VerifierExecutionContext>,
) -> bool {
    let Some(child_row) = child_row else { return false };
    if !final_evidence_matches_accepted_proved_row(&obligation.obligation_id, child_row, finished) {
        return false;
    }

    #[cfg(feature = "trust-build")]
    {
        if receipt.public_obligation_id() != obligation.obligation_id
            || !live_receipt_context_is_live(receipt.dispatch_deadline(), context)
        {
            return false;
        }
        return receipt
            .still_authorizes_under_exact_bundle_seal(obligation)
            .is_ok_and(|strength| Some(strength) == finished.evidence.proof_strength)
            && live_receipt_context_is_live(receipt.dispatch_deadline(), context);
    }

    #[cfg(not(feature = "trust-build"))]
    {
        let _ = (receipt, _bundle, context);
        false
    }
}

fn unique_receipt_obligations(obligations: &[TrustObligation]) -> BTreeMap<&str, &TrustObligation> {
    let mut unique = BTreeMap::new();
    let mut duplicates = std::collections::BTreeSet::new();
    for obligation in obligations {
        let id = obligation.obligation_id.as_str();
        if duplicates.contains(id) {
            continue;
        }
        if unique.insert(id, obligation).is_some() {
            unique.remove(id);
            duplicates.insert(id);
        }
    }
    unique
}

fn direct_receipt_bundle_is_coherent(
    receipts: &BTreeMap<String, DirectTrustVcProofReceipt>,
    bundle: &TrustContractBundle,
) -> bool {
    let Some(first) = receipts.values().next() else { return true };
    first.exact_bundle_matches(bundle)
        && receipts.values().all(|receipt| receipt.shares_exact_bundle(first))
}

fn fresh_receipt_bundle_is_coherent(
    receipts: &BTreeMap<String, FreshExactDirectChcPdrReceipt>,
    bundle: &TrustContractBundle,
) -> bool {
    #[cfg(feature = "trust-build")]
    {
        let Some(first) = receipts.values().next() else { return true };
        return first.exact_bundle_matches(bundle)
            && receipts.values().all(|receipt| receipt.shares_exact_bundle(first));
    }

    #[cfg(not(feature = "trust-build"))]
    {
        let _ = (receipts, bundle);
        receipts.is_empty()
    }
}

fn finalize_direct_receipts_at_publication_boundary(
    receipts: BTreeMap<String, DirectTrustVcProofReceipt>,
    result: &VerificationRunResult,
    bundle: &TrustContractBundle,
    obligations: &[TrustObligation],
    context: &VerifierExecutionContext,
    dispatch_seal: &LiveVerificationDispatchSeal,
) -> BTreeMap<String, DirectTrustVcProofReceipt> {
    if !publication_boundary_is_live(result, bundle, obligations, context) {
        return BTreeMap::new();
    }
    if !direct_receipt_bundle_is_coherent(&receipts, bundle) {
        return BTreeMap::new();
    }
    let obligations_by_id = unique_receipt_obligations(obligations);

    receipts
        .into_iter()
        .filter_map(|(obligation_id, receipt)| {
            let obligation = obligations_by_id.get(obligation_id.as_str()).copied()?;
            let final_row = dispatch_seal.exact_evidence(&obligation_id)?;
            if final_row.status != EvidenceStatus::Proved
                || !receipt.matches_accepted_evidence(final_row)
                || receipt.public_obligation_id() != obligation_id
            {
                return None;
            }
            let receipt = receipt.bind_to_published_run(dispatch_seal)?;
            if !live_receipt_context_is_live(receipt.dispatch_deadline(), Some(context))
                || !receipt
                    .authorizes_accepted_evidence(obligation, final_row, dispatch_seal)
                    .is_ok_and(|strength| Some(strength) == final_row.proof_strength)
                || !live_receipt_context_is_live(receipt.dispatch_deadline(), Some(context))
            {
                return None;
            }
            Some((obligation_id, receipt))
        })
        .collect()
}

fn finalize_fresh_receipts_at_publication_boundary(
    receipts: BTreeMap<String, FreshExactDirectChcPdrReceipt>,
    result: &VerificationRunResult,
    bundle: &TrustContractBundle,
    obligations: &[TrustObligation],
    context: &VerifierExecutionContext,
    dispatch_seal: &LiveVerificationDispatchSeal,
) -> BTreeMap<String, FreshExactDirectChcPdrReceipt> {
    if !publication_boundary_is_live(result, bundle, obligations, context) {
        return BTreeMap::new();
    }
    if !fresh_receipt_bundle_is_coherent(&receipts, bundle) {
        return BTreeMap::new();
    }
    let obligations_by_id = unique_receipt_obligations(obligations);

    receipts
        .into_iter()
        .filter_map(|(obligation_id, receipt)| {
            let obligation = obligations_by_id.get(obligation_id.as_str()).copied()?;
            let final_row = dispatch_seal.exact_evidence(&obligation_id)?;
            if final_row.status != EvidenceStatus::Proved
                || !receipt.matches_accepted_evidence(final_row)
            {
                return None;
            }

            #[cfg(feature = "trust-build")]
            {
                let receipt = receipt.bind_to_published_run(dispatch_seal)?;
                if receipt.public_obligation_id() != obligation_id
                    || !live_receipt_context_is_live(receipt.dispatch_deadline(), Some(context))
                    || !receipt
                        .authorizes_accepted_evidence(obligation, final_row, dispatch_seal)
                        .is_ok_and(|strength| Some(strength) == final_row.proof_strength)
                    || !live_receipt_context_is_live(receipt.dispatch_deadline(), Some(context))
                {
                    return None;
                }
                return Some((obligation_id, receipt));
            }

            #[cfg(not(feature = "trust-build"))]
            {
                let _ = (bundle, obligation, final_row, receipt);
                None
            }
        })
        .collect()
}

fn publication_boundary_is_live(
    result: &VerificationRunResult,
    bundle: &TrustContractBundle,
    obligations: &[TrustObligation],
    context: &VerifierExecutionContext,
) -> bool {
    !context.is_cancelled()
        && !context.budget_exceeded()
        && result.validate_derived_state().is_ok()
        && result.bundle_id == bundle.bundle_id
        && result.subject == bundle.subject
        && result.context == context.snapshot()
        && result.requested_obligations == obligations
}

#[cfg(test)]
fn final_evidence_has_unique_accepted_proved_row(
    obligation_id: &str,
    child_evidence: &[ObligationEvidence],
    finished: &FinishedPrimaryEvidence,
) -> bool {
    let mut matching_rows = child_evidence.iter().filter(|row| row.obligation_id == obligation_id);
    let Some(child_row) = matching_rows.next() else { return false };
    matching_rows.next().is_none()
        && final_evidence_matches_accepted_proved_row(obligation_id, child_row, finished)
}

fn final_evidence_matches_accepted_proved_row(
    obligation_id: &str,
    child_row: &ObligationEvidence,
    finished: &FinishedPrimaryEvidence,
) -> bool {
    finished.accepted
        && finished.evidence.status == EvidenceStatus::Proved
        && child_row.obligation_id == obligation_id
        && child_row.status == EvidenceStatus::Proved
        && child_row.evidence_id == finished.evidence.evidence_id
        && child_row.proof_strength == finished.evidence.proof_strength
}

fn live_receipt_context_is_live(
    dispatch_deadline: Option<Instant>,
    context: Option<&VerifierExecutionContext>,
) -> bool {
    dispatch_deadline == context.and_then(VerifierExecutionContext::deadline)
        && !context.is_some_and(VerifierExecutionContext::is_cancelled)
        && !context.is_some_and(VerifierExecutionContext::budget_exceeded)
}

fn discard_live_receipt_sidecars<R, T>(result: R, receipts: BTreeMap<String, T>) -> R {
    drop(receipts);
    result
}

#[cfg(test)]
mod fresh_receipt_tests {
    use std::sync::{
        Arc,
        atomic::{AtomicUsize, Ordering},
    };
    use std::time::Duration;

    use super::*;

    fn evidence(status: EvidenceStatus) -> ObligationEvidence {
        ObligationEvidence {
            evidence_id: "fresh-row-evidence".to_string(),
            obligation_id: "fresh-row".to_string(),
            engine: EngineManifest::new("trust-mc", API_VERSION, EngineKind::Reachability),
            status,
            proof_strength: (status == EvidenceStatus::Proved).then(|| ProofStrength {
                reasoning: ReasoningKind::Pdr,
                assurance: trust_verifier_api::AssuranceLevel::SmtBacked,
            }),
            artifacts: Vec::new(),
            counterexample: None,
            publication: EvidencePublicationMetadata::default(),
            diagnostics: Vec::new(),
        }
    }

    fn evidence_with_identity(
        obligation_id: impl Into<String>,
        evidence_id: impl Into<String>,
        status: EvidenceStatus,
    ) -> ObligationEvidence {
        let mut evidence = evidence(status);
        evidence.obligation_id = obligation_id.into();
        evidence.evidence_id = evidence_id.into();
        evidence
    }

    fn publication_bundle() -> TrustContractBundle {
        let mut bundle = TrustContractBundle::empty(
            "fresh-bundle",
            trust_verifier_api::BundleSubject::Function {
                crate_name: "fresh".to_string(),
                path: "fresh::f".to_string(),
            },
        );
        bundle.obligations.push(TrustObligation {
            obligation_id: "fresh-row".to_string(),
            kind: trust_verifier_api::ObligationKind::LoopInvariant,
            contract_id: None,
            proof_item_id: None,
            source: trust_verifier_api::SourceLocation::default(),
            description: "fresh exact row".to_string(),
            required_strength: None,
            summary_facts: Vec::new(),
            metadata: Vec::new(),
        });
        bundle
    }

    #[test]
    fn fresh_receipt_structural_gate_clears_demotion_and_conflict() {
        let proved = evidence(EvidenceStatus::Proved);
        let accepted = FinishedPrimaryEvidence { evidence: proved.clone(), accepted: true };
        assert!(final_evidence_has_unique_accepted_proved_row(
            "fresh-row",
            std::slice::from_ref(&proved),
            &accepted,
        ));

        let demoted = FinishedPrimaryEvidence { evidence: proved.clone(), accepted: false };
        assert!(!final_evidence_has_unique_accepted_proved_row(
            "fresh-row",
            std::slice::from_ref(&proved),
            &demoted,
        ));

        let failed = evidence(EvidenceStatus::Failed);
        assert!(!final_evidence_has_unique_accepted_proved_row(
            "fresh-row",
            &[proved.clone(), failed],
            &accepted,
        ));

        let timed_out = FinishedPrimaryEvidence {
            evidence: evidence(EvidenceStatus::Timeout),
            accepted: false,
        };
        assert!(!final_evidence_has_unique_accepted_proved_row(
            "fresh-row",
            std::slice::from_ref(&proved),
            &timed_out,
        ));
    }

    #[test]
    fn primary_evidence_index_preserves_order_conflicts_and_unique_rows() {
        let evidence = vec![
            evidence_with_identity("fresh-row", "unknown-first", EvidenceStatus::Unknown),
            evidence_with_identity("sibling-row", "sibling-only", EvidenceStatus::Proved),
            evidence_with_identity("fresh-row", "failed-first", EvidenceStatus::Failed),
            evidence_with_identity("fresh-row", "failed-second", EvidenceStatus::Failed),
            evidence_with_identity("fresh-row", "proved-last", EvidenceStatus::Proved),
        ];
        let index = PrimaryEvidenceRowIndex::new(&evidence);

        let fresh_rows = index.rows("fresh-row");
        assert_eq!(
            fresh_rows.iter().map(|row| row.evidence_id.as_str()).collect::<Vec<_>>(),
            ["unknown-first", "failed-first", "failed-second", "proved-last"],
            "per-obligation grouping must retain the child engine's original row order",
        );
        let obligation = &publication_bundle().obligations[0];
        assert!(evidence_has_proved_failed_conflict(obligation, fresh_rows));
        assert_eq!(
            rejected_primary_evidence(obligation, fresh_rows)
                .expect("conflicting group has a rejected row")
                .evidence_id,
            "failed-first",
            "rejection priority and first-within-status ordering must remain unchanged",
        );
        assert!(index.unique_row("fresh-row").is_none());
        assert_eq!(
            index.unique_row("sibling-row").map(|row| row.evidence_id.as_str()),
            Some("sibling-only"),
        );
        assert!(index.rows("missing-row").is_empty());
    }

    #[test]
    fn primary_evidence_index_scopes_large_batch_lookups_to_each_identity() {
        const ROWS: usize = 4_096;
        let evidence = (0..ROWS)
            .map(|index| {
                evidence_with_identity(
                    format!("primary-row-{index}"),
                    format!("primary-evidence-{index}"),
                    EvidenceStatus::Proved,
                )
            })
            .collect::<Vec<_>>();
        let index = PrimaryEvidenceRowIndex::new(&evidence);

        assert_eq!(index.indexed_row_count(), ROWS);
        let scoped_row_visits =
            (0..ROWS).map(|row| index.rows(&format!("primary-row-{row}")).len()).sum::<usize>();
        assert_eq!(
            scoped_row_visits, ROWS,
            "looking up every distinct obligation must expose N grouped rows, not N complete batches",
        );
        assert!((0..ROWS).all(|row| index.unique_row(&format!("primary-row-{row}")).is_some()));
    }

    #[test]
    fn fresh_receipt_context_gate_clears_expired_or_foreign_deadlines() {
        let future = Instant::now() + Duration::from_secs(60);
        let live = VerifierExecutionContext::new("fresh-live").with_deadline(future);
        assert!(live_receipt_context_is_live(Some(future), Some(&live)));
        assert!(!live_receipt_context_is_live(Some(future + Duration::from_secs(1)), Some(&live),));

        let elapsed = Instant::now() - Duration::from_millis(1);
        let expired = VerifierExecutionContext::new("fresh-expired").with_deadline(elapsed);
        assert!(!live_receipt_context_is_live(Some(elapsed), Some(&expired)));

        let cancelled = VerifierExecutionContext::new("fresh-cancelled");
        cancelled.cancellation.cancel(trust_verifier_api::CancellationReason::UserRequested);
        assert!(!live_receipt_context_is_live(None, Some(&cancelled)));
    }

    #[test]
    fn publication_boundary_rechecks_derived_state_and_expiry() {
        let bundle = publication_bundle();
        let context = VerifierExecutionContext::new("fresh-publication");
        let result = VerificationRunResult::from_evidence(
            context.snapshot(),
            &bundle,
            EngineManifest::new("trust-full-verifier", API_VERSION, EngineKind::Composite),
            &bundle.obligations,
            vec![evidence(EvidenceStatus::Proved)],
        );
        assert!(publication_boundary_is_live(&result, &bundle, &bundle.obligations, &context,));

        let mut corrupted = result.clone();
        corrupted.evidence.push(evidence(EvidenceStatus::Proved));
        assert!(!publication_boundary_is_live(&corrupted, &bundle, &bundle.obligations, &context,));

        let expired = context.with_deadline(Instant::now() - Duration::from_millis(1));
        assert!(!publication_boundary_is_live(&result, &bundle, &bundle.obligations, &expired,));
    }

    struct DropSpy(Arc<AtomicUsize>);

    impl Drop for DropSpy {
        fn drop(&mut self) {
            self.0.fetch_add(1, Ordering::SeqCst);
        }
    }

    #[test]
    fn ordinary_result_conversion_discards_live_sidecars() {
        let drops = Arc::new(AtomicUsize::new(0));
        let receipts = BTreeMap::from([("fresh-row".to_string(), DropSpy(drops.clone()))]);
        assert_eq!(discard_live_receipt_sidecars("public-result", receipts), "public-result");
        assert_eq!(drops.load(Ordering::SeqCst), 1);
    }
}

fn context_with_wall_time_deadline(context: &VerifierExecutionContext) -> VerifierExecutionContext {
    context.clone().with_wall_time_deadline_from_limits()
}

fn exceeded_obligation_limit(
    context: Option<&VerifierExecutionContext>,
    requested_obligations: usize,
) -> Option<u64> {
    let limit = context.and_then(|context| context.limits.obligation_limit)?;
    ((requested_obligations as u128) > u128::from(limit)).then_some(limit)
}

impl VerificationEngine for FullVerificationEngine {
    fn manifest(&self) -> &EngineManifest {
        &self.manifest
    }

    fn supports(&self, obligation: &TrustObligation) -> SupportLevel {
        let invalid_manifests = &self.invalid_engine_manifests;
        if !invalid_manifests.is_empty() {
            return SupportLevel::Unsupported {
                reason: format!(
                    "full-verification configuration contains invalid engine manifests: {}",
                    invalid_manifests.join("; ")
                ),
            };
        }
        let duplicate_primaries = &self.duplicate_primary_engines;
        if !duplicate_primaries.is_empty() {
            return SupportLevel::Unsupported {
                reason: format!(
                    "full-verification configuration has ambiguous duplicate primary engines: {}",
                    duplicate_primaries.join(", ")
                ),
            };
        }
        if self.policy.require_all_required_engines {
            let missing = &self.missing_required_engines;
            if !missing.is_empty() {
                return SupportLevel::Unsupported {
                    reason: format!(
                        "full verification requires native trust-wp, trust-vc, trust-mc, and TY engines; missing: {}",
                        missing.join(", ")
                    ),
                };
            }
        }
        let Some(route) = obligation_route(obligation) else {
            return SupportLevel::Unsupported {
                reason: format!(
                    "unsupported full-verification obligation kind {:?}",
                    obligation.kind
                ),
            };
        };
        let Some(primary) = self.primary_engine(route.primary) else {
            return SupportLevel::Unsupported {
                reason: format!(
                    "primary owner {} is not configured for {:?}",
                    route.primary.name(),
                    obligation.kind
                ),
            };
        };
        match primary.supports(obligation) {
            SupportLevel::Supported | SupportLevel::Preferred => SupportLevel::Preferred,
            unsupported => unsupported,
        }
    }

    fn verify_validated(
        &self,
        request: ValidatedVerificationRequest<'_>,
    ) -> Vec<ObligationEvidence> {
        let obligations = request.obligations();
        obligations
            .iter()
            .map(|obligation| {
                self.not_attempted(
                    obligation,
                    "trust-full-verifier requires VerifierExecutionContext; call verify_bundle or verify_with_context so resource limits, cancellation, deadlines, and run manifests are enforced",
                )
            })
            .collect()
    }

    fn verify_with_context_validated(
        &self,
        request: ValidatedVerificationRequest<'_>,
        context: &VerifierExecutionContext,
    ) -> VerificationRunResult {
        let (bundle, obligations) = request.into_parts();
        self.verify_with_context_and_native_trust_ir_bundle_with_fresh_receipts(
            bundle,
            obligations,
            context,
            None,
        )
        .into_result()
    }
}
