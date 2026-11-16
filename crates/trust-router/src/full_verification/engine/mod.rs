//! `FullVerificationEngine` orchestration and per-batch dispatch.

mod batch;
mod kernel_replay;
mod native_stop;
use std::collections::{BTreeMap, HashMap};
use std::time::Instant;

pub use kernel_replay::CurrentKernelProofReplay;
use rayon::prelude::*;
use trust_ir_bridge::{NativeVerificationBundle, SourceGenerationAuthority};
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
    CheckedNativeWpProof, DirectTrustVcProofReceipt, FreshExactDirectChcPdrReceipt,
    FreshWholeFunctionChcPdrReceipt, LiveVerificationDispatchSeal, NativeLiveSource,
    NativeSourceReferenceFacts, NativeTrustIrEvidenceIndex, is_native_trust_ir_engine,
    is_native_trust_mc_trust_bmc_engine, native_trust_ir_artifact_match,
    native_trust_ir_bundle_evidence, native_trust_ir_bundle_evidence_is_incomplete,
};
use super::policy::FullVerificationPolicy;
use super::routing::{
    FallbackEligibility, ObligationRoute, PrimaryEngine, REQUIRED_PRIMARY_ENGINES,
    fallback_eligibility, fallback_route, obligation_route,
};
use super::util::{append_unique_artifacts, status_label, support_description, worker_threads};

/// A live full-verification result, checked proof facts and affine sidecars.
///
/// This type is intentionally not cloneable or serializable. The ordinary
/// full-verifier entry points discard these private values; the explicit live
/// API carries them into the compiler's final authority boundary. A checked WP
/// fact can be cloned for identical inputs; transient source receipts cannot.
#[derive(Debug)]
pub struct FullVerificationRunWithFreshReceipts {
    result: VerificationRunResult,
    live_receipts: LiveVerificationReceiptBatch,
    kernel_proof_replays: Vec<CurrentKernelProofReplay>,
}

/// Opaque package of checked proof facts and live dispatch receipts.
///
/// The private dispatch seal, source run, and both receipt maps remain coupled
/// inside this non-cloneable, non-serializable value. Callers may move receipts
/// out for compiler consumption, but can authorize them only through the same
/// package; there is no independent seal/source argument that can be swapped
/// with a byte-identical result from another dispatch. The separately checked
/// WP facts bind content and do not depend on this transient dispatch seal.
#[derive(Debug)]
pub struct LiveVerificationReceiptBatch {
    checked_native_wp_proofs: BTreeMap<String, CheckedNativeWpProof>,
    // `None` is the ordinary, zero-authority case. Avoid minting the seal in
    // that case: minting snapshots the complete source run, so doing it for
    // every result would impose an unnecessary O(run-size) clone on callers
    // that never produced a live receipt.
    dispatch_seal: Option<LiveVerificationDispatchSeal>,
    direct_trust_vc_receipts: BTreeMap<String, DirectTrustVcProofReceipt>,
    fresh_exact_direct_chc_pdr_receipts: BTreeMap<String, FreshExactDirectChcPdrReceipt>,
    fresh_whole_function_chc_pdr_receipts: BTreeMap<String, FreshWholeFunctionChcPdrReceipt>,
}

mod whole_function_receipts;
use whole_function_receipts::{
    finalize_whole_receipts_at_publication_boundary, whole_receipt_authorizes_final_evidence,
    whole_receipt_bundle_is_coherent,
};

impl LiveVerificationReceiptBatch {
    /// Checked proof facts may be reused for identical content. Unlike the
    /// source-generation receipts, they carry no transient dispatch authority.
    #[must_use]
    pub fn checked_native_wp_proofs(&self) -> &BTreeMap<String, CheckedNativeWpProof> {
        &self.checked_native_wp_proofs
    }

    pub fn take_checked_native_wp_proofs(&mut self) -> BTreeMap<String, CheckedNativeWpProof> {
        std::mem::take(&mut self.checked_native_wp_proofs)
    }

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
            checked_native_wp_proofs: BTreeMap::new(),
            dispatch_seal: Some(dispatch_seal),
            direct_trust_vc_receipts: std::iter::once((obligation_id.to_string(), receipt))
                .collect(),
            fresh_exact_direct_chc_pdr_receipts: BTreeMap::new(),
            fresh_whole_function_chc_pdr_receipts: BTreeMap::new(),
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
            checked_native_wp_proofs: BTreeMap::new(),
            dispatch_seal: Some(dispatch_seal),
            direct_trust_vc_receipts: BTreeMap::new(),
            fresh_exact_direct_chc_pdr_receipts: std::iter::once((
                obligation_id.to_string(),
                receipt,
            ))
            .collect(),
            fresh_whole_function_chc_pdr_receipts: BTreeMap::new(),
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
    #[must_use]
    pub fn checked_native_wp_proofs(&self) -> &BTreeMap<String, CheckedNativeWpProof> {
        self.live_receipts.checked_native_wp_proofs()
    }

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

    /// Move checked proof facts out of this actual dispatch once. They remain
    /// non-serializable and require exact current-row admission by a consumer.
    pub fn take_current_kernel_proof_replays(&mut self) -> Vec<CurrentKernelProofReplay> {
        std::mem::take(&mut self.kernel_proof_replays)
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
        let result = discard_live_receipt_sidecars(
            result,
            self.live_receipts.fresh_exact_direct_chc_pdr_receipts,
        );
        discard_live_receipt_sidecars(
            result,
            self.live_receipts.fresh_whole_function_chc_pdr_receipts,
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
    /// Trust (2026-09-18): the session's `-Z trust-verify-timeout-ms`, carried so the
    /// NATIVE TRUST-IR BUNDLE path gets the budget the user asked for.
    ///
    /// The engines vector already honours it — `NativeTrustMcTrustIrEngine::with_timeout_ms`
    /// configures its adapter — but `native_trust_ir_bundle_evidence` does not use that
    /// adapter: it builds its own from `production_trust_mc_native_trust_ir_adapter`, which
    /// hardcoded a mirror of the 5s DEFAULT. So on the one route a `[termination]` obligation
    /// actually takes, raising the flag bought nothing and the run still reported
    /// `exceeded the 7s wall-clock ceiling` at every value (measured 1ms, 1s, 9s, 20s and 60s
    /// — identical message). That is the exact failure mode
    /// `NativeTrustMcTrustIrEngine::with_timeout_ms` documents on itself and warns against;
    /// this is the same bug in a second place.
    ///
    /// SOUND: the budget bounds only how long a sound solver lane may RUN. A larger budget can
    /// turn Unknown into a definite verdict; it can never turn an unproved obligation into a
    /// proof. `new` keeps the session-less default so the 57 existing constructors are
    /// unchanged.
    per_obligation_timeout_ms: u64,
    engines: Vec<Box<dyn VerificationEngine + Send + Sync>>,
    invalid_engine_manifests: Vec<String>,
    duplicate_primary_engines: Vec<&'static str>,
    missing_required_engines: Vec<&'static str>,
    kernel_replay: Option<std::sync::Arc<kernel_replay::KernelReplayInputs>>,
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
            per_obligation_timeout_ms: super::engines::DEFAULT_PER_OBLIGATION_TIMEOUT_MS,
            engines,
            invalid_engine_manifests: Vec::new(),
            duplicate_primary_engines: Vec::new(),
            missing_required_engines: Vec::new(),
            kernel_replay: None,
        };
        // Engine manifests and registrations are immutable after construction.
        // Audit them once instead of rescanning every capability for every
        // obligation in a large bundle.
        verifier.invalid_engine_manifests = verifier.collect_invalid_engine_manifest_diagnostics();
        verifier.duplicate_primary_engines = verifier.collect_duplicate_primary_engine_names();
        verifier.missing_required_engines = verifier.collect_missing_required_engine_names();
        verifier
    }

    /// Supply candidate mathematics for freshly generated compiler VCs. This
    /// association is not program-to-VC authority: native rows remain pending,
    /// and consumers must independently validate their exact current binding.
    #[must_use]
    pub fn with_kernel_proof_replay_candidates(
        mut self,
        bundle: &TrustContractBundle,
        candidates: Vec<(TrustObligation, trust_types::VerificationCondition)>,
        root: std::path::PathBuf,
        context: &VerifierExecutionContext,
    ) -> Self {
        self.kernel_replay =
            kernel_replay::KernelReplayInputs::new(bundle, candidates, root, context)
                .map(std::sync::Arc::new);
        self
    }

    fn replay_before_primary_search(
        &self,
        bundle: &TrustContractBundle,
        obligations: &[TrustObligation],
        obligation: &TrustObligation,
        primary: &EngineManifest,
        context: Option<&VerifierExecutionContext>,
        native_bundle: Option<&NativeVerificationBundle>,
        native_index: Option<&NativeTrustIrEvidenceIndex>,
        live_source: Option<NativeLiveSource<'_>>,
        replay: Option<&mut kernel_replay::KernelReplaySession>,
    ) -> bool {
        let Some(context) = context else { return false };
        // This per-call guard precedes the session's admission memo. A generic
        // sibling must not populate a memo that authorizes a native row, and
        // absent required native/source inputs never reach kernel replay.
        if (is_native_trust_ir_engine(primary) || native_bundle.is_some())
            && (!is_native_trust_mc_trust_bmc_engine(primary)
                || native_bundle.is_none()
                || native_index.is_none()
                || live_source.is_none())
        {
            return false;
        }
        replay.is_some_and(|session| {
            session.replay(bundle, obligation, context, || {
                // A native request/source/refusal cannot disappear behind a
                // valid proof for mathematical bytes supplied by a caller.
                if is_native_trust_ir_engine(primary) || native_bundle.is_some() {
                    let Some(native) = native_bundle else { return Default::default() };
                    let Some(source) = live_source else { return Default::default() };
                    let Some(index) = native_index else { return Default::default() };
                    if !is_native_trust_mc_trust_bmc_engine(primary) {
                        // Other suites keep their ordinary consumer until they
                        // expose an equally complete no-solve admission seam.
                        return Default::default();
                    }
                    let requested = obligations
                        .iter()
                        .filter(|row| {
                            obligation_route(row)
                                .is_some_and(|route| route.primary == PrimaryEngine::TrustMc)
                        })
                        .cloned()
                        .collect::<Vec<_>>();
                    if requested.iter().any(|row| {
                        let Some(route) = obligation_route(row) else { return true };
                        index.artifact_match(route, row).ok().flatten().is_none()
                    }) {
                        return Default::default();
                    }
                    #[cfg(feature = "trust-build")]
                    {
                        let adapter = trust_bmc::TrustMcVerifierApiAdapter::new(
                            trust_bmc::TrustMcConfig::new()
                                .with_proof_mode(trust_bmc::TrustMcProofMode::PdrIc3)
                                .with_timeout(self.per_obligation_timeout_ms),
                        )
                        .with_solve_cutoff(context.native_solve_cutoff);
                        adapter
                            .kernel_replay_admissible_native_obligations(
                                bundle,
                                &requested,
                                native,
                                source.authority,
                                source.reference_facts,
                                context.deadline,
                            )
                            .unwrap_or_default()
                    }
                    #[cfg(not(feature = "trust-build"))]
                    {
                        let _ = (native, source);
                        Default::default()
                    }
                } else {
                    // Non-native component engines carry no typed request or
                    // live-source claim. This branch creates no public proof.
                    obligations.iter().map(|row| row.obligation_id.clone()).collect()
                }
            })
        })
    }

    /// Build a verifier with the required native trust-vc/trust-mc/TY
    /// engines at the `-Z trust-verify-timeout-ms` *default* budget.
    ///
    /// Session-less callers only. Compiler paths should use
    /// [`Self::with_required_native_engines_timeout_ms`] so a user who raises
    /// the flag actually gets the budget they asked for.
    #[must_use]
    pub fn with_required_native_engines() -> Self {
        Self::new(super::engines::required_native_engines(), FullVerificationPolicy::default())
    }

    /// Build a verifier with the required native engines at the compiler's
    /// configured per-obligation SMT budget.
    ///
    /// SOUND: the budget bounds only how long a sound solver lane may run. A
    /// larger budget can turn Unknown into a definite verdict; it can never turn
    /// an unproved obligation into a proof.
    #[must_use]
    pub fn with_required_native_engines_timeout_ms(timeout_ms: u64) -> Self {
        let mut verifier = Self::new(
            super::engines::required_native_engines_with_timeout_ms(timeout_ms),
            FullVerificationPolicy::default(),
        );
        // Carry it for the native trust-ir BUNDLE path too — see the field's note.
        verifier.per_obligation_timeout_ms = timeout_ms;
        verifier
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
    /// and replay boundary for active trust-vc/trust-mc evidence. Historical
    /// TrustWP requests remain parseable but have no routed owner and cannot
    /// become accepted child evidence.
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
            None,
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
            None,
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
            None,
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
            None,
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
        authority: Option<&SourceGenerationAuthority>,
        context: &VerifierExecutionContext,
    ) -> FullVerificationRunWithFreshReceipts {
        self.verify_with_context_and_native_trust_ir_bundle_with_fresh_receipts(
            bundle,
            obligations,
            context,
            native_bundle,
            None,
        )
    }

    /// Verify an exact canonical subset with live source-generation authority.
    ///
    /// Unlike the ordinary native-bundle entry points, this explicit compiler
    /// seam may admit TrustMC source-only semantic shortcuts. The affine token
    /// is borrowed, never cloned, and remains subject to TrustMC's exact-bundle
    /// identity and digest checks.
    #[must_use]
    pub fn verify_obligations_with_native_trust_ir_bundle_and_source_authority_and_live_receipts(
        &self,
        bundle: &TrustContractBundle,
        obligations: &[TrustObligation],
        native_bundle: &NativeVerificationBundle,
        source_generation_authority: &SourceGenerationAuthority,
        context: &VerifierExecutionContext,
    ) -> FullVerificationRunWithFreshReceipts {
        self.verify_with_context_and_native_trust_ir_bundle_with_fresh_receipts(
            bundle,
            obligations,
            context,
            Some(native_bundle),
            Some(NativeLiveSource::authority_only(source_generation_authority)),
        )
    }

    /// Trust (C1, 2026-11-06): [`Self::verify_obligations_with_native_trust_ir_bundle_and_source_authority_and_live_receipts`]
    /// plus the compiler's live source reference facts for the SAME bundle and
    /// authority. The native TrustMC lane then runs its pre-solve translation and
    /// its solve through trust-mc's `_with_source_reference_facts` entries; facts
    /// that do not authorize the exact pair fail that lane closed (trust-bmc's
    /// facts entry), never silently fact-free. The facts are borrowed, never
    /// cloned, cached or serialized.
    #[must_use]
    pub fn verify_obligations_with_native_trust_ir_bundle_and_source_reference_facts_and_live_receipts(
        &self,
        bundle: &TrustContractBundle,
        obligations: &[TrustObligation],
        native_bundle: &NativeVerificationBundle,
        source_generation_authority: &SourceGenerationAuthority,
        source_reference_facts: &NativeSourceReferenceFacts<'_>,
        context: &VerifierExecutionContext,
    ) -> FullVerificationRunWithFreshReceipts {
        self.verify_with_context_and_native_trust_ir_bundle_with_fresh_receipts(
            bundle,
            obligations,
            context,
            Some(native_bundle),
            Some(NativeLiveSource {
                authority: source_generation_authority,
                reference_facts: Some(source_reference_facts),
            }),
        )
    }

    fn verify_batch_with_context_details(
        &self,
        bundle: &TrustContractBundle,
        obligations: &[TrustObligation],
        context: Option<&VerifierExecutionContext>,
        native_trust_ir: Option<&NativeTrustIrEvidenceIndex>,
        native_bundle: Option<&NativeVerificationBundle>,
        live_source: Option<NativeLiveSource<'_>>,
        mut replay: Option<&mut kernel_replay::KernelReplaySession>,
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
                    "full verification requires native trust-vc, trust-mc, and TY engines; missing: {}",
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

            if let Some(reason) = native_trust_mc_solve_cannot_publish(
                self.policy,
                route,
                primary.manifest(),
                obligation,
                native_trust_ir,
            ) {
                results[index] = Some(self.policy_unsupported(obligation, reason));
                continue;
            }

            // Trust: only after every existing routing/support/native-input
            // refusal, try current-kernel replay. Keep the complete request and
            // a pending public row; the actual proof travels separately to the
            // compiler's exact final-row authority gate. Unresolved siblings
            // still enter their ordinary batch (including whole-body work).
            if self.replay_before_primary_search(
                bundle,
                obligations,
                obligation,
                primary.manifest(),
                context,
                native_bundle,
                native_trust_ir,
                live_source,
                replay.as_deref_mut(),
            ) {
                results[index] = Some(self.not_attempted(
                    obligation,
                    "native search omitted after current-kernel proof replay; exact compiler row admission remains pending",
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
        let mut checked_native_wp_proofs = BTreeMap::new();
        let mut direct_trust_vc_receipts = BTreeMap::new();
        let mut fresh_exact_direct_chc_pdr_receipts = BTreeMap::new();
        let mut fresh_whole_function_chc_pdr_receipts = BTreeMap::new();
        let mut duplicate_whole_receipt_ids = std::collections::BTreeSet::new();
        for completed in
            self.execute_engine_batches(bundle, engine_batches, context, native_bundle, live_source)
        {
            diagnostics.push(engine_batch_diagnostic(&completed, context));
            let CompletedEngineBatch {
                batch,
                evidence: child_evidence,
                manifest,
                elapsed_ms: _,
                direct_trust_vc_receipts: mut batch_direct_receipts,
                fresh_exact_direct_chc_pdr_receipts: mut batch_fresh_receipts,
                fresh_whole_function_chc_pdr_receipts: mut batch_whole_receipts,
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
            if !whole_receipt_bundle_is_coherent(
                &batch_whole_receipts,
                bundle,
                native_bundle,
                live_source.map(|source| source.authority),
            ) {
                batch_whole_receipts.clear();
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
                let mut finished = if context.is_some_and(|context| context.budget_exceeded()) {
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
                if let Some(fallback) = fallback_route(&item.obligation) {
                    let fallback_engine = self
                        .engines
                        .iter()
                        .position(|engine| fallback.0.primary.matches_manifest(engine.manifest()));
                    let budget_exceeded = context.is_some_and(|context| {
                        context.budget_exceeded()
                            || context.is_cancelled()
                            || context
                                .solve_deadline()
                                .is_some_and(|deadline| Instant::now() >= deadline)
                    });
                    let definitive = child_rows.iter().any(|row| {
                        matches!(row.status, EvidenceStatus::Proved | EvidenceStatus::Failed)
                    });
                    let primary_engine = self
                        .engines
                        .iter()
                        .position(|engine| item.route.primary.matches_manifest(engine.manifest()));
                    // A missing primary or fallback index means no fallback
                    // attempt: eligibility already refuses a `None` fallback,
                    // and a `None` primary (unreachable for a routed batch
                    // item) fails closed the same way instead of panicking.
                    let eligible = match (primary_engine, fallback_engine) {
                        (Some(primary_engine), Some(_)) => {
                            fallback_eligibility(
                                finished.accepted,
                                finished.evidence.status,
                                finished.evidence.decline,
                                definitive,
                                Some(fallback),
                                primary_engine,
                                fallback_engine,
                                budget_exceeded,
                            ) == FallbackEligibility::Eligible
                        }
                        _ => false,
                    };
                    if let (true, Some(fallback_engine)) = (eligible, fallback_engine) {
                        let alternative_started = Instant::now();
                        let alternative = self.execute_engine_batch(
                            bundle,
                            EngineBatch {
                                engine_index: fallback_engine,
                                batch: vec![RoutedObligation {
                                    index: item.index,
                                    obligation: item.obligation.clone(),
                                    route: fallback.0,
                                }],
                            },
                            context,
                            native_bundle,
                            live_source,
                        );
                        diagnostics.push(engine_batch_diagnostic(&alternative, context));
                        let alternative_rows = alternative.evidence.iter().collect::<Vec<_>>();
                        let mut alternative_finished = if let Some(evidence) =
                            self.fallback_stop_evidence(&item.obligation, context)
                        {
                            FinishedPrimaryEvidence { evidence, accepted: false }
                        } else {
                            self.finish_primary_evidence(
                                bundle,
                                &item.obligation,
                                fallback.0,
                                &alternative_rows,
                                &alternative.manifest,
                                native_trust_ir,
                                None,
                            )
                        };
                        // Certificate checking is part of this attempt too.
                        // Recheck after it, before any proof can be published.
                        if let Some(evidence) =
                            self.fallback_stop_evidence(&item.obligation, context)
                        {
                            alternative_finished =
                                FinishedPrimaryEvidence { evidence, accepted: false };
                        } else if alternative_started.elapsed()
                            >= std::time::Duration::from_millis(self.per_obligation_timeout_ms)
                        {
                            alternative_finished = FinishedPrimaryEvidence {
                                evidence: self.timed_out(
                                    &item.obligation,
                                    "deductive fallback budget expired during certificate checking",
                                ),
                                accepted: false,
                            };
                        }
                        if alternative_finished.accepted
                            || matches!(
                                alternative_finished.evidence.status,
                                EvidenceStatus::Failed
                                    | EvidenceStatus::Canceled
                                    | EvidenceStatus::Timeout
                            )
                        {
                            let original = finished.evidence;
                            finished = alternative_finished;
                            finished.evidence.diagnostics.push(format!(
                                "deductive fallback followed {} from {}; primary diagnostics: {}",
                                status_label(original.status),
                                item.route.primary.name(),
                                original.diagnostics.join("; "),
                            ));
                        } else {
                            finished.evidence.diagnostics.push(format!(
                                "deductive fallback did not discharge the obligation: {}",
                                alternative_finished.evidence.diagnostics.join("; "),
                            ));
                        }
                    }
                }
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
                if finished.accepted
                    && let Some(proof) = native_trust_ir.and_then(|index| {
                        index.checked_wp_proof(bundle, &item.obligation, &finished.evidence)
                    })
                {
                    checked_native_wp_proofs.insert(item.obligation.obligation_id.clone(), proof);
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
                if let Some(receipt) = batch_whole_receipts.remove(&item.obligation.obligation_id)
                    && !duplicate_whole_receipt_ids.contains(&item.obligation.obligation_id)
                    && whole_receipt_authorizes_final_evidence(
                        &receipt,
                        &item.obligation,
                        unique_child_row,
                        &finished,
                        context,
                    )
                    && let Some(receipt) = receipt.bind_to_accepted_evidence(&finished.evidence)
                    && fresh_whole_function_chc_pdr_receipts
                        .insert(item.obligation.obligation_id.clone(), receipt)
                        .is_some()
                {
                    // Retain the ambiguity tombstone: a third duplicate cannot
                    // resurrect a capability discarded by the first collision.
                    duplicate_whole_receipt_ids.insert(item.obligation.obligation_id.clone());
                    fresh_whole_function_chc_pdr_receipts.remove(&item.obligation.obligation_id);
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
            checked_native_wp_proofs,
            direct_trust_vc_receipts,
            fresh_exact_direct_chc_pdr_receipts,
            fresh_whole_function_chc_pdr_receipts,
        }
    }

    /// Run the per-engine batches serially, on a pool of the worker-thread
    /// limit, or on rayon's global pool. Which one is a scheduling choice that
    /// decides no verdict, so the budget profile id leaves the worker count out
    /// (`trust_types::determinism::BudgetProfile::worker_threads`). Batch work
    /// therefore reads no thread-local budget (`trust_types::verify_budget`),
    /// which on a pool thread would not be the function's, and consults no
    /// per-process cache, whose fill order would follow the schedule.
    fn execute_engine_batches(
        &self,
        bundle: &TrustContractBundle,
        engine_batches: Vec<EngineBatch>,
        context: Option<&VerifierExecutionContext>,
        native_bundle: Option<&NativeVerificationBundle>,
        live_source: Option<NativeLiveSource<'_>>,
    ) -> Vec<CompletedEngineBatch> {
        if engine_batches.len() <= 1 || worker_threads(context).is_some_and(|limit| limit <= 1) {
            return self.execute_engine_batches_serial(
                bundle,
                engine_batches,
                context,
                native_bundle,
                live_source,
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
                        live_source,
                    )
                });
            }
            return self.execute_engine_batches_serial(
                bundle,
                engine_batches,
                context,
                native_bundle,
                live_source,
            );
        }

        self.execute_engine_batches_parallel(
            bundle,
            engine_batches,
            context,
            native_bundle,
            live_source,
        )
    }

    fn execute_engine_batches_serial(
        &self,
        bundle: &TrustContractBundle,
        engine_batches: Vec<EngineBatch>,
        context: Option<&VerifierExecutionContext>,
        native_bundle: Option<&NativeVerificationBundle>,
        live_source: Option<NativeLiveSource<'_>>,
    ) -> Vec<CompletedEngineBatch> {
        engine_batches
            .into_iter()
            .map(|engine_batch| {
                self.execute_engine_batch(bundle, engine_batch, context, native_bundle, live_source)
            })
            .collect()
    }

    fn execute_engine_batches_parallel(
        &self,
        bundle: &TrustContractBundle,
        engine_batches: Vec<EngineBatch>,
        context: Option<&VerifierExecutionContext>,
        native_bundle: Option<&NativeVerificationBundle>,
        live_source: Option<NativeLiveSource<'_>>,
    ) -> Vec<CompletedEngineBatch> {
        engine_batches
            .into_par_iter()
            .map(|engine_batch| {
                self.execute_engine_batch(bundle, engine_batch, context, native_bundle, live_source)
            })
            .collect()
    }

    fn execute_engine_batch(
        &self,
        bundle: &TrustContractBundle,
        engine_batch: EngineBatch,
        context: Option<&VerifierExecutionContext>,
        native_bundle: Option<&NativeVerificationBundle>,
        live_source: Option<NativeLiveSource<'_>>,
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
        // Trust (2026-10-17, gate-rca deadline): the native lane stops SOLVING at the
        // context's native solve cutoff — its share of the function clock — while every
        // receipt it mints stays bound to `deadline` (see
        // `VerifierExecutionContext::native_solve_cutoff`).
        let native_solve_cutoff = context.and_then(|ctx| ctx.native_solve_cutoff);
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
                live_source,
                deadline,
                native_solve_cutoff,
                self.per_obligation_timeout_ms,
            )
        }))
        .unwrap_or(None);
        let (
            mut evidence,
            mut direct_trust_vc_receipts,
            mut fresh_exact_direct_chc_pdr_receipts,
            mut fresh_whole_function_chc_pdr_receipts,
        ) = match native_evidence {
            Some(mut native_evidence) => {
                native_stop::qualify_native_stops(
                    &mut native_evidence.evidence,
                    native_bundle.is_some()
                        && is_native_trust_mc_trust_bmc_engine(primary.manifest()),
                );
                (
                    Some(native_evidence.evidence),
                    native_evidence.direct_trust_vc_receipts,
                    native_evidence.fresh_exact_direct_chc_pdr_receipts,
                    native_evidence.fresh_whole_function_chc_pdr_receipts,
                )
            }
            None => (None, BTreeMap::new(), BTreeMap::new(), BTreeMap::new()),
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
            fresh_whole_function_chc_pdr_receipts.clear();
            let mut primary_evidence = if let Some(context) = context {
                // The fallback primary solve is part of the same native lane: it stops at
                // the cutoff too. It mints no receipt (its sidecars were cleared above),
                // and the snapshot does not carry a deadline, so only its solving changes.
                match context.solve_deadline() {
                    Some(solve_deadline) if context.native_solve_cutoff.is_some() => {
                        let solving = context.clone().with_deadline(solve_deadline);
                        primary.verify_with_context(bundle, &requested, &solving).evidence
                    }
                    _ => primary.verify_with_context(bundle, &requested, context).evidence,
                }
            } else {
                primary.verify(bundle, &requested)
            };
            // Generic primary engines cannot claim the built-in native phase,
            // including through a copied producer or already-qualified marker.
            native_stop::qualify_native_stops(&mut primary_evidence, false);
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
            fresh_whole_function_chc_pdr_receipts,
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

    fn fallback_stop_evidence(
        &self,
        obligation: &TrustObligation,
        context: Option<&VerifierExecutionContext>,
    ) -> Option<ObligationEvidence> {
        let context = context?;
        if context.is_cancelled() {
            return Some(self.base_evidence(
                obligation,
                EvidenceStatus::Canceled,
                None,
                vec!["verification canceled before accepting deductive fallback".into()],
            ));
        }
        if context.budget_exceeded()
            || context.solve_deadline().is_some_and(|deadline| Instant::now() >= deadline)
        {
            return Some(self.timed_out(
                obligation,
                "verification budget expired before accepting deductive fallback",
            ));
        }
        None
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
        [PrimaryEngine::TrustWp, PrimaryEngine::TrustVc, PrimaryEngine::TrustMc, PrimaryEngine::Ty]
            .into_iter()
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
            decline: None,
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
        live_source: Option<NativeLiveSource<'_>>,
    ) -> FullVerificationRunWithFreshReceipts {
        // Candidate inputs are immutable; checked state belongs to this
        // invocation, including simultaneous calls on the same engine/context.
        let mut kernel_replay = self
            .kernel_replay
            .as_ref()
            .map(|inputs| kernel_replay::KernelReplaySession::start(std::sync::Arc::clone(inputs)));
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
                live_source,
                kernel_replay.as_mut(),
            )
        };

        let FullVerificationBatchResult {
            evidence,
            diagnostics,
            mut checked_native_wp_proofs,
            direct_trust_vc_receipts,
            fresh_exact_direct_chc_pdr_receipts,
            fresh_whole_function_chc_pdr_receipts,
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
        if !publication_boundary_is_live(&result, bundle, obligations, context) {
            checked_native_wp_proofs.clear();
        } else {
            // Retain only facts for the exact final public row. This performs
            // content comparisons, never another solver invocation or replay.
            let obligations_by_id = obligations
                .iter()
                .map(|obligation| (obligation.obligation_id.as_str(), obligation))
                .collect::<HashMap<_, _>>();
            let rows = PrimaryEvidenceRowIndex::new(&result.evidence);
            checked_native_wp_proofs.retain(|id, proof| {
                let Some(obligation) = obligations_by_id.get(id.as_str()) else { return false };
                let Some(evidence) = rows.unique_row(id) else { return false };
                native_bundle
                    .is_some_and(|native| proof.matches(bundle, native, obligation, evidence))
            });
        }
        let (
            dispatch_seal,
            direct_trust_vc_receipts,
            fresh_exact_direct_chc_pdr_receipts,
            fresh_whole_function_chc_pdr_receipts,
        ) = if direct_trust_vc_receipts.is_empty()
            && fresh_exact_direct_chc_pdr_receipts.is_empty()
            && fresh_whole_function_chc_pdr_receipts.is_empty()
            || !publication_boundary_is_live(&result, bundle, obligations, context)
        {
            // The overwhelmingly common result-only path must not clone
            // the complete publication carrier merely to retain an empty
            // authority package.
            (None, BTreeMap::new(), BTreeMap::new(), BTreeMap::new())
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
            let fresh_whole_function_chc_pdr_receipts =
                finalize_whole_receipts_at_publication_boundary(
                    fresh_whole_function_chc_pdr_receipts,
                    &result,
                    bundle,
                    obligations,
                    native_bundle,
                    live_source.map(|source| source.authority),
                    context,
                    &dispatch_seal,
                );
            if !dispatch_seal.is_live()
                || direct_trust_vc_receipts.is_empty()
                    && fresh_exact_direct_chc_pdr_receipts.is_empty()
                    && fresh_whole_function_chc_pdr_receipts.is_empty()
            {
                (None, BTreeMap::new(), BTreeMap::new(), BTreeMap::new())
            } else {
                (
                    Some(dispatch_seal),
                    direct_trust_vc_receipts,
                    fresh_exact_direct_chc_pdr_receipts,
                    fresh_whole_function_chc_pdr_receipts,
                )
            }
        };
        // Finalization itself consumes time. Do not export newly checked facts
        // after cancellation or a wall-time expiry during that bookkeeping.
        if context.is_cancelled()
            || context.budget_exceeded()
            || result.context != context.snapshot()
        {
            checked_native_wp_proofs.clear();
        }
        let kernel_proof_replays =
            if publication_boundary_is_live(&result, bundle, obligations, context) {
                kernel_replay
                    .as_mut()
                    .map_or_else(Vec::new, |session| session.take_checked(bundle, context))
            } else {
                Vec::new()
            };
        FullVerificationRunWithFreshReceipts {
            result,
            kernel_proof_replays,
            live_receipts: LiveVerificationReceiptBatch {
                checked_native_wp_proofs,
                dispatch_seal,
                direct_trust_vc_receipts,
                fresh_exact_direct_chc_pdr_receipts,
                fresh_whole_function_chc_pdr_receipts,
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

/// The compiler's typed-CHC encoding-fidelity attestation key, and the one value
/// of it that gives a trust-mc refutation authority. Mirrors
/// `TRUST_MC_TYPED_CHC_ENCODING_FIDELITY_*` in `trust-bmc`'s `verifier_api.rs`
/// and in `trust_verify.rs`. Used here only to KEEP dispatching a row, so a
/// rename that this copy misses makes the skip below miss rows, not drop them:
/// postconditions, the only kind the compiler attests, are kept regardless.
pub(super) const TRUST_MC_TYPED_CHC_ENCODING_FIDELITY_METADATA_KEY: &str =
    "trust-trust-mc.typed-chc-obligation.encoding_fidelity";
pub(super) const TRUST_MC_TYPED_CHC_ENCODING_FIDELITY_EXACT: &str = "exact";

/// `Some(reason)` when dispatching `obligation` to the native trust-mc lane
/// cannot change its published verdict, so the solve must not spend the
/// function's wall-clock budget.
///
/// Both of the lane's outcomes that could count are already ruled out before
/// dispatch:
///
/// * **Proved.** Under `require_proof_artifacts`, a proof on a native-bundle
///   route is accepted only through [`native_trust_ir_artifact_match`], which
///   refuses every proof while the bundle index carries a validation error
///   (for example a canonical bundle larger than the inline transport limit,
///   `MAX_EVIDENCE_ARTIFACT_MATERIALIZATION_BYTES`). The index is built from
///   the same bundle before dispatch, so the refusal is already known.
/// * **Failed.** trust-bmc demotes every trust-mc refutation to Unknown unless
///   the row carries the compiler's positive `exact` encoding-fidelity
///   attestation, and the compiler attests only postconditions. Those rows keep
///   dispatching, so no refutation that could count is lost.
///
/// Measured (fix10, 2026-10-13): two `tla-cert` functions spent 125–150 s each
/// in 24 native PDR solves whose 9 proofs were all refused here for a >16 MiB
/// bundle; under the 120 s per-function budget that cost 34 timeout rows and
/// starved the cheap lanes that decide them. See KNOWN_HAZARDS.
///
/// The skipped row is `Unsupported` with this reason: never `Proved`, and
/// later compiler lanes still see it as unproved.
pub(super) fn native_trust_mc_solve_cannot_publish(
    policy: FullVerificationPolicy,
    route: ObligationRoute,
    primary: &EngineManifest,
    obligation: &TrustObligation,
    native_trust_ir: Option<&NativeTrustIrEvidenceIndex>,
) -> Option<String> {
    if !policy.require_proof_artifacts
        || route.primary != PrimaryEngine::TrustMc
        || !is_native_trust_mc_trust_bmc_engine(primary)
        || matches!(obligation.kind, trust_verifier_api::ObligationKind::Postcondition)
        || obligation.metadata.iter().any(|entry| {
            entry.key == TRUST_MC_TYPED_CHC_ENCODING_FIDELITY_METADATA_KEY
                && entry.value == TRUST_MC_TYPED_CHC_ENCODING_FIDELITY_EXACT
        })
    {
        return None;
    }
    let refusal = native_trust_ir?.proof_authority_refusal(route)?;
    Some(format!(
        "native trust-mc solve not dispatched: no outcome could be published ({refusal}; the row carries no exact encoding-fidelity attestation, so a refutation would be demoted to Unknown)"
    ))
}

#[cfg(test)]
mod fresh_receipt_tests {
    use std::sync::Arc;
    use std::sync::atomic::{AtomicUsize, Ordering};
    use std::time::Duration;

    use super::*;

    fn evidence(status: EvidenceStatus) -> ObligationEvidence {
        ObligationEvidence {
            evidence_id: "fresh-row-evidence".to_string(),
            obligation_id: "fresh-row".to_string(),
            engine: EngineManifest::new("trust-mc", API_VERSION, EngineKind::Reachability),
            status,
            decline: None,
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
                        "full verification requires native trust-vc, trust-mc, and TY engines; missing: {}",
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
            None,
        )
        .into_result()
    }
}
