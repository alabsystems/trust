//! Per-suite native TrustIr bundle evidence helpers (trust-wp / trust_vc / trust-mc).

use std::{
    collections::{BTreeMap, BTreeSet},
    sync::Arc,
    time::Instant,
};

#[cfg(feature = "trust-build")]
use trust_bmc::TrustMcVerifierApiAdapter;
use trust_ir_bridge::{
    NativeVerificationBundle, NativeVerificationRequest, SourceGenerationAuthority,
};
#[cfg(feature = "trust-vc-native")]
use trust_vc_bridge::TrustVcVerificationEngine;
#[cfg(feature = "trust-vc-native")]
use trust_verifier_api::VerificationEngine;
use trust_verifier_api::{
    EngineManifest, EvidenceStatus, MetadataEntry, ObligationEvidence, TrustContractBundle,
    TrustObligation, VerificationRunResult, VerifierExecutionContext,
};
#[cfg(feature = "trust-build")]
use trust_wp::TrustWpVerificationEngine;

use super::super::routing::PrimaryEngine;
#[cfg(feature = "trust-build")]
use super::index::NativeTrustIrObligationIdentity;

#[derive(Debug)]
struct LiveVerificationPublishedRun {
    source_run: VerificationRunResult,
    bundle: Arc<TrustContractBundle>,
    bundle_is_valid: bool,
    exact_evidence_positions: BTreeMap<String, usize>,
    source_run_is_valid: bool,
    context: VerifierExecutionContext,
}

/// Opaque identity for one live full-verifier dispatch.
///
/// The seal is neither cloneable nor serializable. Each affine proof receipt
/// retained by the same live call shares its private identity, so receipts
/// cannot be paired with the public result and seal from a second dispatch,
/// even when both public runs are byte-for-byte identical.
#[derive(Debug)]
pub(crate) struct LiveVerificationDispatchSeal {
    published_run: Arc<LiveVerificationPublishedRun>,
}

impl LiveVerificationDispatchSeal {
    pub(crate) fn mint(
        source_run: &VerificationRunResult,
        bundle: &TrustContractBundle,
        context: &VerifierExecutionContext,
    ) -> Self {
        let mut exact_evidence_positions = BTreeMap::new();
        let mut duplicate_ids = BTreeSet::new();
        for (position, evidence) in source_run.evidence.iter().enumerate() {
            let id = evidence.obligation_id.as_str();
            if duplicate_ids.contains(id) {
                continue;
            }
            if exact_evidence_positions.insert(id.to_string(), position).is_some() {
                exact_evidence_positions.remove(id);
                duplicate_ids.insert(id.to_string());
            }
        }
        for skipped in &source_run.skipped {
            exact_evidence_positions.remove(skipped.obligation_id.as_str());
        }
        Self {
            published_run: Arc::new(LiveVerificationPublishedRun {
                source_run: source_run.clone(),
                bundle: Arc::new(bundle.clone()),
                bundle_is_valid: bundle.validate().is_ok(),
                exact_evidence_positions,
                source_run_is_valid: source_run.validate_derived_state().is_ok(),
                context: context.clone(),
            }),
        }
    }

    fn published_run(&self) -> &Arc<LiveVerificationPublishedRun> {
        &self.published_run
    }

    pub(crate) fn source_run(&self) -> &VerificationRunResult {
        &self.published_run.source_run
    }

    pub(crate) fn is_live(&self) -> bool {
        !self.published_run.context.is_cancelled() && !self.published_run.context.budget_exceeded()
    }

    pub(crate) fn deadline(&self) -> Option<Instant> {
        self.published_run.context.deadline()
    }

    pub(crate) fn bundle(&self) -> &TrustContractBundle {
        &self.published_run.bundle
    }

    pub(crate) fn matches_bundle(&self, bundle: &TrustContractBundle) -> bool {
        self.published_run.bundle_is_valid && self.published_run.bundle.as_ref() == bundle
    }

    pub(crate) fn exact_evidence(&self, obligation_id: &str) -> Option<&ObligationEvidence> {
        if !self.published_run.source_run_is_valid {
            return None;
        }
        self.published_run
            .exact_evidence_positions
            .get(obligation_id)
            .and_then(|position| self.published_run.source_run.evidence.get(*position))
    }

    pub(crate) fn fork(&self) -> Self {
        Self { published_run: Arc::clone(&self.published_run) }
    }
}

pub(crate) struct NativeTrustIrBundleEvidence {
    pub(crate) evidence: Vec<ObligationEvidence>,
    // Private post-solve receipts for the dedicated direct TrustVC lane. Only
    // the genuine in-process adapter path below can populate this map after a
    // live release-admitted solve; public evidence cannot reconstruct one.
    pub(crate) direct_trust_vc_receipts: BTreeMap<String, DirectTrustVcProofReceipt>,
    // Affine post-solve authority for compiler-authenticated E4/E5 rows.  The
    // public evidence vector is deliberately insufficient to recreate these
    // values; they are moved through the full-verifier and exposed only by its
    // explicit live-dispatch API.
    pub(crate) fresh_exact_direct_chc_pdr_receipts: BTreeMap<String, FreshExactDirectChcPdrReceipt>,
}

impl NativeTrustIrBundleEvidence {
    fn ordinary(evidence: Vec<ObligationEvidence>) -> Self {
        Self {
            evidence,
            direct_trust_vc_receipts: BTreeMap::new(),
            fresh_exact_direct_chc_pdr_receipts: BTreeMap::new(),
        }
    }
}

/// Opaque live proof receipt for one dedicated direct TrustVC MIR-memory solve.
///
/// This type is neither cloneable nor serializable. It binds the genuine
/// adapter's live release-admitted result to the exact bundle, obligation,
/// structured carrier, dispatch deadline, child evidence row, and final
/// composite evidence row observed during that solve. A configured engine can
/// copy every public field but cannot mint this value.
#[derive(Debug)]
pub struct DirectTrustVcProofReceipt {
    bundle: Arc<TrustContractBundle>,
    obligation: TrustObligation,
    public_semantic_digest: String,
    proof_unit_payload_digest: String,
    typed_predicate_digest: String,
    dispatch_deadline: Option<Instant>,
    solved_evidence: ObligationEvidence,
    accepted_evidence: Option<ObligationEvidence>,
    published_run: Option<Arc<LiveVerificationPublishedRun>>,
}

impl DirectTrustVcProofReceipt {
    #[cfg(feature = "trust-vc-native")]
    fn mint(
        bundle: Arc<TrustContractBundle>,
        obligation: &TrustObligation,
        evidence: &ObligationEvidence,
        dispatch_deadline: Option<Instant>,
    ) -> Option<Self> {
        if !has_exact_deferred_direct_trust_vc_transport(obligation)
            || evidence.status != EvidenceStatus::Proved
            || evidence.obligation_id != obligation.obligation_id
            || !trust_vc_bridge::trust_vc_direct_mir_memory_evidence_has_certificate_shape(evidence)
        {
            return None;
        }
        let binding =
            trust_vc_bridge::trust_vc_direct_mir_memory_carrier_binding(&bundle, obligation)
                .ok()??;
        Some(Self {
            bundle,
            obligation: obligation.clone(),
            public_semantic_digest: binding.public_semantic_digest().to_string(),
            proof_unit_payload_digest: binding.proof_unit_payload_digest().to_string(),
            typed_predicate_digest: binding.typed_predicate_digest().to_string(),
            dispatch_deadline,
            solved_evidence: evidence.clone(),
            accepted_evidence: None,
            published_run: None,
        })
    }

    /// Exact public obligation identity sealed into this live receipt.
    #[must_use]
    pub fn public_obligation_id(&self) -> &str {
        &self.obligation.obligation_id
    }

    /// Absolute deadline frozen into the direct TrustVC dispatch that minted
    /// this affine receipt.
    #[must_use]
    pub fn dispatch_deadline(&self) -> Option<Instant> {
        self.dispatch_deadline
    }

    /// Revalidate the genuine direct solve and the exact composite evidence
    /// row accepted at the router's final publication boundary.
    ///
    /// A different bundle, obligation, carrier digest, evidence field, or
    /// proof strength fails closed. Public result bytes alone cannot construct
    /// this receipt or populate its private accepted-evidence binding.
    pub(crate) fn authorizes_accepted_evidence(
        &self,
        obligation: &TrustObligation,
        evidence: &ObligationEvidence,
        dispatch_seal: &LiveVerificationDispatchSeal,
    ) -> Result<trust_verifier_api::ProofStrength, String> {
        if !dispatch_seal.is_live() || self.dispatch_deadline != dispatch_seal.deadline() {
            return Err(
                "direct TrustVC receipt is late, cancelled, or deadline-mismatched".to_string()
            );
        }
        if !self.matches(dispatch_seal.bundle(), obligation, &self.solved_evidence) {
            return Err(
                "direct TrustVC receipt no longer matches its exact live solve carrier".to_string()
            );
        }
        if evidence.obligation_id != obligation.obligation_id
            || !self.matches_accepted_evidence(evidence)
        {
            return Err("direct TrustVC receipt does not match the router-accepted evidence row"
                .to_string());
        }
        if !published_run_binding_matches(self.published_run.as_ref(), dispatch_seal, evidence) {
            return Err("direct TrustVC receipt does not match its exact live published dispatch"
                .to_string());
        }
        #[cfg(feature = "trust-vc-native")]
        if !trust_vc_bridge::trust_vc_direct_mir_memory_evidence_has_certificate_shape(evidence) {
            return Err(
                "direct TrustVC accepted evidence lost its exact certificate shape".to_string()
            );
        }
        let Some(strength) = self.solved_evidence.proof_strength.clone() else {
            return Err("direct TrustVC live solve carried no proof strength".to_string());
        };
        if evidence.proof_strength.as_ref() != Some(&strength) {
            return Err(
                "direct TrustVC receipt proof strength differs from accepted evidence".to_string()
            );
        }
        Ok(strength)
    }

    pub(crate) fn matches(
        &self,
        bundle: &TrustContractBundle,
        obligation: &TrustObligation,
        evidence: &ObligationEvidence,
    ) -> bool {
        if self.bundle.bundle_id != bundle.bundle_id
            || self.bundle.subject != bundle.subject
            || self.obligation != *obligation
            || self.solved_evidence != *evidence
            || !has_exact_deferred_direct_trust_vc_transport(obligation)
        {
            return false;
        }
        #[cfg(feature = "trust-vc-native")]
        {
            trust_vc_bridge::trust_vc_direct_mir_memory_evidence_has_certificate_shape(evidence)
                && !self.public_semantic_digest.is_empty()
                && !self.proof_unit_payload_digest.is_empty()
                && !self.typed_predicate_digest.is_empty()
        }
        #[cfg(not(feature = "trust-vc-native"))]
        {
            let _ = (bundle, evidence);
            false
        }
    }

    pub(crate) fn exact_bundle_matches(&self, bundle: &TrustContractBundle) -> bool {
        bundle.validate().is_ok() && self.bundle.as_ref() == bundle
    }

    pub(crate) fn shares_exact_bundle(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.bundle, &other.bundle)
    }

    pub(crate) fn bind_to_accepted_evidence(
        mut self,
        evidence: &ObligationEvidence,
    ) -> Option<Self> {
        if self.accepted_evidence.is_some()
            || evidence.status != EvidenceStatus::Proved
            || evidence.proof_strength.as_ref() != self.solved_evidence.proof_strength.as_ref()
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
        dispatch_seal: &LiveVerificationDispatchSeal,
    ) -> Option<Self> {
        if self.published_run.is_some()
            || !published_run_contains_exact_evidence(
                &dispatch_seal.published_run,
                self.accepted_evidence.as_ref()?,
            )
        {
            return None;
        }
        self.published_run = Some(Arc::clone(dispatch_seal.published_run()));
        Some(self)
    }
}

fn has_exact_deferred_direct_trust_vc_transport(obligation: &TrustObligation) -> bool {
    #[cfg(feature = "trust-vc-native")]
    {
        let unique = |key: &str| {
            let mut matching = obligation.metadata.iter().filter(|entry| entry.key == key);
            let value = matching.next()?.value.as_str();
            matching.next().is_none().then_some(value)
        };
        if obligation.metadata.iter().any(|entry| {
            entry.key.starts_with("trust.trust_ir.native.")
                && entry.key
                    != trust_vc_bridge::TRUST_VC_DIRECT_MIR_MEMORY_TRANSPORT_STATUS_METADATA_KEY
                && entry.key
                    != trust_vc_bridge::TRUST_VC_DIRECT_MIR_MEMORY_TRANSPORT_REASON_METADATA_KEY
        }) {
            return false;
        }
        unique(trust_vc_bridge::TRUST_VC_DIRECT_MIR_MEMORY_TRANSPORT_STATUS_METADATA_KEY)
            == Some(trust_vc_bridge::TRUST_VC_DIRECT_MIR_MEMORY_TRANSPORT_STATUS_DEFERRED)
            && unique(trust_vc_bridge::TRUST_VC_DIRECT_MIR_MEMORY_TRANSPORT_REASON_METADATA_KEY)
                == Some(trust_vc_bridge::TRUST_VC_DIRECT_MIR_MEMORY_DEFERRED_REASON)
    }
    #[cfg(not(feature = "trust-vc-native"))]
    {
        let _ = obligation;
        false
    }
}

/// Opaque live proof receipt for one exact compiler-authenticated CHC/PDR row.
///
/// The wrapper intentionally implements neither `Clone` nor serialization.
/// Callers can only revalidate the affine receipt against the exact current
/// bundle and obligation; public evidence, hashes, and diagnostic text cannot
/// construct one.
#[derive(Debug)]
pub struct FreshExactDirectChcPdrReceipt {
    #[cfg(feature = "trust-build")]
    inner: trust_bmc::FreshExactDirectChcPdrReceipt,
    /// Exact composite row accepted at the router publication boundary. A
    /// private clone is intentional: IDs and proof strength alone do not bind
    /// artifacts, diagnostics, publication metadata, or engine identity, and
    /// those bytes must not be replaceable after the native solve.
    accepted_evidence: Option<ObligationEvidence>,
    /// Shared private identity for the exact source run which carried
    /// `accepted_evidence`. One `Arc` per dispatch avoids cloning the complete
    /// run into every receipt while still rejecting byte-identical A/B swaps.
    published_run: Option<Arc<LiveVerificationPublishedRun>>,
    #[cfg(not(feature = "trust-build"))]
    #[allow(dead_code)]
    unavailable: std::convert::Infallible,
}

impl FreshExactDirectChcPdrReceipt {
    #[cfg(feature = "trust-build")]
    fn from_native(inner: trust_bmc::FreshExactDirectChcPdrReceipt) -> Self {
        Self { inner, accepted_evidence: None, published_run: None }
    }

    /// Exact public obligation identity sealed into this live receipt.
    #[cfg(feature = "trust-build")]
    #[must_use]
    pub fn public_obligation_id(&self) -> &str {
        self.inner.public_obligation_id()
    }

    /// Rebind the private live solve to the exact current compiler request.
    #[cfg(feature = "trust-build")]
    pub(crate) fn still_authorizes_under_exact_bundle_seal(
        &self,
        obligation: &TrustObligation,
    ) -> Result<trust_verifier_api::ProofStrength, String> {
        let bundle_seal = self.inner.bundle_seal();
        self.inner.still_authorizes_under_exact_bundle_seal(&bundle_seal, obligation)
    }

    #[cfg(feature = "trust-build")]
    pub(crate) fn exact_bundle_matches(&self, bundle: &TrustContractBundle) -> bool {
        self.inner.bundle_seal().matches_bundle(bundle)
    }

    #[cfg(feature = "trust-build")]
    pub(crate) fn shares_exact_bundle(&self, other: &Self) -> bool {
        self.inner.shares_bundle_seal(&other.inner.bundle_seal())
    }

    /// Revalidate both the affine native solve and the exact composite evidence
    /// row accepted by the router at its final publication boundary.
    ///
    /// This is the compiler-facing authority gate after [`crate::FullVerificationRunWithFreshReceipts::into_parts`]
    /// separates the run from its sidecars. A receipt paired with any different
    /// row field—including engine identity, artifacts, diagnostics, publication
    /// metadata, evidence identity, or proof strength—fails closed before
    /// native replay.
    #[cfg(feature = "trust-build")]
    pub(crate) fn authorizes_accepted_evidence(
        &self,
        obligation: &TrustObligation,
        evidence: &ObligationEvidence,
        dispatch_seal: &LiveVerificationDispatchSeal,
    ) -> Result<trust_verifier_api::ProofStrength, String> {
        if !dispatch_seal.is_live() || self.dispatch_deadline() != dispatch_seal.deadline() {
            return Err(
                "fresh exact-direct receipt is late, cancelled, or deadline-mismatched".to_string()
            );
        }
        if evidence.obligation_id != obligation.obligation_id
            || !self.matches_accepted_evidence(evidence)
        {
            return Err(
                "fresh exact-direct receipt does not match the router-accepted evidence row"
                    .to_string(),
            );
        }
        if !published_run_binding_matches(self.published_run.as_ref(), dispatch_seal, evidence) {
            return Err(
                "fresh exact-direct receipt does not match its exact live published dispatch"
                    .to_string(),
            );
        }
        let strength = self.still_authorizes_under_exact_bundle_seal(obligation)?;
        if evidence.proof_strength.as_ref() != Some(&strength) {
            return Err("fresh exact-direct receipt proof strength differs from accepted evidence"
                .to_string());
        }
        Ok(strength)
    }

    #[cfg(feature = "trust-build")]
    /// Absolute deadline frozen into the native dispatch that produced this
    /// affine receipt. Compiler consumers compare it exactly with their
    /// still-live execution context before minting any private authority.
    #[must_use]
    pub fn dispatch_deadline(&self) -> Option<Instant> {
        self.inner.dispatch_deadline()
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
        dispatch_seal: &LiveVerificationDispatchSeal,
    ) -> Option<Self> {
        if self.published_run.is_some()
            || !published_run_contains_exact_evidence(
                &dispatch_seal.published_run,
                self.accepted_evidence.as_ref()?,
            )
        {
            return None;
        }
        self.published_run = Some(Arc::clone(dispatch_seal.published_run()));
        Some(self)
    }
}

fn accepted_evidence_binding_matches(
    accepted_evidence: Option<&ObligationEvidence>,
    evidence: &ObligationEvidence,
) -> bool {
    evidence.status == EvidenceStatus::Proved
        && evidence.proof_strength.is_some()
        && accepted_evidence == Some(evidence)
}

fn published_run_binding_matches(
    published_run: Option<&Arc<LiveVerificationPublishedRun>>,
    dispatch_seal: &LiveVerificationDispatchSeal,
    evidence: &ObligationEvidence,
) -> bool {
    published_run.is_some_and(|published_run| {
        Arc::ptr_eq(published_run, dispatch_seal.published_run())
            && published_run_contains_exact_evidence(published_run, evidence)
    })
}

fn published_run_contains_exact_evidence(
    published_run: &LiveVerificationPublishedRun,
    evidence: &ObligationEvidence,
) -> bool {
    published_run.source_run_is_valid
        && published_run
            .exact_evidence_positions
            .get(evidence.obligation_id.as_str())
            .and_then(|position| published_run.source_run.evidence.get(*position))
            == Some(evidence)
}

pub(crate) fn native_trust_ir_bundle_evidence(
    manifest: &EngineManifest,
    bundle: &TrustContractBundle,
    obligations: &[TrustObligation],
    native_bundle: Option<&NativeVerificationBundle>,
    source_generation_authority: Option<&SourceGenerationAuthority>,
    deadline: Option<Instant>,
) -> Option<NativeTrustIrBundleEvidence> {
    if is_native_trust_wp_trust_ir_engine(manifest) {
        return trust_wp_native_trust_ir_bundle_evidence(
            bundle,
            obligations,
            native_bundle,
            deadline,
        )
        .map(NativeTrustIrBundleEvidence::ordinary);
    }
    if is_native_trust_vc_trust_ir_engine(manifest) {
        return trust_vc_native_trust_ir_bundle_evidence(
            bundle,
            obligations,
            native_bundle,
            deadline,
        );
    }
    if is_native_trust_mc_trust_bmc_engine(manifest) {
        return trust_mc_native_trust_ir_bundle_evidence(
            bundle,
            obligations,
            native_bundle,
            source_generation_authority,
            deadline,
        );
    }
    None
}

/// Trust: true once the optional per-function wall-clock deadline has
/// elapsed. A `None` deadline (budget disabled) never trips.
#[cfg(feature = "trust-build")]
fn native_trust_ir_budget_exceeded(deadline: Option<Instant>) -> bool {
    deadline.is_some_and(|deadline| Instant::now() >= deadline)
}

pub(crate) fn native_trust_ir_bundle_evidence_is_incomplete(
    obligations: &[TrustObligation],
    evidence: Option<&[ObligationEvidence]>,
) -> bool {
    let Some(evidence) = evidence else {
        return true;
    };
    obligations.iter().any(|obligation| {
        !evidence.iter().any(|item| {
            item.obligation_id == obligation.obligation_id && item.status == EvidenceStatus::Proved
        })
    })
}

pub(crate) fn is_native_trust_wp_trust_ir_engine(manifest: &EngineManifest) -> bool {
    manifest.name == PrimaryEngine::TrustWp.name()
        && manifest.repository.as_deref() == Some("trust-wp")
}

#[cfg(feature = "trust-build")]
fn trust_wp_native_trust_ir_bundle_evidence(
    bundle: &TrustContractBundle,
    obligations: &[TrustObligation],
    native_bundle: Option<&NativeVerificationBundle>,
    deadline: Option<Instant>,
) -> Option<Vec<ObligationEvidence>> {
    let native_bundle = native_bundle?;
    let adapter = TrustWpVerificationEngine::new();
    if let Err(errors) = native_bundle.validate() {
        let reason = format!(
            "typed TrustIr NativeVerificationBundle validation failed: {}",
            errors.into_iter().map(|error| format!("{error:?}")).collect::<Vec<_>>().join("; ")
        );
        return Some(
            obligations
                .iter()
                .map(|obligation| {
                    adapter.native_trust_ir_bundle_unsupported_evidence(
                        bundle,
                        obligation,
                        reason.clone(),
                    )
                })
                .collect(),
        );
    }

    Some(
        obligations
            .iter()
            .map(|obligation| {
                // Trust: once the per-function wall-clock budget is spent,
                // stop solving and degrade the remaining trust-wp obligations to
                // Unsupported (sound: never Proved) instead of running unbounded.
                if native_trust_ir_budget_exceeded(deadline) {
                    return adapter.native_trust_ir_bundle_unsupported_evidence(
                        bundle,
                        obligation,
                        "per-function wall-clock budget (-Ztrust-verify-function-budget-ms) exceeded before trust-wp obligation was solved; degraded to Unsupported (sound: never Proved)".to_string(),
                    );
                }
                match trust_wp_native_trust_ir_request_for_obligation(native_bundle, obligation) {
                    Ok((request, proof_obligation_id)) => adapter
                        .verify_obligation_with_native_trust_ir_request(
                            bundle,
                            obligation,
                            native_bundle,
                            request,
                            proof_obligation_id,
                        ),
                    Err(reason) => {
                        adapter.native_trust_ir_bundle_unsupported_evidence(bundle, obligation, reason)
                    }
                }
            })
            .collect(),
    )
}

#[cfg(not(feature = "trust-build"))]
fn trust_wp_native_trust_ir_bundle_evidence(
    _bundle: &TrustContractBundle,
    _obligations: &[TrustObligation],
    _native_bundle: Option<&NativeVerificationBundle>,
    _deadline: Option<Instant>,
) -> Option<Vec<ObligationEvidence>> {
    None
}

#[cfg(feature = "trust-build")]
fn trust_wp_native_trust_ir_request_for_obligation<'a>(
    native_bundle: &'a NativeVerificationBundle,
    obligation: &TrustObligation,
) -> Result<(&'a trust_ir::TrustWpNativeRequest, trust_ir::ProofId), String> {
    let identity =
        NativeTrustIrObligationIdentity::from_obligation(obligation, PrimaryEngine::TrustWp)?;
    let proof_obligation_id = trust_ir::ProofId::new(identity.proof_obligation_id);
    let request = native_bundle
        .requests
        .iter()
        .filter_map(|request| match request {
            NativeVerificationRequest::TrustWp(request) => Some(request),
            _ => None,
        })
        .find(|request| {
            identity.request_id.is_none_or(|request_id| request.id.index() == request_id)
                && request.obligations.contains(&proof_obligation_id)
        })
        .ok_or_else(|| {
            format!(
                "missing matching trust_wp native TrustIr request for request_id={} proof_obligation_id={}",
                identity
                    .request_id
                    .map_or_else(|| "any".to_string(), |request_id| request_id.to_string()),
                identity.proof_obligation_id
            )
        })?;

    Ok((request, proof_obligation_id))
}

pub(crate) fn is_native_trust_vc_trust_ir_engine(manifest: &EngineManifest) -> bool {
    manifest.name == PrimaryEngine::TrustVc.name()
        && manifest.repository.as_deref() == Some("trust-vc-bridge")
}

#[cfg(feature = "trust-vc-native")]
fn trust_vc_native_trust_ir_bundle_evidence(
    bundle: &TrustContractBundle,
    obligations: &[TrustObligation],
    native_bundle: Option<&NativeVerificationBundle>,
    deadline: Option<Instant>,
) -> Option<NativeTrustIrBundleEvidence> {
    let adapter = TrustVcVerificationEngine::new();

    // A globally invalid native bundle cannot authorize a per-obligation
    // fallback. Preserve the native adapter's fail-closed rejection for the
    // entire batch.
    if let Some(native_bundle) = native_bundle
        && native_bundle.validate().is_err()
    {
        return Some(NativeTrustIrBundleEvidence::ordinary(
            adapter.evidence_from_native_trust_ir_bundle_with_deadline(
                bundle,
                obligations,
                native_bundle,
                deadline,
            ),
        ));
    }

    let direct_candidates = obligations
        .iter()
        .map(|obligation| {
            trust_vc_bridge::trust_vc_native_trust_ir_kind_for_public_obligation(&obligation.kind)
                .is_some()
                && obligation.metadata.iter().any(|entry| {
                    entry.key == trust_vc_bridge::TRUST_VC_MIR_MEMORY_PROOF_UNIT_METADATA_KEY
                        || entry.key.starts_with("trust.trust_ir.native.")
                })
        })
        .collect::<Vec<_>>();
    let direct_eligible = obligations
        .iter()
        .map(|obligation| {
            has_exact_deferred_direct_trust_vc_transport(obligation)
                && native_bundle.is_none_or(|native_bundle| {
                    !trust_vc_request_binds_public_obligation(
                        native_bundle,
                        &obligation.obligation_id,
                    ) && native_bundle
                        .obligation_source_by_public_id(&obligation.obligation_id)
                        .is_none()
                })
                && trust_vc_bridge::trust_vc_has_exact_structured_direct_mir_memory_proof_unit(
                    bundle, obligation,
                )
        })
        .collect::<Vec<_>>();

    // A row that resembles the compiler-deferred transport is handled
    // authoritatively here even when malformed or stale. It must never fall
    // through to a configured lookalike primary.
    if native_bundle.is_none() && !direct_candidates.iter().any(|candidate| *candidate) {
        return None;
    }

    let mut evidence = Vec::with_capacity(obligations.len());
    let mut direct_trust_vc_receipts = BTreeMap::new();
    // Every receipt revalidates the complete bundle, but all rows in this
    // adapter call share one immutable carrier rather than cloning it once per
    // obligation.
    let receipt_bundle = Arc::new(bundle.clone());
    for ((obligation, direct_candidate), direct_eligible) in
        obligations.iter().zip(direct_candidates).zip(direct_eligible)
    {
        let has_matching_request = native_bundle.is_some_and(|native_bundle| {
            trust_vc_request_binds_public_obligation(native_bundle, &obligation.obligation_id)
        });
        let has_matching_source = native_bundle.is_some_and(|native_bundle| {
            native_bundle.obligation_source_by_public_id(&obligation.obligation_id).is_some()
        });

        if has_matching_request || has_matching_source {
            // A present native request is authoritative for routing. A stale or
            // rejected request must not be bypassed through the direct lane.
            if let Some(native_bundle) = native_bundle {
                evidence.extend(adapter.evidence_from_native_trust_ir_bundle_with_deadline(
                    bundle,
                    std::slice::from_ref(obligation),
                    native_bundle,
                    deadline,
                ));
            }
        } else if direct_eligible {
            let mut direct = adapter
                .evidence_from_release_admitted_direct_mir_memory_with_deadline(
                    bundle,
                    std::slice::from_ref(obligation),
                    deadline,
                );
            if let [proved] = direct.as_slice()
                && let Some(receipt) = DirectTrustVcProofReceipt::mint(
                    Arc::clone(&receipt_bundle),
                    obligation,
                    proved,
                    deadline,
                )
            {
                direct_trust_vc_receipts.insert(obligation.obligation_id.clone(), receipt);
            }
            evidence.append(&mut direct);
        } else if let Some(native_bundle) = native_bundle {
            evidence.extend(adapter.evidence_from_native_trust_ir_bundle_with_deadline(
                bundle,
                std::slice::from_ref(obligation),
                native_bundle,
                deadline,
            ));
        } else if direct_candidate {
            evidence.push(unsupported_direct_trust_vc_router_evidence(
                &adapter,
                obligation,
                "obligation did not carry an exact compiler-deferred direct TrustVC receipt input",
            ));
        } else {
            evidence.push(unsupported_direct_trust_vc_router_evidence(
                &adapter,
                obligation,
                "mixed direct TrustVC batch contained a non-candidate obligation",
            ));
        }
    }

    Some(NativeTrustIrBundleEvidence {
        evidence,
        direct_trust_vc_receipts,
        fresh_exact_direct_chc_pdr_receipts: BTreeMap::new(),
    })
}

#[cfg(feature = "trust-vc-native")]
fn unsupported_direct_trust_vc_router_evidence(
    adapter: &TrustVcVerificationEngine,
    obligation: &TrustObligation,
    reason: &str,
) -> ObligationEvidence {
    ObligationEvidence {
        evidence_id: format!("trust-vc:direct-router-rejected:{}", obligation.obligation_id),
        obligation_id: obligation.obligation_id.clone(),
        engine: adapter.manifest().clone(),
        status: EvidenceStatus::Unsupported,
        decline: None,
        proof_strength: None,
        artifacts: Vec::new(),
        counterexample: None,
        publication: Default::default(),
        diagnostics: vec![reason.to_string()],
    }
}

#[cfg(feature = "trust-vc-native")]
fn trust_vc_request_binds_public_obligation(
    native_bundle: &NativeVerificationBundle,
    public_obligation_id: &str,
) -> bool {
    native_bundle.requests.iter().any(|request| {
        let NativeVerificationRequest::TrustVc(request) = request else {
            return false;
        };
        request.obligations.iter().any(|proof_id| {
            native_bundle
                .obligation_source(*proof_id)
                .is_some_and(|source| source.public_obligation_id == public_obligation_id)
        })
    })
}

#[cfg(not(feature = "trust-vc-native"))]
fn trust_vc_native_trust_ir_bundle_evidence(
    _bundle: &TrustContractBundle,
    _obligations: &[TrustObligation],
    _native_bundle: Option<&NativeVerificationBundle>,
    _deadline: Option<Instant>,
) -> Option<NativeTrustIrBundleEvidence> {
    None
}

pub(crate) fn is_native_trust_mc_trust_bmc_engine(manifest: &EngineManifest) -> bool {
    manifest.name == PrimaryEngine::TrustMc.name()
        && manifest.repository.as_deref() == Some("trust-bmc")
        && manifest.version.ends_with("+native-trust-ir-bundle")
}

pub(crate) fn is_native_trust_ir_engine(manifest: &EngineManifest) -> bool {
    is_native_trust_wp_trust_ir_engine(manifest)
        || is_native_trust_vc_trust_ir_engine(manifest)
        || is_native_trust_mc_trust_bmc_engine(manifest)
}

/// Build typed `trust.trust_wp.*` replay metadata for a trust_wp TrustIr native
/// request. The conversion is delegated to `trust-wp`, which in
/// `trust-build` uses trust-wp's native replay metadata helper API.
pub fn trust_wp_native_replay_metadata_entries_for_request(
    native_bundle: &NativeVerificationBundle,
    request: &NativeVerificationRequest,
    proof_obligation_id: trust_ir::ProofId,
) -> Result<Vec<MetadataEntry>, String> {
    #[cfg(feature = "trust-build")]
    {
        let NativeVerificationRequest::TrustWp(request) = request else {
            return Err(
                "cannot build trust_wp replay metadata from a non-trust-wp TrustIr request".into(),
            );
        };
        return trust_wp::trust_wp_native_replay_metadata_entries_from_trust_ir_bundle(
            native_bundle,
            request,
            proof_obligation_id,
        )
        .map_err(|error| error.to_string());
    }

    #[cfg(not(feature = "trust-build"))]
    {
        let _ = (native_bundle, request, proof_obligation_id);
        Err("trust-wp native replay metadata requires trust-router `trust-build`".to_string())
    }
}

#[cfg(feature = "trust-build")]
fn production_trust_mc_native_trust_ir_adapter() -> TrustMcVerifierApiAdapter {
    TrustMcVerifierApiAdapter::new(
        trust_bmc::TrustMcConfig::new()
            .with_proof_mode(trust_bmc::TrustMcProofMode::PdrIc3)
            .with_timeout(5_000),
    )
}

#[cfg(feature = "trust-build")]
fn trust_mc_native_trust_ir_bundle_evidence(
    bundle: &TrustContractBundle,
    obligations: &[TrustObligation],
    native_bundle: Option<&NativeVerificationBundle>,
    source_generation_authority: Option<&SourceGenerationAuthority>,
    deadline: Option<Instant>,
) -> Option<NativeTrustIrBundleEvidence> {
    let native_bundle = native_bundle?;
    // Cap each solve at the intended per-obligation SMT budget (5s), not the
    // loose 30s adapter default, so a grinding obligation bails to Unknown
    // promptly instead of starving the crate's remaining verification time.
    // SOUND: a shorter budget only yields an earlier Unknown, never a proof.
    //
    // Trust (proof-mode wiring — REGRESSION FIX): the native CHC/PDR bundle
    // consumer (`evidence_from_native_trust_ir_bundle_with_deadline_and_fresh_receipts`)
    // fail-closes at its FIRST gate ("configured proof mode {:?} is not CHC/PDR")
    // unless the adapter is configured for CHC or PDR/IC3. `TrustMcConfig::new()`
    // defaults `proof_mode` to `Bmc`, so WITHOUT the PdrIc3 pin (now carried by
    // `production_trust_mc_native_trust_ir_adapter`) the consumer returned
    // Unsupported for EVERY trust-mc obligation before the per-obligation solve
    // ever ran — silently starving the whole-CFG structural default-function CHC
    // and the whole-function panic-freedom transport of the CHC/PDR solver they
    // require. (The per-VC arithmetic obligations were separately rescued by the
    // compiler ay bridge, which is why only the structural obligations regressed
    // to Unknown.) Selecting PdrIc3 admits BOTH the acyclic direct-CHC-validity
    // lane and the cyclic PDR/IC3 lane. SOUND: this only ENABLES the CHC/PDR
    // solve to run; a Proved verdict still requires the solver to genuinely
    // discharge the typed CHC — an unsolved obligation stays Unknown/Unsupported
    // (never Proved).
    let adapter = production_trust_mc_native_trust_ir_adapter();
    if std::env::var("TRUST_NATIVE_DEBUG").is_ok() {
        eprintln!(
            "[NATIVE_TRUSTMC_ENGINE_SELECT] native trust-mc CHC/PDR bundle consumer entered with proof_mode=PdrIc3 (was Bmc-default: fail-closed before the structural solve) for {} obligation(s): {:?}",
            obligations.len(),
            obligations
                .iter()
                .map(|obligation| obligation.obligation_id.as_str())
                .collect::<Vec<_>>(),
        );
    }
    let outcome = match source_generation_authority {
        Some(source_generation_authority) => adapter
            .evidence_from_native_trust_ir_bundle_with_source_authority_and_deadline_and_fresh_receipts(
                bundle,
                obligations,
                native_bundle,
                source_generation_authority,
                deadline,
            ),
        None => adapter.evidence_from_native_trust_ir_bundle_with_deadline_and_fresh_receipts(
            bundle,
            obligations,
            native_bundle,
            deadline,
        ),
    };
    Some(NativeTrustIrBundleEvidence {
        evidence: outcome.evidence,
        direct_trust_vc_receipts: BTreeMap::new(),
        fresh_exact_direct_chc_pdr_receipts: outcome
            .fresh_exact_direct_receipts
            .into_iter()
            .filter_map(|(obligation_id, receipt)| {
                (receipt.public_obligation_id() == obligation_id)
                    .then(|| (obligation_id, FreshExactDirectChcPdrReceipt::from_native(receipt)))
            })
            .collect(),
    })
}

#[cfg(not(feature = "trust-build"))]
fn trust_mc_native_trust_ir_bundle_evidence(
    _bundle: &TrustContractBundle,
    _obligations: &[TrustObligation],
    _native_bundle: Option<&NativeVerificationBundle>,
    _source_generation_authority: Option<&SourceGenerationAuthority>,
    _deadline: Option<Instant>,
) -> Option<NativeTrustIrBundleEvidence> {
    None
}

#[cfg(test)]
mod fresh_receipt_binding_tests {
    use super::*;

    #[cfg(feature = "trust-build")]
    #[test]
    fn production_bundle_adapter_uses_receipt_capable_pdr_mode() {
        let adapter = production_trust_mc_native_trust_ir_adapter();

        assert_eq!(adapter.config().proof_mode, trust_bmc::TrustMcProofMode::PdrIc3);
        assert_eq!(adapter.config().timeout_ms, 5_000);
    }

    #[test]
    fn accepted_evidence_binding_rejects_any_row_mutation() {
        let strength = trust_verifier_api::ProofStrength {
            reasoning: trust_verifier_api::ReasoningKind::Pdr,
            assurance: trust_verifier_api::AssuranceLevel::SmtBacked,
        };
        let mut evidence = ObligationEvidence {
            evidence_id: "accepted-evidence".to_string(),
            obligation_id: "accepted-obligation".to_string(),
            engine: EngineManifest::new(
                "trust-full-verifier",
                trust_verifier_api::API_VERSION,
                trust_verifier_api::EngineKind::Composite,
            ),
            status: EvidenceStatus::Proved,
            decline: None,
            proof_strength: Some(strength.clone()),
            artifacts: vec![trust_verifier_api::EvidenceArtifact {
                kind: trust_verifier_api::EvidenceArtifactKind::SolverTranscript,
                uri: "artifact://accepted-transcript".to_string(),
                hash: trust_verifier_api::ArtifactHash {
                    algorithm: "sha256".to_string(),
                    value: "a".repeat(64),
                },
                materialization: None,
            }],
            counterexample: None,
            publication: Default::default(),
            diagnostics: Vec::new(),
        };
        let accepted = evidence.clone();
        assert!(accepted_evidence_binding_matches(Some(&accepted), &evidence));

        evidence.evidence_id = "substituted-evidence".to_string();
        assert!(!accepted_evidence_binding_matches(Some(&accepted), &evidence));
        evidence.evidence_id = "accepted-evidence".to_string();

        evidence.obligation_id = "substituted-obligation".to_string();
        assert!(!accepted_evidence_binding_matches(Some(&accepted), &evidence));
        evidence.obligation_id = "accepted-obligation".to_string();

        evidence.engine.name = "substituted-engine".to_string();
        assert!(!accepted_evidence_binding_matches(Some(&accepted), &evidence));
        evidence.engine = accepted.engine.clone();

        evidence.status = EvidenceStatus::Failed;
        assert!(!accepted_evidence_binding_matches(Some(&accepted), &evidence));
        evidence.status = EvidenceStatus::Proved;

        evidence.proof_strength = Some(trust_verifier_api::ProofStrength::deductive());
        assert!(!accepted_evidence_binding_matches(Some(&accepted), &evidence));
        evidence.proof_strength = Some(strength);

        evidence.artifacts[0].uri = "artifact://substituted-transcript".to_string();
        assert!(!accepted_evidence_binding_matches(Some(&accepted), &evidence));
        evidence.artifacts = accepted.artifacts.clone();

        evidence.diagnostics.push("mutated after native solve".to_string());
        assert!(!accepted_evidence_binding_matches(Some(&accepted), &evidence));
        evidence.diagnostics.clear();

        evidence.counterexample = Some(trust_verifier_api::Counterexample {
            format: "trust.counterexample.v1".to_string(),
            data: serde_json::json!({"mutated": true}),
        });
        assert!(!accepted_evidence_binding_matches(Some(&accepted), &evidence));
        evidence.counterexample = None;

        evidence.publication.evidence_bundle_hash = Some("mutated-publication".to_string());
        assert!(!accepted_evidence_binding_matches(Some(&accepted), &evidence));
    }
}
