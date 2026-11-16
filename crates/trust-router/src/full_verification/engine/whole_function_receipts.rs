//! Distinct whole-function sidecars at the live publication boundary.

use super::*;

impl LiveVerificationReceiptBatch {
    #[must_use]
    pub fn fresh_whole_function_chc_pdr_receipts(
        &self,
    ) -> &BTreeMap<String, FreshWholeFunctionChcPdrReceipt> {
        &self.fresh_whole_function_chc_pdr_receipts
    }

    /// Move each whole-function capability out exactly once.
    pub fn take_fresh_whole_function_chc_pdr_receipts(
        &mut self,
    ) -> BTreeMap<String, FreshWholeFunctionChcPdrReceipt> {
        std::mem::take(&mut self.fresh_whole_function_chc_pdr_receipts)
    }

    /// Split one receipt while preserving its original private dispatch seal.
    pub fn take_fresh_whole_function_chc_pdr_receipt_batch(&mut self, id: &str) -> Option<Self> {
        let dispatch_seal = self.dispatch_seal.as_ref()?.fork();
        let receipt = self.fresh_whole_function_chc_pdr_receipts.remove(id)?;
        Some(Self {
            checked_native_wp_proofs: BTreeMap::new(),
            dispatch_seal: Some(dispatch_seal),
            direct_trust_vc_receipts: BTreeMap::new(),
            fresh_exact_direct_chc_pdr_receipts: BTreeMap::new(),
            fresh_whole_function_chc_pdr_receipts: std::iter::once((id.to_owned(), receipt))
                .collect(),
        })
    }

    /// Revalidate exact module contents AND a current live source authority.
    /// A separately source-authorized equal-content bundle may reauthenticate
    /// those same contents; decoded/cloned content with the old source token
    /// cannot. The receipt still belongs to its original private dispatch,
    /// even if another dispatch publishes byte-identical public evidence.
    #[cfg(feature = "trust-build")]
    pub fn authorizes_fresh_whole_function_chc_pdr_receipt(
        &self,
        receipt: &FreshWholeFunctionChcPdrReceipt,
        native: &NativeVerificationBundle,
        source: &SourceGenerationAuthority,
        obligation: &TrustObligation,
        evidence: &ObligationEvidence,
    ) -> Result<ProofStrength, String> {
        let seal = self
            .dispatch_seal
            .as_ref()
            .ok_or("whole-function receipt batch has no dispatch authority")?;
        if !seal.is_live() || receipt.dispatch_deadline() != seal.deadline() {
            return Err("whole-function dispatch is late, cancelled, or deadline-mismatched".into());
        }
        if !source.authorizes_bundle(native) || !receipt.exact_bundles_match(seal.bundle(), native)
        {
            return Err("whole-function receipt does not match the exact live compiler source/native bundle".into());
        }
        let strength = receipt.authorizes_accepted_evidence(obligation, evidence, seal)?;
        if !seal.is_live() || receipt.dispatch_deadline() != seal.deadline() {
            return Err("whole-function dispatch expired during replay".into());
        }
        Ok(strength)
    }
}

impl FullVerificationRunWithFreshReceipts {
    #[must_use]
    pub fn fresh_whole_function_chc_pdr_receipts(
        &self,
    ) -> &BTreeMap<String, FreshWholeFunctionChcPdrReceipt> {
        &self.live_receipts.fresh_whole_function_chc_pdr_receipts
    }
}

pub(super) fn whole_receipt_bundle_is_coherent(
    receipts: &BTreeMap<String, FreshWholeFunctionChcPdrReceipt>,
    bundle: &TrustContractBundle,
    native: Option<&NativeVerificationBundle>,
    source: Option<&SourceGenerationAuthority>,
) -> bool {
    #[cfg(feature = "trust-build")]
    {
        let Some(first) = receipts.values().next() else { return true };
        let (Some(native), Some(source)) = (native, source) else { return false };
        source.authorizes_bundle(native)
            && first.exact_bundles_match(bundle, native)
            && receipts.values().all(|receipt| receipt.shares_exact_bundles(first))
    }
    #[cfg(not(feature = "trust-build"))]
    {
        let _ = (bundle, native, source);
        receipts.is_empty()
    }
}

pub(super) fn whole_receipt_authorizes_final_evidence(
    receipt: &FreshWholeFunctionChcPdrReceipt,
    obligation: &TrustObligation,
    child: Option<&ObligationEvidence>,
    finished: &FinishedPrimaryEvidence,
    context: Option<&VerifierExecutionContext>,
) -> bool {
    let Some(child) = child else { return false };
    if !final_evidence_matches_accepted_proved_row(&obligation.obligation_id, child, finished) {
        return false;
    }
    #[cfg(feature = "trust-build")]
    {
        receipt.public_obligation_id() == obligation.obligation_id
            && live_receipt_context_is_live(receipt.dispatch_deadline(), context)
            && receipt
                .still_authorizes_sealed_obligation(obligation)
                .is_ok_and(|strength| Some(strength) == finished.evidence.proof_strength)
            && live_receipt_context_is_live(receipt.dispatch_deadline(), context)
    }
    #[cfg(not(feature = "trust-build"))]
    {
        let _ = (receipt, context);
        false
    }
}

pub(super) fn finalize_whole_receipts_at_publication_boundary(
    receipts: BTreeMap<String, FreshWholeFunctionChcPdrReceipt>,
    result: &VerificationRunResult,
    bundle: &TrustContractBundle,
    obligations: &[TrustObligation],
    native: Option<&NativeVerificationBundle>,
    source: Option<&SourceGenerationAuthority>,
    context: &VerifierExecutionContext,
    seal: &LiveVerificationDispatchSeal,
) -> BTreeMap<String, FreshWholeFunctionChcPdrReceipt> {
    if !publication_boundary_is_live(result, bundle, obligations, context)
        || !whole_receipt_bundle_is_coherent(&receipts, bundle, native, source)
    {
        return BTreeMap::new();
    }
    let obligations_by_id = unique_receipt_obligations(obligations);
    receipts
        .into_iter()
        .filter_map(|(id, receipt)| {
            let obligation = obligations_by_id.get(id.as_str()).copied()?;
            let final_row = seal.exact_evidence(&id)?;
            if final_row.status != EvidenceStatus::Proved
                || !receipt.matches_accepted_evidence(final_row)
            {
                return None;
            }
            #[cfg(feature = "trust-build")]
            {
                let receipt = receipt.bind_to_published_run(seal)?;
                if receipt.public_obligation_id() != id
                    || !live_receipt_context_is_live(receipt.dispatch_deadline(), Some(context))
                    || !receipt
                        .authorizes_accepted_evidence(obligation, final_row, seal)
                        .is_ok_and(|strength| Some(strength) == final_row.proof_strength)
                    || !live_receipt_context_is_live(receipt.dispatch_deadline(), Some(context))
                {
                    return None;
                }
                Some((id, receipt))
            }
            #[cfg(not(feature = "trust-build"))]
            {
                let _ = (obligation, receipt);
                None
            }
        })
        .collect()
}
