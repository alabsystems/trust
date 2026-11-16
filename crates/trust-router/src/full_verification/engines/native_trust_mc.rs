//! Built-in trust_mc adapter selected when a typed TrustIr native bundle is available.

use trust_bmc::TrustMcVerifierApiAdapter;
use trust_verifier_api::{
    EngineManifest, ObligationEvidence, SupportLevel, TrustObligation,
    ValidatedVerificationRequest, VerificationEngine, VerificationRunResult,
    VerifierExecutionContext,
};

/// Built-in trust_mc adapter selected by the full verifier when a typed TrustIr
/// native bundle is available.
pub struct NativeTrustMcTrustIrEngine {
    adapter: TrustMcVerifierApiAdapter,
    manifest: EngineManifest,
}

/// The `-Z trust-verify-timeout-ms` default, mirrored for callers that have no
/// `Session` to read it from (tests, `Default`). The option layer in
/// `rustc_session::options` owns the authoritative value; this constant exists
/// only so a session-less constructor lands on the same budget the compiler
/// would have chosen by default. Keep the two in sync.
// Trust: 2026-09-21 — 5_000 -> 20_000, mirroring the `-Z trust-verify-timeout-ms`
// default raised in `rustc_session::options` in the same commit. The native lane
// derives its wall-clock watchdog as `timeout + 2s`, so the old value gave a 7s
// ceiling against a MEASURED 3.3s idle PDR cost for a 64-bit `decreases` ranking
// VC — a margin ordinary parallel load consumed, which made the verdict depend on
// machine load rather than on the obligation.
pub const DEFAULT_PER_OBLIGATION_TIMEOUT_MS: u64 = 20_000;

impl NativeTrustMcTrustIrEngine {
    /// Build the engine with the compiler's configured per-obligation SMT budget.
    ///
    /// Prefer this over [`Self::new`] anywhere a `Session` is reachable: `new`
    /// can only mirror the *default*, so a user who raises
    /// `-Z trust-verify-timeout-ms` would otherwise get no additional budget on
    /// this engine and hard-but-provable obligations would keep reporting
    /// Unknown/Timeout no matter what they asked for.
    ///
    /// SOUND: the budget only bounds how long a sound solver lane may run. A
    /// larger budget can turn Unknown into a definite verdict; it can never turn
    /// an unproved obligation into a proof.
    #[must_use]
    pub fn with_timeout_ms(timeout_ms: u64) -> Self {
        // Honor the per-obligation SMT budget rather than the loose 30s adapter
        // default. That default let a single hard obligation (e.g. `Rat::inv`,
        // deeply-nested rationals) consume up to the per-FUNCTION budget in ONE
        // solve, starving the rest of the crate of verification time so the pass
        // stopped ~82/293 functions in. Bounding each solve by the intended
        // per-obligation budget (combined with the per-function deadline clamp)
        // lets grinding obligations bail to Unknown/Timeout promptly and the
        // whole crate get verified. SOUND: a shorter budget only ever yields an
        // EARLIER Unknown/Timeout (fail-closed) — never a proof.
        //
        // Enable the native CHC/PDR family. Each retained native request
        // selects its checked execution profile; this global mode is only
        // the family admission gate. The request keeps caller timeout and
        // certificate ceilings and cannot borrow an ambient solver selection.
        let adapter = TrustMcVerifierApiAdapter::new(
            trust_bmc::TrustMcConfig::new()
                .with_proof_mode(trust_bmc::TrustMcProofMode::PdrIc3)
                .with_timeout(timeout_ms),
        );
        let mut manifest = adapter.manifest().clone();
        manifest.version = format!("{}+native-trust-ir-bundle", manifest.version);
        manifest.repository = Some("trust-bmc".to_string());
        Self { adapter, manifest }
    }

    /// Build the engine at the `-Z trust-verify-timeout-ms` *default* budget.
    ///
    /// Session-less callers only. See [`Self::with_timeout_ms`].
    #[must_use]
    pub fn new() -> Self {
        Self::with_timeout_ms(DEFAULT_PER_OBLIGATION_TIMEOUT_MS)
    }
}

impl Default for NativeTrustMcTrustIrEngine {
    fn default() -> Self {
        Self::new()
    }
}

impl VerificationEngine for NativeTrustMcTrustIrEngine {
    fn manifest(&self) -> &EngineManifest {
        &self.manifest
    }

    fn supports(&self, obligation: &TrustObligation) -> SupportLevel {
        self.adapter.supports(obligation)
    }

    fn verify_validated(
        &self,
        request: ValidatedVerificationRequest<'_>,
    ) -> Vec<ObligationEvidence> {
        // The public trait entrypoint already checked this exact immutable
        // bundle/subset. Preserve that validation across the adapter boundary.
        self.adapter.verify_validated(request)
    }

    fn verify_with_context_validated(
        &self,
        request: ValidatedVerificationRequest<'_>,
        context: &VerifierExecutionContext,
    ) -> VerificationRunResult {
        self.adapter.verify_with_context_validated(request, context)
    }
}

#[cfg(test)]
mod tests {
    use trust_verifier_api::{
        BundleSubject, CancellationReason, EvidenceStatus, ObligationKind, SkipReason,
        SourceLocation, TrustContractBundle,
    };

    use super::*;

    fn request_bundle() -> TrustContractBundle {
        let mut bundle = TrustContractBundle::empty(
            "mc-forwarding",
            BundleSubject::Artifact { name: "caller".into(), kind: "test".into() },
        );
        for id in ["first", "second"] {
            bundle.obligations.push(TrustObligation {
                obligation_id: id.into(),
                kind: ObligationKind::Postcondition,
                contract_id: None,
                proof_item_id: None,
                source: SourceLocation::default(),
                description: "no typed formula: must remain unsupported".into(),
                required_strength: None,
                summary_facts: Vec::new(),
                metadata: Vec::new(),
            });
        }
        bundle
    }

    #[test]
    fn production_adapter_uses_receipt_capable_pdr_mode() {
        let engine = NativeTrustMcTrustIrEngine::new();

        assert_eq!(engine.adapter.config().proof_mode, trust_bmc::TrustMcProofMode::PdrIc3);
        // Assert the CONSTANT, not a literal: this pin exists to prove the engine
        // carries the compiler's default budget, not to freeze a particular number.
        // The literal drifted out of sync when the default was raised 5_000 -> 20_000.
        assert_eq!(engine.adapter.config().timeout_ms, DEFAULT_PER_OBLIGATION_TIMEOUT_MS);
    }

    #[test]
    fn forwarding_preserves_the_exact_requested_subset_and_missing_formula_refusal() {
        let engine = NativeTrustMcTrustIrEngine::new();
        let bundle = request_bundle();
        let requested = &bundle.obligations[1..];
        bundle.validate_requested_obligations(requested).unwrap();

        let evidence = engine.verify(&bundle, requested);
        assert_eq!(evidence.len(), 1);
        assert_eq!(evidence[0].obligation_id, "second");
        assert_eq!(evidence[0].status, EvidenceStatus::Unsupported);
        let result = engine.verify_with_context(
            &bundle,
            requested,
            &VerifierExecutionContext::new("mc-subset"),
        );
        assert_eq!(result.evidence, evidence);
    }

    #[test]
    fn forwarding_keeps_public_rejection_of_substituted_and_duplicate_requests() {
        let engine = NativeTrustMcTrustIrEngine::new();
        let bundle = request_bundle();
        let mut substituted = bundle.obligations[0].clone();
        substituted.description.push_str(" changed");
        for requested in
            [vec![substituted], vec![bundle.obligations[0].clone(), bundle.obligations[0].clone()]]
        {
            assert!(engine.verify(&bundle, &requested).is_empty());
            let result = engine.verify_with_context(
                &bundle,
                &requested,
                &VerifierExecutionContext::new("mc-invalid"),
            );
            assert!(result.evidence.is_empty());
            assert!(result.diagnostics.iter().any(|message| {
                message.contains("verifier rejected non-canonical obligation request")
            }));
        }
    }

    #[test]
    fn forwarding_preserves_cancellation_before_adapter_execution() {
        let engine = NativeTrustMcTrustIrEngine::new();
        let bundle = request_bundle();
        let context = VerifierExecutionContext::new("mc-cancelled");
        context.cancellation.cancel(CancellationReason::UserRequested);
        let result = engine.verify_with_context(&bundle, &bundle.obligations, &context);
        assert!(result.evidence.is_empty());
        assert_eq!(result.skipped.len(), 2);
        assert!(result.skipped.iter().all(|row| {
            matches!(
                row.reason,
                SkipReason::Canceled { reason: Some(CancellationReason::UserRequested) }
            )
        }));
    }
}
