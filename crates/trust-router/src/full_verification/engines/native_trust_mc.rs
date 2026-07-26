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

impl NativeTrustMcTrustIrEngine {
    #[must_use]
    pub fn new() -> Self {
        // Honor the per-obligation SMT budget the compiler drives ny-cert with
        // (`-Z trust-verify-timeout-ms=5000`) instead of the loose 30s adapter
        // default. The default let a single hard obligation (e.g. `Rat::inv`,
        // deeply-nested rationals) consume up to the per-FUNCTION budget in ONE
        // solve, starving the rest of the crate of verification time so the pass
        // stopped ~82/293 functions in. Capping each solve at the intended
        // per-obligation budget (combined with the per-function deadline clamp)
        // lets grinding obligations bail to Unknown/Timeout promptly and the
        // whole crate get verified. SOUND: a shorter budget only ever yields an
        // EARLIER Unknown/Timeout (fail-closed) — never a proof.
        // TODO: thread the actual `-Z trust-verify-timeout-ms` value through the
        // full-verification engine construction rather than mirroring its
        // default here.
        // Trust (proof-mode wiring — REGRESSION FIX): the native trust-mc engine
        // exists to discharge the typed CHC/PDR bundle. Its consumer
        // (`evidence_from_native_trust_ir_bundle_with_deadline`) fail-closes at
        // its first gate unless the adapter is configured for CHC or PDR/IC3, but
        // `TrustMcConfig::new()` defaults `proof_mode` to `Bmc`. Configure PdrIc3
        // here too so this engine's adapter agrees with the native-bundle consumer
        // (`bundle_evidence.rs`) instead of leaving a Bmc adapter that can never
        // reach the CHC/PDR solve. SOUND: proof mode only selects which sound
        // solver lane runs; it never turns an unsolved obligation into a proof.
        let adapter = TrustMcVerifierApiAdapter::new(
            trust_bmc::TrustMcConfig::new()
                .with_proof_mode(trust_bmc::TrustMcProofMode::PdrIc3)
                .with_timeout(5_000),
        );
        let mut manifest = adapter.manifest().clone();
        manifest.version = format!("{}+native-trust-ir-bundle", manifest.version);
        manifest.repository = Some("trust-bmc".to_string());
        Self { adapter, manifest }
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
        let (bundle, obligations) = request.into_parts();
        self.adapter.verify(bundle, obligations)
    }

    fn verify_with_context_validated(
        &self,
        request: ValidatedVerificationRequest<'_>,
        context: &VerifierExecutionContext,
    ) -> VerificationRunResult {
        let (bundle, obligations) = request.into_parts();
        self.adapter.verify_with_context(bundle, obligations, context)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn production_adapter_uses_receipt_capable_pdr_mode() {
        let engine = NativeTrustMcTrustIrEngine::new();

        assert_eq!(engine.adapter.config().proof_mode, trust_bmc::TrustMcProofMode::PdrIc3);
        assert_eq!(engine.adapter.config().timeout_ms, 5_000);
    }
}
