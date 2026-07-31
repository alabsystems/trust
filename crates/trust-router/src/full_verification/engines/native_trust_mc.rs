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
pub const DEFAULT_PER_OBLIGATION_TIMEOUT_MS: u64 = 5_000;

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
        // Trust (proof-mode wiring — REGRESSION FIX): the native trust-mc engine
        // exists to discharge the typed CHC/PDR bundle. Its consumer
        // (`evidence_from_native_trust_ir_bundle_with_deadline`) fail-closes at
        // its first gate unless the adapter is configured for CHC or PDR/IC3, but
        // `TrustMcConfig::new()` defaults `proof_mode` to `Bmc`. Configure PdrIc3
        // here too so this engine's adapter agrees with the native-bundle consumer
        // (`bundle_evidence.rs`) instead of leaving a Bmc adapter that can never
        // reach the CHC/PDR solve. SOUND: proof mode only selects which sound
        // solver lane runs; it never turns an unsolved obligation into a proof.
        // NOTE: `Chc` and `PdrIc3` both clear that gate and both carry the same
        // `TrustMcProofProvenance::unbounded` strength (trust-bmc
        // `subprocess.rs`), so this choice is not what bounds the engine's
        // capability — the budget is.
        //
        // Do NOT "upgrade" this to `Chc` expecting a broader portfolio. It is a
        // tempting misread and it is wrong in both directions.
        // `chc_pdr_engine_from_config` (trust-bmc `verifier_api.rs`) does map
        // Chc -> AdaptivePortfolio and PdrIc3 -> Pdr, but `options.engine`
        // selects a solver in exactly ONE place — the `match request.options
        // .engine` inside `solve_typed_chc_pdr_with_ay` (trust-mc-driver
        // `native.rs`), reachable only through `NativeTypedChcPdrRunner::solve`,
        // which no production call site here uses. Every adapter entry point
        // that actually solves lands in `solve_typed_chc_pdr_full_with_ay`,
        // which hardcodes `Engine::Pdr` + `ProofMode::Strict` and never reads
        // `options.engine`; ay-encode's `invoke.rs` says the same in its own
        // words ("`solve_pdr_proof` always drives the PDR/IC3 engine").
        // So flipping would select no new solver, and WOULD relabel a run that
        // provably executed PDR — `engine: "AdaptivePortfolio"` in the options
        // artifact, plus a moved full-verification cache key and artifact
        // directory (pinned by
        // `typed_full_verification_cache_key_changes_with_options`). Broadening
        // the lanes is a trust-mc-driver change, not a value change here.
        // (This is a property of the CURRENT call sites, not an enforced
        // invariant — re-derive before relying on it.)
        //
        // The `PdrIc3` pin is DUPLICATED in a second adapter,
        // `full_verification/native_trust_ir/bundle_evidence.rs`. Change both or
        // neither.
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
