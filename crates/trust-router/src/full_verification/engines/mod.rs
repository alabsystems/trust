//! Built-in verifier engines used by the full verifier.

mod native_trust_mc;
mod native_ty;

pub use native_trust_mc::{DEFAULT_PER_OBLIGATION_TIMEOUT_MS, NativeTrustMcTrustIrEngine};
// Trust (b62 timeout-tuning regression): the one shared budgeted+proof-capable
pub use native_ty::NativeTyEngine;

use trust_vc_bridge::TrustVcVerificationEngine;
use trust_verifier_api::VerificationEngine;
use trust_wp::TrustWpVerificationEngine;

/// Required native engines for every full-verifier lane, at the compiler's
/// configured per-obligation SMT budget (`-Z trust-verify-timeout-ms`).
///
/// SOUND: the budget bounds only how long a sound solver lane may run. A larger
/// budget can turn Unknown into a definite verdict; it can never turn an
/// unproved obligation into a proof.
#[must_use]
pub fn required_native_engines_with_timeout_ms(
    timeout_ms: u64,
) -> Vec<Box<dyn VerificationEngine + Send + Sync>> {
    vec![
        Box::new(TrustWpVerificationEngine::new()),
        Box::new(TrustVcVerificationEngine::new()),
        Box::new(NativeTrustMcTrustIrEngine::with_timeout_ms(timeout_ms)),
        Box::new(NativeTyEngine::new()),
    ]
}

/// Required native engines at the `-Z trust-verify-timeout-ms` *default* budget.
///
/// Session-less callers only (tests, tooling). Compiler paths should use
/// [`required_native_engines_with_timeout_ms`] so a user who raises the flag
/// actually gets the budget they asked for.
#[must_use]
pub fn required_native_engines() -> Vec<Box<dyn VerificationEngine + Send + Sync>> {
    required_native_engines_with_timeout_ms(DEFAULT_PER_OBLIGATION_TIMEOUT_MS)
}
