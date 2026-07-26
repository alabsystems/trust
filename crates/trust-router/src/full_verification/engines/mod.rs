//! Built-in verifier engines used by the full verifier.

mod native_trust_mc;
mod native_ty;

pub use native_trust_mc::NativeTrustMcTrustIrEngine;
// Trust (b62 timeout-tuning regression): the one shared budgeted+proof-capable
pub use native_ty::NativeTyEngine;

use trust_vc_bridge::TrustVcVerificationEngine;
use trust_verifier_api::VerificationEngine;
use trust_wp::TrustWpVerificationEngine;

/// Required native engines for every full-verifier lane.
#[must_use]
pub fn required_native_engines() -> Vec<Box<dyn VerificationEngine + Send + Sync>> {
    vec![
        Box::new(TrustWpVerificationEngine::new()),
        Box::new(TrustVcVerificationEngine::new()),
        Box::new(NativeTrustMcTrustIrEngine::new()),
        Box::new(NativeTyEngine::new()),
    ]
}
