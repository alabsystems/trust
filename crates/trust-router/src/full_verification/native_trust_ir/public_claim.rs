//! Delegate original public/native claim binding to the shared engine boundary.

use trust_ir::{Module, ProofObligation};
use trust_verifier_api::{TrustContractBundle, TrustObligation};

pub(crate) fn validate_public_claim(
    module: &Module,
    proof: Option<&ProofObligation>,
    bundle: &TrustContractBundle,
    obligation: &TrustObligation,
) -> Result<(), String> {
    #[cfg(feature = "trust-build")]
    {
        trust_verifier_api::native_contract_claim::validate_native_public_contract_claim(
            module,
            proof.ok_or("native raw claim has no proof obligation")?,
            bundle,
            obligation,
        )
    }
    #[cfg(not(feature = "trust-build"))]
    {
        let _ = (module, proof, bundle, obligation);
        Err("native body-WP claim validation requires the Trust build".into())
    }
}
