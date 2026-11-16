//! Test-only untrusted legacy-wire producer. It returns DATA, never a checked
//! token. Existing replay must independently check its goal, environment and term.
use super::*;

impl OriginalConjunctionCertificate {
    pub(crate) fn test_legacy_wire_advice(&self) -> Result<Self, String> {
        require_production_allowed();
        if self.packet.model != MODEL {
            return Err("test legacy advice requires a current v2 seed; historical packets cannot be retagged".into());
        }
        // Seed only from a successful normal current-context replay. This test
        // producer never repairs, relabels or accepts a stale v1 environment.
        self.packet.replay(self.original_equations())?;
        let (goal, context) =
            crate::verify_output_instantiate::original_conjunction_goal_version(
                &self.packet.original, 1,
            )
            .ok_or("test legacy advice: original is outside model 1")?;
        let (_, proof) = self.packet.terms.restore()?;
        let environment = environment(&context, 1)?;
        let mut packet = self.packet.clone();
        packet.model = 1;
        packet.context_sha256 = encoded_hash(&context, MAX_ORIGINAL_BYTES)?.0;
        packet.context = context;
        packet.terms = TermPacket::capture(&goal, &proof)?;
        packet.goal_sha256 = encoded_hash(&goal, 64 * 1024 * 1024)?.0;
        packet.proof_sha256 = encoded_hash(&proof, 64 * 1024 * 1024)?.0;
        packet.environment_sha256 = environment_digest(&environment, 1)?;
        packet.environment_mode = format!("{:?}", environment.mode());
        packet.environment_recipe = LEGACY_RECIPE.into();
        packet.kernel_version = clean_kernel::VERSION.into();
        packet.validate()?;
        // This new wire identity does not rewrite or requalify the historical
        // packet. No validity or subject authority is minted by this producer.
        Ok(Self { subject: self.subject.clone(), packet })
    }
}
