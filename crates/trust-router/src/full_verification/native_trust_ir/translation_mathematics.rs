//! Consume the question retained by independent native WP replay.
//! No question is regenerated here, and no solver, source or grade authority
//! follows from an unbound mathematical translation fact.
use std::sync::Arc;

use clean_olean::semr_native_execution::{
    CheckedUnboundNativeWpTranslation, NativeExecutionBinding, NativeExecutionPlace,
    NativeWpTranslationPacket, NativeWpTranslationSubject, UnboundNativeWpTranslationContext,
};
use trust_ir::{NativeRequestId, ProofId, ValidatedNativeBundle};
use trust_ir_build::ModuleValidationReport;
use trust_verifier_api::{ObligationEvidence, TrustContractBundle, TrustObligation};
use trust_wp_lib::BundleClaimFormat;

use super::{CheckedNativeWpProof, execution_mathematics};

/// Select exact original bytes and the actual same-derivation VC retained by
/// the existing native certificate checker. The checked WP fact must still
/// match the entire original input and accepted evidence, including public
/// program carriers. Neither the diagnostic witness nor its body census is a
/// mathematical proof or a source-refinement premise.
pub fn native_wp_translation_subject(
    admitted: &ValidatedNativeBundle<'_>,
    semantics: &ModuleValidationReport<'_>,
    public: &TrustContractBundle,
    obligation: &TrustObligation,
    accepted_evidence: &ObligationEvidence,
    wp: &CheckedNativeWpProof,
) -> Result<NativeWpTranslationSubject, String> {
    let native = admitted.bundle();
    if !wp.matches(public, native, obligation, accepted_evidence) {
        return Err("checked native WP question differs from the original input or evidence".into());
    }
    let request_id = NativeRequestId::new(wp.native_request_id());
    let proof_id = ProofId::new(wp.native_proof_id());
    let original = execution_mathematics::native_wp_execution_subject(
        admitted, semantics, request_id, proof_id, public, obligation,
    )?;
    let witness = wp
        .translation_witness()
        .ok_or("checked native WP evidence has no same-derivation translation witness")?;
    if witness.native_bundle_digest != native.stable_digest()
        || witness.module_digest != native.trust_ir_module_digest
        || witness.request != request_id
        || witness.function.index() != original.function
    {
        return Err(
            "checked translation witness differs from the complete original question".into()
        );
    }
    let request = native
        .requests
        .iter()
        .find(|request| request.id() == request_id)
        .ok_or("checked translation request is absent")?;
    if witness.native_request_digest != request.stable_digest()
        || witness.function_body_digest != native.module.function_body_digest(witness.function)?
    {
        return Err("checked translation witness has a different request or function body".into());
    }
    let proof = native
        .module
        .proof_obligations
        .iter()
        .find(|proof| proof.id == proof_id)
        .ok_or("checked translation original postcondition is absent")?;
    let formula = proof.formula.as_ref().ok_or("checked translation has no original contract")?;
    let mut contracts = witness.contracts.iter().filter(|(id, _)| *id == proof_id);
    if contracts.next().map(|(_, formula)| formula) != Some(formula) || contracts.next().is_some() {
        return Err("checked translation contract differs from the original authored clause".into());
    }
    let mut outputs = witness.derived_request.obligations.iter().filter(|output| {
        output.metadata.native_origin.as_ref().is_some_and(|origin| {
            origin.request_id == request_id.index()
                && origin.obligation_id == proof_id.index()
                && origin.function_id == original.function
        })
    });
    let output = outputs.next().ok_or("checked translation has no exact derived obligation")?;
    if outputs.next().is_some()
        || output.claim.format != BundleClaimFormat::TrustFormulaV1
        || !output.summary_facts.is_empty()
        || !output.metadata.proof_context.assumptions.is_empty()
        || !output.metadata.proof_context.assertions.is_empty()
    {
        return Err("checked translation VC is ambiguous or adds unsupported proof premises".into());
    }
    let function = native
        .module
        .function_by_id(witness.function)
        .ok_or("checked translation function is absent")?;
    let entry = function
        .blocks
        .iter()
        .find(|block| block.id == function.entry)
        .ok_or("checked translation entry block is absent")?;
    if witness.parameters.len() != entry.params.len() {
        return Err("checked translation changed the entry parameter inventory".into());
    }
    let mut vc_bindings = Vec::with_capacity(entry.params.len());
    for (ordinal, ((value, name), (actual_value, actual_type))) in
        witness.parameters.iter().zip(&entry.params).enumerate()
    {
        if value != actual_value {
            return Err("checked translation changed an original entry SSA identity".into());
        }
        let (ty, _) = execution_mathematics::scalar_binding_type(actual_type)?;
        vc_bindings.push(NativeExecutionBinding {
            name: name.as_bytes().to_vec(),
            place: NativeExecutionPlace::Param(
                ordinal.try_into().map_err(|_| "native entry parameter index exceeds u32")?,
            ),
            ty,
        });
    }
    Ok(NativeWpTranslationSubject {
        original,
        vc_bytes: Arc::from(output.claim.payload.as_bytes()),
        vc_bindings,
    })
}

/// Unbound conditional mathematics over the same checked original WP question.
/// There is no serialization, evidence conversion, grade or source/ABI token.
#[derive(Clone, Debug)]
pub struct CheckedNativeWpTranslationMathematics {
    wp: CheckedNativeWpProof,
    mathematics: CheckedUnboundNativeWpTranslation,
}

impl CheckedNativeWpTranslationMathematics {
    pub fn mathematics(&self) -> &CheckedUnboundNativeWpTranslation {
        &self.mathematics
    }

    /// Check immutable correspondence without rerunning a solver or CIC proof.
    pub fn matches(
        &self,
        public: &TrustContractBundle,
        native: &trust_ir::NativeVerificationBundle,
        obligation: &TrustObligation,
        accepted_evidence: &ObligationEvidence,
        context: &UnboundNativeWpTranslationContext,
    ) -> bool {
        self.mathematics.context() == context.digest()
            && self.wp.matches(public, native, obligation, accepted_evidence)
    }
}

/// Check the fixed indexed Clean certificate for the independently expected
/// original subject and the question actually used by native verification.
pub fn check_native_wp_translation_mathematics(
    admitted: &ValidatedNativeBundle<'_>,
    semantics: &ModuleValidationReport<'_>,
    public: &TrustContractBundle,
    obligation: &TrustObligation,
    accepted_evidence: &ObligationEvidence,
    wp: &CheckedNativeWpProof,
    context: &UnboundNativeWpTranslationContext,
    packet: &NativeWpTranslationPacket,
) -> Result<CheckedNativeWpTranslationMathematics, String> {
    let subject = native_wp_translation_subject(
        admitted,
        semantics,
        public,
        obligation,
        accepted_evidence,
        wp,
    )?;
    let mathematics = context.check(&subject, packet).map_err(|error| error.to_string())?;
    Ok(CheckedNativeWpTranslationMathematics { wp: wp.clone(), mathematics })
}
