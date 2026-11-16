//! Independently select the original native input for Clean's fixed SemR goal.
//!
//! This is data extraction and input mathematics, not another WP calculus or
//! source decoder. The existing module validator, public-claim boundary and
//! Clean goal constructor keep their respective ownership. The model context
//! remains explicitly unbound until its source owner authenticates it; no
//! routed evidence, source/ABI permission or proof grade is minted here.

use std::sync::Arc;

use clean_olean::semr_native_execution::{
    CheckedUnboundNativeExecutionMathematics, NativeExecutionBinding,
    NativeExecutionContractFormat, NativeExecutionIntegerType, NativeExecutionModuleSubject,
    NativeExecutionPacket, NativeExecutionPlace, NativeExecutionSubject, NativeExecutionType,
    UnboundNativeExecutionMathematicsContext,
};
use trust_ir::proof::{ClausePlace, ClauseSort};
use trust_ir::{
    NativeRequestId, NativeVerificationBundle, NativeVerificationRequest, ProofId, Ty,
    ValidatedNativeBundle,
};
use trust_ir_build::ModuleValidationReport;
use trust_verifier_api::{TrustContractBundle, TrustObligation};

const CODEC_FUEL: u64 = 4096;

/// Select the actual WP sibling, independently of the public primary-engine
/// route, and quote its complete original program and original authored clause.
///
/// Both existing admission facts must refer to the same immutably borrowed
/// module. Reusing them does not repeat either validation pass. The returned
/// subject grants no authority and is not a proof that the Rust WP translator
/// is sound. Clean's successful-execution proposition quantifies every valid
/// input and every call-depth budget; proofs for calls remain outside the
/// currently qualified mathematical fragment.
pub fn native_wp_execution_subject(
    admitted: &ValidatedNativeBundle<'_>,
    semantics: &ModuleValidationReport<'_>,
    request_id: NativeRequestId,
    proof_id: ProofId,
    public: &TrustContractBundle,
    obligation: &TrustObligation,
) -> Result<NativeExecutionSubject, String> {
    let native = admitted.bundle();
    let module = &native.module;
    let validated = semantics.validated_module().ok_or("invalid native module semantics")?;
    if !std::ptr::eq(validated, module) || !semantics.handle_registry_is_pinned() {
        return Err(
            "native mathematical input needs the same module and pinned semantic policy".into()
        );
    }
    if module.stable_digest() != native.trust_ir_module_digest {
        return Err("native mathematical input has a stale recorded module digest".into());
    }
    let mut selected = native.requests.iter().filter(|request| request.id() == request_id);
    let Some(NativeVerificationRequest::TrustWp(request)) = selected.next() else {
        return Err("original native request is not a WP request".into());
    };
    if selected.next().is_some()
        || request.mode != trust_ir::TrustWpVerificationMode::WeakestPrecondition
        || !request.obligations.contains(&proof_id)
    {
        return Err(
            "native mathematical input needs one original WP request containing the proof".into()
        );
    }
    let mut proofs = module.proof_obligations.iter().filter(|proof| proof.id == proof_id);
    let proof = proofs.next().ok_or("original native proof obligation is missing")?;
    if proofs.next().is_some()
        || proof.kind != trust_ir::ObligationKind::Postcondition
        || proof.function != Some(request.function)
        || proof.site.is_some()
    {
        return Err(
            "native mathematical input needs the selected function's original postcondition".into(),
        );
    }
    super::validate_public_claim(module, Some(proof), public, obligation)?;
    let formula = proof.formula.as_ref().ok_or("original native postcondition has no formula")?;
    let contract_format = NativeExecutionContractFormat::from_schema(&formula.schema)
        .map_err(|error| error.to_string())?;
    let function =
        module.function_by_id(request.function).ok_or("original native function is missing")?;
    let signature = module.func_type(function.ty).ok_or("original native signature is missing")?;
    let mut typed_bindings = Vec::with_capacity(formula.bindings.len());
    for (name, binding) in &formula.bindings {
        let (place, actual) = match binding.place {
            ClausePlace::Param { index } => {
                (NativeExecutionPlace::Param(index), signature.params.get(index as usize))
            }
            ClausePlace::ResultSlot { index } => {
                (NativeExecutionPlace::Result(index), signature.returns.get(index as usize))
            }
            _ => return Err("original native contract place has no SemR scalar binding".into()),
        };
        let ty = binding_type(
            actual.ok_or("original native contract place is out of range")?,
            &binding.sort,
        )?;
        typed_bindings.push(NativeExecutionBinding { name: name.as_bytes().to_vec(), place, ty });
    }
    // The old 153-byte fixture clears a proof obligation before serialization.
    // The mathematical subject here retains ALL original module fields.
    let bytes = trust_ir::binary::serialize_module(module).map_err(|error| error.to_string())?;
    let module =
        NativeExecutionModuleSubject::new(Arc::from(bytes)).map_err(|error| error.to_string())?;
    Ok(NativeExecutionSubject {
        module: Arc::new(module),
        function: request.function.index(),
        codec_fuel: CODEC_FUEL,
        contract_format,
        contract_bytes: Arc::from(formula.payload.as_bytes()),
        typed_bindings,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn exact_binding_types_do_not_invent_signedness_or_erase_width() {
        for (ty, sort) in [
            (Ty::Bool, ClauseSort::Bool),
            (Ty::U8, ClauseSort::BitVec(8)),
            (Ty::U32, ClauseSort::BitVec(32)),
            (Ty::U64, ClauseSort::BitVec(64)),
        ] {
            assert!(binding_type(&ty, &sort).is_ok());
        }
        for (ty, sort) in [
            (Ty::I8, ClauseSort::BitVec(8)),
            (Ty::I32, ClauseSort::BitVec(32)),
            (Ty::I64, ClauseSort::BitVec(64)),
            (Ty::U8, ClauseSort::BitVec(32)),
            (Ty::U64, ClauseSort::Int),
            (Ty::Bool, ClauseSort::BitVec(1)),
        ] {
            assert!(binding_type(&ty, &sort).is_err(), "{ty:?} / {sort:?}");
        }
    }
}

fn binding_type(actual: &Ty, declared: &ClauseSort) -> Result<NativeExecutionType, String> {
    let (ty, expected) = scalar_binding_type(actual)?;
    if declared != &expected {
        return Err("original native contract sort differs from its exact scalar type".into());
    }
    Ok(ty)
}

pub(super) fn scalar_binding_type(
    actual: &Ty,
) -> Result<(NativeExecutionType, ClauseSort), String> {
    let (ty, sort) = match actual {
        Ty::Bool => (NativeExecutionType::Bool, ClauseSort::Bool),
        Ty::U8 => (NativeExecutionType::Int(NativeExecutionIntegerType::U8), ClauseSort::BitVec(8)),
        Ty::U32 => {
            (NativeExecutionType::Int(NativeExecutionIntegerType::U32), ClauseSort::BitVec(32))
        }
        Ty::U64 => {
            (NativeExecutionType::Int(NativeExecutionIntegerType::U64), ClauseSort::BitVec(64))
        }
        _ => {
            return Err(
                "native mathematical binding is outside the exact unsigned scalar fragment".into(),
            );
        }
    };
    Ok((ty, sort))
}

/// A kernel-checked mathematical fact tied to one full original native input.
///
/// Its fields are private and it has no serialization, evidence or grade
/// conversion. An unbound model theorem does not establish canonical model
/// provenance, source refinement, ABI behavior or emitted-code correctness.
#[derive(Clone, Debug)]
pub struct CheckedNativeWpInputMathematics {
    native: Arc<NativeVerificationBundle>,
    request_id: NativeRequestId,
    proof_id: ProofId,
    public_semantic_digest: String,
    mathematics: CheckedUnboundNativeExecutionMathematics,
}

impl CheckedNativeWpInputMathematics {
    pub fn mathematics(&self) -> &CheckedUnboundNativeExecutionMathematics {
        &self.mathematics
    }

    /// Match the entire original input and current public program constraints;
    /// this checks correspondence without rerunning a solver or kernel proof.
    pub fn matches(
        &self,
        native: &NativeVerificationBundle,
        request_id: NativeRequestId,
        proof_id: ProofId,
        public: &TrustContractBundle,
        obligation: &TrustObligation,
        context: &UnboundNativeExecutionMathematicsContext,
    ) -> bool {
        if native != self.native.as_ref()
            || request_id != self.request_id
            || proof_id != self.proof_id
            || self.mathematics.context() != context.digest()
        {
            return false;
        }
        let Some(proof) = native.module.proof_obligations.iter().find(|proof| proof.id == proof_id)
        else {
            return false;
        };
        trust_verifier_api::native_contract_claim::validate_native_public_module_binding(
            &native.module,
            proof,
            obligation,
        )
        .is_ok()
            && public
                .canonical_obligation_semantic_digest_sha256(obligation)
                .is_ok_and(|digest| digest == self.public_semantic_digest)
    }
}

/// Independently reconstruct the exact goal before checking untrusted proof
/// data. The selected original request and all other native input rows remain
/// in the fact's immutable binding; no scoped replacement input is invented.
pub fn check_native_wp_input_mathematics(
    admitted: &ValidatedNativeBundle<'_>,
    semantics: &ModuleValidationReport<'_>,
    request_id: NativeRequestId,
    proof_id: ProofId,
    public: &TrustContractBundle,
    obligation: &TrustObligation,
    context: &UnboundNativeExecutionMathematicsContext,
    packet: &NativeExecutionPacket,
) -> Result<CheckedNativeWpInputMathematics, String> {
    let expected =
        native_wp_execution_subject(admitted, semantics, request_id, proof_id, public, obligation)?;
    let mathematics = context.check(&expected, packet).map_err(|error| error.to_string())?;
    Ok(CheckedNativeWpInputMathematics {
        native: Arc::new(admitted.bundle().clone()),
        request_id,
        proof_id,
        public_semantic_digest: public.canonical_obligation_semantic_digest_sha256(obligation)?,
        mathematics,
    })
}
