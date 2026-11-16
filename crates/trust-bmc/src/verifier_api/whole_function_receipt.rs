//! Whole-function safety capability, never standalone-formula authority.

use super::*;

#[derive(Debug)]
struct WholeFunctionSnapshot {
    public: TrustContractBundle,
    native: trust_ir::NativeVerificationBundle,
    claims: NativeTrustIrPublicClaimBindingContext,
}

/// Immutable public/native snapshot identity shared by one source-authorized
/// dispatch. Cloning this token cannot clone a live proof or source authority.
#[derive(Debug, Clone)]
pub struct FreshWholeFunctionChcPdrBundleSeal {
    snapshot: Arc<WholeFunctionSnapshot>,
}

impl FreshWholeFunctionChcPdrBundleSeal {
    pub(super) fn from_source_authorized_bundles(
        public: &TrustContractBundle,
        requested: &[TrustObligation],
        native: &trust_ir::NativeVerificationBundle,
        source: &trust_ir::SourceGenerationAuthority,
    ) -> Result<Self, String> {
        if !source.authorizes_bundle(native) {
            return Err("whole-function receipt requires this exact live source authority".into());
        }
        validate_trust_mc_native_admission_contract(native)?;
        let claims = NativeTrustIrPublicClaimBindingContext::build(public, requested, native)?;
        Ok(Self {
            snapshot: Arc::new(WholeFunctionSnapshot {
                public: public.clone(),
                // A clone is CONTENT only: it deliberately carries no live
                // SourceGenerationAuthority identity. Never use it to mint one.
                native: native.clone(),
                claims,
            }),
        })
    }

    /// Check the complete current public and native contents, including all
    /// member bodies, requests, replay inventory, source facts, and policies.
    /// The compiler separately revalidates its current live source authority.
    #[must_use]
    pub fn matches_bundles(
        &self,
        public: &TrustContractBundle,
        native: &trust_ir::NativeVerificationBundle,
    ) -> bool {
        public.validate().is_ok()
            && native.validate().is_ok()
            && self.snapshot.public == *public
            && self.snapshot.native == *native
    }

    fn shares_identity(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.snapshot, &other.snapshot)
    }
}

/// Owned proof from a fresh source-authorized full safety query. This type is
/// intentionally neither Clone nor serializable and has no public constructor.
/// It authorizes only the canonical formula-less panic-freedom aggregate, not
/// a standalone formula or any sibling/member obligation.
#[derive(Debug)]
pub struct FreshWholeFunctionChcPdrReceipt {
    seal: FreshWholeFunctionChcPdrBundleSeal,
    public_obligation: TrustObligation,
    native_evidence: ObligationEvidence,
    dispatch_deadline: Option<Instant>,
    completed_at: Instant,
    pre_solve_input: TrustMcNativeTypedChcPdrNormalizedInput,
    proof: NativeTrustIrChcPdrAuthorizedProof,
}

impl FreshWholeFunctionChcPdrReceipt {
    #[cfg(test)]
    pub(super) fn assert_private_mutation_controls(mut self) {
        let row = self.public_obligation.clone();
        let check =
            |receipt: &Self| receipt.still_authorizes_under_exact_bundle_seal(&receipt.seal, &row);
        assert!(check(&self).is_ok());
        self.proof.request_id += 1;
        assert!(check(&self).is_err(), "wrong numeric request");
        self.proof.request_id -= 1;
        self.proof.function_id += 1;
        assert!(check(&self).is_err(), "wrong function");
        self.proof.function_id -= 1;
        self.proof.proof_ids.push(self.proof.proof_ids[0]);
        assert!(check(&self).is_err(), "duplicate public proof membership");
        self.proof.proof_ids.pop();
        self.proof.lineage_roots.push(u32::MAX);
        assert!(check(&self).is_err(), "changed lineage roots");
        self.proof.lineage_roots.pop();
        let original_id = self.proof.evidence.translated.obligation.obligation_id.clone();
        self.proof.evidence.translated.obligation.obligation_id =
            original_id.replace("trust_mc", "trust-mc");
        assert!(check(&self).is_err(), "normalized native-ID alias is not authority");
        self.proof.evidence.translated.obligation.obligation_id = original_id;
        let original_source = self.proof.evidence.translated.obligation.native_metadata.clone();
        self.proof
            .evidence
            .translated
            .obligation
            .native_metadata
            .as_mut()
            .unwrap()
            .trust_ir_module_digest
            .value = "0".repeat(64);
        assert!(check(&self).is_err(), "same IDs with changed source body digest");
        self.proof.evidence.translated.obligation.native_metadata = original_source;
        let original_deadline = self.dispatch_deadline;
        self.dispatch_deadline = Some(Instant::now() - std::time::Duration::from_secs(1));
        assert!(check(&self).is_err(), "late live receipt");
        self.dispatch_deadline = original_deadline;
        assert!(check(&self).is_ok());
        let mut changed_before = self.proof.evidence.translated.clone();
        // The translated VC is shared (`Arc<ChcVc>`, trust-mc 5f805b33): copy it on
        // write so only this altered pre-solve query changes, never the proof's own.
        let rule =
            std::sync::Arc::make_mut(&mut changed_before.obligation.vc).rules.first_mut().unwrap();
        let mut constraints = rule.body.constraints.iter().cloned().collect::<Vec<_>>();
        constraints.push(Expr::bool_const(false));
        rule.body = trust_mc_core::RuleBody::new(rule.body.relation.clone(), constraints);
        let cloned_proof_error = NativeTrustIrChcPdrAuthorizedProof::try_from_bundle_evidence(
            self.proof.evidence.clone(),
        )
        .expect_err("cloning the native response does not clone its private proof seal");
        assert!(cloned_proof_error.contains("missing private in-process"), "{cloned_proof_error}");
        let reason = Self::try_from_native(
            self.seal.clone(),
            &row,
            &self.native_evidence,
            &changed_before,
            self.proof,
            original_deadline,
        )
        .expect_err("same IDs/metadata cannot replace the independent pre-solve query");
        assert!(reason.contains("independent pre-solve translation"), "{reason}");
    }

    pub(super) fn try_from_native(
        seal: FreshWholeFunctionChcPdrBundleSeal,
        obligation: &TrustObligation,
        evidence: &ObligationEvidence,
        before_solve: &trust_mc_trust_bmc::NativeTrustMcChcPdrObligation,
        proof: NativeTrustIrChcPdrAuthorizedProof,
        deadline: Option<Instant>,
    ) -> Result<Self, String> {
        let pre_solve_input =
            trust_mc_driver::normalized_typed_chc_pdr_input(&before_solve.obligation)
                .map_err(native_typed_chc_pdr_error_reason)?;
        if before_solve.request_id.index() != proof.request_id
            || before_solve.function.index() != proof.function_id
            || before_solve.obligations.iter().map(|id| id.index()).collect::<Vec<_>>()
                != proof.proof_ids
            || before_solve.lineage_roots.iter().map(|id| id.index()).collect::<Vec<_>>()
                != proof.lineage_roots
            || pre_solve_input != proof.expected_normalized_input
        {
            return Err(
                "whole-function proof differs from the independent pre-solve translation".into()
            );
        }
        let receipt = Self {
            seal,
            public_obligation: obligation.clone(),
            native_evidence: evidence.clone(),
            dispatch_deadline: deadline,
            completed_at: Instant::now(),
            pre_solve_input,
            proof,
        };
        let strength =
            receipt.still_authorizes_under_exact_bundle_seal(&receipt.seal, obligation)?;
        if evidence.status != EvidenceStatus::Proved
            || evidence.obligation_id != obligation.obligation_id
            || evidence.proof_strength.as_ref() != Some(&strength)
        {
            return Err("whole-function proof is not the exact published native result".into());
        }
        Ok(receipt)
    }

    #[must_use]
    pub fn public_obligation_id(&self) -> &str {
        &self.public_obligation.obligation_id
    }

    #[must_use]
    pub fn dispatch_deadline(&self) -> Option<Instant> {
        self.dispatch_deadline
    }

    #[must_use]
    pub fn bundle_seal(&self) -> FreshWholeFunctionChcPdrBundleSeal {
        self.seal.clone()
    }

    #[must_use]
    pub fn shares_bundle_seal(&self, other: &FreshWholeFunctionChcPdrBundleSeal) -> bool {
        self.seal.shares_identity(other)
    }

    pub(super) fn matches_native_evidence(&self, evidence: &ObligationEvidence) -> bool {
        evidence.status == EvidenceStatus::Proved && evidence == &self.native_evidence
    }

    /// Validate a complete current public/native pair before the local affine
    /// replay. Content equality does not replace compiler source authority.
    pub fn still_authorizes(
        &self,
        public: &TrustContractBundle,
        native: &trust_ir::NativeVerificationBundle,
        obligation: &TrustObligation,
    ) -> Result<ProofStrength, String> {
        if !self.seal.matches_bundles(public, native) {
            return Err("whole-function receipt public/native snapshot changed".into());
        }
        self.still_authorizes_under_exact_bundle_seal(&self.seal, obligation)
    }

    /// Receipt-local replay after an outer boundary validated both complete
    /// immutable bundles. The separate whole-function seal cannot authorize a
    /// direct-formula proof or be reconstructed from public evidence.
    #[doc(hidden)]
    pub fn still_authorizes_under_exact_bundle_seal(
        &self,
        seal: &FreshWholeFunctionChcPdrBundleSeal,
        obligation: &TrustObligation,
    ) -> Result<ProofStrength, String> {
        if !self.seal.shares_identity(seal) || obligation != &self.public_obligation {
            return Err("whole-function receipt exact bundle/row identity changed".into());
        }
        if !fresh_exact_direct_completion_is_timely(self.dispatch_deadline, self.completed_at)
            || trust_mc_budget_deadline_exceeded(self.dispatch_deadline)
        {
            return Err("whole-function receipt dispatch deadline elapsed".into());
        }
        let snapshot = &seal.snapshot;
        if !obligation_is_whole_function_panic_freedom(&snapshot.public, obligation) {
            return Err(
                "whole-function receipt requires the canonical formula-less panic aggregate".into(),
            );
        }
        validate_native_trust_ir_public_claim_binding(
            &snapshot.public,
            obligation,
            &snapshot.native,
            &snapshot.claims,
        )?;
        let request_id = canonical_u32_metadata_value(
            obligation_metadata_value(obligation, TRUST_TRUST_IR_NATIVE_REQUEST_ID_METADATA_KEY)
                .ok_or("missing whole-function request id")?,
        )
        .ok_or("invalid whole-function request id")?;
        let proof_id = canonical_u32_metadata_value(
            obligation_metadata_value(
                obligation,
                TRUST_TRUST_IR_NATIVE_PROOF_OBLIGATION_ID_METADATA_KEY,
            )
            .ok_or("missing whole-function proof id")?,
        )
        .ok_or("invalid whole-function proof id")?;
        let indices = snapshot
            .claims
            .trust_mc_requests
            .get(&request_id)
            .ok_or("whole-function request disappeared")?;
        let [index] = indices.as_slice() else {
            return Err("whole-function request is not unique".into());
        };
        let trust_ir::NativeVerificationRequest::TrustMc(request) =
            &snapshot.native.requests[*index]
        else {
            return Err("whole-function request changed family".into());
        };
        let actual = &self.proof.evidence.translated;
        // This first family is deliberately 1:1 at the PUBLIC aggregate seam:
        // the solved function is a full-module safety query, but its request
        // owns exactly this aggregate, never an arbitrary set of formula rows.
        if request.obligations.as_slice() != [trust_ir::ProofId::new(proof_id)]
            || self.proof.request_id != request_id
            || self.proof.function_id != request.function.index()
            || self.proof.proof_ids != [proof_id]
            || self.proof.lineage_roots
                != request.lineage_roots.iter().map(|id| id.index()).collect::<Vec<_>>()
            || actual.request_id != request.id
            || actual.function != request.function
            || actual.obligations != request.obligations
            || actual.lineage_roots != request.lineage_roots
        {
            return Err(
                "whole-function numeric request/function/proof/lineage membership differs".into()
            );
        }
        let canonical_native_id =
            format!("trust_ir-native-trust_mc-request-{request_id}-proof-{proof_id}");
        if actual.obligation.obligation_id != canonical_native_id {
            return Err(
                "whole-function native id is not the exact canonical numeric projection".into()
            );
        }
        let metadata = actual
            .obligation
            .native_metadata
            .as_ref()
            .ok_or("whole-function translated query has no native source binding")?;
        let digest_matches = |actual: &trust_mc_core::NativeArtifactDigest,
                              expected: trust_ir::ProofDigest| {
            format!("{}:{}", actual.algorithm, actual.value) == expected.to_string()
        };
        if !digest_matches(&metadata.trust_ir_module_digest, snapshot.native.trust_ir_module_digest)
            || !digest_matches(
                &metadata.lineage_manifest_digest,
                snapshot.native.lineage.stable_digest(),
            )
            || !metadata.compiler_facts_digest.as_ref().is_some_and(|digest| {
                digest_matches(digest, snapshot.native.compiler_facts.stable_digest())
            })
            || match (metadata.source_digest.as_ref(), snapshot.native.source_digest()) {
                (Some(actual), Some(expected)) => !digest_matches(actual, expected),
                (None, None) => false,
                _ => true,
            }
        {
            return Err(
                "whole-function proof has a different body/source/compiler-fact/lineage digest"
                    .into(),
            );
        }
        let normalized = trust_mc_driver::normalized_typed_chc_pdr_input(&actual.obligation)
            .map_err(native_typed_chc_pdr_error_reason)?;
        if normalized != self.pre_solve_input || normalized != self.proof.expected_normalized_input
        {
            return Err("whole-function typed request changed after solve".into());
        }
        validate_native_full_verification_normalized_input(
            &self.proof.evidence.verification,
            &normalized,
        )?;
        let authority = self
            .proof
            .evidence
            .verification
            .authorized_native_proof()
            .map_err(native_typed_chc_pdr_error_reason)?;
        let transport = authority.transport_record();
        if transport != self.proof.evidence.transport
            || transport.native_id != canonical_native_id
            || transport.request_id != request_id
            || transport.proof_id != Some(proof_id)
        {
            return Err("whole-function live proof/transport identity differs".into());
        }
        validate_native_typed_transport_common(
            &snapshot.public,
            obligation,
            &transport,
            Some(&normalized),
        )
        .map_err(|reasons| reasons.join("; "))?;
        let strength = native_typed_proof_strength(transport.proof_strength)
            .ok_or("whole-function proof strength is unsupported")?;
        if strength.assurance != trust_verifier_api::AssuranceLevel::SmtBacked
            || !matches!(
                strength.reasoning,
                trust_verifier_api::ReasoningKind::Chc | trust_verifier_api::ReasoningKind::Pdr
            )
        {
            return Err("whole-function receipt never grants kernel-certified authority".into());
        }
        Ok(strength)
    }
}
