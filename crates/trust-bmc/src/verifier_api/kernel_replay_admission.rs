//! The existing native consumer's admission boundary, without a solver call.

use super::*;

impl TrustMcVerifierApiAdapter {
    /// Determine which original native claims may omit search after an
    /// independently current-kernel-checked VC proof. This returns scheduling
    /// data only. All checks are the same functions used by the ordinary
    /// native consumer; neither data nor a successful preflight proves a row.
    ///
    /// A miss leaves the original consumer responsible for its original
    /// evidence/refusal. Source authority is required conservatively here;
    /// ordinary exact-direct routes without it retain their existing behavior.
    pub fn kernel_replay_admissible_native_obligations(
        &self,
        bundle: &TrustContractBundle,
        obligations: &[TrustObligation],
        native: &trust_ir::NativeVerificationBundle,
        authority: &trust_ir::SourceGenerationAuthority,
        facts: Option<&SourceReferenceFacts<'_>>,
        deadline: Option<Instant>,
    ) -> Result<BTreeSet<String>, String> {
        let solve_deadline = self.solve_deadline(deadline);
        if !authority.authorizes_bundle(native)
            || facts.is_some_and(|facts| !facts.authorizes_bundle(native, authority))
        {
            return Err(
                "kernel replay requires the original exact live native source authority/facts"
                    .into(),
            );
        }
        if !matches!(self.config.proof_mode, TrustMcProofMode::Chc | TrustMcProofMode::PdrIc3)
            || trust_mc_budget_deadline_exceeded(solve_deadline)
        {
            return Err("native replay admission has no live CHC/PDR solve scope".into());
        }
        native.validate().map_err(|errors| format!("invalid native bundle: {errors:?}"))?;
        validate_trust_mc_native_admission_contract(native)?;
        let binding = NativeTrustIrPublicClaimBindingContext::build(bundle, obligations, native)?;
        let translated = self.native_trust_ir_chc_pdr_translated_obligations_in_live_source(
            native,
            Some(NativeLiveSource { authority, reference_facts: facts }),
            solve_deadline,
        )?;
        let mut translated_by_id = BTreeMap::<String, Vec<_>>::new();
        let refused_ids = translated
            .refused_requests
            .iter()
            .map(|row| native_trust_mc_obligation_lookup_key(&row.native_obligation_id))
            .collect::<BTreeSet<_>>();
        for row in &translated.obligations {
            translated_by_id
                .entry(native_trust_mc_obligation_lookup_key(&row.obligation.obligation_id))
                .or_default()
                .push(row);
        }
        let mut admitted = BTreeSet::new();
        for obligation in obligations {
            if !is_trust_mc_owned_obligation(obligation)
                || owned_e4_e5_pre_solve_rejection(obligation).is_some()
            {
                continue;
            }
            let Ok(claim) =
                validate_native_trust_ir_public_claim_binding(bundle, obligation, native, &binding)
            else {
                continue;
            };
            // Raw source clauses are not generated violation VCs. Their
            // source/body admission and fallback remain the ordinary path.
            if matches!(claim, NativePublicClaimKind::RawPostcondition { .. }) {
                continue;
            }
            let id = native_trust_ir_expected_trust_mc_obligation_id(obligation)
                .unwrap_or_else(|| obligation.obligation_id.clone());
            let lookup_key = native_trust_mc_obligation_lookup_key(&id);
            if refused_ids.contains(&lookup_key) {
                continue;
            }
            let Some(rows) = translated_by_id.get(&lookup_key) else {
                continue;
            };
            let [row] = rows.as_slice() else { continue };
            if row.diagnostics.is_empty()
                && validate_native_trust_mc_row_request_config(row).is_ok()
                && !trust_mc_budget_deadline_exceeded(solve_deadline)
            {
                admitted.insert(obligation.obligation_id.clone());
            }
        }
        Ok(admitted)
    }
}
