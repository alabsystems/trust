//! Compiler-private whole-function native safety consumption.
//!
//! The affine producer/router family proves the translated complete function,
//! not a standalone formula. Exact-direct bookkeeping is shared only as an
//! immutable result/run identity carrier. No kernel grade is manufactured.

use super::*;

#[derive(Debug, Clone)]
pub(super) struct FreshWholeFunctionChcPdrAuthority {
    pub(super) exact: ExactLiveChcPdrAuthority,
    // Content snapshots never carry a cloned source-generation capability.
    // Actual live source authentication is required at receipt consumption.
    native_snapshot: Arc<trust_ir::NativeVerificationBundle>,
    native_digest: trust_ir::ProofDigest,
}

impl FreshWholeFunctionChcPdrAuthority {
    pub(super) fn authorizes_final_run(
        &self,
        run: &trust_verifier_api::VerificationRunResult,
    ) -> bool {
        self.exact.authorizes_final_run(run)
            && self.native_snapshot.validate().is_ok()
            && self.native_snapshot.stable_digest() == self.native_digest
    }
}

#[derive(Debug, Default)]
pub(super) struct FreshWholeFunctionChcPdrMintReport {
    pub(super) minted: usize,
    pub(super) rejected: Vec<String>,
    /// Determinism plan §3.7: the obligation IDs among `rejected` the
    /// per-function deadline refused (`record_live_mint_clock_stops`).
    pub(super) clock_rejected: Vec<String>,
}

/// Consume the affine sidecars returned by the genuine native dispatch and
/// mint compiler-private whole-function tokens only against the final, post-bridge public
/// carrier. The public run is never edited here. Every rejection is local and
/// fail-closed; malformed global carrier state rejects the whole receipt set.
pub(super) fn install_fresh_whole_function_chc_pdr_authorities(
    function: &trust_types::VerifiableFunction,
    bundle: &trust_verifier_api::TrustContractBundle,
    dispatched_obligations: &[trust_verifier_api::TrustObligation],
    native: Option<&trust_ir::NativeVerificationBundle>,
    source: Option<&trust_ir::SourceGenerationAuthority>,
    context: &trust_router::VerifierExecutionContext,
    final_run: &trust_verifier_api::VerificationRunResult,
    live_receipts: Option<&mut trust_router::LiveVerificationReceiptBatch>,
    results: &[(VerificationCondition, VerificationResult)],
    result_bindings: &[Option<ResultObligationBinding>],
    proof_authorities: &mut [Option<ResultProofAuthority>],
) -> FreshWholeFunctionChcPdrMintReport {
    let mut report = FreshWholeFunctionChcPdrMintReport::default();
    let Some(live_receipts) = live_receipts else { return report };
    let fresh_receipts = live_receipts.take_fresh_whole_function_chc_pdr_receipts();
    if fresh_receipts.is_empty() {
        return report;
    }
    let (Some(native), Some(source)) = (native, source) else {
        report.rejected.extend(fresh_receipts.into_keys().map(|id| {
            format!("{id}: whole-function consumption requires the current live source/native pair")
        }));
        return report;
    };
    let Some(source_run) = live_receipts.source_run() else {
        report.rejected.extend(fresh_receipts.into_keys().map(|obligation_id| {
            format!("{obligation_id}: live receipt batch has no source dispatch authority")
        }));
        return report;
    };

    let global_error = if !source.authorizes_bundle(native) {
        Some("current native bundle does not have valid live source authority")
    } else if bundle.validate().is_err() {
        Some("the exact compiler bundle is invalid")
    } else if !live_receipts.matches_bundle(bundle) {
        Some("the live receipt batch was minted for a different exact bundle")
    } else if bundle.validate_requested_obligations(dispatched_obligations).is_err() {
        Some("the dispatched obligation inventory is not an exact canonical bundle subset")
    } else if context.is_cancelled() {
        Some("the verifier execution context was cancelled before compiler mint")
    } else if context.budget_exceeded() {
        Some(LIVE_MINT_DEADLINE_EXPIRED)
    } else if source_run.validate_derived_state().is_err()
        || final_run.validate_derived_state().is_err()
    {
        Some("the source or final public run has invalid derived state")
    } else if !is_permitted_bridge_publication_transition(source_run, final_run) {
        Some("the source-to-final public run transition is not an exact bridge publication")
    } else if final_run.bundle_id != bundle.bundle_id || final_run.subject != bundle.subject {
        Some("the final public run identifies a different bundle or subject")
    } else if source_run.bundle_id != bundle.bundle_id || source_run.subject != bundle.subject {
        Some("the source public run identifies a different bundle or subject")
    } else if final_run.context != context.snapshot() || final_run.run_id != context.run_id {
        Some("the final public run has a different execution context")
    } else if source_run.context != context.snapshot() || source_run.run_id != context.run_id {
        Some("the source public run has a different execution context")
    } else if final_run.requested_obligations != dispatched_obligations {
        Some("the final public run has a different dispatched obligation inventory")
    } else if source_run.requested_obligations != dispatched_obligations {
        Some("the source public run has a different dispatched obligation inventory")
    } else if final_run.summary.publication_conflicts != 0 {
        Some("the final public run contains publication conflicts")
    } else if results.len() != result_bindings.len() || results.len() != proof_authorities.len() {
        Some("the compiler result, binding, and authority carriers are not row-aligned")
    } else {
        None
    };
    if let Some(error) = global_error {
        // Determinism plan §3.7: a receipt the deadline refused at mint left
        // its natively proved row to the clock.
        if error == LIVE_MINT_DEADLINE_EXPIRED {
            report.clock_rejected.extend(fresh_receipts.keys().cloned());
        }
        report.rejected.extend(
            fresh_receipts.into_keys().map(|obligation_id| format!("{obligation_id}: {error}")),
        );
        return report;
    }
    let (dispatched_by_id, duplicate_dispatched_ids) =
        unique_index_and_duplicates_by_id(dispatched_obligations, |obligation| {
            obligation.obligation_id.as_str()
        });
    let binding_rows = build_exact_result_binding_row_index(results, result_bindings);
    let final_index = build_full_verification_evidence_index(final_run);
    let strict_accepted_evidence_positions = strict_accepted_evidence_positions(final_run);
    let run_seal = Arc::new(ExactLiveChcPdrRunSeal {
        bundle: bundle.clone(),
        dispatched_obligations: dispatched_obligations.to_vec(),
        context: context.snapshot(),
        dispatch_deadline: context.deadline(),
        source_run: source_run.clone(),
        final_run: final_run.clone(),
        strict_accepted_evidence_positions,
    });
    if !run_seal.envelope_is_valid() {
        report.rejected.extend(fresh_receipts.into_keys().map(|obligation_id| {
            format!("{obligation_id}: compiler-private FreshExact run seal failed exact validation")
        }));
        return report;
    }

    let native_snapshot = Arc::new(native.clone());
    let native_digest = native.stable_digest();
    let expected_crate_name = match &bundle.subject {
        trust_verifier_api::BundleSubject::Function { crate_name, .. } => Some(crate_name.as_str()),
        _ => None,
    };
    for (map_id, receipt) in fresh_receipts {
        let reject = |report: &mut FreshWholeFunctionChcPdrMintReport, reason: &str| {
            report.rejected.push(format!("{map_id}: {reason}"));
        };
        if receipt.public_obligation_id() != map_id {
            reject(&mut report, "receipt/map obligation identity mismatch");
            continue;
        }
        let Some(obligation) = dispatched_by_id.get(map_id.as_str()).copied() else {
            reject(&mut report, "receipt obligation is absent from the dispatched inventory");
            continue;
        };
        if duplicate_dispatched_ids.contains(map_id.as_str()) || obligation.is_default_admission() {
            reject(&mut report, "receipt obligation is duplicated or is a synthetic admission");
            continue;
        }
        if !obligation_is_synthesized_whole_function_panic_freedom(
            function,
            expected_crate_name,
            obligation,
        ) {
            reject(&mut report, "row is not this compiler function's exact synthesized aggregate");
            continue;
        }
        let Some(evidence) =
            final_index.strict_accepted_by_obligation_id.get(map_id.as_str()).copied()
        else {
            reject(
                &mut report,
                "no unique conflict-free accepted Proved evidence row survived final publication",
            );
            continue;
        };
        if receipt.dispatch_deadline() != context.deadline() {
            reject(&mut report, "receipt deadline differs from the compiler execution deadline");
            continue;
        }
        let Ok(proof_strength) = live_receipts.authorizes_fresh_whole_function_chc_pdr_receipt(
            &receipt, native, source, obligation, evidence,
        ) else {
            reject(&mut report, "affine receipt rejected the final accepted evidence row");
            continue;
        };
        if context.is_cancelled()
            || context.budget_exceeded()
            || receipt.dispatch_deadline() != context.deadline()
        {
            if context.budget_exceeded() {
                report.clock_rejected.push(map_id.clone());
            }
            reject(&mut report, "execution context became late, cancelled, or changed at mint");
            continue;
        }
        if evidence.proof_strength.as_ref() != Some(&proof_strength)
            || !exact_direct_chc_pdr_strength_is_authoritative(&proof_strength)
        {
            reject(&mut report, "receipt is not CHC/PDR evidence at SmtBacked assurance");
            continue;
        }

        if binding_rows.ambiguous_ids.contains(map_id.as_str()) {
            reject(&mut report, "multiple current compiler result rows match the receipt");
            continue;
        }
        let Some(row_index) = binding_rows.unique_rows.get(map_id.as_str()).copied() else {
            reject(&mut report, "no exact current compiler result binding matches the receipt");
            continue;
        };
        if !result_bindings[row_index]
            .as_ref()
            .is_some_and(|binding| binding.matches_public_obligation(obligation))
        {
            reject(&mut report, "no exact current compiler result binding matches the receipt");
            continue;
        }
        let (vc, result) = &results[row_index];
        let Some(expected_legacy_strength) = legacy_proof_strength(&proof_strength) else {
            reject(&mut report, "receipt strength has no exact compiler result representation");
            continue;
        };
        if !matches!(
            result,
            VerificationResult::Proved { strength, .. } if strength == &expected_legacy_strength
        ) {
            reject(&mut report, "current compiler result row or proof strength changed");
            continue;
        }
        let Some(compiler_result) = ExactLiveCompilerProvedResult::from_result(result) else {
            reject(&mut report, "current compiler result is not an exact Proved carrier");
            continue;
        };
        // Kernel authority has precedence. S1/R1, source-derived, certified,
        // assumption, and compatibility-native authority are not
        // interchangeable with this receipt and are never overwritten.
        if proof_authorities[row_index].is_some() {
            reject(&mut report, "current row already carries a different private authority");
            continue;
        }
        let Some(row) = exact_result_row_identity(row_index, vc) else {
            reject(&mut report, "current compiler result row has no canonical exact identity");
            continue;
        };
        let Some(binding) = result_bindings[row_index].as_ref().cloned() else {
            reject(&mut report, "current compiler result binding disappeared");
            continue;
        };
        let authority = ExactLiveChcPdrAuthority {
            row,
            binding,
            obligation: obligation.clone(),
            compiler_result,
            accepted_evidence: evidence.clone(),
            evidence_id: evidence.evidence_id.clone(),
            proof_strength,
            dispatch_deadline: context.deadline(),
            run_seal: Arc::clone(&run_seal),
        };
        if !authority.authorizes_row(row_index, vc, result_bindings[row_index].as_ref())
            || !authority.authorizes_compiler_result(result)
        {
            reject(&mut report, "compiler-private exact carrier self-check failed");
            continue;
        }
        if context.is_cancelled()
            || context.budget_exceeded()
            || receipt.dispatch_deadline() != context.deadline()
        {
            if context.budget_exceeded() {
                report.clock_rejected.push(map_id.clone());
            }
            reject(
                &mut report,
                "execution context became late, cancelled, or changed at final mint",
            );
            continue;
        }
        let authority = FreshWholeFunctionChcPdrAuthority {
            exact: authority,
            native_snapshot: Arc::clone(&native_snapshot),
            native_digest: native_digest.clone(),
        };
        if !authority.authorizes_final_run(final_run) {
            reject(&mut report, "whole-function source snapshot failed exact final validation");
            continue;
        }
        if context.is_cancelled() || context.budget_exceeded() {
            if context.budget_exceeded() {
                report.clock_rejected.push(map_id.clone());
            }
            reject(&mut report, "whole-function context expired at final snapshot validation");
            continue;
        }
        proof_authorities[row_index] =
            Some(ResultProofAuthority::FreshWholeFunctionChcPdr { authority });
        report.minted += 1;
    }

    report
}
