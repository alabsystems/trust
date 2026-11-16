//! Trust: retain a non-proving source question across a typed lowering decline.
//! No decline is a body proof, source discharge, or monitor certificate.

use super::*;

#[cfg(test)]
mod tests;

#[derive(Debug)]
pub(super) struct Claim {
    source: SourceClauseIdentity,
    marker_id: String,
    vc_index: usize,
}

fn claim(
    function: &trust_types::VerifiableFunction,
    contracts: &trust_types::CompilerContractBundle,
    bundle: &trust_verifier_api::TrustContractBundle,
    vcs: &[VerificationCondition],
    obligation: &trust_verifier_api::TrustObligation,
    vc_index: usize,
    expected_function: &trust_verifier_api::FunctionContext,
) -> Option<Claim> {
    let vc = vcs.get(vc_index)?;
    let bound = trust_source_contract::validated_source_body_decline(function, contracts, vc)?;
    let contract_id = obligation.contract_id.as_deref()?;
    let contract = exactly_one_original_contract(bundle, contract_id)?;
    if !trust_source_contract::source_body_decline_metadata_matches_contract(
        function,
        contracts,
        vc,
        expected_function,
        contract,
        obligation,
    ) {
        return None;
    }
    let source = source_clause_identity_from_contract(
        bundle,
        obligation,
        bound.source_contract_index(),
        contract_id,
    )?;
    let mut markers = bundle
        .obligations
        .iter()
        .filter(|row| source_clause_marker_identity(bundle, row).as_ref() == Some(&source));
    let marker_id = markers.next()?.obligation_id.clone();
    if markers.next().is_some() || marker_id == obligation.obligation_id {
        return None;
    }
    Some(Claim { source, marker_id, vc_index })
}

/// Called only after the complete compiler-authored fresh inventory has been
/// sealed. Public metadata or a serialized Claim cannot recreate this table.
pub(super) fn freeze_from_reference(
    reference: Option<&MonitorReference>,
    function: &trust_types::VerifiableFunction,
    contracts: &trust_types::CompilerContractBundle,
    bundle: &trust_verifier_api::TrustContractBundle,
    vcs: &[VerificationCondition],
    bindings: &BTreeMap<String, ExactFreshVcRekeyBinding>,
    authority: &CompilerFunctionAuthority,
) -> BTreeMap<String, Claim> {
    reference.map_or_else(BTreeMap::new, |reference| {
        reference.freeze_current(function, contracts, bundle, vcs, bindings, authority)
    })
}

/// Compiler constructor output retained before monitor/native rewriting. The
/// source claim is authenticated against the actual query-owned typed input,
/// rather than against the verifier-returned copy of this public row.
pub(super) struct MonitorReference {
    bundle: trust_verifier_api::TrustContractBundle,
    claims: BTreeMap<String, Claim>,
    typed_input_digest: String,
    fresh_payloads: Vec<RowKey>,
}

impl MonitorReference {
    pub(super) fn capture(
        function: &trust_types::VerifiableFunction,
        contracts: &trust_types::CompilerContractBundle,
        bundle: &trust_verifier_api::TrustContractBundle,
        vcs: &[VerificationCondition],
        authority: &CompilerFunctionAuthority,
    ) -> Option<Self> {
        if !vcs.iter().any(|vc| vc.kind.declined_contract_body().is_some())
            || !authority.matches_bundle(bundle)
        {
            return None;
        }
        let stable_crate_id = match authority {
            CompilerFunctionAuthority::Exact { stable_crate_id, .. } => *stable_crate_id,
            #[cfg(test)]
            CompilerFunctionAuthority::CompatibilityForTest { .. } => return None,
        };
        // Rebuild from the actual query/model, not from the submitted public
        // row. The new association admits only declared fixed scalar domains;
        // target-dependent elaborations that differ with no width supplied
        // refuse this correspondence rather than guessing a target width.
        let reference = trust_mir_extract::function_to_verifier_api_bundle_with_compiler_identity(
            function,
            contracts,
            vcs,
            &authority.function().crate_name,
            stable_crate_id,
            None,
        );
        if !authority.matches_bundle(&reference) {
            return None;
        }
        let source_digest = trust_mir_extract::verifier_source_digest(function);
        let multiplicity =
            exact_fresh_vc_match_multiplicity(function, bundle, vcs, &source_digest, authority);
        let claims = bundle
            .obligations
            .iter()
            .filter_map(|obligation| {
                exactly_one_monitor_reference_obligation(&reference, obligation)?;
                let contract =
                    exactly_one_original_contract(bundle, obligation.contract_id.as_deref()?)?;
                exactly_one_monitor_reference_contract(&reference, contract)?;
                let index = exact_unique_fresh_vc_index_for_obligation_and_crate_name(
                    function,
                    obligation,
                    vcs,
                    &multiplicity,
                    &source_digest,
                    &authority.function().crate_name,
                )?;
                let claim = claim(
                    function,
                    contracts,
                    bundle,
                    vcs,
                    obligation,
                    index,
                    authority.function(),
                )?;
                Some((obligation.obligation_id.clone(), claim))
            })
            .collect::<BTreeMap<_, _>>();
        if claims.is_empty() {
            return None;
        }
        Some(Self {
            bundle: reference,
            claims,
            typed_input_digest:
                trust_types::expanded_function_identity::expanded_typed_input_digest(
                    function, contracts,
                )?,
            fresh_payloads: vcs.iter().map(RowKey::of).collect::<Option<Vec<_>>>()?,
        })
    }

    /// Run the same query-owned constructor on the independent reference.
    /// Never copy bindings or other metadata from the routed public carrier.
    pub(super) fn bind_query(
        &mut self,
        module: &trust_ir::Module,
        function: &trust_types::VerifiableFunction,
        source: Option<&native_wp_source::CapturedSource>,
    ) -> Result<(), String> {
        native_wp_source::attach(module, function, &mut self.bundle, source)
    }

    fn freeze_current(
        &self,
        function: &trust_types::VerifiableFunction,
        contracts: &trust_types::CompilerContractBundle,
        bundle: &trust_verifier_api::TrustContractBundle,
        vcs: &[VerificationCondition],
        bindings: &BTreeMap<String, ExactFreshVcRekeyBinding>,
        authority: &CompilerFunctionAuthority,
    ) -> BTreeMap<String, Claim> {
        if !authority.matches_bundle(&self.bundle)
            || !authority.matches_bundle(bundle)
            || trust_types::expanded_function_identity::expanded_typed_input_digest(
                function, contracts,
            )
            .as_deref()
                != Some(self.typed_input_digest.as_str())
            || vcs.iter().map(RowKey::of).collect::<Option<Vec<_>>>().as_ref()
                != Some(&self.fresh_payloads)
        {
            return BTreeMap::new();
        }
        self.claims
            .iter()
            .filter_map(|(id, original)| {
                let mut rows = bundle.obligations.iter().filter(|row| &row.obligation_id == id);
                let row = rows.next()?;
                if rows.next().is_some() || bindings.get(id)?.vc_index != original.vc_index {
                    return None;
                }
                exactly_one_monitor_reference_obligation(&self.bundle, row)?;
                let contract = exactly_one_original_contract(bundle, row.contract_id.as_deref()?)?;
                exactly_one_monitor_reference_contract(&self.bundle, contract)?;
                let current = claim(
                    function,
                    contracts,
                    bundle,
                    vcs,
                    row,
                    original.vc_index,
                    authority.function(),
                )?;
                (current.source == original.source && current.marker_id == original.marker_id)
                    .then_some((id.clone(), current))
            })
            .collect()
    }
}

pub(super) fn stamp_monitors(
    tcx: TyCtxt<'_>,
    body: &Body<'_>,
    reference: &MonitorReference,
    bundle: &mut trust_verifier_api::TrustContractBundle,
) {
    let Some(local) = body.source.def_id().as_local() else { return };
    let authority = CompilerFunctionAuthority::exact(
        trust_verifier_api::FunctionContext {
            crate_name: tcx.crate_name(body.source.def_id().krate).to_string(),
            path: trust_mir_extract::safe_def_path_str(tcx, body.source.def_id()),
        },
        tcx.stable_crate_id(body.source.def_id().krate).as_u64(),
    );
    let records = tcx.sess.with_trust_compiler_state::<SessionCertifiedMonitors, _>(|state| {
        state.functions.get(&local).cloned().unwrap_or_default()
    });
    stamp_monitors_from_records(&records, &authority, reference, bundle);
}

fn stamp_monitors_from_records(
    records: &[ClauseMonitorRecord],
    authority: &CompilerFunctionAuthority,
    reference: &MonitorReference,
    bundle: &mut trust_verifier_api::TrustContractBundle,
) {
    let authenticated =
        authority.matches_bundle(&reference.bundle) && authority.matches_bundle(bundle);
    let eligible = bundle
        .obligations
        .iter()
        .filter_map(|obligation| {
            if !authenticated
                || bundle
                    .obligations
                    .iter()
                    .filter(|row| row.obligation_id == obligation.obligation_id)
                    .count()
                    != 1
            {
                return None;
            }
            let claim = reference.claims.get(&obligation.obligation_id)?;
            exactly_one_monitor_reference_obligation(&reference.bundle, obligation)?;
            let contract = exactly_one_monitor_contract(
                &bundle.contracts,
                &claim.source.contract_id,
            )
            .filter(|contract| {
                exactly_one_monitor_reference_contract(&reference.bundle, contract).is_some()
            })?;
            let mut candidates =
                records.iter().filter(|record| record.source_index == claim.source.index);
            let record = candidates.next()?;
            if candidates.next().is_some()
                || record.typed_proposition_digest.is_none()
                || !monitor_record_matches_public_contract(
                    record,
                    contract,
                    &authority.function().path,
                )
            {
                return None;
            }
            Some((obligation.obligation_id.clone(), record))
        })
        .collect::<BTreeMap<_, _>>();
    for obligation in &mut bundle.obligations {
        if !reference.claims.contains_key(&obligation.obligation_id)
            && !matches!(&obligation.kind, trust_verifier_api::ObligationKind::Custom { namespace, name }
                if namespace == "trust.vc" && name == "declined_contract_body")
        {
            continue;
        }
        // This retains Monitored only when the original kernel-certified
        // evaluator also passed the existing actual MIR placement preflight.
        // Provisional certification and every refusal stay non-executable.
        if let Some(record) = eligible.get(&obligation.obligation_id) {
            stamp_clause_monitor_metadata(&mut obligation.metadata, record);
        } else {
            let digest = fallback_public_obligation_monitor_digest(obligation);
            stamp_unmatched_public_monitor_metadata(
                &mut obligation.metadata,
                "no exact current typed decline matched the live certified monitor",
                digest,
            );
        }
    }
}

fn original_evidence<'a>(
    run: &'a trust_verifier_api::VerificationRunResult,
    id: &str,
) -> Option<&'a trust_verifier_api::ObligationEvidence> {
    if run.skipped.iter().any(|row| row.obligation_id == id) {
        return None;
    }
    let mut rows = run.evidence.iter().filter(|row| row.obligation_id == id);
    let row = rows.next()?;
    rows.next().is_none().then_some(row)
}

fn clean_unsupported(evidence: &trust_verifier_api::ObligationEvidence) -> bool {
    evidence.status == trust_verifier_api::EvidenceStatus::Unsupported
        && evidence.proof_strength.is_none()
        && evidence.artifacts.is_empty()
        && evidence.counterexample.is_none()
        && evidence.decline.is_none()
}

fn retain_rejected_marker_stop(
    result: &mut VerificationResult,
    evidence: &trust_verifier_api::ObligationEvidence,
) {
    use trust_types::determinism::StopCause;
    let VerificationResult::Unknown { reason, .. } = result else { return };
    let original = evidence.diagnostics.join("; ");
    let mut cause = match evidence.status {
        trust_verifier_api::EvidenceStatus::Timeout
        | trust_verifier_api::EvidenceStatus::Canceled => StopCause::WallBackstop,
        _ => StopCause::Unclassified,
    };
    for fact in
        [StopCause::from_reason(&original), StopCause::from_reason(reason)].into_iter().flatten()
    {
        cause = StopCause::combine(cause, fact);
    }
    *reason = cause.stamp(&format!(
        "{reason}; original source evidence {:?} cannot be explained by a clean typed body decline; {original}",
        evidence.status,
    ));
}

fn decline_reason(
    description: &str,
    evidence: &trust_verifier_api::ObligationEvidence,
    latest: &trust_verifier_api::ObligationEvidence,
    current: &VerificationResult,
    marker: bool,
) -> Option<String> {
    use trust_types::determinism::StopCause;
    let VerificationResult::Unknown { solver, reason, .. } = current else { return None };
    let original = evidence.diagnostics.join("; ");
    let latest_diagnostics = latest.diagnostics.join("; ");
    let mut reason_out =
        StopCause::Unsupported.stamp(&format!("{description}; {original}; {latest_diagnostics}"));
    match evidence.status {
        trust_verifier_api::EvidenceStatus::Timeout
        | trust_verifier_api::EvidenceStatus::Canceled => {
            reason_out = StopCause::WallBackstop.stamp(&reason_out);
        }
        trust_verifier_api::EvidenceStatus::Unknown => {
            reason_out = StopCause::from_reason(&original)
                .unwrap_or(StopCause::Unclassified)
                .stamp(&reason_out);
        }
        _ => {}
    }
    // The ordinary importer adds its own default Unclassified token when a
    // producer supplied no cause. Only that exact import, or this phase's
    // pending marker, can be explained by the freshly sealed typed decline.
    // Any later unexplained work or stronger stop remains a blocker.
    if !(marker
        && solver.as_str() == "trust-exact-source-clause-discharge"
        && StopCause::from_reason(reason).is_none())
        && reason != &evidence_unknown_reason(evidence)
    {
        reason_out =
            StopCause::from_reason(reason).unwrap_or(StopCause::Unclassified).stamp(&reason_out);
    }
    Some(reason_out)
}

fn evidence_pair<'a, 'b>(
    original: &'a trust_verifier_api::VerificationRunResult,
    current: &'b trust_verifier_api::VerificationRunResult,
    id: &str,
    result: &mut VerificationResult,
) -> Option<(&'a trust_verifier_api::ObligationEvidence, &'b trust_verifier_api::ObligationEvidence)>
{
    use trust_types::determinism::StopCause;
    let before = original_evidence(original, id);
    let after = original_evidence(current, id);
    // These facts must survive even if a sibling row later blocks association.
    if let VerificationResult::Unknown { reason, .. } = result {
        for evidence in [before, after].into_iter().flatten() {
            if let Some(cause) = StopCause::from_reason(&evidence.diagnostics.join("; ")) {
                *reason = cause.stamp(reason);
            }
        }
    }
    if let (Some(before), Some(after)) = (before, after)
        && clean_unsupported(before)
        && clean_unsupported(after)
    {
        return Some((before, after));
    }
    if env_flag_enabled("TRUST_NATIVE_DEBUG") {
        eprintln!(
            "[SOURCE_BODY_DECLINE_EVIDENCE_REFUSED] id={id} original={before:?} current={after:?}"
        );
    }
    for evidence in [before, after].into_iter().flatten() {
        retain_rejected_marker_stop(result, evidence);
    }
    if (before.is_none() || after.is_none())
        && let VerificationResult::Unknown { reason, .. } = result
    {
        *reason = StopCause::Unclassified
            .stamp(&format!("{reason}; missing unique original/current decline evidence"));
    }
    None
}

fn invalidate_owned_classifications(results: &mut [(VerificationCondition, VerificationResult)]) {
    for (_, result) in results {
        if let VerificationResult::Unknown { solver, reason, .. } = result
            && solver.as_str() == "trust-source-body-decline"
        {
            *reason = trust_types::determinism::StopCause::Unclassified
                .stamp(&format!("{reason}; current decline correspondence no longer qualifies",));
        }
    }
}

/// Reclassify only the actual non-proving decline and its authored question.
/// Whole-carrier freshness is mandatory even if the selected row is unchanged.
/// This installs neither proof authority nor runtime-monitor authority.
pub(super) fn apply(
    bundle: &trust_verifier_api::TrustContractBundle,
    original_run: &trust_verifier_api::VerificationRunResult,
    run: &trust_verifier_api::VerificationRunResult,
    vcs: &[VerificationCondition],
    snapshot: &ExactFreshVcRekeySnapshot,
    results: &mut [(VerificationCondition, VerificationResult)],
    bindings: &[Option<ResultObligationBinding>],
    authorities: &[Option<ResultProofAuthority>],
) -> usize {
    if vcs.is_empty()
        || !snapshot.complete
        || snapshot.source_body_declines.is_empty()
        || results.len() != bindings.len()
        || results.len() != authorities.len()
        || trust_types::verify_budget::exhausted_readonly()
        || !exact_fresh_vc_rekey_run_is_complete(bundle, original_run, vcs, snapshot)
        || !exact_fresh_vc_rekey_run_is_complete(bundle, run, vcs, snapshot)
    {
        invalidate_owned_classifications(results);
        return 0;
    }
    let Some(rows) = bound_result_rows(snapshot, results, bindings) else {
        invalidate_owned_classifications(results);
        return 0;
    };
    let mut changed = 0;
    for (id, claim) in &snapshot.source_body_declines {
        let (Some(&body), Some(&marker)) =
            (rows.get(id.as_str()), rows.get(claim.marker_id.as_str()))
        else {
            continue;
        };
        let marker_pair = if authorities[marker].is_none() {
            evidence_pair(original_run, run, &claim.marker_id, &mut results[marker].1)
        } else {
            None
        };
        if authorities[body].is_some()
            || RowKey::of(&results[body].0) != vcs.get(claim.vc_index).and_then(RowKey::of)
        {
            continue;
        }
        let Some((evidence, latest)) = evidence_pair(original_run, run, id, &mut results[body].1)
        else {
            continue;
        };
        let Some(reason) = decline_reason(
            "authored postcondition body lowering declined at an unconstrained return call",
            evidence,
            latest,
            &results[body].1,
            false,
        ) else {
            continue;
        };
        results[body].1 = VerificationResult::Unknown {
            solver: "trust-source-body-decline".into(),
            time_ms: 0,
            reason,
        };
        changed += 1;
        if authorities[marker].is_some() {
            continue;
        }
        let Some((marker_evidence, latest_marker)) = marker_pair else { continue };
        // VCgen's structural refusal is not the stop cause of an independent
        // native attempt on the authored proposition. Keep the native owner's
        // existing qualified pre-solve/fidelity boundary; generic post-solve
        // Unsupported remains unexplained even with a fresh VCgen decline.
        if trust_verifier_api::qualified_native_structural_stop(marker_evidence).is_none()
            || trust_verifier_api::qualified_native_structural_stop(latest_marker).is_none()
        {
            if env_flag_enabled("TRUST_NATIVE_DEBUG") {
                eprintln!(
                    "[SOURCE_BODY_DECLINE_NATIVE_ORIGIN_REFUSED] id={} original={marker_evidence:?} current={latest_marker:?}",
                    claim.marker_id
                );
            }
            retain_rejected_marker_stop(&mut results[marker].1, marker_evidence);
            retain_rejected_marker_stop(&mut results[marker].1, latest_marker);
            continue;
        }
        let Some(reason) = decline_reason(
            "authored postcondition remains unproved: its exact current body has a typed lowering decline",
            marker_evidence,
            latest_marker,
            &results[marker].1,
            true,
        ) else {
            continue;
        };
        results[marker].1 = VerificationResult::Unknown {
            solver: "trust-source-body-decline".into(),
            time_ms: 0,
            reason,
        };
        changed += 1;
    }
    changed
}

/// Exactly the non-admission catalog population, sealed to current rows.
/// Equal cardinality plus membership in the unfiltered catalog is insufficient:
/// a synthetic admission must not replace an unrelated real obligation.
fn bound_result_rows<'a>(
    snapshot: &ExactFreshVcRekeySnapshot,
    results: &[(VerificationCondition, VerificationResult)],
    bindings: &'a [Option<ResultObligationBinding>],
) -> Option<BTreeMap<&'a str, usize>> {
    if results.len() != bindings.len()
        || results.len()
            != snapshot.catalog_obligations.iter().filter(|row| !row.is_default_admission()).count()
    {
        return None;
    }
    let catalog = snapshot
        .catalog_obligations
        .iter()
        .map(|row| (row.obligation_id.as_str(), row))
        .collect::<BTreeMap<_, _>>();
    let mut rows = BTreeMap::new();
    for (index, ((vc, _), binding)) in results.iter().zip(bindings).enumerate() {
        let binding = binding.as_ref().filter(|binding| binding.matches_row(index, vc))?;
        if binding.canonical_obligation.is_default_admission()
            || catalog.get(binding.public_obligation_id.as_str()).copied()
                != Some(&binding.canonical_obligation)
            || rows.insert(binding.public_obligation_id.as_str(), index).is_some()
        {
            return None;
        }
    }
    Some(rows)
}
