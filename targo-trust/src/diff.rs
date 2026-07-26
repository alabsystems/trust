// targo trust diff: Compare verification state against a baseline JSON report
//
// Loads a baseline `JsonProofReport` (or legacy `SavedReport`) and compares
// against a current report. Produces function-level diff with color-coded
// terminal output. Exits non-zero on regressions for CI gate use.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::BTreeMap;
use std::path::Path;
use std::process::ExitCode;

use serde::de::DeserializeOwned;
use serde::{Deserialize, Serialize};
use trust_types::{
    FunctionVerdict, JsonProofReport, ObligationProofEvidenceReport,
    ObligationTransportEvidenceReport, ProofEvidence, ProofStrength, SavedReportSanitization,
    UntrustedSavedObligationClaim, UntrustedSavedOutcomeClaim, UntrustedSavedReportClaims,
};

use crate::input_limits::{MAX_SAVED_PROOF_REPORT_BYTES, read_bounded_file};
use crate::types::OutputFormat;

// ---------------------------------------------------------------------------
// Diff data structures
// ---------------------------------------------------------------------------

/// The status of a function in a verification report, normalized for comparison.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) enum FunctionStatus {
    Verified,
    RuntimeChecked,
    HasViolations,
    Inconclusive,
    NoObligations,
}

impl FunctionStatus {
    fn from_verdict(v: FunctionVerdict) -> Self {
        match v {
            FunctionVerdict::Verified => Self::Verified,
            FunctionVerdict::RuntimeChecked => Self::RuntimeChecked,
            FunctionVerdict::HasViolations => Self::HasViolations,
            FunctionVerdict::Inconclusive => Self::Inconclusive,
            FunctionVerdict::NoObligations => Self::NoObligations,
            _ => Self::Inconclusive, // future-proof for non_exhaustive
        }
    }

    fn label(self) -> &'static str {
        match self {
            Self::Verified => "proved",
            Self::RuntimeChecked => "runtime_checked",
            Self::HasViolations => "failed",
            Self::Inconclusive => "unknown",
            Self::NoObligations => "no_obligations",
        }
    }

    /// True if this status represents a "good" state (proved or no obligations).
    fn is_good(self) -> bool {
        matches!(self, Self::Verified | Self::NoObligations | Self::RuntimeChecked)
    }
}

/// Per-function snapshot: status + obligation counts.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub(crate) struct FunctionSnapshot {
    pub status: FunctionStatus,
    pub proved: usize,
    pub runtime_checked: usize,
    pub failed: usize,
    pub unknown: usize,
    pub total: usize,
}

/// Direction of change for a single function.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) enum ChangeDirection {
    /// Function went from bad to good (e.g., failed -> proved).
    Improved,
    /// Function went from good to bad (e.g., proved -> failed).
    Regressed,
    /// Function is new in the current report.
    Added,
    /// Function was removed from the current report.
    Removed,
    /// Obligation counts changed but verdict stayed the same.
    ObligationChanged,
    /// No change.
    Unchanged,
}

impl ChangeDirection {
    #[cfg(test)]
    fn label(self) -> &'static str {
        match self {
            Self::Improved => "improved",
            Self::Regressed => "REGRESSED",
            Self::Added => "added",
            Self::Removed => "removed",
            Self::ObligationChanged => "changed",
            Self::Unchanged => "unchanged",
        }
    }
}

/// A single entry in the diff report.
#[derive(Debug, Clone, Serialize)]
pub(crate) struct DiffEntry {
    pub function: String,
    pub direction: ChangeDirection,
    /// Whether this entry contributes to the CI regression count. Added and
    /// removed entries retain their useful direction labels while still making
    /// their fail-closed gate effect explicit.
    pub is_regression: bool,
    pub baseline: Option<FunctionSnapshot>,
    pub current: Option<FunctionSnapshot>,
}

/// Complete diff report between baseline and current verification state.
#[derive(Debug, Clone, Serialize)]
pub(crate) struct FullDiffReport {
    // Baseline summary
    pub baseline_functions: usize,
    pub baseline_proved: usize,
    pub baseline_failed: usize,
    pub baseline_unknown: usize,
    pub baseline_total_obligations: usize,

    // Current summary
    pub current_functions: usize,
    pub current_proved: usize,
    pub current_failed: usize,
    pub current_unknown: usize,
    pub current_total_obligations: usize,

    // Diff counts
    pub improvements: usize,
    pub regressions: usize,
    pub added: usize,
    pub removed: usize,
    pub obligation_changes: usize,
    pub unchanged: usize,

    // Detailed entries (only changed functions)
    pub entries: Vec<DiffEntry>,

    /// Reasons the two reports cannot be compared as the same verification
    /// experiment. A policy/identity mismatch is itself a fail-closed CI-gate
    /// failure; otherwise changing the subject or weakening verification could
    /// make disappearing proof coverage look like an improvement.
    pub compatibility_errors: Vec<String>,

    /// Raw serialized claims retained strictly for observational saved-report
    /// comparison. These never contribute proof credit to either report.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub non_authoritative_saved_claims: Option<NonAuthoritativeSavedClaimDiff>,

    // CI gate: true if any proof coverage regressed or the reports are not
    // policy/identity compatible.
    pub has_regressions: bool,
}

/// Comparison of explicitly untrusted serialized claims.
#[derive(Debug, Clone, Serialize)]
pub(crate) struct NonAuthoritativeSavedClaimDiff {
    /// Machine-readable warning: these claims carry no proof authority.
    pub authority: &'static str,
    pub baseline_claimed_proved: usize,
    pub current_claimed_proved: usize,
    pub baseline_claimed_runtime_checked: usize,
    pub current_claimed_runtime_checked: usize,
    pub regressions: Vec<NonAuthoritativeClaimRegression>,
}

/// A prior favorable serialized claim weakened in the current serialized row.
#[derive(Debug, Clone, Serialize)]
pub(crate) struct NonAuthoritativeClaimRegression {
    pub function: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub obligation_id: Option<String>,
    pub obligation_index: usize,
    pub baseline_claim: &'static str,
    pub current_claim: &'static str,
}

// ---------------------------------------------------------------------------
// Building the diff
// ---------------------------------------------------------------------------

/// Extract a function name -> snapshot map from a `JsonProofReport`.
fn extract_function_map(
    report: &JsonProofReport,
) -> (BTreeMap<String, FunctionSnapshot>, Vec<String>) {
    let mut map = BTreeMap::new();
    let mut duplicates = Vec::new();
    for func in &report.functions {
        let snap = FunctionSnapshot {
            status: FunctionStatus::from_verdict(func.summary.verdict),
            proved: func.summary.proved,
            runtime_checked: func.summary.runtime_checked,
            failed: func.summary.failed,
            unknown: func.summary.unknown,
            total: func.summary.total_obligations,
        };
        if map.contains_key(&func.function) {
            duplicates.push(func.function.clone());
        } else {
            map.insert(func.function.clone(), snap);
        }
    }
    (map, duplicates)
}

/// Build a full diff report from two `JsonProofReport` instances.
pub(crate) fn build_diff(baseline: &JsonProofReport, current: &JsonProofReport) -> FullDiffReport {
    build_diff_impl(baseline, current, true)
}

fn build_diff_impl(
    baseline: &JsonProofReport,
    current: &JsonProofReport,
    require_live_success_gate: bool,
) -> FullDiffReport {
    let (base_map, baseline_duplicates) = extract_function_map(baseline);
    let (curr_map, current_duplicates) = extract_function_map(current);
    let mut compatibility_errors =
        comparison_compatibility_errors(baseline, current, require_live_success_gate);
    compatibility_errors.extend(
        baseline_duplicates.into_iter().map(|function| {
            format!("baseline report has duplicate function identity `{function}`")
        }),
    );
    compatibility_errors.extend(
        current_duplicates
            .into_iter()
            .map(|function| format!("current report has duplicate function identity `{function}`")),
    );
    let strict_lane = current
        .verification_gate
        .as_ref()
        .is_some_and(|gate| matches!(gate.lane.as_str(), "strict" | "full-verifier"));

    let mut entries = Vec::new();
    let mut improvements = 0usize;
    let mut regressions = 0usize;
    let mut added = 0usize;
    let mut removed = 0usize;
    let mut obligation_changes = 0usize;
    let mut unchanged = 0usize;

    // Check functions in current report against baseline.
    for (name, curr_snap) in &curr_map {
        if let Some(base_snap) = base_map.get(name) {
            let direction = classify_change(base_snap, curr_snap, strict_lane);
            match direction {
                ChangeDirection::Improved => improvements += 1,
                ChangeDirection::Regressed => regressions += 1,
                ChangeDirection::ObligationChanged => obligation_changes += 1,
                ChangeDirection::Unchanged => {
                    unchanged += 1;
                    continue; // Don't include unchanged in entries
                }
                _ => {}
            }
            entries.push(DiffEntry {
                function: name.clone(),
                direction,
                is_regression: direction == ChangeDirection::Regressed,
                baseline: Some(base_snap.clone()),
                current: Some(curr_snap.clone()),
            });
        } else {
            // New function.
            added += 1;
            // New code with unresolved/refuted obligations expands the
            // unverified surface and must fail the same CI gate even though it
            // remains labelled `Added` in the human diff.
            let is_regression = !curr_snap.status.is_good()
                || curr_snap.failed > 0
                || curr_snap.unknown > 0
                || (strict_lane && curr_snap.runtime_checked > 0);
            if is_regression {
                regressions += 1;
            }
            entries.push(DiffEntry {
                function: name.clone(),
                direction: ChangeDirection::Added,
                is_regression,
                baseline: None,
                current: Some(curr_snap.clone()),
            });
        }
    }

    // Check for removed functions (in baseline but not in current).
    for (name, base_snap) in &base_map {
        if !curr_map.contains_key(name) {
            removed += 1;
            // Every baseline function row is authenticated coverage inventory,
            // including the typed `NoObligations` rows.  Removing one contracts
            // the observed function universe even when it carried no proof
            // obligations; treating that as neutral would let a current report
            // hide an omitted function simply by dropping its inventory row.
            // Keep the useful `Removed` direction, but always fail the CI gate.
            let is_regression = true;
            if is_regression {
                regressions += 1;
            }
            entries.push(DiffEntry {
                function: name.clone(),
                direction: ChangeDirection::Removed,
                is_regression,
                baseline: Some(base_snap.clone()),
                current: None,
            });
        }
    }

    // Sort entries: regressions first, then removed, then added, then changes.
    entries.sort_by_key(|e| match e.direction {
        ChangeDirection::Regressed => 0,
        ChangeDirection::Removed => 1,
        ChangeDirection::Added => 2,
        ChangeDirection::Improved => 3,
        ChangeDirection::ObligationChanged => 4,
        ChangeDirection::Unchanged => 5,
    });

    let has_regressions = regressions > 0 || !compatibility_errors.is_empty();

    FullDiffReport {
        baseline_functions: base_map.len(),
        baseline_proved: baseline.summary.total_proved,
        baseline_failed: baseline.summary.total_failed,
        baseline_unknown: baseline.summary.total_unknown,
        baseline_total_obligations: baseline.summary.total_obligations,

        current_functions: curr_map.len(),
        current_proved: current.summary.total_proved,
        current_failed: current.summary.total_failed,
        current_unknown: current.summary.total_unknown,
        current_total_obligations: current.summary.total_obligations,

        improvements,
        regressions,
        added,
        removed,
        obligation_changes,
        unchanged,

        entries,
        compatibility_errors,
        non_authoritative_saved_claims: None,
        has_regressions,
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
enum UntrustedClaimIdentity {
    Stable {
        function: String,
        obligation_id: String,
        claim_fingerprint: String,
    },
    Positional {
        function: String,
        function_index: usize,
        obligation_index: usize,
        claim_fingerprint: String,
    },
}

fn untrusted_claim_identity(claim: &UntrustedSavedObligationClaim) -> UntrustedClaimIdentity {
    if let Some(obligation_id) = claim.obligation_id() {
        UntrustedClaimIdentity::Stable {
            function: claim.function().to_string(),
            obligation_id: obligation_id.to_string(),
            claim_fingerprint: claim.claim_fingerprint().to_string(),
        }
    } else {
        UntrustedClaimIdentity::Positional {
            function: claim.function().to_string(),
            function_index: claim.function_index(),
            obligation_index: claim.obligation_index(),
            claim_fingerprint: claim.claim_fingerprint().to_string(),
        }
    }
}

fn untrusted_claim_label(claim: UntrustedSavedOutcomeClaim) -> &'static str {
    match claim {
        UntrustedSavedOutcomeClaim::Proved => "claimed_proved",
        UntrustedSavedOutcomeClaim::Failed => "claimed_failed",
        UntrustedSavedOutcomeClaim::Unknown => "claimed_unknown",
        UntrustedSavedOutcomeClaim::RuntimeChecked => "claimed_runtime_checked",
        UntrustedSavedOutcomeClaim::Timeout => "claimed_timeout",
        UntrustedSavedOutcomeClaim::DesignRequirement => "claimed_design_requirement",
    }
}

fn compare_untrusted_saved_claims(
    baseline: &UntrustedSavedReportClaims,
    current: &UntrustedSavedReportClaims,
) -> NonAuthoritativeSavedClaimDiff {
    let mut current_by_identity: BTreeMap<UntrustedClaimIdentity, Vec<UntrustedSavedOutcomeClaim>> =
        BTreeMap::new();
    for claim in current.obligations() {
        current_by_identity
            .entry(untrusted_claim_identity(claim))
            .or_default()
            .push(claim.outcome());
    }

    let baseline_claimed_proved = baseline
        .obligations()
        .iter()
        .filter(|claim| claim.outcome() == UntrustedSavedOutcomeClaim::Proved)
        .count();
    let current_claimed_proved = current
        .obligations()
        .iter()
        .filter(|claim| claim.outcome() == UntrustedSavedOutcomeClaim::Proved)
        .count();
    let baseline_claimed_runtime_checked = baseline
        .obligations()
        .iter()
        .filter(|claim| claim.outcome() == UntrustedSavedOutcomeClaim::RuntimeChecked)
        .count();
    let current_claimed_runtime_checked = current
        .obligations()
        .iter()
        .filter(|claim| claim.outcome() == UntrustedSavedOutcomeClaim::RuntimeChecked)
        .count();
    let mut regressions = Vec::new();

    // Match the stronger claim first so a duplicate current `proved` row
    // cannot satisfy both a baseline `proved` and `runtime_checked` row.
    for baseline_outcome in
        [UntrustedSavedOutcomeClaim::Proved, UntrustedSavedOutcomeClaim::RuntimeChecked]
    {
        for baseline_claim in
            baseline.obligations().iter().filter(|claim| claim.outcome() == baseline_outcome)
        {
            let preserves_baseline = |current: UntrustedSavedOutcomeClaim| match baseline_outcome {
                UntrustedSavedOutcomeClaim::Proved => current == UntrustedSavedOutcomeClaim::Proved,
                UntrustedSavedOutcomeClaim::RuntimeChecked => matches!(
                    current,
                    UntrustedSavedOutcomeClaim::Proved | UntrustedSavedOutcomeClaim::RuntimeChecked
                ),
                _ => false,
            };
            let identity = untrusted_claim_identity(baseline_claim);
            let current_claim = current_by_identity.get_mut(&identity).and_then(|claims| {
                let index = claims.iter().position(|claim| preserves_baseline(*claim)).unwrap_or(0);
                (!claims.is_empty()).then(|| claims.swap_remove(index))
            });
            if current_claim.is_some_and(preserves_baseline) {
                continue;
            }
            regressions.push(NonAuthoritativeClaimRegression {
                function: baseline_claim.function().to_string(),
                obligation_id: baseline_claim.obligation_id().map(str::to_string),
                obligation_index: baseline_claim.obligation_index(),
                baseline_claim: untrusted_claim_label(baseline_outcome),
                current_claim: current_claim.map(untrusted_claim_label).unwrap_or("missing"),
            });
        }
    }

    NonAuthoritativeSavedClaimDiff {
        authority: "untrusted_observational_only_no_proof_credit",
        baseline_claimed_proved,
        current_claimed_proved,
        baseline_claimed_runtime_checked,
        current_claimed_runtime_checked,
        regressions,
    }
}

fn build_loaded_diff(baseline: &LoadedReport, current: &LoadedReport) -> FullDiffReport {
    // Saved reports have deliberately had every unreplayed `Proved` or
    // `RuntimeChecked` row and successful gate downgraded. Requiring that sanitized DTO to retain a
    // successful gate would make even two identical genuine saved reports
    // incomparable. Policy/count integrity still applies; only the live-gate
    // success precondition is omitted for this explicitly observational path.
    let mut diff = build_diff_impl(&baseline.report, &current.report, false);
    let claim_diff =
        compare_untrusted_saved_claims(&baseline.untrusted_claims, &current.untrusted_claims);
    if !claim_diff.regressions.is_empty() {
        diff.has_regressions = true;
    }
    diff.non_authoritative_saved_claims = Some(claim_diff);
    diff
}

/// Fail closed unless reports describe the same authenticated subject and the
/// same verification policy. Result fields (verdict, decision, timings, and
/// hardened evidence inventories) are intentionally excluded: those are the
/// things being compared, not prerequisites for comparison.
fn canonical_verification_lane(lane: &str) -> Option<&'static str> {
    match lane {
        "advisory" | "default" => Some("advisory"),
        "memory-safe" => Some("memory-safe"),
        "strict" | "full-verifier" => Some("strict"),
        _ => None,
    }
}

fn comparison_compatibility_errors(
    baseline: &JsonProofReport,
    current: &JsonProofReport,
    require_live_success_gate: bool,
) -> Vec<String> {
    let mut errors = Vec::new();

    if baseline.crate_name != current.crate_name {
        errors.push(format!(
            "report subject differs: baseline `{}` vs current `{}`",
            baseline.crate_name, current.crate_name
        ));
    }
    if matches!(
        baseline.crate_name.as_str(),
        "" | "crate" | "unknown" | "empty" | "cargo-targets[]"
    ) || matches!(
        current.crate_name.as_str(),
        "" | "crate" | "unknown" | "empty" | "cargo-targets[]"
    ) {
        errors.push(
            "report subject is an unscoped placeholder; regenerate reports with authenticated package/target identity"
                .to_string(),
        );
    }
    if baseline.metadata.schema_version != current.metadata.schema_version {
        errors.push(format!(
            "report schema version differs: baseline `{}` vs current `{}`",
            baseline.metadata.schema_version, current.metadata.schema_version
        ));
    }
    if baseline.metadata.trust_version != current.metadata.trust_version {
        errors.push(format!(
            "Trust producer version differs: baseline `{}` vs current `{}`",
            baseline.metadata.trust_version, current.metadata.trust_version
        ));
    }

    match (baseline.metadata.timeout_ms, current.metadata.timeout_ms) {
        (Some(baseline_timeout), Some(current_timeout)) if baseline_timeout == current_timeout => {}
        (Some(baseline_timeout), Some(current_timeout)) => errors.push(format!(
            "per-obligation timeout differs: baseline {baseline_timeout}ms vs current {current_timeout}ms"
        )),
        _ => errors.push(
            "per-obligation timeout metadata is missing; regenerate both reports before comparing"
                .to_string(),
        ),
    }

    match (baseline.metadata.function_budget_ms, current.metadata.function_budget_ms) {
        (Some(baseline_budget), Some(current_budget)) if baseline_budget == current_budget => {}
        (Some(baseline_budget), Some(current_budget)) => errors.push(format!(
            "function budget differs: baseline {baseline_budget}ms vs current {current_budget}ms"
        )),
        _ => errors.push(
            "function budget metadata is missing; regenerate both reports before comparing"
                .to_string(),
        ),
    }

    match (&baseline.verification_gate, &current.verification_gate) {
        (Some(baseline_gate), Some(current_gate)) => {
            if canonical_verification_lane(&baseline_gate.lane)
                != canonical_verification_lane(&current_gate.lane)
            {
                errors.push(format!(
                    "verification policy lane differs: baseline `{}` vs current `{}`",
                    baseline_gate.lane, current_gate.lane
                ));
            }
            match (
                baseline_gate.verification_level.as_deref(),
                current_gate.verification_level.as_deref(),
            ) {
                (Some(baseline_level), Some(current_level))
                    if baseline_level == current_level => {}
                (Some(baseline_level), Some(current_level)) => errors.push(format!(
                    "verification level differs: baseline `{baseline_level}` vs current `{current_level}`"
                )),
                _ => errors.push(
                    "verification level metadata is missing; regenerate both reports before comparing"
                        .to_string(),
                ),
            }
            errors.extend(verification_gate_integrity_errors(
                "baseline",
                baseline_gate,
                &baseline.summary,
                require_live_success_gate,
            ));
            errors.extend(verification_gate_integrity_errors(
                "current",
                current_gate,
                &current.summary,
                require_live_success_gate,
            ));
            match (&baseline_gate.test_execution, &current_gate.test_execution) {
                (Some(baseline_execution), Some(current_execution)) => {
                    if baseline_execution.schema != current_execution.schema {
                        errors.push(format!(
                            "certified test execution schema differs: baseline {:?} vs current {:?}",
                            baseline_execution.schema, current_execution.schema
                        ));
                    }
                    if baseline_execution.completion_scope != current_execution.completion_scope {
                        errors.push(
                            "certified test execution completion scope differs between reports"
                                .to_string(),
                        );
                    }
                    if baseline_execution.requested != current_execution.requested {
                        errors.push(
                            "certified test execution request semantics differ between reports"
                                .to_string(),
                        );
                    }
                    if baseline_execution.scope != current_execution.scope {
                        errors.push(format!(
                            "certified test execution scope differs: baseline {:?} vs current {:?}",
                            baseline_execution.scope, current_execution.scope
                        ));
                    }
                    if baseline_execution.compile_only != current_execution.compile_only {
                        errors.push(format!(
                            "certified test execution intent differs: baseline compile_only={} vs current compile_only={}",
                            baseline_execution.compile_only, current_execution.compile_only
                        ));
                    }
                    let baseline_targets = baseline_execution
                        .authorized_executables
                        .iter()
                        .map(|executable| executable.target.as_str())
                        .collect::<std::collections::BTreeSet<_>>();
                    let current_targets = current_execution
                        .authorized_executables
                        .iter()
                        .map(|executable| executable.target.as_str())
                        .collect::<std::collections::BTreeSet<_>>();
                    if baseline_targets != current_targets {
                        errors.push(
                            "certified test executable target inventory differs between reports"
                                .to_string(),
                        );
                    }
                }
                (None, None) => {}
                _ => errors.push(
                    "certified test execution metadata is present in only one report".to_string(),
                ),
            }
        }
        _ => errors.push(
            "verification policy metadata is missing; regenerate both reports before comparing"
                .to_string(),
        ),
    }

    let hardened_policy = |report: &JsonProofReport| {
        report.hardened.as_ref().map(|context| {
            (
                context.profile.clone(),
                context.assurance.as_ref().map(|assurance| {
                    (assurance.proof_evidence_policy.clone(), assurance.proof_evidence_required)
                }),
            )
        })
    };
    let baseline_hardened_policy = hardened_policy(baseline);
    let current_hardened_policy = hardened_policy(current);
    if baseline_hardened_policy != current_hardened_policy {
        errors.push("hardened verification profile/assurance policy differs".to_string());
    }

    errors
}

fn verification_gate_integrity_errors(
    side: &str,
    gate: &trust_types::VerificationGateReport,
    summary: &trust_types::CrateSummary,
    require_live_success_gate: bool,
) -> Vec<String> {
    let mut errors = Vec::new();
    let counts = &gate.counts;
    let partition_total = [
        counts.proved,
        counts.failed,
        counts.unknown,
        counts.runtime_checked,
        counts.assumed,
        counts.mandated,
        counts.contract_panics,
    ]
    .into_iter()
    .try_fold(0usize, usize::checked_add);
    if partition_total != Some(counts.total) {
        errors.push(format!("{side} verification gate counts do not form a disjoint total"));
    }

    let summary_unknown = counts
        .unknown
        .checked_add(counts.assumed)
        .and_then(|unknown| unknown.checked_add(counts.contract_panics));
    if counts.total != summary.total_obligations
        || counts.proved != summary.total_proved
        || counts.failed != summary.total_failed
        || counts.runtime_checked != summary.total_runtime_checked
        || summary_unknown != Some(summary.total_unknown)
        || counts.mandated != summary.total_design_requirements
    {
        errors.push(format!(
            "{side} verification gate counts do not match the sanitized canonical summary"
        ));
    }
    if gate.conditional_on_assumption_rows != (counts.assumed > 0) {
        errors.push(format!(
            "{side} verification gate assumption conditional flag contradicts its counts"
        ));
    }
    if gate.conditional_on_runtime_checks != (counts.runtime_checked > 0) {
        errors.push(format!(
            "{side} verification gate runtime-check conditional flag contradicts its counts"
        ));
    }
    // Dependency and visitation conditionals are crate-scope inventories not
    // represented in CrateSummary, so they cannot be independently recomputed
    // by the diff loader. They remain informational and never make a gate pass.

    let conditional = counts
        .assumed
        .saturating_add(counts.mandated)
        .saturating_add(counts.runtime_checked)
        .saturating_add(counts.contract_panics);
    let unresolved = counts.unknown.saturating_add(conditional);
    let expected_decision = match gate.lane.as_str() {
        "advisory" | "default" if counts.failed > 0 => Some("fail"),
        "advisory" | "default" if counts.unknown > 0 || counts.total == 0 => Some("inconclusive"),
        "advisory" | "default" if conditional > 0 => Some("conditional-pass"),
        "advisory" | "default" => Some("pass"),
        "memory-safe" if counts.failed > 0 => Some("fail"),
        "memory-safe"
            if counts.total == 0
                || counts.unknown > 0
                || counts.mandated > 0
                || counts.runtime_checked > 0
                || counts.contract_panics > 0 =>
        {
            Some("inconclusive")
        }
        "memory-safe" if counts.assumed > 0 => Some("conditional-pass"),
        "memory-safe" => Some("pass"),
        "strict" | "full-verifier" if counts.failed > 0 => Some("fail"),
        "strict" | "full-verifier" if counts.total == 0 || unresolved > 0 => Some("inconclusive"),
        "strict" | "full-verifier" => Some("pass"),
        _ => None,
    };
    match expected_decision {
        Some(expected) if gate.decision == expected => {}
        Some(expected) => errors.push(format!(
            "{side} verification gate decision is inconsistent with its counts: stored `{}`, expected `{expected}`",
            gate.decision
        )),
        None => errors.push(format!(
            "{side} verification gate uses unknown policy lane `{}`",
            gate.lane
        )),
    }

    let accepted_decision = gate.decision == "pass"
        || (matches!(gate.lane.as_str(), "advisory" | "default" | "memory-safe")
            && gate.decision == "conditional-pass");
    if require_live_success_gate && (gate.exit_code != 0 || !accepted_decision) {
        errors.push(format!(
            "{side} verification gate was not successful: lane=`{}`, decision=`{}`, exit_code={}",
            gate.lane, gate.decision, gate.exit_code
        ));
    }
    if let Some(execution) = gate.test_execution.as_ref() {
        errors.extend(certified_test_execution_integrity_errors(side, execution));
    }
    errors
}

fn certified_test_execution_integrity_errors(
    side: &str,
    execution: &trust_types::CertifiedTestExecutionReport,
) -> Vec<String> {
    use trust_types::CertifiedTestExecutionPhaseState;

    let mut errors = Vec::new();
    if execution.schema != trust_types::CERTIFIED_TEST_EXECUTION_SCHEMA_VERSION {
        errors.push(format!(
            "{side} certified test execution uses unsupported nested schema {:?}",
            execution.schema
        ));
    }
    if execution.completion_scope
        != trust_types::CertifiedTestExecutionCompletionScope::TopLevelCargoChildExitOnlyV1
    {
        errors
            .push(format!("{side} certified test execution uses unsupported completion semantics"));
    }
    if !execution.requested {
        errors.push(format!(
            "{side} certified test execution metadata denies that execution was requested"
        ));
    }
    if execution.scope != trust_types::CERTIFIED_TEST_EXECUTION_SCOPE {
        errors.push(format!(
            "{side} certified test execution uses unknown scope {:?}",
            execution.scope
        ));
    }
    if execution.phase_a_success != (execution.phase_a_status == 0) {
        errors.push(format!("{side} certified test phase-A status contradicts its success flag"));
    }
    if !execution.phase_a_success {
        errors.push(format!("{side} certified test phase A was not successful"));
    }

    if execution.compile_only {
        if execution.phase_b_state != CertifiedTestExecutionPhaseState::NotRequested
            || execution.phase_b_exit.is_some()
        {
            errors
                .push(format!("{side} compile-only certified test report claims phase-B activity"));
        }
    } else if execution.phase_b_state != CertifiedTestExecutionPhaseState::CargoInvocationExited
        || execution.phase_b_exit != Some(0)
    {
        errors.push(format!("{side} top-level phase-B Cargo invocation did not exit successfully"));
    }
    if execution.blocker.is_some() {
        errors
            .push(format!("{side} successful certified test report retains an execution blocker"));
    }

    let mut targets = std::collections::BTreeSet::new();
    let mut paths = std::collections::BTreeSet::new();
    for executable in &execution.authorized_executables {
        if executable.target.is_empty()
            || executable.path.is_empty()
            || executable.size == 0
            || !trust_types::digest::is_stable_sha256_hex(&executable.sha256)
        {
            errors.push(format!(
                "{side} certified test executable inventory contains malformed identity metadata"
            ));
            break;
        }
        if !targets.insert(executable.target.as_str()) || !paths.insert(executable.path.as_str()) {
            errors.push(format!(
                "{side} certified test executable inventory contains duplicate target/path identity"
            ));
            break;
        }
    }
    if !execution.compile_only {
        if execution.authorized_executables.is_empty()
            || execution
                .authorized_inventory_sha256
                .as_deref()
                .is_none_or(|digest| !trust_types::digest::is_stable_sha256_hex(digest))
            || execution.target_directory.as_deref().is_none_or(str::is_empty)
        {
            errors.push(format!(
                "{side} exited phase-B Cargo invocation lacks its authenticated executable inventory"
            ));
        }
    }
    errors
}


/// Classify how a function's verification status changed.
fn classify_change(
    baseline: &FunctionSnapshot,
    current: &FunctionSnapshot,
    strict_lane: bool,
) -> ChangeDirection {
    if baseline.status == current.status
        && baseline.proved == current.proved
        && baseline.runtime_checked == current.runtime_checked
        && baseline.failed == current.failed
        && baseline.unknown == current.unknown
        && baseline.total == current.total
    {
        return ChangeDirection::Unchanged;
    }

    // Obligation inventory and proved-coverage contraction are regressions in
    // their own right. Verdict-only comparison would accept 10/10 -> 1/1 as
    // unchanged-good and let nine proved obligations disappear silently.
    if current.total < baseline.total
        || current.proved < baseline.proved
        || (strict_lane && current.runtime_checked > baseline.runtime_checked)
        || current.failed > baseline.failed
        || current.unknown > baseline.unknown
    {
        return ChangeDirection::Regressed;
    }

    let base_good = baseline.status.is_good();
    let curr_good = current.status.is_good();

    if !base_good && curr_good {
        ChangeDirection::Improved
    } else if base_good && !curr_good {
        ChangeDirection::Regressed
    } else {
        // Same category but counts changed.
        ChangeDirection::ObligationChanged
    }
}

// ---------------------------------------------------------------------------
// Rendering
// ---------------------------------------------------------------------------

// ANSI color codes for terminal output.
const RED: &str = "\x1b[31m";
const GREEN: &str = "\x1b[32m";
const YELLOW: &str = "\x1b[33m";
const CYAN: &str = "\x1b[36m";
const BOLD: &str = "\x1b[1m";
const RESET: &str = "\x1b[0m";

/// Check if color output should be used (respects NO_COLOR env var).
fn use_color() -> bool {
    std::env::var("NO_COLOR").is_err()
}

fn color(code: &str, text: &str) -> String {
    if use_color() { format!("{code}{text}{RESET}") } else { text.to_string() }
}

fn bold(text: &str) -> String {
    if use_color() { format!("{BOLD}{text}{RESET}") } else { text.to_string() }
}

impl FullDiffReport {
    pub(crate) fn render(&self, format: OutputFormat) {
        match format {
            OutputFormat::Json => match serde_json::to_string_pretty(self) {
                Ok(json) => println!("{json}"),
                Err(e) => eprintln!("targo trust: failed to serialize diff: {e}"),
            },
            OutputFormat::Terminal | OutputFormat::Html => {
                self.render_terminal();
            }
        }
    }

    fn render_terminal(&self) {
        eprintln!();
        eprintln!("{}", bold("=== Trust Verification Diff ==="));
        eprintln!();

        // Summary comparison
        eprintln!(
            "  Baseline: {} functions, {} proved / {} failed / {} unknown  ({} obligations)",
            self.baseline_functions,
            self.baseline_proved,
            self.baseline_failed,
            self.baseline_unknown,
            self.baseline_total_obligations,
        );
        eprintln!(
            "  Current:  {} functions, {} proved / {} failed / {} unknown  ({} obligations)",
            self.current_functions,
            self.current_proved,
            self.current_failed,
            self.current_unknown,
            self.current_total_obligations,
        );

        // Delta
        let dp = self.current_proved as i64 - self.baseline_proved as i64;
        let df = self.current_failed as i64 - self.baseline_failed as i64;
        let du = self.current_unknown as i64 - self.baseline_unknown as i64;
        let dt = self.current_total_obligations as i64 - self.baseline_total_obligations as i64;
        eprintln!(
            "  Delta:    proved {:+}, failed {:+}, unknown {:+}, obligations {:+}",
            dp, df, du, dt,
        );
        eprintln!();

        if let Some(claims) = &self.non_authoritative_saved_claims {
            eprintln!(
                "  {}",
                color(YELLOW, "Untrusted saved claims (observational only; no proof credit):")
            );
            eprintln!(
                "    baseline claimed proved/runtime-checked: {}/{}, current: {}/{}",
                claims.baseline_claimed_proved,
                claims.baseline_claimed_runtime_checked,
                claims.current_claimed_proved,
                claims.current_claimed_runtime_checked,
            );
            for regression in &claims.regressions {
                let function = crate::solver_detect::terminal_safe(&regression.function);
                let obligation = regression
                    .obligation_id
                    .as_deref()
                    .map(crate::solver_detect::terminal_safe)
                    .unwrap_or_else(|| format!("row#{}", regression.obligation_index));
                eprintln!(
                    "    - CLAIM REGRESSION: {function} [{obligation}] {} -> {}",
                    regression.baseline_claim, regression.current_claim
                );
            }
            eprintln!();
        }

        if !self.compatibility_errors.is_empty() {
            eprintln!("  {}", color(RED, "Reports are not comparison-compatible:"));
            for error in &self.compatibility_errors {
                eprintln!("    - {error}");
            }
            eprintln!();
        }

        // Detailed entries
        if self.entries.is_empty() {
            eprintln!("  No changes detected.");
        } else {
            for entry in &self.entries {
                let (icon, colored_status) = match (entry.direction, entry.is_regression) {
                    (ChangeDirection::Added, true) => {
                        (color(RED, "+"), color(RED, "ADDED (REGRESSION)"))
                    }
                    (ChangeDirection::Removed, true) => {
                        (color(RED, "-"), color(RED, "REMOVED (REGRESSION)"))
                    }
                    (ChangeDirection::Improved, _) => (color(GREEN, "+"), color(GREEN, "IMPROVED")),
                    (ChangeDirection::Regressed, _) => (color(RED, "-"), color(RED, "REGRESSED")),
                    (ChangeDirection::Added, false) => (color(CYAN, "+"), color(CYAN, "ADDED")),
                    (ChangeDirection::Removed, false) => {
                        (color(YELLOW, "-"), color(YELLOW, "REMOVED"))
                    }
                    (ChangeDirection::ObligationChanged, _) => {
                        (color(YELLOW, "~"), color(YELLOW, "CHANGED"))
                    }
                    (ChangeDirection::Unchanged, _) => (" ".to_string(), "unchanged".to_string()),
                };

                let detail = match (&entry.baseline, &entry.current) {
                    (Some(b), Some(c)) => {
                        format!(
                            "{} -> {}  ({}/{} -> {}/{})",
                            b.status.label(),
                            c.status.label(),
                            b.proved,
                            b.total,
                            c.proved,
                            c.total,
                        )
                    }
                    (None, Some(c)) => {
                        format!("(new) {}  ({}/{})", c.status.label(), c.proved, c.total,)
                    }
                    (Some(b), None) => {
                        format!("{} -> (removed)  (was {}/{})", b.status.label(), b.proved, b.total,)
                    }
                    (None, None) => String::new(),
                };

                eprintln!("  [{icon}] {colored_status:>12}  {}  {detail}", bold(&entry.function),);
            }
        }

        eprintln!();

        // Counts summary
        eprintln!(
            "  {} improvements, {} regressions, {} added, {} removed, {} obligation changes",
            color(GREEN, &self.improvements.to_string()),
            color(if self.regressions > 0 { RED } else { GREEN }, &self.regressions.to_string()),
            color(CYAN, &self.added.to_string()),
            color(YELLOW, &self.removed.to_string()),
            self.obligation_changes,
        );

        // CI gate result
        if self.has_regressions {
            eprintln!(
                "  {}",
                color(
                    RED,
                    "FAIL: verification regression or incompatible comparison detected (exit 1)"
                ),
            );
        } else {
            eprintln!("  {}", color(GREEN, "PASS: no verification regressions"),);
        }

        eprintln!("{}", bold("================================"));
    }
}

// ---------------------------------------------------------------------------
// Loading reports from files
// ---------------------------------------------------------------------------

/// A fail-closed saved report together with the receipt from its first and only
/// sanitization pass.
///
/// Observational consumers may inspect `report`, including the `Unknown` rows
/// produced by sanitization. Authority-consuming callers must inspect
/// `sanitization` and either replay the live operation or reject serialized
/// favorable claims; verifier and compiler/monitor authority is deliberately
/// not serializable.
#[derive(Debug)]
pub(crate) struct LoadedReport {
    pub(crate) report: JsonProofReport,
    pub(crate) sanitization: SavedReportSanitization,
    pub(crate) untrusted_claims: UntrustedSavedReportClaims,
}

impl LoadedReport {
    pub(crate) fn provenance_notice(&self, role: &str, path: &Path) -> Option<String> {
        self.sanitization.has_authority_downgrades().then(|| {
            let path = crate::solver_detect::terminal_safe(&path.display().to_string());
            format!(
                "{role} saved report `{path}` contained {} serialized proved and {} runtime-checked obligation(s); loaded them as unknown because live verifier/compiler authority was not replayed",
                self.sanitization.downgraded_proved,
                self.sanitization.downgraded_runtime_checked,
            )
        })
    }

    pub(crate) fn reject_unreplayed_proved_claims(&self, path: &Path) -> Result<(), String> {
        if self.sanitization.has_evidence_defects() {
            let path = crate::solver_detect::terminal_safe(&path.display().to_string());
            return Err(format!(
                "saved report authority gate failed for `{path}`: {} serialized proved obligation(s) lacked live verifier replay authority",
                self.sanitization.evidence_defects
            ));
        }
        Ok(())
    }
}

/// Load either the canonical `JsonProofReport` format or the legacy
/// `SavedReport` format (which only has `results: Vec<VerificationResult>`).
///
/// This is an observational boundary: serialized proof claims are downgraded,
/// not treated as a parse error. The returned sanitization receipt lets each
/// caller choose whether observing the fail-closed report is sufficient or a
/// live verifier replay is required.
pub(crate) fn load_report(path: &Path) -> Result<LoadedReport, String> {
    let canonical_path = path
        .canonicalize()
        .map_err(|e| format!("failed to canonicalize `{}`: {e}", path.display()))?;
    let report_root = canonical_path.parent().ok_or_else(|| {
        format!("saved report `{}` has no canonical parent directory", path.display())
    })?;
    let content = read_bounded_file(&canonical_path, MAX_SAVED_PROOF_REPORT_BYTES)
        .map_err(|e| format!("failed to read `{}`: {e}", path.display()))?;

    // Try canonical format first. The explicit decoder returns the receipt from
    // the first and only sanitization pass; re-sanitizing an already downgraded
    // report would erase whether the input attempted to assert `Proved`.
    if let Ok((report, sanitization, untrusted_claims)) =
        JsonProofReport::decode_saved_json(&content, Some(report_root))
    {
        return Ok(LoadedReport { report, sanitization, untrusted_claims });
    }

    // Try legacy format: { results: [...] }
    if let Ok(legacy) = serde_json::from_slice::<LegacySavedReport>(&content) {
        let mut report = legacy_to_json_proof_report(&legacy);
        let untrusted_claims = UntrustedSavedReportClaims::from_untrusted_report(&report);
        let sanitization = report.sanitize_deserialized_at_root(report_root);
        return Ok(LoadedReport { report, sanitization, untrusted_claims });
    }

    Err(format!("failed to parse `{}` as JsonProofReport or legacy report", path.display()))
}

/// Legacy saved report format for backward compatibility.
#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct LegacySavedReport {
    results: Vec<LegacyResult>,
}

#[derive(Debug, Deserialize)]
struct LegacyResult {
    kind: String,
    message: String,
    outcome: LegacyOutcome,
    backend: String,
    time_ms: Option<u64>,
    #[serde(default)]
    evidence: Option<serde_json::Value>,
    #[serde(default)]
    proof_evidence: Option<serde_json::Value>,
    #[serde(default)]
    transport_evidence: Option<serde_json::Value>,
}

#[derive(Debug, Clone, Copy, Deserialize, PartialEq, Eq)]
enum LegacyOutcome {
    Proved,
    Failed,
    Unknown,
}

#[derive(Debug, Default)]
struct LegacyStructuredEvidence {
    evidence: Option<ProofEvidence>,
    proof_evidence: Option<ObligationProofEvidenceReport>,
    transport_evidence: Option<ObligationTransportEvidenceReport>,
}

impl LegacyStructuredEvidence {
    fn from_result(result: &LegacyResult) -> Self {
        Self {
            evidence: deserialize_legacy_evidence(&result.evidence),
            proof_evidence: deserialize_legacy_evidence(&result.proof_evidence),
            transport_evidence: deserialize_legacy_evidence(&result.transport_evidence),
        }
    }
}

fn deserialize_legacy_evidence<T>(value: &Option<serde_json::Value>) -> Option<T>
where
    T: DeserializeOwned,
{
    value.as_ref().and_then(|value| serde_json::from_value(value.clone()).ok())
}

/// Convert a legacy saved report into the canonical `JsonProofReport` format.
fn legacy_to_json_proof_report(legacy: &LegacySavedReport) -> JsonProofReport {
    use trust_types::*;

    // Group results by kind as pseudo-functions.
    let mut groups: BTreeMap<String, Vec<&LegacyResult>> = BTreeMap::new();
    for r in &legacy.results {
        groups.entry(r.kind.clone()).or_default().push(r);
    }

    let mut functions = Vec::new();
    let mut total_proved = 0usize;
    let mut total_failed = 0usize;
    let mut total_unknown = 0usize;

    for (kind, results) in &groups {
        let obligations: Vec<ObligationReport> =
            results.iter().map(|r| legacy_result_to_obligation(r)).collect();
        let proved = obligations
            .iter()
            .filter(|obligation| matches!(obligation.outcome, ObligationOutcome::Proved { .. }))
            .count();
        let failed = obligations
            .iter()
            .filter(|obligation| matches!(obligation.outcome, ObligationOutcome::Failed { .. }))
            .count();
        let unknown = obligations
            .iter()
            .filter(|obligation| matches!(obligation.outcome, ObligationOutcome::Unknown { .. }))
            .count();
        let total = results.len();

        total_proved += proved;
        total_failed += failed;
        total_unknown += unknown;

        let verdict = if failed > 0 {
            FunctionVerdict::HasViolations
        } else if unknown > 0 {
            FunctionVerdict::Inconclusive
        } else {
            FunctionVerdict::Verified
        };

        let total_time_ms: u64 = results.iter().filter_map(|r| r.time_ms).sum();

        functions.push(FunctionProofReport {
            function: kind.clone(),
            summary: FunctionSummary {
                total_obligations: total,
                proved,
                runtime_checked: 0,
                failed,
                unknown,
                timed_out: 0,
                design_requirements: 0,
                unattributed_failed: 0,
                unattributed_unknown: 0,
                unattributed_proved: 0,
                total_time_ms,
                max_proof_level: Some(ProofLevel::L0Safety),
                verdict,
            },
            obligations,
        });
    }

    let total = total_proved + total_failed + total_unknown;
    let functions_verified =
        functions.iter().filter(|f| f.summary.verdict == FunctionVerdict::Verified).count();
    let functions_with_violations =
        functions.iter().filter(|f| f.summary.verdict == FunctionVerdict::HasViolations).count();
    let functions_inconclusive =
        functions.iter().filter(|f| f.summary.verdict == FunctionVerdict::Inconclusive).count();

    let verdict = if total_failed > 0 {
        CrateVerdict::HasViolations
    } else if total_unknown > 0 {
        CrateVerdict::Inconclusive
    } else if total_proved > 0 {
        CrateVerdict::Verified
    } else {
        CrateVerdict::NoObligations
    };

    JsonProofReport {
        metadata: ReportMetadata {
            schema_version: "1.0".to_string(),
            trust_version: "legacy".to_string(),
            timestamp: String::new(),
            total_time_ms: 0,
            timeout_ms: None,
            function_budget_ms: None,
        },
        crate_name: "unknown".to_string(),
        summary: CrateSummary {
            functions_analyzed: functions.len(),
            functions_verified,
            functions_runtime_checked: 0,
            functions_with_violations,
            functions_inconclusive,
            total_obligations: total,
            total_proved,
            total_runtime_checked: 0,
            total_failed,
            total_unknown,
            total_timed_out: 0,
            total_design_requirements: 0,
            total_unattributed_failed: 0,
            total_unattributed_unknown: 0,
            total_unattributed_proved: 0,
            proof_grade_engine_statuses: summarize_proof_grade_engine_statuses(&functions),
            verdict,
        },
        functions,
        hardened: None,
        assumptions: Vec::new(),
        cargo_proof_inventory: None,
        verification_gate: None,
    }
}

fn legacy_result_to_obligation(result: &LegacyResult) -> trust_types::ObligationReport {
    use trust_types::*;

    let structured_evidence = LegacyStructuredEvidence::from_result(result);
    let evidence = legacy_result_evidence(&structured_evidence);
    let outcome = match result.outcome {
        LegacyOutcome::Proved => ObligationOutcome::Proved {
            strength: legacy_result_proof_strength(&structured_evidence),
        },
        LegacyOutcome::Failed => ObligationOutcome::Failed { counterexample: None },
        LegacyOutcome::Unknown => ObligationOutcome::Unknown { reason: "unknown".to_string() },
    };

    ObligationReport {
        obligation_id: None,
        description: result.message.clone(),
        kind: result.kind.clone(),
        proof_level: ProofLevel::L0Safety,
        location: None,
        outcome,
        solver: result.backend.clone(),
        time_ms: result.time_ms.unwrap_or(0),
        evidence,
        proof_evidence: structured_evidence.proof_evidence,
        transport_evidence: structured_evidence.transport_evidence,
    }
}

fn legacy_result_proof_strength(evidence: &LegacyStructuredEvidence) -> ProofStrength {
    evidence
        .proof_evidence
        .as_ref()
        .map(|proof| proof.strength.clone())
        .or_else(|| {
            evidence
                .transport_evidence
                .as_ref()
                .and_then(|transport| transport.proof_evidence.as_ref())
                .and_then(|proof| proof.strength.clone())
        })
        .unwrap_or_else(ProofStrength::smt_unsat)
}

fn legacy_result_evidence(evidence: &LegacyStructuredEvidence) -> Option<ProofEvidence> {
    evidence
        .evidence
        .clone()
        .or_else(|| evidence.proof_evidence.as_ref().map(|proof| proof.evidence.clone()))
        .or_else(|| {
            evidence
                .transport_evidence
                .as_ref()
                .and_then(|transport| transport.proof_evidence.as_ref())
                .and_then(|proof| proof.evidence.clone())
        })
}

// ---------------------------------------------------------------------------
// Subcommand entry point
// ---------------------------------------------------------------------------

/// Run the `targo trust diff` subcommand.
///
/// Requires `--baseline <path>` pointing to a saved JSON report.
/// Optionally accepts a second positional argument `--current <path>` for
/// comparing two saved reports (otherwise compares baseline against the
/// current verification run or an empty report).
pub(crate) fn run_diff_command(
    baseline_path: &str,
    current_path: Option<&str>,
    format: OutputFormat,
) -> ExitCode {
    // Load baseline.
    let baseline_path = Path::new(baseline_path);
    let baseline = match load_report(baseline_path) {
        Ok(r) => r,
        Err(e) => {
            eprintln!("targo trust: {e}");
            return ExitCode::from(2);
        }
    };
    if let Some(notice) = baseline.provenance_notice("baseline", baseline_path) {
        eprintln!("targo trust diff: {notice}");
    }

    // Load current report (or use an empty one if no current path given).
    let current = if let Some(path) = current_path {
        let path = Path::new(path);
        match load_report(path) {
            Ok(r) => {
                if let Some(notice) = r.provenance_notice("current", path) {
                    eprintln!("targo trust diff: {notice}");
                }
                r
            }
            Err(e) => {
                eprintln!("targo trust: {e}");
                return ExitCode::from(2);
            }
        }
    } else {
        // Show baseline summary against empty.
        eprintln!("targo trust: no --current specified, showing baseline summary against empty");
        LoadedReport {
            report: empty_report(),
            sanitization: SavedReportSanitization::default(),
            untrusted_claims: UntrustedSavedReportClaims::default(),
        }
    };

    let diff = build_loaded_diff(&baseline, &current);
    diff.render(format);

    if diff.has_regressions { ExitCode::FAILURE } else { ExitCode::SUCCESS }
}

/// Create an empty `JsonProofReport` for comparison.
fn empty_report() -> JsonProofReport {
    use trust_types::*;
    JsonProofReport {
        metadata: ReportMetadata {
            schema_version: "1.0".to_string(),
            trust_version: "empty".to_string(),
            timestamp: String::new(),
            total_time_ms: 0,
            timeout_ms: None,
            function_budget_ms: None,
        },
        crate_name: "empty".to_string(),
        summary: CrateSummary {
            functions_analyzed: 0,
            functions_verified: 0,
            functions_runtime_checked: 0,
            functions_with_violations: 0,
            functions_inconclusive: 0,
            total_obligations: 0,
            total_proved: 0,
            total_runtime_checked: 0,
            total_failed: 0,
            total_unknown: 0,
            total_timed_out: 0,
            total_design_requirements: 0,
            total_unattributed_failed: 0,
            total_unattributed_unknown: 0,
            total_unattributed_proved: 0,
            proof_grade_engine_statuses: summarize_proof_grade_engine_statuses(&[]),
            verdict: CrateVerdict::Verified,
        },
        functions: vec![],
        hardened: None,
        assumptions: Vec::new(),
        cargo_proof_inventory: None,
        verification_gate: None,
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use std::path::PathBuf;
    use std::time::{SystemTime, UNIX_EPOCH};
    use std::{env, fs};

    use trust_types::*;

    use super::*;

    fn make_report(
        functions: Vec<(&str, FunctionVerdict, usize, usize, usize)>,
    ) -> JsonProofReport {
        let mut funcs = Vec::new();
        let mut tp = 0;
        let mut tf = 0;
        let mut tu = 0;

        for (name, verdict, proved, failed, unknown) in &functions {
            tp += proved;
            tf += failed;
            tu += unknown;
            let total = proved + failed + unknown;

            let obligations = Vec::new(); // not needed for diff tests

            funcs.push(FunctionProofReport {
                function: name.to_string(),
                summary: FunctionSummary {
                    total_obligations: total,
                    proved: *proved,
                    runtime_checked: 0,
                    failed: *failed,
                    unknown: *unknown,
                    timed_out: 0,
                    design_requirements: 0,
                    unattributed_failed: 0,
                    unattributed_unknown: 0,
                    unattributed_proved: 0,
                    total_time_ms: 0,
                    max_proof_level: Some(ProofLevel::L0Safety),
                    verdict: *verdict,
                },
                obligations,
            });
        }

        let fv = funcs.iter().filter(|f| f.summary.verdict == FunctionVerdict::Verified).count();
        let fviol =
            funcs.iter().filter(|f| f.summary.verdict == FunctionVerdict::HasViolations).count();
        let finc =
            funcs.iter().filter(|f| f.summary.verdict == FunctionVerdict::Inconclusive).count();

        let verdict = if tf > 0 {
            CrateVerdict::HasViolations
        } else if tu > 0 {
            CrateVerdict::Inconclusive
        } else if tp > 0 {
            CrateVerdict::Verified
        } else {
            CrateVerdict::NoObligations
        };

        JsonProofReport {
            metadata: ReportMetadata {
                schema_version: "1.0".to_string(),
                trust_version: "test".to_string(),
                timestamp: String::new(),
                total_time_ms: 0,
                timeout_ms: Some(5_000),
                function_budget_ms: Some(120_000),
            },
            crate_name: "test_crate".to_string(),
            summary: CrateSummary {
                functions_analyzed: funcs.len(),
                functions_verified: fv,
                functions_runtime_checked: 0,
                functions_with_violations: fviol,
                functions_inconclusive: finc,
                total_obligations: tp + tf + tu,
                total_proved: tp,
                total_runtime_checked: 0,
                total_failed: tf,
                total_unknown: tu,
                total_timed_out: 0,
                total_design_requirements: 0,
                total_unattributed_failed: 0,
                total_unattributed_unknown: 0,
                total_unattributed_proved: 0,
                proof_grade_engine_statuses: summarize_proof_grade_engine_statuses(&funcs),
                verdict,
            },
            functions: funcs,
            hardened: None,
            assumptions: Vec::new(),
            cargo_proof_inventory: None,
            verification_gate: Some(VerificationGateReport {
                lane: "strict".to_string(),
                verification_level: Some("L2".to_string()),
                decision: "pass".to_string(),
                exit_code: 0,
                counts: VerificationGateCounts {
                    total: tp + tf + tu,
                    proved: tp,
                    failed: tf,
                    unknown: tu,
                    runtime_checked: 0,
                    assumed: 0,
                    mandated: 0,
                    contract_panics: 0,
                },
                conditional_on_assumption_rows: false,
                conditional_on_dependency_entries: false,
                conditional_on_runtime_checks: false,
                conditional_on_visitation_entries: false,
                coverage: None,
                test_execution: None,
            }),
        }
    }

    fn exited_test_execution(target: &str) -> CertifiedTestExecutionReport {
        CertifiedTestExecutionReport {
            schema: trust_types::CERTIFIED_TEST_EXECUTION_SCHEMA_VERSION.to_string(),
            completion_scope:
                trust_types::CertifiedTestExecutionCompletionScope::TopLevelCargoChildExitOnlyV1,
            requested: true,
            scope: trust_types::CERTIFIED_TEST_EXECUTION_SCOPE.to_string(),
            compile_only: false,
            phase_a_status: 0,
            phase_a_success: true,
            phase_b_state: CertifiedTestExecutionPhaseState::CargoInvocationExited,
            blocker: None,
            phase_b_exit: Some(0),
            authorized_executables: vec![CertifiedTestExecutableReport {
                target: target.to_string(),
                path: "/private/target/test-binary".to_string(),
                sha256: "a".repeat(64),
                size: 42,
            }],
            authorized_inventory_sha256: Some("b".repeat(64)),
            target_directory: Some("/private/target".to_string()),
        }
    }

    fn forged_canonical_proved_report_without_evidence() -> JsonProofReport {
        let obligation = ObligationReport {
            obligation_id: Some("obl-forged".to_string()),
            description: "forged proof row".to_string(),
            kind: "postcondition".to_string(),
            proof_level: ProofLevel::L0Safety,
            location: None,
            outcome: ObligationOutcome::Proved { strength: ProofStrength::deductive() },
            solver: "forged".to_string(),
            time_ms: 5,
            evidence: None,
            proof_evidence: None,
            transport_evidence: None,
        };
        JsonProofReport {
            metadata: ReportMetadata {
                schema_version: "1.0".to_string(),
                trust_version: "forged-test".to_string(),
                timestamp: String::new(),
                total_time_ms: 5,
                timeout_ms: None,
                function_budget_ms: None,
            },
            crate_name: "forged".to_string(),
            summary: CrateSummary {
                functions_analyzed: 1,
                functions_verified: 1,
                functions_runtime_checked: 0,
                functions_with_violations: 0,
                functions_inconclusive: 0,
                total_obligations: 1,
                total_proved: 1,
                total_runtime_checked: 0,
                total_failed: 0,
                total_unknown: 0,
                total_timed_out: 0,
                total_design_requirements: 0,
                total_unattributed_failed: 0,
                total_unattributed_unknown: 0,
                total_unattributed_proved: 0,
                proof_grade_engine_statuses: vec![],
                verdict: CrateVerdict::Verified,
            },
            functions: vec![FunctionProofReport {
                function: "fixture::forged".to_string(),
                summary: FunctionSummary {
                    total_obligations: 1,
                    proved: 1,
                    runtime_checked: 0,
                    failed: 0,
                    unknown: 0,
                    timed_out: 0,
                    design_requirements: 0,
                    unattributed_failed: 0,
                    unattributed_unknown: 0,
                    unattributed_proved: 0,
                    total_time_ms: 5,
                    max_proof_level: Some(ProofLevel::L0Safety),
                    verdict: FunctionVerdict::Verified,
                },
                obligations: vec![obligation],
            }],
            hardened: None,
            assumptions: Vec::new(),
            cargo_proof_inventory: None,
            verification_gate: None,
        }
    }

    fn canonical_runtime_checked_report() -> JsonProofReport {
        let mut report = forged_canonical_proved_report_without_evidence();
        report.metadata.timeout_ms = Some(5_000);
        report.metadata.function_budget_ms = Some(120_000);
        report.functions[0].obligations[0].outcome = ObligationOutcome::RuntimeChecked {
            note: Some("certified monitor installed".to_string()),
        };
        report.functions[0].summary.proved = 0;
        report.functions[0].summary.runtime_checked = 1;
        report.functions[0].summary.verdict = FunctionVerdict::RuntimeChecked;
        report.summary.functions_verified = 0;
        report.summary.functions_runtime_checked = 1;
        report.summary.total_proved = 0;
        report.summary.total_runtime_checked = 1;
        report.summary.verdict = CrateVerdict::RuntimeChecked;
        report.verification_gate = Some(VerificationGateReport {
            lane: "advisory".to_string(),
            verification_level: Some("L0".to_string()),
            decision: "conditional-pass".to_string(),
            exit_code: 0,
            counts: VerificationGateCounts {
                total: 1,
                proved: 0,
                failed: 0,
                unknown: 0,
                runtime_checked: 1,
                assumed: 0,
                mandated: 0,
                contract_panics: 0,
            },
            conditional_on_assumption_rows: false,
            conditional_on_dependency_entries: false,
            conditional_on_runtime_checks: true,
            conditional_on_visitation_entries: false,
            coverage: None,
            test_execution: None,
        });
        report
    }

    fn temp_report_path(name: &str) -> PathBuf {
        let millis = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .expect("system time before epoch")
            .as_millis();
        env::temp_dir().join(format!("trust-diff-{name}-{}-{millis}.json", std::process::id()))
    }

    fn write_json_report(path: &Path, report: &JsonProofReport) {
        fs::write(path, serde_json::to_vec_pretty(report).expect("serialize report"))
            .expect("write report");
    }

    #[test]
    fn test_diff_no_changes() {
        let baseline = make_report(vec![
            ("safe_add", FunctionVerdict::Verified, 2, 0, 0),
            ("safe_div", FunctionVerdict::Verified, 1, 0, 0),
        ]);
        let current = make_report(vec![
            ("safe_add", FunctionVerdict::Verified, 2, 0, 0),
            ("safe_div", FunctionVerdict::Verified, 1, 0, 0),
        ]);

        let diff = build_diff(&baseline, &current);
        assert_eq!(diff.improvements, 0);
        assert_eq!(diff.regressions, 0);
        assert_eq!(diff.added, 0);
        assert_eq!(diff.removed, 0);
        assert_eq!(diff.unchanged, 2);
        assert!(diff.entries.is_empty());
        assert!(!diff.has_regressions);
    }

    #[test]
    fn test_diff_regression() {
        let baseline = make_report(vec![("safe_add", FunctionVerdict::Verified, 2, 0, 0)]);
        let current = make_report(vec![("safe_add", FunctionVerdict::HasViolations, 1, 1, 0)]);

        let diff = build_diff(&baseline, &current);
        assert_eq!(diff.regressions, 1);
        assert_eq!(diff.improvements, 0);
        assert!(diff.has_regressions);
        assert_eq!(diff.entries.len(), 1);
        assert_eq!(diff.entries[0].direction, ChangeDirection::Regressed);
    }

    #[test]
    fn test_diff_improvement() {
        let baseline = make_report(vec![("buggy_fn", FunctionVerdict::HasViolations, 0, 2, 0)]);
        let current = make_report(vec![("buggy_fn", FunctionVerdict::Verified, 2, 0, 0)]);

        let diff = build_diff(&baseline, &current);
        assert_eq!(diff.improvements, 1);
        assert_eq!(diff.regressions, 0);
        assert!(diff.has_regressions, "a failed baseline is not an accepted comparison anchor");
        assert_eq!(diff.entries.len(), 1);
        assert_eq!(diff.entries[0].direction, ChangeDirection::Improved);
    }

    #[test]
    fn test_diff_added_function() {
        let baseline = make_report(vec![("old_fn", FunctionVerdict::Verified, 1, 0, 0)]);
        let current = make_report(vec![
            ("old_fn", FunctionVerdict::Verified, 1, 0, 0),
            ("new_fn", FunctionVerdict::Verified, 2, 0, 0),
        ]);

        let diff = build_diff(&baseline, &current);
        assert_eq!(diff.added, 1);
        assert_eq!(diff.unchanged, 1);
        assert!(!diff.has_regressions);
        assert_eq!(diff.entries.len(), 1);
        assert_eq!(diff.entries[0].direction, ChangeDirection::Added);
        assert_eq!(diff.entries[0].function, "new_fn");
    }

    #[test]
    fn test_diff_removed_function() {
        let baseline = make_report(vec![
            ("old_fn", FunctionVerdict::Verified, 1, 0, 0),
            ("removed_fn", FunctionVerdict::HasViolations, 0, 1, 0),
        ]);
        let current = make_report(vec![("old_fn", FunctionVerdict::Verified, 1, 0, 0)]);

        let diff = build_diff(&baseline, &current);
        assert_eq!(diff.removed, 1);
        assert_eq!(diff.unchanged, 1);
        assert_eq!(diff.regressions, 1);
        assert!(diff.has_regressions);
        assert_eq!(diff.entries.len(), 1);
        assert_eq!(diff.entries[0].direction, ChangeDirection::Removed);
        assert_eq!(diff.entries[0].function, "removed_fn");
    }

    #[test]
    fn test_diff_obligation_count_change() {
        let baseline = make_report(vec![("fn_a", FunctionVerdict::Verified, 2, 0, 0)]);
        let current = make_report(vec![("fn_a", FunctionVerdict::Verified, 3, 0, 0)]);

        let diff = build_diff(&baseline, &current);
        assert_eq!(diff.obligation_changes, 1);
        assert_eq!(diff.regressions, 0);
        assert!(!diff.has_regressions);
        assert_eq!(diff.entries.len(), 1);
        assert_eq!(diff.entries[0].direction, ChangeDirection::ObligationChanged);
    }

    #[test]
    fn test_diff_proved_coverage_contraction_is_regression() {
        let baseline = make_report(vec![("fn_a", FunctionVerdict::Verified, 10, 0, 0)]);
        let current = make_report(vec![("fn_a", FunctionVerdict::Verified, 1, 0, 0)]);

        let diff = build_diff(&baseline, &current);
        assert_eq!(diff.regressions, 1);
        assert!(diff.has_regressions);
        assert_eq!(diff.entries[0].direction, ChangeDirection::Regressed);
    }

    #[test]
    fn test_diff_removed_verified_function_is_regression() {
        let baseline = make_report(vec![("removed_fn", FunctionVerdict::Verified, 3, 0, 0)]);
        let current = make_report(vec![]);

        let diff = build_diff(&baseline, &current);
        assert_eq!(diff.removed, 1);
        assert_eq!(diff.regressions, 1);
        assert!(diff.has_regressions);
        assert_eq!(diff.entries[0].direction, ChangeDirection::Removed);
        assert!(diff.entries[0].is_regression);
    }

    #[test]
    fn test_diff_removed_zero_obligation_inventory_is_regression() {
        let baseline = make_report(vec![("removed_fn", FunctionVerdict::NoObligations, 0, 0, 0)]);
        let current = make_report(vec![]);

        let diff = build_diff(&baseline, &current);
        assert_eq!(diff.removed, 1);
        assert_eq!(diff.regressions, 1);
        assert!(diff.has_regressions);
        assert_eq!(diff.entries[0].direction, ChangeDirection::Removed);
        assert!(diff.entries[0].is_regression);
    }

    #[test]
    fn test_diff_verified_to_no_obligations_is_coverage_regression() {
        let baseline = make_report(vec![("fn_a", FunctionVerdict::Verified, 1, 0, 0)]);
        let current = make_report(vec![("fn_a", FunctionVerdict::NoObligations, 0, 0, 0)]);

        let diff = build_diff(&baseline, &current);
        assert_eq!(diff.regressions, 1);
        assert!(diff.has_regressions);
        assert_eq!(diff.entries[0].direction, ChangeDirection::Regressed);
    }

    #[test]
    fn test_diff_mixed_changes() {
        let baseline = make_report(vec![
            ("proved_fn", FunctionVerdict::Verified, 2, 0, 0),
            ("failed_fn", FunctionVerdict::HasViolations, 0, 1, 0),
            ("will_remove", FunctionVerdict::Verified, 1, 0, 0),
            ("stable_fn", FunctionVerdict::Verified, 1, 0, 0),
        ]);
        let current = make_report(vec![
            ("proved_fn", FunctionVerdict::HasViolations, 1, 1, 0), // regressed
            ("failed_fn", FunctionVerdict::Verified, 1, 0, 0),      // improved
            ("new_fn", FunctionVerdict::Verified, 2, 0, 0),         // added
            ("stable_fn", FunctionVerdict::Verified, 1, 0, 0),      // unchanged
        ]);

        let diff = build_diff(&baseline, &current);
        assert_eq!(diff.regressions, 2);
        assert_eq!(diff.improvements, 1);
        assert_eq!(diff.added, 1);
        assert_eq!(diff.removed, 1);
        assert_eq!(diff.unchanged, 1);
        assert!(diff.has_regressions);

        // Check sort order: regressions first
        assert_eq!(diff.entries[0].direction, ChangeDirection::Regressed);
    }

    #[test]
    fn test_diff_ci_gate_no_regressions() {
        let baseline = make_report(vec![("fn_a", FunctionVerdict::Verified, 1, 0, 0)]);
        let current = make_report(vec![
            ("fn_a", FunctionVerdict::Verified, 1, 0, 0),
            ("fn_b", FunctionVerdict::Verified, 2, 0, 0),
        ]);

        let diff = build_diff(&baseline, &current);
        // Stable proof plus newly proved coverage is safe.
        assert!(!diff.has_regressions);
    }

    #[test]
    fn test_diff_new_failed_or_unknown_function_is_regression() {
        let baseline = make_report(vec![("fn_a", FunctionVerdict::Verified, 1, 0, 0)]);
        let current = make_report(vec![
            ("fn_a", FunctionVerdict::Verified, 1, 0, 0),
            ("failed", FunctionVerdict::HasViolations, 0, 1, 0),
            ("unknown", FunctionVerdict::Inconclusive, 0, 0, 1),
        ]);

        let diff = build_diff(&baseline, &current);
        assert_eq!(diff.added, 2);
        assert_eq!(diff.regressions, 2);
        assert!(diff.has_regressions);
        assert!(diff.entries.iter().all(|entry| {
            entry.function == "fn_a" || entry.direction == ChangeDirection::Added
        }));
        assert!(diff.entries.iter().all(|entry| entry.is_regression));
    }

    #[test]
    fn test_diff_increased_failed_or_unknown_counts_are_regressions() {
        for (baseline, current) in [
            (
                make_report(vec![("fn_a", FunctionVerdict::HasViolations, 0, 1, 0)]),
                make_report(vec![("fn_a", FunctionVerdict::HasViolations, 0, 2, 0)]),
            ),
            (
                make_report(vec![("fn_a", FunctionVerdict::Inconclusive, 0, 0, 1)]),
                make_report(vec![("fn_a", FunctionVerdict::Inconclusive, 0, 0, 2)]),
            ),
        ] {
            let diff = build_diff(&baseline, &current);
            assert_eq!(diff.regressions, 1);
            assert!(diff.has_regressions);
            assert_eq!(diff.entries[0].direction, ChangeDirection::Regressed);
        }
    }

    #[test]
    fn test_diff_json_serialization() {
        let baseline = make_report(vec![("fn_a", FunctionVerdict::Verified, 2, 0, 0)]);
        let current = make_report(vec![("fn_a", FunctionVerdict::HasViolations, 1, 1, 0)]);

        let diff = build_diff(&baseline, &current);
        let json = serde_json::to_string(&diff).expect("should serialize FullDiffReport");
        assert!(json.contains("\"has_regressions\":true"));
        assert!(json.contains("\"regressions\":1"));
        assert!(json.contains("\"Regressed\""));
    }

    #[test]
    fn test_diff_empty_baseline_all_added() {
        let baseline = make_report(vec![]);
        let current = make_report(vec![
            ("fn_a", FunctionVerdict::Verified, 1, 0, 0),
            ("fn_b", FunctionVerdict::HasViolations, 0, 1, 0),
        ]);

        let diff = build_diff(&baseline, &current);
        assert_eq!(diff.added, 2);
        assert_eq!(diff.regressions, 1);
        assert!(diff.has_regressions);
    }

    #[test]
    fn test_diff_empty_current_all_removed() {
        let baseline = make_report(vec![
            ("fn_a", FunctionVerdict::Verified, 1, 0, 0),
            ("fn_b", FunctionVerdict::HasViolations, 0, 1, 0),
        ]);
        let current = make_report(vec![]);

        let diff = build_diff(&baseline, &current);
        assert_eq!(diff.removed, 2);
        assert_eq!(diff.regressions, 2);
        assert!(diff.has_regressions);
    }

    #[test]
    fn test_diff_rejects_incompatible_identity_policy_level_budget_and_version() {
        let baseline = make_report(vec![("fn_a", FunctionVerdict::Verified, 1, 0, 0)]);
        let mut current = baseline.clone();
        current.crate_name = "other_package:other_target".to_string();
        current.metadata.schema_version = "2.0".to_string();
        current.metadata.trust_version = "other-version".to_string();
        current.metadata.timeout_ms = Some(2);
        current.metadata.function_budget_ms = Some(1);
        let gate = current.verification_gate.as_mut().expect("test gate");
        gate.lane = "default".to_string();
        gate.verification_level = Some("L0".to_string());

        let diff = build_diff(&baseline, &current);
        assert!(diff.has_regressions);
        assert_eq!(diff.regressions, 0);
        assert!(diff.compatibility_errors.iter().any(|error| error.contains("subject differs")));
        assert!(diff.compatibility_errors.iter().any(|error| error.contains("schema version")));
        assert!(diff.compatibility_errors.iter().any(|error| error.contains("producer version")));
        assert!(diff.compatibility_errors.iter().any(|error| error.contains("timeout differs")));
        assert!(diff.compatibility_errors.iter().any(|error| error.contains("budget differs")));
        assert!(diff.compatibility_errors.iter().any(|error| error.contains("policy lane")));
        assert!(diff.compatibility_errors.iter().any(|error| error.contains("level differs")));
    }

    #[test]
    fn test_diff_rejects_missing_comparison_policy_metadata() {
        let baseline = make_report(vec![("fn_a", FunctionVerdict::Verified, 1, 0, 0)]);
        let mut current = baseline.clone();
        current.metadata.timeout_ms = None;
        current.metadata.function_budget_ms = None;
        current.verification_gate = None;

        let diff = build_diff(&baseline, &current);
        assert!(diff.has_regressions);
        assert!(diff.compatibility_errors.iter().any(|error| error.contains("timeout metadata")));
        assert!(diff.compatibility_errors.iter().any(|error| error.contains("budget metadata")));
        assert!(diff.compatibility_errors.iter().any(|error| error.contains("policy metadata")));
    }

    #[test]
    fn test_diff_rejects_empty_cargo_target_aggregate_subject() {
        let mut report = make_report(vec![("fn_a", FunctionVerdict::Verified, 1, 0, 0)]);
        report.crate_name = "cargo-targets[]".to_string();

        let diff = build_diff(&report, &report);
        assert!(diff.has_regressions);
        assert!(
            diff.compatibility_errors.iter().any(|error| error.contains("unscoped placeholder")),
            "{:?}",
            diff.compatibility_errors
        );
    }

    #[test]
    fn test_diff_rejects_unsuccessful_baseline_or_current_gate() {
        for failed_side in ["baseline", "current"] {
            let mut baseline = make_report(vec![("fn_a", FunctionVerdict::Verified, 1, 0, 0)]);
            let mut current = baseline.clone();
            let report = if failed_side == "baseline" { &mut baseline } else { &mut current };
            let gate = report.verification_gate.as_mut().expect("test gate");
            gate.decision = "fail".to_string();
            gate.exit_code = 1;

            let diff = build_diff(&baseline, &current);
            assert!(diff.has_regressions);
            assert!(diff.compatibility_errors.iter().any(|error| {
                error.contains(failed_side) && error.contains("gate was not successful")
            }));
        }
    }

    #[test]
    fn test_diff_requires_matching_certified_test_execution_intent_and_inventory() {
        let mut baseline = make_report(vec![("fn_a", FunctionVerdict::Verified, 1, 0, 0)]);
        baseline.verification_gate.as_mut().expect("baseline gate").test_execution =
            Some(exited_test_execution("demo::integration"));

        let current_without_execution =
            make_report(vec![("fn_a", FunctionVerdict::Verified, 1, 0, 0)]);
        let diff = build_diff(&baseline, &current_without_execution);
        assert!(diff.has_regressions);
        assert!(
            diff.compatibility_errors.iter().any(|error| {
                error.contains("execution metadata is present in only one report")
            })
        );

        let mut current_compile_only = baseline.clone();
        let execution = current_compile_only
            .verification_gate
            .as_mut()
            .expect("current gate")
            .test_execution
            .as_mut()
            .expect("current execution");
        execution.compile_only = true;
        execution.phase_b_state = CertifiedTestExecutionPhaseState::NotRequested;
        execution.phase_b_exit = None;
        execution.authorized_executables.clear();
        execution.authorized_inventory_sha256 = None;
        execution.target_directory = None;
        let diff = build_diff(&baseline, &current_compile_only);
        assert!(diff.has_regressions);
        assert!(
            diff.compatibility_errors
                .iter()
                .any(|error| { error.contains("execution intent differs") })
        );

        let mut current_other_target = baseline.clone();
        current_other_target
            .verification_gate
            .as_mut()
            .expect("current gate")
            .test_execution
            .as_mut()
            .expect("current execution")
            .authorized_executables[0]
            .target = "demo::other-integration".to_string();
        let diff = build_diff(&baseline, &current_other_target);
        assert!(diff.has_regressions);
        assert!(
            diff.compatibility_errors
                .iter()
                .any(|error| { error.contains("executable target inventory differs") })
        );

        let mut current_other_schema = baseline.clone();
        current_other_schema
            .verification_gate
            .as_mut()
            .expect("current gate")
            .test_execution
            .as_mut()
            .expect("current execution")
            .schema = "trust.certified-test-execution.v0".to_string();
        let diff = build_diff(&baseline, &current_other_schema);
        assert!(diff.has_regressions);
        assert!(diff.compatibility_errors.iter().any(|error| {
            error.contains("certified test execution schema differs")
                || error.contains("unsupported nested schema")
        }));

        let mut current_other_scope = baseline.clone();
        current_other_scope
            .verification_gate
            .as_mut()
            .expect("current gate")
            .test_execution
            .as_mut()
            .expect("current execution")
            .scope = "all tests and monitors completed".to_string();
        let diff = build_diff(&baseline, &current_other_scope);
        assert!(diff.has_regressions);
        assert!(diff.compatibility_errors.iter().any(|error| {
            error.contains("certified test execution scope differs")
                || error.contains("uses unknown scope")
        }));
    }

    #[test]
    fn test_diff_rejects_forged_successful_gate_with_incomplete_test_execution() {
        let mut report = make_report(vec![("fn_a", FunctionVerdict::Verified, 1, 0, 0)]);
        let mut execution = exited_test_execution("demo::integration");
        execution.phase_b_state = CertifiedTestExecutionPhaseState::Blocked;
        execution.phase_b_exit = None;
        execution.blocker = Some("proof evidence missing".to_string());
        report.verification_gate.as_mut().expect("gate").test_execution = Some(execution);

        let diff = build_diff(&report, &report);
        assert!(diff.has_regressions);
        assert!(diff.compatibility_errors.iter().any(|error| {
            error.contains("did not exit successfully")
                || error.contains("retains an execution blocker")
        }));
    }

    #[test]
    fn test_diff_rejects_forged_pass_gate_over_failed_summary() {
        let forged = make_report(vec![("fn_a", FunctionVerdict::HasViolations, 0, 1, 0)]);

        let diff = build_diff(&forged, &forged);
        assert!(diff.has_regressions);
        assert!(diff.compatibility_errors.iter().any(|error| {
            error.contains("decision is inconsistent") || error.contains("gate was not successful")
        }));
    }

    #[test]
    fn test_diff_rejects_conditional_flags_that_contradict_gate_counts() {
        let baseline = make_report(vec![("fn_a", FunctionVerdict::Verified, 1, 0, 0)]);
        let mut current = baseline.clone();
        let gate = current.verification_gate.as_mut().expect("test gate");
        gate.conditional_on_assumption_rows = true;
        gate.conditional_on_runtime_checks = true;

        let diff = build_diff(&baseline, &current);
        assert!(diff.has_regressions);
        assert!(diff.compatibility_errors.iter().any(|error| {
            error.contains("assumption conditional flag")
                || error.contains("runtime-check conditional flag")
        }));
    }

    #[test]
    fn test_diff_strict_lane_runtime_checked_expansion_is_regression() {
        let baseline = make_report(vec![("fn_a", FunctionVerdict::NoObligations, 0, 0, 0)]);
        let mut current = baseline.clone();
        let summary = &mut current.functions[0].summary;
        summary.total_obligations = 1;
        summary.runtime_checked = 1;
        summary.verdict = FunctionVerdict::RuntimeChecked;

        let diff = build_diff(&baseline, &current);
        assert_eq!(diff.regressions, 1);
        assert!(diff.has_regressions);
        assert_eq!(diff.entries[0].direction, ChangeDirection::Regressed);
    }

    #[test]
    fn contract_panic_gate_integrity_is_conditional_only_for_advisory() {
        let mut report = make_report(vec![("fn_a", FunctionVerdict::Verified, 1, 0, 0)]);
        report.summary.total_obligations = 2;
        report.summary.total_unknown = 1;
        let gate = report.verification_gate.as_mut().expect("test gate");
        gate.counts.total = 2;
        gate.counts.proved = 1;
        gate.counts.contract_panics = 1;

        gate.lane = "advisory".to_string();
        gate.decision = "conditional-pass".to_string();
        gate.exit_code = 0;
        assert!(
            verification_gate_integrity_errors("advisory", gate, &report.summary, true).is_empty(),
            "advisory is the sole contract-panic conditional policy"
        );

        for lane in ["strict", "memory-safe"] {
            gate.lane = lane.to_string();
            gate.decision = "inconclusive".to_string();
            gate.exit_code = 1;
            let errors = verification_gate_integrity_errors(lane, gate, &report.summary, true);
            assert_eq!(errors.len(), 1, "{lane}: {errors:?}");
            assert!(errors[0].contains("gate was not successful"), "{lane}: {errors:?}");
        }
    }

    #[test]
    fn memory_safe_integrity_rejects_overflow_counts_without_panicking() {
        let report = make_report(vec![("fn_a", FunctionVerdict::Verified, 1, 0, 0)]);
        let mut gate = report.verification_gate.clone().expect("test gate");
        gate.lane = "memory-safe".to_string();
        gate.decision = "inconclusive".to_string();
        gate.exit_code = 1;
        gate.counts.total = usize::MAX;
        gate.counts.unknown = usize::MAX;
        gate.counts.mandated = usize::MAX;
        gate.counts.runtime_checked = usize::MAX;
        gate.counts.contract_panics = usize::MAX;

        let errors = verification_gate_integrity_errors("hostile", &gate, &report.summary, true);
        assert!(
            errors.iter().any(|error| error.contains("disjoint total")),
            "overflowing untrusted counters must fail closed: {errors:?}"
        );
    }

    #[test]
    fn test_diff_rejects_duplicate_function_identity_in_either_report() {
        for duplicate_side in ["baseline", "current"] {
            let mut baseline = make_report(vec![("fn_a", FunctionVerdict::Verified, 1, 0, 0)]);
            let mut current = baseline.clone();
            let report = if duplicate_side == "baseline" { &mut baseline } else { &mut current };
            report.functions.push(report.functions[0].clone());

            let diff = build_diff(&baseline, &current);
            assert!(diff.has_regressions);
            assert!(diff.compatibility_errors.iter().any(|error| {
                error.contains(duplicate_side) && error.contains("duplicate function identity")
            }));
        }
    }

    #[test]
    fn test_diff_hardened_compatibility_uses_policy_not_result_context() {
        let mut baseline = make_report(vec![("fn_a", FunctionVerdict::Verified, 1, 0, 0)]);
        baseline.hardened = Some(HardenedReportContext {
            profile: Some(HardenedProfileReport {
                name: Some("unix_hardened".to_string()),
                version: Some("1".to_string()),
                enabled_categories: vec!["ffi".to_string()],
            }),
            assurance: Some(HardenedAssuranceReport {
                level: Some("inventory_only".to_string()),
                model: Some("model-a".to_string()),
                proof_evidence_policy: Some("required".to_string()),
                proof_evidence_required: true,
            }),
            ..HardenedReportContext::default()
        });
        let mut current = baseline.clone();
        {
            let assurance = current
                .hardened
                .as_mut()
                .and_then(|context| context.assurance.as_mut())
                .expect("assurance context");
            assurance.level = Some("proof_backed".to_string());
            assurance.model = Some("model-b".to_string());
        }

        let compatible = build_diff(&baseline, &current);
        assert!(compatible.compatibility_errors.is_empty());

        current
            .hardened
            .as_mut()
            .and_then(|context| context.assurance.as_mut())
            .expect("assurance context")
            .proof_evidence_required = false;
        let incompatible = build_diff(&baseline, &current);
        assert!(incompatible.has_regressions);
        assert!(
            incompatible
                .compatibility_errors
                .iter()
                .any(|error| error.contains("hardened verification"))
        );
    }

    #[test]
    fn test_function_status_labels() {
        assert_eq!(FunctionStatus::Verified.label(), "proved");
        assert_eq!(FunctionStatus::HasViolations.label(), "failed");
        assert_eq!(FunctionStatus::Inconclusive.label(), "unknown");
        assert_eq!(FunctionStatus::RuntimeChecked.label(), "runtime_checked");
        assert_eq!(FunctionStatus::NoObligations.label(), "no_obligations");
    }

    #[test]
    fn test_function_status_is_good() {
        assert!(FunctionStatus::Verified.is_good());
        assert!(FunctionStatus::NoObligations.is_good());
        assert!(FunctionStatus::RuntimeChecked.is_good());
        assert!(!FunctionStatus::HasViolations.is_good());
        assert!(!FunctionStatus::Inconclusive.is_good());
    }

    #[test]
    fn test_change_direction_labels() {
        assert_eq!(ChangeDirection::Improved.label(), "improved");
        assert_eq!(ChangeDirection::Regressed.label(), "REGRESSED");
        assert_eq!(ChangeDirection::Added.label(), "added");
        assert_eq!(ChangeDirection::Removed.label(), "removed");
    }

    #[test]
    fn load_report_returns_sanitized_canonical_report_and_first_pass_provenance() {
        let path = temp_report_path("canonical-forged");
        write_json_report(&path, &forged_canonical_proved_report_without_evidence());

        let loaded = load_report(&path).expect("observational load must remain available");

        assert_eq!(loaded.sanitization.downgraded_proved, 1);
        assert_eq!(loaded.sanitization.evidence_defects, 1);
        assert_eq!(loaded.untrusted_claims.obligations().len(), 1);
        assert_eq!(
            loaded.untrusted_claims.obligations()[0].outcome(),
            UntrustedSavedOutcomeClaim::Proved
        );
        assert_eq!(loaded.report.summary.total_proved, 0);
        assert_eq!(loaded.report.summary.total_unknown, 1);
        assert_eq!(loaded.report.summary.verdict, CrateVerdict::Inconclusive);
        let notice = loaded
            .provenance_notice("baseline", &path)
            .expect("downgrade provenance must be visible to observational consumers");
        assert!(notice.contains("contained 1 serialized proved and 0 runtime-checked"), "{notice}");
        assert!(notice.contains("loaded them as unknown"), "{notice}");
        let error = loaded
            .reject_unreplayed_proved_claims(&path)
            .expect_err("proof consumption must require verifier replay");
        assert!(error.contains("saved report authority gate failed"), "{error}");
        assert!(error.contains("lacked live verifier replay authority"), "{error}");
        let _ = fs::remove_file(path);
    }

    #[test]
    fn load_report_downgrades_runtime_claim_and_reports_first_pass_provenance() {
        let path = temp_report_path("canonical-runtime");
        write_json_report(&path, &canonical_runtime_checked_report());

        let loaded = load_report(&path).expect("observational load must remain available");

        assert_eq!(loaded.sanitization.downgraded_proved, 0);
        assert_eq!(loaded.sanitization.downgraded_runtime_checked, 1);
        assert_eq!(loaded.sanitization.evidence_defects, 0);
        assert_eq!(
            loaded.untrusted_claims.obligations()[0].outcome(),
            UntrustedSavedOutcomeClaim::RuntimeChecked
        );
        assert_eq!(loaded.report.summary.total_runtime_checked, 0);
        assert_eq!(loaded.report.summary.total_unknown, 1);
        assert_eq!(loaded.report.summary.verdict, CrateVerdict::Inconclusive);
        let gate = loaded.report.verification_gate.as_ref().expect("diagnostic gate");
        assert_eq!(gate.counts.runtime_checked, 0);
        assert_eq!(gate.counts.unknown, 1);
        assert!(!gate.conditional_on_runtime_checks);
        let notice = loaded
            .provenance_notice("baseline", &path)
            .expect("runtime downgrade provenance must be visible");
        assert!(notice.contains("0 serialized proved and 1 runtime-checked"), "{notice}");
        assert!(notice.contains("loaded them as unknown"), "{notice}");
        assert!(
            loaded.reject_unreplayed_proved_claims(&path).is_ok(),
            "runtime authority defects must not be mislabeled as proof-evidence defects"
        );
        let _ = fs::remove_file(path);
    }

    #[test]
    fn load_report_returns_first_pass_provenance_for_legacy_proved_rows() {
        let path = temp_report_path("legacy-forged");
        fs::write(
            &path,
            serde_json::to_vec_pretty(&serde_json::json!({
                "results": [{
                    "kind": "postcondition",
                    "message": "legacy forged proof row",
                    "outcome": "Proved",
                    "backend": "forged",
                    "time_ms": 5
                }]
            }))
            .expect("serialize legacy fixture"),
        )
        .expect("write legacy fixture");

        let loaded = load_report(&path).expect("legacy observational load must remain available");

        assert_eq!(loaded.sanitization.downgraded_proved, 1);
        assert_eq!(loaded.sanitization.evidence_defects, 1);
        assert_eq!(loaded.untrusted_claims.obligations().len(), 1);
        assert_eq!(
            loaded.untrusted_claims.obligations()[0].outcome(),
            UntrustedSavedOutcomeClaim::Proved
        );
        assert_eq!(loaded.report.summary.total_proved, 0);
        assert_eq!(loaded.report.summary.total_unknown, 1);
        assert!(loaded.reject_unreplayed_proved_claims(&path).is_err());
        let _ = fs::remove_file(path);
    }

    #[test]
    fn saved_diff_detects_claimed_proved_to_claimed_unknown_without_granting_proof_credit() {
        let baseline_path = temp_report_path("baseline-claimed-proved");
        let current_path = temp_report_path("current-claimed-unknown");
        let baseline_raw = forged_canonical_proved_report_without_evidence();
        let mut current_raw = baseline_raw.clone();
        current_raw.functions[0].obligations[0].outcome = ObligationOutcome::Unknown {
            reason: "current verifier could not prove the claim".to_string(),
        };
        write_json_report(&baseline_path, &baseline_raw);
        write_json_report(&current_path, &current_raw);

        let baseline = load_report(&baseline_path).expect("load claimed-Proved baseline");
        let current = load_report(&current_path).expect("load claimed-Unknown current");
        assert_eq!(baseline.report.summary.total_proved, 0);
        assert_eq!(current.report.summary.total_proved, 0);
        assert_eq!(baseline.report.summary.total_unknown, 1);
        assert_eq!(current.report.summary.total_unknown, 1);

        let sanitized_only = build_diff(&baseline.report, &current.report);
        assert_eq!(
            sanitized_only.regressions, 0,
            "sanitized Unknown rows alone cannot retain the prior raw claim"
        );
        let diff = build_loaded_diff(&baseline, &current);
        let claims = diff
            .non_authoritative_saved_claims
            .as_ref()
            .expect("saved diff must label its raw claim comparison");
        assert_eq!(claims.authority, "untrusted_observational_only_no_proof_credit");
        assert_eq!(claims.baseline_claimed_proved, 1);
        assert_eq!(claims.current_claimed_proved, 0);
        assert_eq!(claims.regressions.len(), 1);
        assert_eq!(claims.regressions[0].baseline_claim, "claimed_proved");
        assert_eq!(claims.regressions[0].current_claim, "claimed_unknown");
        assert!(diff.has_regressions);

        let status = run_diff_command(
            baseline_path.to_str().expect("baseline path utf-8"),
            Some(current_path.to_str().expect("current path utf-8")),
            OutputFormat::Json,
        );
        assert_eq!(status, ExitCode::FAILURE);
        let _ = fs::remove_file(baseline_path);
        let _ = fs::remove_file(current_path);
    }

    #[test]
    fn identical_saved_runtime_claims_remain_observationally_comparable() {
        let baseline_path = temp_report_path("runtime-identical-baseline");
        let current_path = temp_report_path("runtime-identical-current");
        let report = canonical_runtime_checked_report();
        write_json_report(&baseline_path, &report);
        write_json_report(&current_path, &report);

        let baseline = load_report(&baseline_path).expect("load runtime baseline");
        let current = load_report(&current_path).expect("load runtime current");
        assert_eq!(baseline.report.summary.total_runtime_checked, 0);
        assert_eq!(current.report.summary.total_runtime_checked, 0);
        assert_eq!(baseline.report.summary.total_unknown, 1);
        assert_eq!(current.report.summary.total_unknown, 1);

        let diff = build_loaded_diff(&baseline, &current);
        assert!(diff.compatibility_errors.is_empty(), "{:?}", diff.compatibility_errors);
        assert!(!diff.has_regressions);
        let claims = diff.non_authoritative_saved_claims.as_ref().expect("saved claim comparison");
        assert_eq!(claims.baseline_claimed_runtime_checked, 1);
        assert_eq!(claims.current_claimed_runtime_checked, 1);
        assert!(claims.regressions.is_empty());

        let _ = fs::remove_file(baseline_path);
        let _ = fs::remove_file(current_path);
    }

    #[test]
    fn saved_diff_detects_runtime_checked_to_unknown_observational_regression() {
        let baseline_path = temp_report_path("runtime-to-unknown-baseline");
        let current_path = temp_report_path("runtime-to-unknown-current");
        let baseline_raw = canonical_runtime_checked_report();
        let mut current_raw = baseline_raw.clone();
        current_raw.functions[0].obligations[0].outcome = ObligationOutcome::Unknown {
            reason: "current compiler installed no certified monitor".to_string(),
        };
        current_raw.functions[0].summary.runtime_checked = 0;
        current_raw.functions[0].summary.unknown = 1;
        current_raw.functions[0].summary.verdict = FunctionVerdict::Inconclusive;
        current_raw.summary.functions_runtime_checked = 0;
        current_raw.summary.functions_inconclusive = 1;
        current_raw.summary.total_runtime_checked = 0;
        current_raw.summary.total_unknown = 1;
        current_raw.summary.verdict = CrateVerdict::Inconclusive;
        let gate = current_raw.verification_gate.as_mut().expect("runtime gate");
        gate.decision = "inconclusive".to_string();
        gate.exit_code = 1;
        gate.counts.runtime_checked = 0;
        gate.counts.unknown = 1;
        gate.conditional_on_runtime_checks = false;
        write_json_report(&baseline_path, &baseline_raw);
        write_json_report(&current_path, &current_raw);

        let baseline = load_report(&baseline_path).expect("load runtime baseline");
        let current = load_report(&current_path).expect("load unknown current");
        let diff = build_loaded_diff(&baseline, &current);
        let claims = diff.non_authoritative_saved_claims.as_ref().expect("saved claim comparison");
        assert_eq!(claims.baseline_claimed_runtime_checked, 1);
        assert_eq!(claims.current_claimed_runtime_checked, 0);
        assert_eq!(claims.regressions.len(), 1);
        assert_eq!(claims.regressions[0].baseline_claim, "claimed_runtime_checked");
        assert_eq!(claims.regressions[0].current_claim, "claimed_unknown");
        assert!(diff.has_regressions);

        let _ = fs::remove_file(baseline_path);
        let _ = fs::remove_file(current_path);
    }

    #[test]
    fn saved_diff_accepts_runtime_checked_to_proved_as_observational_improvement() {
        let baseline_path = temp_report_path("runtime-to-proved-baseline");
        let current_path = temp_report_path("runtime-to-proved-current");
        let baseline_raw = canonical_runtime_checked_report();
        let mut current_raw = baseline_raw.clone();
        current_raw.functions[0].obligations[0].outcome =
            ObligationOutcome::Proved { strength: ProofStrength::deductive() };
        current_raw.functions[0].summary.proved = 1;
        current_raw.functions[0].summary.runtime_checked = 0;
        current_raw.functions[0].summary.verdict = FunctionVerdict::Verified;
        current_raw.summary.functions_verified = 1;
        current_raw.summary.functions_runtime_checked = 0;
        current_raw.summary.total_proved = 1;
        current_raw.summary.total_runtime_checked = 0;
        current_raw.summary.verdict = CrateVerdict::Verified;
        let gate = current_raw.verification_gate.as_mut().expect("runtime gate");
        gate.decision = "pass".to_string();
        gate.counts.proved = 1;
        gate.counts.runtime_checked = 0;
        gate.conditional_on_runtime_checks = false;
        write_json_report(&baseline_path, &baseline_raw);
        write_json_report(&current_path, &current_raw);

        let baseline = load_report(&baseline_path).expect("load runtime baseline");
        let current = load_report(&current_path).expect("load proved current");
        let diff = build_loaded_diff(&baseline, &current);
        assert!(diff.compatibility_errors.is_empty(), "{:?}", diff.compatibility_errors);
        let claims = diff.non_authoritative_saved_claims.as_ref().expect("saved claim comparison");
        assert_eq!(claims.baseline_claimed_runtime_checked, 1);
        assert_eq!(claims.current_claimed_proved, 1);
        assert!(claims.regressions.is_empty());
        assert!(!diff.has_regressions);

        let _ = fs::remove_file(baseline_path);
        let _ = fs::remove_file(current_path);
    }

    #[test]
    fn identical_saved_passing_reports_remain_observationally_comparable() {
        let baseline_path = temp_report_path("identical-pass-baseline");
        let current_path = temp_report_path("identical-pass-current");
        let report = make_report(vec![("fn_a", FunctionVerdict::Verified, 1, 0, 0)]);
        write_json_report(&baseline_path, &report);
        write_json_report(&current_path, &report);

        let baseline = load_report(&baseline_path).expect("load saved baseline");
        let current = load_report(&current_path).expect("load saved current");
        assert_eq!(baseline.report.summary.total_proved, 0);
        assert_eq!(current.report.summary.total_proved, 0);

        let diff = build_loaded_diff(&baseline, &current);
        assert!(diff.compatibility_errors.is_empty(), "{:?}", diff.compatibility_errors);
        assert_eq!(diff.regressions, 0);
        assert!(!diff.has_regressions);
        let claims = diff.non_authoritative_saved_claims.as_ref().expect("saved claim comparison");
        assert!(claims.regressions.is_empty());

        let _ = fs::remove_file(baseline_path);
        let _ = fs::remove_file(current_path);
    }

    #[test]
    fn saved_diff_rejects_obligation_id_reuse_for_changed_claim() {
        let baseline_path = temp_report_path("changed-claim-baseline");
        let current_path = temp_report_path("changed-claim-current");
        let baseline_raw = forged_canonical_proved_report_without_evidence();
        let mut current_raw = baseline_raw.clone();
        current_raw.functions[0].obligations[0].kind = "different_semantic_claim".into();
        current_raw.functions[0].obligations[0].description =
            "same ID, different verification condition".into();
        write_json_report(&baseline_path, &baseline_raw);
        write_json_report(&current_path, &current_raw);

        let baseline = load_report(&baseline_path).expect("load baseline claim");
        let current = load_report(&current_path).expect("load changed claim");
        let diff = build_loaded_diff(&baseline, &current);
        let claims = diff.non_authoritative_saved_claims.as_ref().expect("saved claim comparison");
        assert_eq!(claims.regressions.len(), 1);
        assert_eq!(claims.regressions[0].current_claim, "missing");
        assert!(diff.has_regressions);

        let _ = fs::remove_file(baseline_path);
        let _ = fs::remove_file(current_path);
    }

    #[test]
    fn load_report_rejects_oversized_file_before_json_deserialization() {
        let path = temp_report_path("oversized");
        let file = fs::File::create(&path).expect("create sparse report");
        file.set_len(MAX_SAVED_PROOF_REPORT_BYTES as u64 + 1).expect("extend sparse report");

        let error = load_report(&path).expect_err("oversized saved report must be bounded");

        assert!(error.contains("safety limit"), "{error}");
        let _ = fs::remove_file(path);
    }

    #[test]
    fn malformed_canonical_report_cannot_fall_back_to_empty_legacy_report() {
        let path = temp_report_path("canonical-no-legacy-fallback");
        let mut malformed =
            serde_json::to_value(empty_report()).expect("serialize canonical fixture");
        malformed["functions"] = serde_json::json!("not an array");
        fs::write(
            &path,
            serde_json::to_vec_pretty(&malformed).expect("serialize malformed fixture"),
        )
        .expect("write malformed canonical report");

        let error = load_report(&path)
            .expect_err("malformed canonical input must not become an empty legacy report");

        assert!(error.contains("failed to parse"), "{error}");
        let _ = fs::remove_file(path);
    }

    #[test]
    fn run_diff_command_observes_sanitized_current_report_instead_of_parse_rejecting_it() {
        let baseline_path = temp_report_path("baseline-good");
        let current_path = temp_report_path("current-forged");
        write_json_report(&baseline_path, &empty_report());
        write_json_report(&current_path, &forged_canonical_proved_report_without_evidence());

        let status = run_diff_command(
            baseline_path.to_str().expect("baseline path utf-8"),
            Some(current_path.to_str().expect("current path utf-8")),
            OutputFormat::Json,
        );

        assert_eq!(status, ExitCode::FAILURE);
        let _ = fs::remove_file(baseline_path);
        let _ = fs::remove_file(current_path);
    }

    #[test]
    fn run_diff_command_observes_sanitized_baseline_report_instead_of_parse_rejecting_it() {
        let baseline_path = temp_report_path("baseline-forged");
        let current_path = temp_report_path("current-good");
        write_json_report(&baseline_path, &forged_canonical_proved_report_without_evidence());
        write_json_report(&current_path, &empty_report());

        let status = run_diff_command(
            baseline_path.to_str().expect("baseline path utf-8"),
            Some(current_path.to_str().expect("current path utf-8")),
            OutputFormat::Json,
        );

        assert_eq!(status, ExitCode::FAILURE);
        let _ = fs::remove_file(baseline_path);
        let _ = fs::remove_file(current_path);
    }

    #[test]
    fn test_unknown_to_proved_is_improvement() {
        let baseline = make_report(vec![("fn_a", FunctionVerdict::Inconclusive, 0, 0, 2)]);
        let current = make_report(vec![("fn_a", FunctionVerdict::Verified, 2, 0, 0)]);

        let diff = build_diff(&baseline, &current);
        assert_eq!(diff.improvements, 1);
        assert!(
            diff.has_regressions,
            "an inconclusive baseline is not an accepted comparison anchor"
        );
    }

    #[test]
    fn test_proved_to_unknown_is_regression() {
        let baseline = make_report(vec![("fn_a", FunctionVerdict::Verified, 2, 0, 0)]);
        let current = make_report(vec![("fn_a", FunctionVerdict::Inconclusive, 0, 0, 2)]);

        let diff = build_diff(&baseline, &current);
        assert_eq!(diff.regressions, 1);
        assert!(diff.has_regressions);
    }

    #[test]
    fn test_legacy_report_conversion() {
        let legacy = LegacySavedReport {
            results: vec![
                LegacyResult {
                    kind: "overflow:add".to_string(),
                    message: "arithmetic overflow".to_string(),
                    outcome: LegacyOutcome::Proved,
                    backend: "ay".to_string(),
                    time_ms: Some(5),
                    evidence: None,
                    proof_evidence: None,
                    transport_evidence: None,
                },
                LegacyResult {
                    kind: "div_by_zero".to_string(),
                    message: "division by zero".to_string(),
                    outcome: LegacyOutcome::Failed,
                    backend: "ay".to_string(),
                    time_ms: Some(3),
                    evidence: None,
                    proof_evidence: None,
                    transport_evidence: None,
                },
            ],
        };

        let report = legacy_to_json_proof_report(&legacy);
        assert_eq!(report.functions.len(), 2);
        assert_eq!(report.summary.total_proved, 1);
        assert_eq!(report.summary.total_failed, 1);
        assert_eq!(report.summary.total_unknown, 0);

        // Check that div_by_zero function has violations
        let div_fn = report.functions.iter().find(|f| f.function == "div_by_zero").unwrap();
        assert_eq!(div_fn.summary.verdict, FunctionVerdict::HasViolations);

        // Conversion preserves legacy Proved rows so the shared saved-report
        // sanitizer can classify the missing proof evidence as a load defect.
        let ov_fn = report.functions.iter().find(|f| f.function == "overflow:add").unwrap();
        assert_eq!(ov_fn.summary.verdict, FunctionVerdict::Verified);
        assert_eq!(ov_fn.summary.proved, 1);
        assert_eq!(ov_fn.summary.unknown, 0);
        assert!(matches!(ov_fn.obligations[0].outcome, ObligationOutcome::Proved { .. }));

        let mut sanitized = report;
        let sanitization = sanitized.sanitize_deserialized();
        assert_eq!(sanitization.evidence_defects, 1);
        assert_eq!(sanitized.summary.total_proved, 0);
        assert_eq!(sanitized.summary.total_unknown, 1);
    }

    #[test]
    fn test_legacy_proved_preserves_structured_evidence_for_sanitizer() {
        let legacy = LegacySavedReport {
            results: vec![LegacyResult {
                kind: "postcondition".to_string(),
                message: "ensures result is bounded".to_string(),
                outcome: LegacyOutcome::Proved,
                backend: "trust-full-verifier".to_string(),
                time_ms: Some(11),
                evidence: None,
                proof_evidence: Some(serde_json::json!({
                    "suite": "trust-wp",
                    "backend": "trust-full-verifier",
                    "request_id": "req-7",
                    "proof_id": "proof-42",
                    "native_id": "native-42",
                    "status": "proved",
                    "provenance": {
                        "kind": "native_backend",
                        "verifier": "trust-full-verifier"
                    },
                    "strength": {
                        "reasoning": "Deductive",
                        "assurance": "Sound"
                    },
                    "evidence": {
                        "reasoning": "Deductive",
                        "assurance": "SmtBacked"
                    }
                })),
                transport_evidence: None,
            }],
        };

        let report = legacy_to_json_proof_report(&legacy);

        assert_eq!(report.summary.total_proved, 1);
        assert_eq!(report.summary.total_unknown, 0);
        let function = report.functions.iter().find(|f| f.function == "postcondition").unwrap();
        assert_eq!(function.summary.verdict, FunctionVerdict::Verified);
        assert!(matches!(function.obligations[0].outcome, ObligationOutcome::Proved { .. }));
        assert!(function.obligations[0].proof_evidence.is_some());

        let mut sanitized = report;
        let sanitization = sanitized.sanitize_deserialized();
        assert_eq!(sanitization.evidence_defects, 1);
        assert_eq!(sanitized.summary.total_proved, 0);
        assert_eq!(sanitized.summary.total_unknown, 1);
    }
}
