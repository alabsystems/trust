// trust-proof-cert binary decompilation certification scaffold
//
// Public summary and release-gate helpers for proof-grade binary
// decompilation certificates.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::BTreeMap;

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
/// Artifact trust level used by binary decompilation summaries.
///
/// This intentionally references the shared `trust-types` trust-level model
/// rather than the certificate-signing trust level re-exported at this crate root.
pub use trust_types::TrustLevel as BinaryArtifactTrustLevel;
use trust_types::{
    BinaryOrigin, BinarySourceProvenanceSummary, BinaryVerificationSummary, DecompilationArtifact,
    DecompileTarget, DecompiledOutput, ExploitWitness,
    ProofCertificateProductionCheckerEvidenceRef, ProofCertificateProductionCheckerEvidenceStatus,
    ProofCertificateStatus, ReconstructionValidationStatus, RefutationKind, ReplayStatus,
    SolverDispatchRecord, SolverDispatchStatus, SolverQuerySemantics, UnsupportedLedger,
    VerificationResult,
};

use crate::CertError;

/// Compact summary of unsupported binary/decompilation records.
#[derive(Debug, Clone, PartialEq, Eq, Default, Serialize, Deserialize)]
pub struct UnsupportedLedgerSummary {
    /// Number of unsupported records in the ledger.
    pub total_records: usize,
    /// Unsupported record counts grouped by producing stage.
    pub by_stage: BTreeMap<String, usize>,
    /// Unsupported record counts grouped by feature.
    pub by_feature: BTreeMap<String, usize>,
}

impl UnsupportedLedgerSummary {
    /// Build a deterministic aggregate summary from a shared unsupported ledger.
    #[must_use]
    pub fn from_ledger(ledger: &UnsupportedLedger) -> Self {
        let mut summary =
            Self { total_records: ledger.records.len(), ..UnsupportedLedgerSummary::default() };

        for record in &ledger.records {
            *summary.by_stage.entry(record.stage.clone()).or_default() += 1;
            *summary.by_feature.entry(record.feature.clone()).or_default() += 1;
        }

        summary
    }

    /// True when the ledger has no unsupported records.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.total_records == 0 && self.by_stage.is_empty() && self.by_feature.is_empty()
    }
}

/// Aggregate solver outcome counts for the VCs emitted from a lifted binary.
#[derive(Debug, Clone, PartialEq, Eq, Default, Serialize, Deserialize)]
pub struct BinarySolverResultSummary {
    /// Number of solver results included in this summary.
    pub total_results: usize,
    /// VCs proved by a solver/prover.
    pub proved: usize,
    /// Proved VCs that also carry checked proof certificates.
    ///
    /// Raw solver certificate bytes are not enough for proof-grade binary
    /// release. Use [`BinarySolverResultSummary::from_solver_dispatch_records`]
    /// when checked certificate status is available.
    #[serde(default)]
    pub proved_with_certificates: usize,
    /// VCs with counterexamples.
    pub failed: usize,
    /// VCs reported unknown, including future unclassified result variants.
    pub unknown: usize,
    /// VCs that timed out.
    pub timed_out: usize,
}

/// Per-dispatch certificate candidate and check status used by binary gates.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct BinaryCertificateCheckRecord {
    /// Stable solver dispatch id.
    pub dispatch_id: String,
    /// Function associated with the VC, when known.
    #[serde(default)]
    pub function: Option<String>,
    /// True when the dispatch exposes certificate-shaped evidence.
    pub candidate_present: bool,
    /// True only when certificate evidence has been independently checked.
    pub checked: bool,
    /// True when the candidate was rejected by a checker.
    pub rejected: bool,
    /// True when raw solver proof bytes were attached to the solver result.
    pub raw_solver_proof_bytes: bool,
    /// Stable label for the source/status of this certificate candidate.
    pub status: String,
    /// Typed production-checker evidence parsed from checked certificate status.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub production_checker_evidence: Option<ProofCertificateProductionCheckerEvidenceRef>,
    /// True when the checked status is bound to coherent VC/replay/origin metadata.
    #[serde(default)]
    pub coherent_checked_coverage: bool,
    /// Deterministic reasons this dispatch cannot count as checked coverage.
    #[serde(default)]
    pub coherence_failures: Vec<String>,
}

/// Aggregate certificate-candidate/check status for a binary verification summary.
#[derive(Debug, Clone, PartialEq, Eq, Default, Serialize, Deserialize)]
pub struct BinaryCertificateCheckSummary {
    /// Required binary VC count.
    pub required_vcs: usize,
    /// Number of solver dispatch records considered.
    pub solver_dispatches: usize,
    /// Dispatches with certificate-shaped evidence.
    pub certificate_candidates: usize,
    /// Dispatches with independently checked certificate evidence.
    pub checked_certificates: usize,
    /// Required VCs still missing checked certificate coverage.
    pub missing_checked_certificates: usize,
    /// Dispatches with rejected certificate candidates.
    pub rejected_certificates: usize,
    /// Dispatches with raw solver proof bytes.
    pub raw_solver_proof_bytes: usize,
    /// True when checked certificates cover every required VC.
    pub checked_certificates_satisfy_coverage: bool,
    /// Always false when raw solver proof bytes are the only evidence model.
    pub raw_solver_proof_bytes_satisfy_coverage: bool,
    /// Per-dispatch certificate candidate/check records.
    pub records: Vec<BinaryCertificateCheckRecord>,
}

/// Per-witness replay/capture status for independent exploit refutations.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct BinaryExploitRefutationRecord {
    /// Component that made the claim being refuted.
    pub component: String,
    /// Exact claim text supplied by the witness producer.
    pub claim: String,
    /// Function associated with the exploit input.
    pub function: String,
    /// Refutation class reported for this witness.
    pub refutation: RefutationKind,
    /// True when both the exact claim and concrete exploit input are captured.
    pub exact_claim_and_input_captured: bool,
    /// True when the captured exploit input was replayed.
    pub replayed: bool,
    /// Raw replay status for diagnostics.
    pub replay: ReplayStatus,
    /// Deterministic reasons this witness cannot count as an independent refutation.
    #[serde(default)]
    pub failures: Vec<String>,
}

/// Aggregate replay/capture status for independent exploit refutations.
#[derive(Debug, Clone, PartialEq, Eq, Default, Serialize, Deserialize)]
pub struct BinaryExploitRefutationSummary {
    /// Number of exploit refutation witnesses inspected.
    pub total_refutations: usize,
    /// Witnesses with exact claim/input capture and successful replay.
    pub captured_and_replayed: usize,
    /// Witnesses missing exact claim text or concrete exploit input.
    pub missing_exact_inputs: usize,
    /// Witnesses that did not replay the captured input.
    pub not_replayed: usize,
    /// Witnesses whose refutation kind is unknown.
    pub unknown_refutations: usize,
    /// Per-witness capture/replay status.
    pub records: Vec<BinaryExploitRefutationRecord>,
}

impl BinaryExploitRefutationSummary {
    /// Build an independent-refutation summary from exploit witnesses.
    #[must_use]
    pub fn from_witnesses(witnesses: &[ExploitWitness]) -> Self {
        let mut summary = Self {
            total_refutations: witnesses.len(),
            ..BinaryExploitRefutationSummary::default()
        };

        for witness in witnesses {
            let failures = exploit_refutation_failures(witness);
            let exact_claim_and_input_captured = !failures.iter().any(|failure| {
                matches!(
                    failure.as_str(),
                    "missing claim component"
                        | "missing exploit claim"
                        | "missing exploit function"
                        | "missing concrete exploit input"
                )
            });
            let replayed = witness.replay == ReplayStatus::Replayed;

            if exact_claim_and_input_captured && replayed && failures.is_empty() {
                summary.captured_and_replayed += 1;
            }
            if !exact_claim_and_input_captured {
                summary.missing_exact_inputs += 1;
            }
            if !replayed {
                summary.not_replayed += 1;
            }
            if witness.refutation == RefutationKind::Unknown {
                summary.unknown_refutations += 1;
            }

            summary.records.push(BinaryExploitRefutationRecord {
                component: witness.claim.component.clone(),
                claim: witness.claim.claim.clone(),
                function: witness.function.clone(),
                refutation: witness.refutation.clone(),
                exact_claim_and_input_captured,
                replayed,
                replay: witness.replay,
                failures,
            });
        }

        summary
    }

    /// True when every exploit refutation was captured exactly and replayed.
    #[must_use]
    pub fn all_captured_and_replayed(&self) -> bool {
        self.captured_and_replayed == self.total_refutations
    }
}

impl BinaryCertificateCheckSummary {
    /// Build an aggregate certificate-check summary from solver dispatch records.
    #[must_use]
    pub fn from_solver_dispatch_records(
        vc_count: usize,
        dispatches: &[SolverDispatchRecord],
    ) -> Self {
        let mut summary = Self {
            required_vcs: vc_count,
            solver_dispatches: dispatches.len(),
            ..BinaryCertificateCheckSummary::default()
        };
        let mut records = Vec::with_capacity(dispatches.len());

        for dispatch in dispatches {
            let raw_solver_proof_bytes =
                raw_solver_result_has_certificate_bytes(dispatch.result.as_ref());
            let candidate_present =
                certificate_candidate_present(&dispatch.certificate) || raw_solver_proof_bytes;
            let coherence_failures = checked_certificate_coherence_failures(dispatch);
            let production_checker_evidence = dispatch.certificate.production_checker_evidence();
            let rejected = matches!(dispatch.certificate, ProofCertificateStatus::Rejected { .. });

            if candidate_present {
                summary.certificate_candidates += 1;
            }
            if rejected {
                summary.rejected_certificates += 1;
            }
            if raw_solver_proof_bytes {
                summary.raw_solver_proof_bytes += 1;
            }

            records.push(BinaryCertificateCheckRecord {
                dispatch_id: dispatch.id.clone(),
                function: dispatch.function.clone(),
                candidate_present,
                checked: false,
                rejected,
                raw_solver_proof_bytes,
                status: certificate_status_label(&dispatch.certificate).to_string(),
                production_checker_evidence,
                coherent_checked_coverage: false,
                coherence_failures,
            });
        }

        push_duplicate_manifest_identity_failures(&mut records, dispatches);
        for (record, dispatch) in records.iter_mut().zip(dispatches) {
            let coherent_checked_coverage = dispatch.certificate.is_checked()
                && dispatch_proves_required_vc(dispatch)
                && record.coherence_failures.is_empty();
            record.coherent_checked_coverage = coherent_checked_coverage;
            record.checked = coherent_checked_coverage;
            if record.checked {
                summary.checked_certificates += 1;
            }
        }
        summary.records = records;

        summary.missing_checked_certificates =
            vc_count.saturating_sub(summary.checked_certificates);
        summary.checked_certificates_satisfy_coverage =
            summary.checked_certificates == vc_count && dispatches.len() == vc_count;
        summary.raw_solver_proof_bytes_satisfy_coverage = false;
        summary
    }

    /// Build a raw-result-only summary. Raw solver proof bytes are candidates
    /// for auditing, but are never checked certificate coverage.
    #[must_use]
    pub fn from_results(vc_count: usize, results: &[VerificationResult]) -> Self {
        let raw_solver_proof_bytes = raw_solver_proof_bytes_from_results(results);
        Self {
            required_vcs: vc_count,
            solver_dispatches: results.len(),
            certificate_candidates: raw_solver_proof_bytes,
            checked_certificates: 0,
            missing_checked_certificates: vc_count,
            rejected_certificates: 0,
            raw_solver_proof_bytes,
            checked_certificates_satisfy_coverage: false,
            raw_solver_proof_bytes_satisfy_coverage: false,
            records: Vec::new(),
        }
    }
}

impl BinarySolverResultSummary {
    /// Summarize shared `trust-types` verification results.
    #[must_use]
    pub fn from_results(results: &[VerificationResult]) -> Self {
        let mut summary =
            Self { total_results: results.len(), ..BinarySolverResultSummary::default() };

        for result in results {
            match result {
                VerificationResult::Proved { proof_certificate: _, .. } => {
                    summary.proved += 1;
                }
                VerificationResult::Failed { .. } => summary.failed += 1,
                VerificationResult::Unknown { .. } => summary.unknown += 1,
                VerificationResult::Timeout { .. } => summary.timed_out += 1,
                _ => summary.unknown += 1,
            }
        }

        summary
    }

    /// Summarize per-VC solver dispatch records, counting only checked proof
    /// certificates as certificate coverage.
    #[must_use]
    pub fn from_solver_dispatch_records(dispatches: &[SolverDispatchRecord]) -> Self {
        let certificate_checks = BinaryCertificateCheckSummary::from_solver_dispatch_records(
            dispatches.len(),
            dispatches,
        );
        Self::from_solver_dispatch_records_with_certificate_checks(dispatches, &certificate_checks)
    }

    fn from_solver_dispatch_records_with_certificate_checks(
        dispatches: &[SolverDispatchRecord],
        certificate_checks: &BinaryCertificateCheckSummary,
    ) -> Self {
        let mut summary =
            Self { total_results: dispatches.len(), ..BinarySolverResultSummary::default() };

        for (index, dispatch) in dispatches.iter().enumerate() {
            match (dispatch.status, dispatch.query_semantics) {
                (SolverDispatchStatus::Unsat, SolverQuerySemantics::SatIsCounterexample) => {
                    summary.proved += 1;
                    if certificate_checks.records.get(index).is_some_and(|record| record.checked) {
                        summary.proved_with_certificates += 1;
                    }
                }
                (SolverDispatchStatus::Sat, SolverQuerySemantics::SatIsCounterexample) => {
                    summary.failed += 1;
                }
                (SolverDispatchStatus::Timeout, _) => summary.timed_out += 1,
                _ => summary.unknown += 1,
            }
        }

        summary
    }

    /// Number of solver results that are not proved.
    #[must_use]
    pub fn non_proved_results(&self) -> usize {
        self.total_results.saturating_sub(self.proved)
    }

    /// Number of expected VCs without a proved solver result.
    #[must_use]
    pub fn unproved_vcs_for(&self, vc_count: usize) -> usize {
        vc_count.saturating_sub(self.proved)
    }

    /// True when every expected VC has exactly one proved solver result.
    #[must_use]
    pub fn all_proved_for(&self, vc_count: usize) -> bool {
        self.total_results == vc_count
            && self.proved == vc_count
            && self.non_proved_results() == 0
            && self.failed == 0
            && self.unknown == 0
            && self.timed_out == 0
    }

    /// Number of proved results that are missing checked proof certificates.
    #[must_use]
    pub fn proved_without_certificates(&self) -> usize {
        self.proved.saturating_sub(self.proved_with_certificates)
    }

    /// Number of expected VCs without checked proof-certificate coverage.
    #[must_use]
    pub fn unchecked_certificate_vcs_for(&self, vc_count: usize) -> usize {
        vc_count.saturating_sub(self.proved_with_certificates)
    }

    /// True when every expected VC was proved and backed by a checked proof certificate.
    #[must_use]
    pub fn all_proved_with_certificates_for(&self, vc_count: usize) -> bool {
        self.all_proved_for(vc_count) && self.proved_with_certificates == vc_count
    }
}

/// Aggregate replay status for proof/model replay associated with a binary cert.
#[derive(Debug, Clone, PartialEq, Eq, Default, Serialize, Deserialize)]
pub struct BinaryReplayStatusSummary {
    /// Number of replay records summarized.
    pub total: usize,
    /// Replay succeeded.
    pub replayed: usize,
    /// Replay was not attempted, so the replay status is unknown.
    pub not_attempted: usize,
    /// Replay showed the witness/model was spurious.
    pub spurious: usize,
    /// Replay failed.
    pub failed: usize,
}

impl BinaryReplayStatusSummary {
    /// Summarize shared replay statuses.
    #[must_use]
    pub fn from_statuses(statuses: &[ReplayStatus]) -> Self {
        let mut summary = Self { total: statuses.len(), ..BinaryReplayStatusSummary::default() };

        for status in statuses {
            match status {
                ReplayStatus::Replayed => summary.replayed += 1,
                ReplayStatus::NotAttempted => summary.not_attempted += 1,
                ReplayStatus::Spurious => summary.spurious += 1,
                ReplayStatus::Failed => summary.failed += 1,
                _ => summary.not_attempted += 1,
            }
        }

        summary
    }

    /// Count replay statuses that are unknown for release-gate purposes.
    #[must_use]
    pub fn unknown_count(&self) -> usize {
        self.not_attempted
    }

    /// Count replay statuses that were attempted but did not replay successfully.
    #[must_use]
    pub fn unsuccessful_count(&self) -> usize {
        self.spurious + self.failed
    }

    /// True when there is at least one replay record and every one succeeded.
    #[must_use]
    pub fn all_replayed(&self) -> bool {
        self.total > 0 && self.replayed == self.total
    }

    /// True when every expected VC has one successful replay record.
    #[must_use]
    pub fn all_replayed_for(&self, vc_count: usize) -> bool {
        self.total == vc_count && self.replayed == vc_count
    }
}

/// Public binary decompilation certificate prerequisite summary.
///
/// This is intentionally local scaffolding until the binary decompilation
/// report schema is shared across more crates. Integration path: move this
/// summary into `trust-types` once `trust-lift`, `trust-report`, and certificate
/// generation all consume the same stable binary-cert schema.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct BinaryVerificationCertificateSummary {
    /// SHA-256 digest of the lifted binary artifact being certified.
    pub lifted_binary_digest: [u8; 32],
    /// Lifted artifact format, e.g. `trust_ir+binary`, `elf`, or `mach-o`.
    pub lifted_binary_format: String,
    /// Architecture for the lifted binary, e.g. `x86_64` or `aarch64`.
    pub architecture: String,
    /// SHA-256 digest of the serialized unsupported ledger.
    pub unsupported_ledger_hash: [u8; 32],
    /// Aggregate unsupported-record summary.
    pub unsupported_ledger_summary: UnsupportedLedgerSummary,
    /// Number of verification conditions generated for the lifted binary.
    pub vc_count: usize,
    /// Aggregate solver result counts.
    pub solver_results: BinarySolverResultSummary,
    /// Aggregate proof/model replay status.
    pub replay_status: BinaryReplayStatusSummary,
    /// Raw solver proof blobs seen while aggregating evidence.
    ///
    /// These are reported for auditability only and never count as checked
    /// proof-certificate coverage.
    #[serde(default)]
    pub raw_solver_proof_bytes: usize,
    /// Per-dispatch certificate candidate/check summary.
    #[serde(default)]
    pub certificate_checks: BinaryCertificateCheckSummary,
    /// Independent exploit-refutation witnesses attached to this verification summary.
    #[serde(default)]
    pub exploit_refutations: BinaryExploitRefutationSummary,
    /// Preserved `trust_symbolic.formula` payloads that require target proof-consumer evidence.
    #[serde(default)]
    pub preserved_symbolic_formulas: usize,
    /// True only when target proof semantics explicitly consumed preserved symbolic formulas.
    #[serde(default)]
    pub symbolic_formula_consumer_accepted: bool,
    /// Final artifact trust level from `trust-types`.
    pub final_trust_level: BinaryArtifactTrustLevel,
}

impl BinaryVerificationCertificateSummary {
    /// Build a summary from shared ledger, solver result, and replay status types.
    #[allow(clippy::too_many_arguments)] // certificate summary inherently aggregates every facet of a binary verification run
    pub fn from_results(
        lifted_binary_digest: [u8; 32],
        lifted_binary_format: impl Into<String>,
        architecture: impl Into<String>,
        unsupported_ledger: &UnsupportedLedger,
        vc_count: usize,
        solver_results: &[VerificationResult],
        replay_statuses: &[ReplayStatus],
        final_trust_level: BinaryArtifactTrustLevel,
    ) -> Result<Self, CertError> {
        Ok(Self {
            lifted_binary_digest,
            lifted_binary_format: lifted_binary_format.into(),
            architecture: architecture.into(),
            unsupported_ledger_hash: hash_unsupported_ledger(unsupported_ledger)?,
            unsupported_ledger_summary: UnsupportedLedgerSummary::from_ledger(unsupported_ledger),
            vc_count,
            solver_results: BinarySolverResultSummary::from_results(solver_results),
            replay_status: BinaryReplayStatusSummary::from_statuses(replay_statuses),
            raw_solver_proof_bytes: raw_solver_proof_bytes_from_results(solver_results),
            certificate_checks: BinaryCertificateCheckSummary::from_results(
                vc_count,
                solver_results,
            ),
            exploit_refutations: BinaryExploitRefutationSummary::default(),
            preserved_symbolic_formulas: 0,
            symbolic_formula_consumer_accepted: false,
            final_trust_level,
        })
    }

    /// Build a summary from per-VC solver dispatch records.
    ///
    /// This is the proof-grade path: unlike raw [`VerificationResult`] values,
    /// dispatch records include certificate checking status and replay coverage.
    pub fn from_solver_dispatch_records(
        lifted_binary_digest: [u8; 32],
        lifted_binary_format: impl Into<String>,
        architecture: impl Into<String>,
        unsupported_ledger: &UnsupportedLedger,
        solver_dispatch: &[SolverDispatchRecord],
        final_trust_level: BinaryArtifactTrustLevel,
    ) -> Result<Self, CertError> {
        Self::from_required_solver_dispatch_records(
            lifted_binary_digest,
            lifted_binary_format,
            architecture,
            unsupported_ledger,
            solver_dispatch.len(),
            solver_dispatch,
            final_trust_level,
        )
    }

    /// Build a summary from per-VC solver dispatch records and an explicit
    /// required-VC count.
    ///
    /// Use this when the verifier knows how many binary VCs were required even
    /// if not every VC reached solver dispatch. Missing dispatches, raw solver
    /// proof bytes, and unchecked certificates remain non-proof-grade evidence.
    pub fn from_required_solver_dispatch_records(
        lifted_binary_digest: [u8; 32],
        lifted_binary_format: impl Into<String>,
        architecture: impl Into<String>,
        unsupported_ledger: &UnsupportedLedger,
        vc_count: usize,
        solver_dispatch: &[SolverDispatchRecord],
        final_trust_level: BinaryArtifactTrustLevel,
    ) -> Result<Self, CertError> {
        let replay_statuses =
            solver_dispatch.iter().map(|dispatch| dispatch.replay).collect::<Vec<_>>();

        let certificate_checks =
            BinaryCertificateCheckSummary::from_solver_dispatch_records(vc_count, solver_dispatch);

        Ok(Self {
            lifted_binary_digest,
            lifted_binary_format: lifted_binary_format.into(),
            architecture: architecture.into(),
            unsupported_ledger_hash: hash_unsupported_ledger(unsupported_ledger)?,
            unsupported_ledger_summary: UnsupportedLedgerSummary::from_ledger(unsupported_ledger),
            vc_count,
            solver_results:
                BinarySolverResultSummary::from_solver_dispatch_records_with_certificate_checks(
                    solver_dispatch,
                    &certificate_checks,
                ),
            replay_status: BinaryReplayStatusSummary::from_statuses(&replay_statuses),
            raw_solver_proof_bytes: raw_solver_proof_bytes_from_dispatches(solver_dispatch),
            certificate_checks,
            exploit_refutations: BinaryExploitRefutationSummary::default(),
            preserved_symbolic_formulas: 0,
            symbolic_formula_consumer_accepted: false,
            final_trust_level,
        })
    }

    /// Build a certificate summary from a shared binary verification summary.
    ///
    /// Aggregation is intentionally based on structured solver dispatch
    /// records. Raw aggregate counts and raw solver proof bytes in
    /// [`VerificationResult`] do not count as checked certificate evidence.
    pub fn from_binary_verification_summary(
        lifted_binary_digest: [u8; 32],
        lifted_binary_format: impl Into<String>,
        architecture: impl Into<String>,
        unsupported_ledger: &UnsupportedLedger,
        verification: &BinaryVerificationSummary,
        final_trust_level: BinaryArtifactTrustLevel,
    ) -> Result<Self, CertError> {
        let mut summary = Self::from_required_solver_dispatch_records(
            lifted_binary_digest,
            lifted_binary_format,
            architecture,
            unsupported_ledger,
            verification.total_vcs,
            &verification.solver_dispatch,
            final_trust_level,
        )?;
        summary.exploit_refutations =
            BinaryExploitRefutationSummary::from_witnesses(&verification.witnesses);
        Ok(summary)
    }

    /// Attach target proof-consumer evidence for preserved symbolic formulas.
    ///
    /// This is fail-closed: any non-zero preserved formula count rejects the
    /// proof-grade certificate summary unless explicit consumer evidence is
    /// reported by the caller.
    #[must_use]
    pub fn with_symbolic_formula_consumer_evidence(
        mut self,
        preserved_symbolic_formulas: usize,
        symbolic_formula_consumer_accepted: bool,
    ) -> Self {
        self.preserved_symbolic_formulas = preserved_symbolic_formulas;
        self.symbolic_formula_consumer_accepted = symbolic_formula_consumer_accepted;
        self
    }

    /// Evaluate whether this summary can pass the proof-grade release gate.
    #[must_use]
    pub fn proof_grade_release_gate(&self) -> BinaryReleaseGateDecision {
        evaluate_binary_proof_grade_release_gate(self)
    }
}

/// Compute the SHA-256 digest of lifted binary artifact bytes.
#[must_use]
pub fn digest_lifted_binary(bytes: &[u8]) -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update(bytes);
    hasher.finalize().into()
}

/// Compute the SHA-256 digest of a serialized unsupported ledger.
pub fn hash_unsupported_ledger(ledger: &UnsupportedLedger) -> Result<[u8; 32], CertError> {
    let bytes = serde_json::to_vec(ledger)
        .map_err(|e| CertError::SerializationFailed { reason: e.to_string() })?;
    let mut hasher = Sha256::new();
    hasher.update(bytes);
    Ok(hasher.finalize().into())
}

fn raw_solver_proof_bytes_from_results(results: &[VerificationResult]) -> usize {
    results
        .iter()
        .filter(|result| {
            matches!(result, VerificationResult::Proved { proof_certificate: Some(_), .. })
        })
        .count()
}

fn raw_solver_proof_bytes_from_dispatches(dispatches: &[SolverDispatchRecord]) -> usize {
    dispatches
        .iter()
        .filter(|dispatch| raw_solver_result_has_certificate_bytes(dispatch.result.as_ref()))
        .count()
}

fn raw_solver_result_has_certificate_bytes(result: Option<&VerificationResult>) -> bool {
    matches!(result, Some(VerificationResult::Proved { proof_certificate: Some(_), .. }))
}

fn dispatch_proves_required_vc(dispatch: &SolverDispatchRecord) -> bool {
    dispatch.status == SolverDispatchStatus::Unsat
        && dispatch.query_semantics == SolverQuerySemantics::SatIsCounterexample
}

fn checked_certificate_coherence_failures(dispatch: &SolverDispatchRecord) -> Vec<String> {
    let mut failures = Vec::new();

    if dispatch.id.trim().is_empty() {
        failures.push("missing dispatch id".to_string());
    }

    if let ProofCertificateStatus::Checked { checker, format, sha256 } = &dispatch.certificate {
        if checker.trim().is_empty() {
            failures.push("missing certificate checker".to_string());
        } else {
            match dispatch.certificate.production_checker_evidence_status() {
                ProofCertificateProductionCheckerEvidenceStatus::Present { .. } => {}
                ProofCertificateProductionCheckerEvidenceStatus::Missing => {
                    failures.push("missing production checker evidence".to_string());
                }
                ProofCertificateProductionCheckerEvidenceStatus::Malformed { reason } => {
                    failures.push(format!("malformed production checker evidence: {reason}"));
                }
            }
        }
        if format.trim().is_empty() {
            failures.push("missing certificate format".to_string());
        }
        match sha256.as_deref() {
            None => failures.push("missing checked certificate digest".to_string()),
            Some(digest) if digest.trim().is_empty() => {
                failures.push("missing checked certificate digest".to_string());
            }
            Some(digest) if !is_canonical_sha256_hex(digest) => {
                failures.push(
                    "checked certificate digest is not canonical lowercase sha256 hex".to_string(),
                );
            }
            Some(_) => {}
        }
    }
    failures.extend(
        crate::checked_binary_certificate::checked_certificate_manifest_identity_failures(dispatch),
    );

    if !dispatch_proves_required_vc(dispatch) {
        failures.push("dispatch is not a proved proof-grade VC".to_string());
    }

    if dispatch.replay != ReplayStatus::Replayed {
        failures.push("dispatch replay did not succeed".to_string());
    }

    match &dispatch.origin {
        Some(origin) => failures.extend(binary_origin_coherence_failures(origin)),
        None => failures.push("missing binary origin".to_string()),
    }

    if let Some(function) = &dispatch.function
        && function.trim().is_empty()
    {
        failures.push("empty dispatch function".to_string());
    }

    if let Some(vc) = &dispatch.vc
        && let Some(function) = &dispatch.function
        && vc.function != *function
    {
        failures.push("VC function does not match dispatch function".to_string());
    }

    failures
}

fn push_duplicate_manifest_identity_failures(
    records: &mut [BinaryCertificateCheckRecord],
    dispatches: &[SolverDispatchRecord],
) {
    let mut seen_vcs = BTreeMap::<String, String>::new();
    let mut seen_certificates = BTreeMap::<String, String>::new();
    let mut seen_proof_exports = BTreeMap::<String, String>::new();

    for (record, dispatch) in records.iter_mut().zip(dispatches) {
        if !dispatch.certificate.is_checked()
            || !dispatch_proves_required_vc(dispatch)
            || !record.coherence_failures.is_empty()
        {
            continue;
        }

        let Ok(Some(identity)) =
            crate::checked_binary_certificate::checked_certificate_manifest_identity_entry(
                dispatch,
            )
        else {
            continue;
        };

        push_duplicate_manifest_identity_failure(
            &mut record.coherence_failures,
            &mut seen_vcs,
            "VC",
            &identity.artifact_identity.vc_sha256,
            &dispatch.id,
        );
        push_duplicate_manifest_identity_failure(
            &mut record.coherence_failures,
            &mut seen_certificates,
            "certificate",
            &identity.artifact_identity.certificate_sha256,
            &dispatch.id,
        );
        push_duplicate_manifest_identity_failure(
            &mut record.coherence_failures,
            &mut seen_proof_exports,
            "proof export",
            &identity.artifact_identity.proof_export_sha256,
            &dispatch.id,
        );
    }
}

fn push_duplicate_manifest_identity_failure(
    failures: &mut Vec<String>,
    seen: &mut BTreeMap<String, String>,
    identity_kind: &str,
    identity: &str,
    dispatch_id: &str,
) {
    match seen.entry(identity.to_string()) {
        std::collections::btree_map::Entry::Vacant(entry) => {
            entry.insert(dispatch_id.to_string());
        }
        std::collections::btree_map::Entry::Occupied(entry) => {
            failures.push(format!(
                "duplicate manifest-backed checked certificate {identity_kind} identity `{identity}` also used by dispatch `{}`",
                entry.get()
            ));
        }
    }
}

fn binary_origin_coherence_failures(origin: &BinaryOrigin) -> Vec<String> {
    let mut failures = Vec::new();

    if origin.binary_path.as_deref().is_none_or(str::is_empty) {
        failures.push("missing binary path".to_string());
    }
    if let Some(entry) = origin.function_entry {
        if origin.instruction_address < entry {
            failures.push("instruction address precedes function entry".to_string());
        }
    } else {
        failures.push("missing function entry".to_string());
    }
    if origin.instruction_size.is_none_or(|size| size == 0) {
        failures.push("missing instruction size".to_string());
    }
    if origin.instruction_bytes.is_empty() {
        failures.push("missing instruction bytes".to_string());
    }
    if let Some(size) = origin.instruction_size
        && !origin.instruction_bytes.is_empty()
        && origin.instruction_bytes.len() != usize::from(size)
    {
        failures.push("instruction bytes length does not match instruction size".to_string());
    }

    failures
}

fn exploit_refutation_failures(witness: &ExploitWitness) -> Vec<String> {
    let mut failures = Vec::new();

    if witness.claim.component.trim().is_empty() {
        failures.push("missing claim component".to_string());
    }
    if witness.claim.claim.trim().is_empty() {
        failures.push("missing exploit claim".to_string());
    }
    if witness.function.trim().is_empty() {
        failures.push("missing exploit function".to_string());
    }
    if witness
        .model
        .as_ref()
        .is_none_or(|model| model.assignments.is_empty() && model.trace.is_none())
    {
        failures.push("missing concrete exploit input".to_string());
    }
    if witness.replay != ReplayStatus::Replayed {
        failures.push("exact exploit input was not replayed".to_string());
    }
    if witness.refutation == RefutationKind::Unknown {
        failures.push("unknown refutation kind".to_string());
    }

    failures
}

fn certificate_candidate_present(status: &ProofCertificateStatus) -> bool {
    matches!(
        status,
        ProofCertificateStatus::Present { .. }
            | ProofCertificateStatus::Checked { .. }
            | ProofCertificateStatus::Rejected { .. }
    )
}

fn certificate_status_label(status: &ProofCertificateStatus) -> &'static str {
    match status {
        ProofCertificateStatus::Checked { checker, format, sha256 }
            if !checker.trim().is_empty()
                && status.production_checker_evidence_status().is_present()
                && !format.trim().is_empty()
                && sha256.as_deref().is_some_and(is_canonical_sha256_hex) =>
        {
            "checked"
        }
        ProofCertificateStatus::Checked { .. } => "checked-invalid",
        ProofCertificateStatus::Present { .. } => "present-unchecked",
        ProofCertificateStatus::Unavailable { .. } => "unavailable",
        ProofCertificateStatus::Rejected { .. } => "rejected",
        ProofCertificateStatus::NotRequested => "not-requested",
        _ => "unknown",
    }
}

fn is_canonical_sha256_hex(value: &str) -> bool {
    value.len() == 64
        && value.bytes().all(|byte| byte.is_ascii_digit() || matches!(byte, b'a'..=b'f'))
}

/// Proof-grade binary release-gate outcome.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct BinaryReleaseGateDecision {
    /// True when the summary satisfies all proof-grade release criteria.
    pub accepted: bool,
    /// Concrete rejection reasons. Empty iff `accepted` is true.
    pub rejections: Vec<BinaryReleaseGateRejection>,
}

/// Stable JSON summary for proof-grade certificate gate serialization.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct BinaryCertificateProofGradeGateSummary {
    /// True when the certificate summary satisfies all proof-grade prerequisites.
    pub accepted: bool,
    /// Required binary VC count.
    pub required_vcs: usize,
    /// Number of solver dispatch/result records available to the gate.
    pub solver_dispatches: usize,
    /// Number of required VCs with checked proof certificates.
    pub checked_certificates: usize,
    /// Number of required VCs with successful replay.
    pub replayed_vcs: usize,
    /// Raw solver proof blobs seen during aggregation.
    pub raw_solver_proof_bytes: usize,
    /// Concrete proof-grade rejection reasons.
    pub rejections: Vec<BinaryReleaseGateRejection>,
}

impl BinaryReleaseGateDecision {
    /// True when the release gate rejected the summary.
    #[must_use]
    pub fn rejected(&self) -> bool {
        !self.accepted
    }
}

/// Build a stable JSON certificate gate summary from certificate prerequisites.
#[must_use]
pub fn summarize_binary_certificate_proof_grade_gate(
    summary: &BinaryVerificationCertificateSummary,
) -> BinaryCertificateProofGradeGateSummary {
    let decision = evaluate_binary_proof_grade_release_gate(summary);
    BinaryCertificateProofGradeGateSummary {
        accepted: decision.accepted,
        required_vcs: summary.vc_count,
        solver_dispatches: summary.solver_results.total_results,
        checked_certificates: summary.solver_results.proved_with_certificates,
        replayed_vcs: summary.replay_status.replayed,
        raw_solver_proof_bytes: summary.raw_solver_proof_bytes,
        rejections: decision.rejections,
    }
}

/// Proof-grade release-gate outcome for a full decompilation artifact.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct BinaryDecompilationReleaseGateDecision {
    /// True when the artifact-level gate and every function-level gate accepted.
    pub accepted: bool,
    /// Artifact-level binary verification gate decision.
    pub artifact: BinaryReleaseGateDecision,
    /// Per-function binary verification gate decisions.
    pub functions: Vec<BinaryFunctionReleaseGateDecision>,
}

impl BinaryDecompilationReleaseGateDecision {
    /// True when the full-artifact release gate rejected the artifact.
    #[must_use]
    pub fn rejected(&self) -> bool {
        !self.accepted
    }
}

/// Proof-grade release-gate outcome for one decompiled function.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct BinaryFunctionReleaseGateDecision {
    /// Recovered function name.
    pub name: String,
    /// Function entry address.
    pub entry: u64,
    /// Function-level binary verification gate decision.
    pub decision: BinaryReleaseGateDecision,
}

/// Specific reason a binary summary cannot be certified as proof-grade.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum BinaryReleaseGateRejection {
    /// The summary did not request/report proof-grade trust.
    FinalTrustLevelNotProofGrade { found: BinaryArtifactTrustLevel },
    /// Unsupported binary constructs remain.
    UnsupportedRecordsPresent { count: usize, ledger_hash: [u8; 32] },
    /// Required VC accounting does not cover every expected binary VC exactly once.
    RequiredVcCoverageIncomplete { vc_count: usize, solver_dispatches: usize },
    /// Some expected VCs are missing proved solver results or have non-proved outcomes.
    NonProvedVerificationConditions {
        vc_count: usize,
        total_results: usize,
        proved: usize,
        unproved_vcs: usize,
        non_proved_results: usize,
    },
    /// Some expected VCs are missing checked proof-certificate evidence.
    MissingProofCertificates {
        vc_count: usize,
        proved: usize,
        proved_with_certificates: usize,
        missing_certificates: usize,
    },
    /// No replay status was recorded, so replay is unknown.
    ReplayStatusMissing,
    /// Replay records do not cover every required VC.
    ReplayCoverageIncomplete { vc_count: usize, replay_records: usize, replayed: usize },
    /// At least one replay status is unknown/not attempted.
    ReplayStatusUnknown { not_attempted: usize },
    /// At least one replay was attempted but did not replay successfully.
    ReplayNotSuccessful { failed: usize, spurious: usize },
    /// Reconstructed output was not semantically validated against the lifted binary.
    ReconstructionValidationNotValidated { status: ReconstructionValidationStatus },
    /// Debug/source provenance was not exact, so proof-grade source backpropagation is closed.
    SourceProvenanceNotExact {
        status: String,
        exact_mapping_count: usize,
        ambiguous_mapping_count: usize,
        source_backpropagation_allowed: bool,
    },
    /// Independent exploit refutations must capture and replay the exact claim/input.
    ExploitRefutationReplayIncomplete {
        refutations: usize,
        captured_and_replayed: usize,
        missing_exact_inputs: usize,
        not_replayed: usize,
        unknown_refutations: usize,
    },
    /// Preserved `trust_symbolic.formula` payloads remain without an explicit proof consumer.
    SymbolicFormulasNotConsumed { target: DecompileTarget, count: usize },
    /// Raw solver proof blobs were present; only checked certificate status is proof-grade.
    RawSolverProofBytesPresent { count: usize },
}

/// Evaluate the proof-grade release gate for a binary verification certificate summary.
///
/// The gate is deliberately strict: proof-grade binary certification requires
/// no unsupported ledger entries, every required VC proved with checked
/// certificate evidence, and replay coverage that is complete and successful.
#[must_use]
pub fn evaluate_binary_proof_grade_release_gate(
    summary: &BinaryVerificationCertificateSummary,
) -> BinaryReleaseGateDecision {
    let mut rejections = Vec::new();

    if summary.final_trust_level != BinaryArtifactTrustLevel::ProofGrade {
        rejections.push(BinaryReleaseGateRejection::FinalTrustLevelNotProofGrade {
            found: summary.final_trust_level,
        });
    }

    if !summary.unsupported_ledger_summary.is_empty() {
        rejections.push(BinaryReleaseGateRejection::UnsupportedRecordsPresent {
            count: summary.unsupported_ledger_summary.total_records,
            ledger_hash: summary.unsupported_ledger_hash,
        });
    }

    if summary.solver_results.total_results != summary.vc_count {
        rejections.push(BinaryReleaseGateRejection::RequiredVcCoverageIncomplete {
            vc_count: summary.vc_count,
            solver_dispatches: summary.solver_results.total_results,
        });
    }

    if !summary.solver_results.all_proved_for(summary.vc_count) {
        rejections.push(BinaryReleaseGateRejection::NonProvedVerificationConditions {
            vc_count: summary.vc_count,
            total_results: summary.solver_results.total_results,
            proved: summary.solver_results.proved,
            unproved_vcs: summary.solver_results.unproved_vcs_for(summary.vc_count),
            non_proved_results: summary.solver_results.non_proved_results(),
        });
    }

    let missing_certificates =
        summary.solver_results.unchecked_certificate_vcs_for(summary.vc_count);
    if missing_certificates > 0 {
        rejections.push(BinaryReleaseGateRejection::MissingProofCertificates {
            vc_count: summary.vc_count,
            proved: summary.solver_results.proved,
            proved_with_certificates: summary.solver_results.proved_with_certificates,
            missing_certificates,
        });
    }

    if summary.replay_status.total == 0 {
        rejections.push(BinaryReleaseGateRejection::ReplayStatusMissing);
    } else if !summary.replay_status.all_replayed_for(summary.vc_count) {
        if summary.replay_status.total != summary.vc_count {
            rejections.push(BinaryReleaseGateRejection::ReplayCoverageIncomplete {
                vc_count: summary.vc_count,
                replay_records: summary.replay_status.total,
                replayed: summary.replay_status.replayed,
            });
        }

        if summary.replay_status.unknown_count() > 0 {
            rejections.push(BinaryReleaseGateRejection::ReplayStatusUnknown {
                not_attempted: summary.replay_status.not_attempted,
            });
        }

        if summary.replay_status.unsuccessful_count() > 0 {
            rejections.push(BinaryReleaseGateRejection::ReplayNotSuccessful {
                failed: summary.replay_status.failed,
                spurious: summary.replay_status.spurious,
            });
        }
    } else {
        debug_assert_eq!(summary.replay_status.unknown_count(), 0);
        debug_assert_eq!(summary.replay_status.unsuccessful_count(), 0);
    }

    if summary.raw_solver_proof_bytes > 0 {
        rejections.push(BinaryReleaseGateRejection::RawSolverProofBytesPresent {
            count: summary.raw_solver_proof_bytes,
        });
    }

    push_symbolic_formula_summary_rejection(
        &mut rejections,
        summary.preserved_symbolic_formulas,
        summary.symbolic_formula_consumer_accepted,
    );

    push_exploit_refutation_rejection(&mut rejections, &summary.exploit_refutations);

    BinaryReleaseGateDecision { accepted: rejections.is_empty(), rejections }
}

/// Evaluate proof-grade prerequisites for a full decompilation artifact.
///
/// The artifact-level verification summary and every recovered function are
/// evaluated independently using their required VC counts, unsupported ledgers,
/// checked certificate statuses, replay records, and final trust levels. Raw
/// solver proof bytes attached to solver results never count as checked
/// certificate coverage.
pub fn evaluate_binary_decompilation_artifact_proof_grade_release_gate(
    lifted_binary_digest: [u8; 32],
    artifact: &DecompilationArtifact,
) -> Result<BinaryDecompilationReleaseGateDecision, CertError> {
    let artifact_unsupported = combined_unsupported_ledger(
        &artifact.unsupported,
        &artifact.verification.unsupported_ledger,
    );
    let artifact_summary = BinaryVerificationCertificateSummary::from_binary_verification_summary(
        lifted_binary_digest,
        format!("{:?}", artifact.binary.format),
        artifact.binary.architecture.clone(),
        &artifact_unsupported,
        &artifact.verification,
        artifact.trust_level,
    )?;
    let mut artifact_decision = artifact_summary.proof_grade_release_gate();
    push_reconstruction_validation_rejection(
        &mut artifact_decision.rejections,
        artifact.reconstruction.validation,
    );
    push_symbolic_formula_consumer_rejection(
        &mut artifact_decision.rejections,
        &artifact.reconstruction.target,
        &artifact.reconstruction.outputs,
    );
    push_source_provenance_rejection(
        &mut artifact_decision.rejections,
        &artifact.source_provenance,
    );
    push_exploit_refutation_rejection(
        &mut artifact_decision.rejections,
        &BinaryExploitRefutationSummary::from_witnesses(&artifact.witnesses),
    );
    artifact_decision.accepted = artifact_decision.rejections.is_empty();

    let mut functions = Vec::with_capacity(artifact.functions.len());
    for function in &artifact.functions {
        let function_unsupported = combined_unsupported_ledger(
            &function.unsupported,
            &function.verification.unsupported_ledger,
        );
        let function_summary =
            BinaryVerificationCertificateSummary::from_binary_verification_summary(
                lifted_binary_digest,
                format!("{:?}", artifact.binary.format),
                artifact.binary.architecture.clone(),
                &function_unsupported,
                &function.verification,
                function.trust_level,
            )?;
        let mut decision = function_summary.proof_grade_release_gate();
        let reconstruction_status = function
            .output
            .as_ref()
            .map_or(ReconstructionValidationStatus::NotAttempted, |output| output.validation);
        push_reconstruction_validation_rejection(&mut decision.rejections, reconstruction_status);
        if let Some(output) = &function.output {
            push_symbolic_formula_consumer_rejection(
                &mut decision.rejections,
                &output.target,
                std::slice::from_ref(output),
            );
        }
        decision.accepted = decision.rejections.is_empty();
        functions.push(BinaryFunctionReleaseGateDecision {
            name: function.name.clone(),
            entry: function.entry,
            decision,
        });
    }

    let accepted =
        artifact_decision.accepted && functions.iter().all(|function| function.decision.accepted);

    Ok(BinaryDecompilationReleaseGateDecision { accepted, artifact: artifact_decision, functions })
}

fn combined_unsupported_ledger(
    primary: &UnsupportedLedger,
    verification: &UnsupportedLedger,
) -> UnsupportedLedger {
    let mut records = Vec::with_capacity(primary.records.len() + verification.records.len());
    records.extend(primary.records.iter().cloned());
    records.extend(verification.records.iter().cloned());
    UnsupportedLedger { records }
}

fn push_source_provenance_rejection(
    rejections: &mut Vec<BinaryReleaseGateRejection>,
    source_provenance: &BinarySourceProvenanceSummary,
) {
    if !source_provenance.effective_source_backpropagation_allowed() {
        rejections.push(BinaryReleaseGateRejection::SourceProvenanceNotExact {
            status: source_provenance.status.clone(),
            exact_mapping_count: source_provenance.exact_mapping_count,
            ambiguous_mapping_count: source_provenance.ambiguous_mapping_count,
            source_backpropagation_allowed: source_provenance.source_backpropagation_allowed,
        });
    }
}

fn push_exploit_refutation_rejection(
    rejections: &mut Vec<BinaryReleaseGateRejection>,
    summary: &BinaryExploitRefutationSummary,
) {
    if summary.total_refutations > 0 && !summary.all_captured_and_replayed() {
        rejections.push(BinaryReleaseGateRejection::ExploitRefutationReplayIncomplete {
            refutations: summary.total_refutations,
            captured_and_replayed: summary.captured_and_replayed,
            missing_exact_inputs: summary.missing_exact_inputs,
            not_replayed: summary.not_replayed,
            unknown_refutations: summary.unknown_refutations,
        });
    }
}

fn push_symbolic_formula_summary_rejection(
    rejections: &mut Vec<BinaryReleaseGateRejection>,
    preserved_symbolic_formulas: usize,
    symbolic_formula_consumer_accepted: bool,
) {
    if preserved_symbolic_formulas > 0 && !symbolic_formula_consumer_accepted {
        rejections.push(BinaryReleaseGateRejection::SymbolicFormulasNotConsumed {
            target: DecompileTarget::TrustIr,
            count: preserved_symbolic_formulas,
        });
    }
}

fn push_reconstruction_validation_rejection(
    rejections: &mut Vec<BinaryReleaseGateRejection>,
    status: ReconstructionValidationStatus,
) {
    if status != ReconstructionValidationStatus::Validated {
        rejections
            .push(BinaryReleaseGateRejection::ReconstructionValidationNotValidated { status });
    }
}

fn push_symbolic_formula_consumer_rejection(
    rejections: &mut Vec<BinaryReleaseGateRejection>,
    target: &DecompileTarget,
    outputs: &[DecompiledOutput],
) {
    let count = outputs
        .iter()
        .filter(|output| &output.target == target)
        .filter(|output| !output_symbolic_formulas_have_consumer(output))
        .map(|output| output.preserved_symbolic_formulas.len())
        .sum();

    if count > 0 {
        rejections.push(BinaryReleaseGateRejection::SymbolicFormulasNotConsumed {
            target: target.clone(),
            count,
        });
    }
}

fn output_symbolic_formulas_have_consumer(output: &DecompiledOutput) -> bool {
    output.preserved_symbolic_formulas.is_empty()
        || (output.target_validation_blockers.is_empty()
            && output.preserved_symbolic_formulas.iter().all(|formula| {
                output
                    .diagnostics
                    .iter()
                    .any(|diagnostic| formula.matches_schema_aware_consumer_diagnostic(diagnostic))
            }))
}

#[cfg(test)]
mod tests {
    use trust_types::{
        BinaryArtifactDigest, BinaryArtifactDigestIdentity, BinarySelectedImageIdentity,
        BinaryVerificationSummary, DecompiledFunction, DecompiledOutput, Formula,
        PreservedSymbolicFormula, ProofCertificateStatus, ProofStrength, ReconstructionSummary,
        Sort, UnsupportedRecord,
    };

    use super::*;

    fn proved() -> VerificationResult {
        VerificationResult::Proved {
            solver: "ay".into(),
            time_ms: 1,
            strength: ProofStrength::smt_unsat(),
            proof_certificate: Some(b"checked-binary-proof".to_vec()),
            solver_warnings: None,
            native_proof_envelope: None,
        }
    }

    fn proved_without_certificate() -> VerificationResult {
        VerificationResult::Proved {
            solver: "ay".into(),
            time_ms: 1,
            strength: ProofStrength::smt_unsat(),
            proof_certificate: None,
            solver_warnings: None,
            native_proof_envelope: None,
        }
    }

    fn unknown() -> VerificationResult {
        VerificationResult::Unknown {
            solver: "ay".into(),
            time_ms: 1,
            reason: "solver returned unknown".to_string(),
        }
    }

    fn unsupported_ledger() -> UnsupportedLedger {
        UnsupportedLedger {
            records: vec![UnsupportedRecord {
                stage: "lift".to_string(),
                architecture: Some("x86_64".to_string()),
                origin: None,
                opcode: Some("syscall".to_string()),
                operand: None,
                feature: "system-call-side-effects".to_string(),
            }],
        }
    }

    fn summary(
        ledger: &UnsupportedLedger,
        vc_count: usize,
        results: &[VerificationResult],
        replay_statuses: &[ReplayStatus],
    ) -> BinaryVerificationCertificateSummary {
        BinaryVerificationCertificateSummary::from_results(
            digest_lifted_binary(b"lifted-trust_ir"),
            "trust_ir+binary",
            "x86_64",
            ledger,
            vc_count,
            results,
            replay_statuses,
            BinaryArtifactTrustLevel::ProofGrade,
        )
        .expect("summary should build")
    }

    fn dispatch_summary(
        ledger: &UnsupportedLedger,
        dispatches: &[SolverDispatchRecord],
    ) -> BinaryVerificationCertificateSummary {
        BinaryVerificationCertificateSummary::from_solver_dispatch_records(
            digest_lifted_binary(b"lifted-trust_ir"),
            "trust_ir+binary",
            "x86_64",
            ledger,
            dispatches,
            BinaryArtifactTrustLevel::ProofGrade,
        )
        .expect("summary should build")
    }

    fn dispatch_summary_with_vc_count(
        ledger: &UnsupportedLedger,
        vc_count: usize,
        dispatches: &[SolverDispatchRecord],
    ) -> BinaryVerificationCertificateSummary {
        BinaryVerificationCertificateSummary::from_required_solver_dispatch_records(
            digest_lifted_binary(b"lifted-trust_ir"),
            "trust_ir+binary",
            "x86_64",
            ledger,
            vc_count,
            dispatches,
            BinaryArtifactTrustLevel::ProofGrade,
        )
        .expect("summary should build")
    }

    fn checked_dispatch(id: &str) -> SolverDispatchRecord {
        let canonical_vc_bytes = canonical_vc_bytes(id);
        let export_dispatch = SolverDispatchRecord {
            id: format!("export-run:{id}"),
            solver: "ay".to_string(),
            backend: Some("ay-lfsc".to_string()),
            status: SolverDispatchStatus::Unsat,
            query_semantics: SolverQuerySemantics::SatIsCounterexample,
            replay: ReplayStatus::Replayed,
            origin: Some(binary_origin()),
            binary_artifact_digest_identity: Some(binary_artifact_digest_identity()),
            certificate: ProofCertificateStatus::Present {
                format: "lfsc".to_string(),
                sha256: None,
                artifact_path: None,
            },
            ..Default::default()
        };
        let export = crate::checked_binary_certificate::SolverProofExport::new(
            &export_dispatch,
            &canonical_vc_bytes,
            "lfsc",
            format!("normalized lfsc proof bytes for {id}").into_bytes(),
            Some("4.13.0".to_string()),
            1_777_070_400_000,
        );
        let checker = crate::checked_binary_certificate::StructuralBinaryCertificateChecker::new(
            "ay-cert-check",
            "1.0.0",
            vec!["lfsc".to_string()],
            1_777_070_401_000,
        );
        let dir = temp_artifact_dir(format!("manifest-backed-{}", id.replace(':', "-")).as_str());
        let artifact_ref = crate::checked_binary_certificate::produce_checked_certificate_artifact(
            &checker,
            crate::checked_binary_certificate::BinaryCertificateCheckRequest::from_export(
                &export_dispatch,
                &canonical_vc_bytes,
                &export,
            ),
            &dir,
        )
        .expect("checked artifact should persist for manifest-backed dispatch");
        let manifest = crate::checked_binary_certificate::CheckedBinaryCertificateManifest::from_artifact_refs(
            &dir,
            &[artifact_ref],
        )
        .expect("manifest should build from checked artifact");
        let entry =
            manifest.certificates.first().expect("manifest should contain checked artifact");
        let acceptance_request =
            crate::checked_binary_certificate::CheckedBinaryCertificateManifestAcceptanceRequest::from_manifest_entry_and_solver_proof_export_metadata(
                entry,
                export.normalized_metadata(),
            )
            .expect("acceptance request should bind solver proof export")
            .with_production_checker_evidence(production_checker_evidence(entry))
            .expect("acceptance request should bind production checker evidence");

        let mut dispatch = SolverDispatchRecord {
            id: id.to_string(),
            solver: "ay".to_string(),
            backend: Some("ay-lfsc".to_string()),
            status: SolverDispatchStatus::Unsat,
            query_semantics: SolverQuerySemantics::SatIsCounterexample,
            replay: ReplayStatus::Replayed,
            origin: Some(binary_origin()),
            binary_artifact_digest_identity: Some(binary_artifact_digest_identity()),
            certificate: ProofCertificateStatus::Present {
                format: "lfsc".to_string(),
                sha256: None,
                artifact_path: None,
            },
            ..Default::default()
        };
        crate::checked_binary_certificate::import_checked_certificate_manifest_entry_for_dispatch(
            &mut dispatch,
            &canonical_vc_bytes,
            &dir,
            entry,
            &acceptance_request,
        )
        .expect("manifest-backed checked dispatch should import");
        let _ = std::fs::remove_dir_all(&dir);
        dispatch
    }

    fn canonical_vc_bytes(id: &str) -> Vec<u8> {
        format!(r#"{{"vc":"binary safety {id}"}}"#).into_bytes()
    }

    fn temp_artifact_dir(name: &str) -> std::path::PathBuf {
        static COUNTER: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
        let unique = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .expect("system time should be after Unix epoch")
            .as_nanos();
        let counter = COUNTER.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        std::env::temp_dir()
            .join(format!("trust-proof-cert-{name}-{}-{unique}-{counter}", std::process::id()))
    }

    fn production_checker_evidence(
        entry: &crate::checked_binary_certificate::CheckedBinaryCertificateManifestEntry,
    ) -> crate::checked_binary_certificate::CheckedBinaryCertificateProductionCheckerEvidence {
        let transcript =
            crate::checked_binary_certificate::CheckedBinaryCertificateExternalProcessTranscript::new(
                "ay-cert-check",
                [
                    "ay-cert-check".to_string(),
                    "--format".to_string(),
                    entry.format.clone(),
                    "--certificate".to_string(),
                    entry.certificate_path.display().to_string(),
                ],
                0,
                Some(trust_types::stable_sha256_hex(
                    b"checker stdout: accepted",
                )),
                Some(trust_types::stable_sha256_hex(b"")),
            );
        crate::checked_binary_certificate::CheckedBinaryCertificateProductionCheckerEvidence::external_process_for_manifest_entry(
            entry,
            trust_types::stable_sha256_hex(b"ay-cert-check production executable"),
            Some(trust_types::stable_sha256_hex(
                b"ay-cert-check production config",
            )),
            transcript,
            1_777_070_401_000,
        )
        .expect("production checker evidence should build")
    }

    fn binary_origin() -> BinaryOrigin {
        BinaryOrigin {
            binary_path: Some("fixtures/tiny".to_string()),
            function_entry: Some(0x401000),
            instruction_address: 0x401010,
            instruction_size: Some(4),
            encoding: Some(0x90),
            instruction_bytes: vec![0x90, 0x90, 0x90, 0x90],
            source: None,
        }
    }

    fn binary_artifact_digest_identity() -> BinaryArtifactDigestIdentity {
        BinaryArtifactDigestIdentity {
            root_artifact_digest: Some(BinaryArtifactDigest::sha256(
                trust_types::stable_sha256_hex(b"fixtures/tiny root artifact"),
            )),
            selected_image: Some(BinarySelectedImageIdentity {
                file_offset: 0,
                file_size: 4,
                sha256: trust_types::stable_sha256_hex(&[0x90, 0x90, 0x90, 0x90]),
            }),
        }
    }

    fn checked_function_dispatch(id: &str, function: &str) -> SolverDispatchRecord {
        SolverDispatchRecord { function: Some(function.to_string()), ..checked_dispatch(id) }
    }

    fn raw_unchecked_unreplayed_dispatch(id: &str, function: &str) -> SolverDispatchRecord {
        SolverDispatchRecord {
            id: id.to_string(),
            function: Some(function.to_string()),
            solver: "ay".to_string(),
            status: SolverDispatchStatus::Unsat,
            replay: ReplayStatus::NotAttempted,
            certificate: ProofCertificateStatus::Present {
                format: "lfsc".to_string(),
                sha256: Some(format!("{id}-raw-sha256")),
                artifact_path: None,
            },
            result: Some(VerificationResult::Proved {
                solver: "ay".into(),
                time_ms: 1,
                strength: ProofStrength::smt_unsat(),
                proof_certificate: Some(b"raw solver proof bytes".to_vec()),
                solver_warnings: None,
                native_proof_envelope: None,
            }),
            ..Default::default()
        }
    }

    fn verification_summary(
        required_vcs: usize,
        dispatches: Vec<SolverDispatchRecord>,
    ) -> BinaryVerificationSummary {
        let mut summary = BinaryVerificationSummary::from_solver_dispatch(dispatches);
        summary.total_vcs = required_vcs;
        summary.trust_level = BinaryArtifactTrustLevel::ProofGrade;
        summary
    }

    fn proof_grade_function(
        name: &str,
        entry: u64,
        required_vcs: usize,
        dispatches: Vec<SolverDispatchRecord>,
    ) -> DecompiledFunction {
        DecompiledFunction {
            name: name.to_string(),
            entry,
            verification: verification_summary(required_vcs, dispatches),
            output: Some(validated_output()),
            trust_level: BinaryArtifactTrustLevel::ProofGrade,
            ..Default::default()
        }
    }

    fn validated_output() -> DecompiledOutput {
        DecompiledOutput {
            validation: ReconstructionValidationStatus::Validated,
            trust_level: BinaryArtifactTrustLevel::ProofGrade,
            ..Default::default()
        }
    }

    fn consumed_symbolic_output() -> DecompiledOutput {
        let formula = preserved_symbolic_formula();
        DecompiledOutput {
            preserved_symbolic_formulas: vec![formula.clone()],
            diagnostics: vec![formula.schema_aware_consumer_diagnostic()],
            ..validated_output()
        }
    }

    fn unconsumed_symbolic_output() -> DecompiledOutput {
        DecompiledOutput {
            preserved_symbolic_formulas: vec![preserved_symbolic_formula()],
            ..validated_output()
        }
    }

    fn preserved_symbolic_formula() -> PreservedSymbolicFormula {
        PreservedSymbolicFormula {
            target: DecompileTarget::TrustIr,
            function: Some("main".to_string()),
            block: Some(0),
            statement_index: Some(1),
            location: "bb0[1].rvalue".to_string(),
            formula: Formula::BvAdd(
                Box::new(Formula::Var("x0".to_string(), Sort::BitVec(64))),
                Box::new(Formula::BitVec { value: 1, width: 64 }),
                64,
            ),
        }
    }

    fn validated_reconstruction() -> ReconstructionSummary {
        ReconstructionSummary {
            validation: ReconstructionValidationStatus::Validated,
            trust_level: BinaryArtifactTrustLevel::ProofGrade,
            ..Default::default()
        }
    }

    fn exact_source_provenance() -> BinarySourceProvenanceSummary {
        BinarySourceProvenanceSummary {
            status: "exact".to_string(),
            exact_mapping_count: 1,
            ambiguous_mapping_count: 0,
            diagnostics: Vec::new(),
            source_backpropagation_allowed: true,
        }
    }

    fn present_unchecked_dispatch(id: &str) -> SolverDispatchRecord {
        SolverDispatchRecord {
            certificate: ProofCertificateStatus::Present {
                format: "lfsc".to_string(),
                sha256: Some(format!("{id}-sha256")),
                artifact_path: None,
            },
            ..checked_dispatch(id)
        }
    }

    #[test]
    fn proof_grade_gate_rejects_certificate_shaped_bytes_until_checked() {
        let ledger = UnsupportedLedger::default();
        let results = vec![proved(), proved()];
        let summary =
            summary(&ledger, 2, &results, &[ReplayStatus::Replayed, ReplayStatus::Replayed]);

        let decision = summary.proof_grade_release_gate();

        assert!(decision.rejected());
        assert!(decision.rejections.iter().any(|reason| {
            matches!(
                reason,
                BinaryReleaseGateRejection::MissingProofCertificates {
                    vc_count: 2,
                    proved: 2,
                    proved_with_certificates: 0,
                    missing_certificates: 2,
                }
            )
        }));
    }

    #[test]
    fn certificate_gate_summary_json_uses_stable_field_names() {
        let ledger = UnsupportedLedger::default();
        let results = vec![proved()];
        let summary = summary(&ledger, 1, &results, &[ReplayStatus::Replayed]);
        let gate_summary = summarize_binary_certificate_proof_grade_gate(&summary);

        let json = serde_json::to_value(&gate_summary).expect("gate summary should serialize");
        for field in [
            "required_vcs",
            "solver_dispatches",
            "checked_certificates",
            "replayed_vcs",
            "raw_solver_proof_bytes",
            "accepted",
            "rejections",
        ] {
            assert!(json.get(field).is_some(), "missing stable field {field}: {json}");
        }
        assert_eq!(json["required_vcs"], 1);
        assert_eq!(json["solver_dispatches"], 1);
        assert_eq!(json["checked_certificates"], 0);
        assert_eq!(json["replayed_vcs"], 1);
        assert_eq!(json["raw_solver_proof_bytes"], 1);
        assert_eq!(json["accepted"], false);
        assert!(!json["rejections"].as_array().expect("rejections array").is_empty());

        let certificate_json =
            serde_json::to_value(&summary).expect("certificate summary should serialize");
        assert!(certificate_json.get("raw_solver_proof_bytes").is_some());
        assert_eq!(certificate_json["raw_solver_proof_bytes"], 1);
        assert!(certificate_json.get("certificate_checks").is_some());
        assert_eq!(certificate_json["certificate_checks"]["raw_solver_proof_bytes"], 1);
        assert_eq!(
            certificate_json["certificate_checks"]["raw_solver_proof_bytes_satisfy_coverage"],
            false
        );
        assert!(certificate_json.get("solver_results").is_some());
        assert!(certificate_json.get("replay_status").is_some());
    }

    #[test]
    fn proof_grade_gate_accepts_only_checked_certificates_with_full_replay() {
        let ledger = UnsupportedLedger::default();
        let dispatches = vec![checked_dispatch("vc0"), checked_dispatch("vc1")];
        let summary = dispatch_summary(&ledger, &dispatches);

        let decision = summary.proof_grade_release_gate();

        assert_eq!(summary.solver_results.proved, 2);
        assert_eq!(summary.solver_results.proved_with_certificates, 2);
        assert_eq!(summary.replay_status.replayed, 2);
        assert_eq!(summary.certificate_checks.required_vcs, 2);
        assert_eq!(summary.certificate_checks.certificate_candidates, 2);
        assert_eq!(summary.certificate_checks.checked_certificates, 2);
        assert_eq!(summary.certificate_checks.missing_checked_certificates, 0);
        assert!(summary.certificate_checks.checked_certificates_satisfy_coverage);
        assert!(!summary.certificate_checks.raw_solver_proof_bytes_satisfy_coverage);
        assert!(summary.certificate_checks.records.iter().all(|record| record.checked));
        assert!(!decision.rejected(), "{:?}", decision.rejections);
    }

    #[test]
    fn proof_grade_gate_rejects_present_but_unchecked_dispatch_certificates() {
        let ledger = UnsupportedLedger::default();
        let dispatches = vec![checked_dispatch("vc0"), present_unchecked_dispatch("vc1")];
        let summary = dispatch_summary(&ledger, &dispatches);

        let decision = summary.proof_grade_release_gate();

        assert!(decision.rejected());
        assert!(decision.rejections.iter().any(|reason| {
            matches!(
                reason,
                BinaryReleaseGateRejection::MissingProofCertificates {
                    vc_count: 2,
                    proved: 2,
                    proved_with_certificates: 1,
                    missing_certificates: 1,
                }
            )
        }));
    }

    #[test]
    fn proof_grade_gate_rejects_checked_status_without_canonical_digest() {
        let ledger = UnsupportedLedger::default();
        let mut dispatch = checked_dispatch("vc0");
        dispatch.certificate = ProofCertificateStatus::Checked {
            checker: "ay-cert-check".to_string(),
            format: "lfsc".to_string(),
            sha256: Some("vc0-sha256".to_string()),
        };
        let summary = dispatch_summary(&ledger, &[dispatch]);

        let decision = summary.proof_grade_release_gate();

        assert!(decision.rejected());
        assert_eq!(summary.solver_results.proved, 1);
        assert_eq!(summary.solver_results.proved_with_certificates, 0);
        assert_eq!(summary.certificate_checks.checked_certificates, 0);
        assert_eq!(summary.certificate_checks.records[0].status, "checked-invalid");
        assert!(
            summary.certificate_checks.records[0].coherence_failures.iter().any(|failure| failure
                == "checked certificate digest is not canonical lowercase sha256 hex")
        );
        assert!(decision.rejections.iter().any(|reason| {
            matches!(
                reason,
                BinaryReleaseGateRejection::MissingProofCertificates {
                    vc_count: 1,
                    proved: 1,
                    proved_with_certificates: 0,
                    missing_certificates: 1,
                }
            )
        }));
    }

    #[test]
    fn decompilation_artifact_gate_rejects_mixed_function_missing_cert_and_replay_coverage() {
        let good = checked_function_dispatch("good:vc0", "good");
        let raw_bad = raw_unchecked_unreplayed_dispatch("bad:vc0", "bad");
        let artifact = DecompilationArtifact {
            verification: verification_summary(3, vec![good.clone(), raw_bad.clone()]),
            functions: vec![
                proof_grade_function("good", 0x401000, 1, vec![good]),
                proof_grade_function("bad", 0x402000, 2, vec![raw_bad]),
            ],
            reconstruction: validated_reconstruction(),
            source_provenance: exact_source_provenance(),
            trust_level: BinaryArtifactTrustLevel::ProofGrade,
            ..Default::default()
        };

        let decision = evaluate_binary_decompilation_artifact_proof_grade_release_gate(
            digest_lifted_binary(b"mixed-artifact"),
            &artifact,
        )
        .expect("artifact gate should evaluate");

        assert!(decision.rejected());
        assert!(decision.artifact.rejections.iter().any(|reason| {
            matches!(
                reason,
                BinaryReleaseGateRejection::MissingProofCertificates {
                    vc_count: 3,
                    proved: 2,
                    proved_with_certificates: 1,
                    missing_certificates: 2,
                }
            )
        }));
        assert!(decision.artifact.rejections.iter().any(|reason| {
            matches!(
                reason,
                BinaryReleaseGateRejection::ReplayCoverageIncomplete {
                    vc_count: 3,
                    replay_records: 2,
                    replayed: 1,
                }
            )
        }));

        assert_eq!(decision.functions.len(), 2);
        assert!(!decision.functions[0].decision.rejected());
        let bad = &decision.functions[1];
        assert_eq!(bad.name, "bad");
        assert_eq!(bad.entry, 0x402000);
        assert!(bad.decision.rejected());
        assert!(bad.decision.rejections.iter().any(|reason| {
            matches!(
                reason,
                BinaryReleaseGateRejection::MissingProofCertificates {
                    vc_count: 2,
                    proved: 1,
                    proved_with_certificates: 0,
                    missing_certificates: 2,
                }
            )
        }));
        assert!(bad.decision.rejections.iter().any(|reason| {
            matches!(
                reason,
                BinaryReleaseGateRejection::ReplayCoverageIncomplete {
                    vc_count: 2,
                    replay_records: 1,
                    replayed: 0,
                }
            )
        }));
    }

    #[test]
    fn decompilation_artifact_gate_accepts_manifest_backed_proof_grade_artifact() {
        let main = checked_function_dispatch("main:vc0", "main");
        let helper = checked_function_dispatch("helper:vc0", "helper");
        let artifact = DecompilationArtifact {
            verification: verification_summary(2, vec![main.clone(), helper.clone()]),
            functions: vec![
                proof_grade_function("main", 0x401000, 1, vec![main]),
                proof_grade_function("helper", 0x402000, 1, vec![helper]),
            ],
            reconstruction: validated_reconstruction(),
            source_provenance: exact_source_provenance(),
            trust_level: BinaryArtifactTrustLevel::ProofGrade,
            ..Default::default()
        };

        let decision = evaluate_binary_decompilation_artifact_proof_grade_release_gate(
            digest_lifted_binary(b"accepted-artifact"),
            &artifact,
        )
        .expect("artifact gate should evaluate");

        assert!(!decision.rejected(), "{:?}", decision);
        assert!(decision.artifact.accepted);
        assert_eq!(decision.functions.len(), 2);
        assert!(decision.functions.iter().all(|function| function.decision.accepted));
    }

    #[test]
    fn decompilation_artifact_gate_rejects_unconsumed_preserved_symbolic_formulas() {
        let dispatch = checked_function_dispatch("main:vc0", "main");
        let artifact = DecompilationArtifact {
            verification: verification_summary(1, vec![dispatch.clone()]),
            functions: vec![DecompiledFunction {
                output: Some(unconsumed_symbolic_output()),
                ..proof_grade_function("main", 0x401000, 1, vec![dispatch])
            }],
            reconstruction: ReconstructionSummary {
                outputs: vec![unconsumed_symbolic_output()],
                ..validated_reconstruction()
            },
            source_provenance: exact_source_provenance(),
            trust_level: BinaryArtifactTrustLevel::ProofGrade,
            ..Default::default()
        };

        let decision = evaluate_binary_decompilation_artifact_proof_grade_release_gate(
            digest_lifted_binary(b"unconsumed-symbolic-formula"),
            &artifact,
        )
        .expect("artifact gate should evaluate");

        assert!(decision.rejected());
        assert!(decision.artifact.rejections.iter().any(|reason| {
            matches!(
                reason,
                BinaryReleaseGateRejection::SymbolicFormulasNotConsumed {
                    target: DecompileTarget::TrustIr,
                    count: 1,
                }
            )
        }));
        assert!(decision.functions[0].decision.rejections.iter().any(|reason| {
            matches!(
                reason,
                BinaryReleaseGateRejection::SymbolicFormulasNotConsumed {
                    target: DecompileTarget::TrustIr,
                    count: 1,
                }
            )
        }));
        assert!(!decision.artifact.rejections.iter().any(|reason| {
            matches!(reason, BinaryReleaseGateRejection::MissingProofCertificates { .. })
        }));
    }

    #[test]
    fn decompilation_artifact_gate_accepts_symbolic_formulas_with_consumer_evidence() {
        let dispatch = checked_function_dispatch("main:vc0", "main");
        let artifact = DecompilationArtifact {
            verification: verification_summary(1, vec![dispatch.clone()]),
            functions: vec![DecompiledFunction {
                output: Some(consumed_symbolic_output()),
                ..proof_grade_function("main", 0x401000, 1, vec![dispatch])
            }],
            reconstruction: ReconstructionSummary {
                outputs: vec![consumed_symbolic_output()],
                ..validated_reconstruction()
            },
            source_provenance: exact_source_provenance(),
            trust_level: BinaryArtifactTrustLevel::ProofGrade,
            ..Default::default()
        };

        let decision = evaluate_binary_decompilation_artifact_proof_grade_release_gate(
            digest_lifted_binary(b"consumed-symbolic-formula"),
            &artifact,
        )
        .expect("artifact gate should evaluate");

        assert!(!decision.rejected(), "{:?}", decision);
        assert!(decision.artifact.accepted);
        assert!(decision.functions.iter().all(|function| function.decision.accepted));
    }

    #[test]
    fn proof_grade_summary_gate_rejects_preserved_symbolic_formulas_without_consumer_evidence() {
        let ledger = UnsupportedLedger::default();
        let dispatch = checked_function_dispatch("main:vc0", "main");
        let mut summary = dispatch_summary(&ledger, &[dispatch]);
        summary.preserved_symbolic_formulas = 1;

        let decision = summary.proof_grade_release_gate();

        assert!(!summary.symbolic_formula_consumer_accepted);
        assert!(decision.rejected());
        assert!(decision.rejections.iter().any(|reason| {
            matches!(
                reason,
                BinaryReleaseGateRejection::SymbolicFormulasNotConsumed {
                    target: DecompileTarget::TrustIr,
                    count: 1,
                }
            )
        }));
        assert!(!decision.rejections.iter().any(|reason| {
            matches!(reason, BinaryReleaseGateRejection::MissingProofCertificates { .. })
        }));
    }

    #[test]
    fn proof_grade_summary_gate_accepts_consumed_preserved_symbolic_formulas() {
        let ledger = UnsupportedLedger::default();
        let dispatch = checked_function_dispatch("main:vc0", "main");
        let summary =
            dispatch_summary(&ledger, &[dispatch]).with_symbolic_formula_consumer_evidence(1, true);

        let decision = summary.proof_grade_release_gate();

        assert!(!decision.rejected(), "{:?}", decision);
    }

    #[test]
    fn decompilation_artifact_gate_rejects_checked_replayed_supported_artifact_without_exact_provenance()
     {
        let dispatch = checked_function_dispatch("main:vc0", "main");
        let artifact = DecompilationArtifact {
            verification: verification_summary(1, vec![dispatch.clone()]),
            functions: vec![proof_grade_function("main", 0x401000, 1, vec![dispatch])],
            reconstruction: validated_reconstruction(),
            trust_level: BinaryArtifactTrustLevel::ProofGrade,
            ..Default::default()
        };

        let decision = evaluate_binary_decompilation_artifact_proof_grade_release_gate(
            digest_lifted_binary(b"no-exact-provenance-artifact"),
            &artifact,
        )
        .expect("artifact gate should evaluate");

        assert!(decision.rejected());
        assert!(decision.artifact.rejections.iter().any(|reason| {
            matches!(
                reason,
                BinaryReleaseGateRejection::SourceProvenanceNotExact {
                    status,
                    exact_mapping_count: 0,
                    ambiguous_mapping_count: 0,
                    source_backpropagation_allowed: false,
                } if status == "unavailable"
            )
        }));
        assert!(!decision.artifact.rejections.iter().any(|reason| {
            matches!(
                reason,
                BinaryReleaseGateRejection::MissingProofCertificates { .. }
                    | BinaryReleaseGateRejection::ReplayStatusMissing
                    | BinaryReleaseGateRejection::ReplayCoverageIncomplete { .. }
                    | BinaryReleaseGateRejection::ReplayStatusUnknown { .. }
                    | BinaryReleaseGateRejection::ReplayNotSuccessful { .. }
                    | BinaryReleaseGateRejection::UnsupportedRecordsPresent { .. }
            )
        }));
    }

    #[test]
    fn decompilation_artifact_gate_rejects_unvalidated_reconstruction() {
        let dispatch = checked_function_dispatch("main:vc0", "main");
        let artifact = DecompilationArtifact {
            verification: verification_summary(1, vec![dispatch.clone()]),
            functions: vec![DecompiledFunction {
                output: Some(DecompiledOutput {
                    validation: ReconstructionValidationStatus::Unknown,
                    ..validated_output()
                }),
                ..proof_grade_function("main", 0x401000, 1, vec![dispatch])
            }],
            source_provenance: exact_source_provenance(),
            trust_level: BinaryArtifactTrustLevel::ProofGrade,
            ..Default::default()
        };

        let decision = evaluate_binary_decompilation_artifact_proof_grade_release_gate(
            digest_lifted_binary(b"unvalidated-reconstruction"),
            &artifact,
        )
        .expect("artifact gate should evaluate");

        assert!(decision.rejected());
        assert!(decision.artifact.rejections.iter().any(|reason| {
            matches!(
                reason,
                BinaryReleaseGateRejection::ReconstructionValidationNotValidated {
                    status: ReconstructionValidationStatus::NotAttempted,
                }
            )
        }));
        assert!(decision.functions[0].decision.rejections.iter().any(|reason| {
            matches!(
                reason,
                BinaryReleaseGateRejection::ReconstructionValidationNotValidated {
                    status: ReconstructionValidationStatus::Unknown,
                }
            )
        }));
    }

    #[test]
    fn proof_grade_gate_rejects_missing_required_vc_dispatch_coverage() {
        let ledger = UnsupportedLedger::default();
        let dispatches = vec![checked_dispatch("vc0")];
        let summary = dispatch_summary_with_vc_count(&ledger, 2, &dispatches);

        let decision = summary.proof_grade_release_gate();

        assert!(decision.rejected());
        assert!(decision.rejections.iter().any(|reason| {
            matches!(
                reason,
                BinaryReleaseGateRejection::RequiredVcCoverageIncomplete {
                    vc_count: 2,
                    solver_dispatches: 1,
                }
            )
        }));
        assert!(decision.rejections.iter().any(|reason| {
            matches!(
                reason,
                BinaryReleaseGateRejection::NonProvedVerificationConditions {
                    vc_count: 2,
                    total_results: 1,
                    proved: 1,
                    unproved_vcs: 1,
                    non_proved_results: 0,
                }
            )
        }));
        assert!(decision.rejections.iter().any(|reason| {
            matches!(
                reason,
                BinaryReleaseGateRejection::MissingProofCertificates {
                    vc_count: 2,
                    proved: 1,
                    proved_with_certificates: 1,
                    missing_certificates: 1,
                }
            )
        }));
        assert!(decision.rejections.iter().any(|reason| {
            matches!(
                reason,
                BinaryReleaseGateRejection::ReplayCoverageIncomplete {
                    vc_count: 2,
                    replay_records: 1,
                    replayed: 1,
                }
            )
        }));
    }

    #[test]
    fn proof_grade_gate_from_verification_summary_ignores_raw_aggregate_counts() {
        let ledger = UnsupportedLedger::default();
        let verification = BinaryVerificationSummary {
            trust_level: BinaryArtifactTrustLevel::ProofGrade,
            total_vcs: 1,
            proved: 1,
            proof_certificate: ProofCertificateStatus::Checked {
                checker: "raw-summary".to_string(),
                format: "aggregate".to_string(),
                sha256: None,
            },
            replay: ReplayStatus::Replayed,
            ..Default::default()
        };
        let summary = BinaryVerificationCertificateSummary::from_binary_verification_summary(
            digest_lifted_binary(b"lifted-trust_ir"),
            "trust_ir+binary",
            "x86_64",
            &ledger,
            &verification,
            BinaryArtifactTrustLevel::ProofGrade,
        )
        .expect("summary should build");

        let decision = summary.proof_grade_release_gate();

        assert_eq!(summary.solver_results.proved, 0);
        assert_eq!(summary.solver_results.proved_with_certificates, 0);
        assert!(decision.rejected());
        assert!(decision.rejections.iter().any(|reason| {
            matches!(
                reason,
                BinaryReleaseGateRejection::NonProvedVerificationConditions {
                    vc_count: 1,
                    total_results: 0,
                    proved: 0,
                    unproved_vcs: 1,
                    non_proved_results: 0,
                }
            )
        }));
        assert!(decision.rejections.iter().any(|reason| {
            matches!(
                reason,
                BinaryReleaseGateRejection::MissingProofCertificates {
                    vc_count: 1,
                    proved: 0,
                    proved_with_certificates: 0,
                    missing_certificates: 1,
                }
            )
        }));
        assert!(
            decision.rejections.iter().any(|reason| {
                matches!(reason, BinaryReleaseGateRejection::ReplayStatusMissing)
            })
        );
    }

    #[test]
    fn proof_grade_gate_rejects_raw_solver_proof_bytes_even_with_checked_status() {
        let ledger = UnsupportedLedger::default();
        let mut dispatch = checked_dispatch("vc0");
        dispatch.result = Some(proved());
        let summary = dispatch_summary(&ledger, &[dispatch]);

        let decision = summary.proof_grade_release_gate();
        let json = serde_json::to_value(&decision).expect("decision should serialize");

        assert!(decision.rejected());
        assert_eq!(summary.raw_solver_proof_bytes, 1);
        assert_eq!(summary.certificate_checks.certificate_candidates, 1);
        assert_eq!(summary.certificate_checks.checked_certificates, 1);
        assert_eq!(summary.certificate_checks.raw_solver_proof_bytes, 1);
        assert!(summary.certificate_checks.checked_certificates_satisfy_coverage);
        assert!(!summary.certificate_checks.raw_solver_proof_bytes_satisfy_coverage);
        assert!(summary.certificate_checks.records[0].raw_solver_proof_bytes);
        assert!(decision.rejections.iter().any(|reason| {
            matches!(reason, BinaryReleaseGateRejection::RawSolverProofBytesPresent { count: 1 })
        }));
        assert!(
            json["rejections"]
                .as_array()
                .expect("rejections array")
                .iter()
                .any(|reason| reason.get("RawSolverProofBytesPresent").is_some()),
            "{json}"
        );
    }

    #[test]
    fn proof_grade_gate_rejects_unsupported_records() {
        let ledger = unsupported_ledger();
        let results = vec![proved()];
        let summary = summary(&ledger, 1, &results, &[ReplayStatus::Replayed]);

        let decision = evaluate_binary_proof_grade_release_gate(&summary);

        assert!(decision.rejected());
        assert!(decision.rejections.iter().any(|reason| {
            matches!(reason, BinaryReleaseGateRejection::UnsupportedRecordsPresent { count: 1, .. })
        }));
    }

    #[test]
    fn proof_grade_gate_rejects_unknown_replay() {
        let ledger = UnsupportedLedger::default();
        let results = vec![proved()];
        let summary = summary(&ledger, 1, &results, &[ReplayStatus::NotAttempted]);

        let decision = summary.proof_grade_release_gate();

        assert!(decision.rejected());
        assert!(decision.rejections.iter().any(|reason| {
            matches!(reason, BinaryReleaseGateRejection::ReplayStatusUnknown { not_attempted: 1 })
        }));
    }

    #[test]
    fn proof_grade_gate_rejects_non_proved_vcs() {
        let ledger = UnsupportedLedger::default();
        let results = vec![proved(), unknown()];
        let summary =
            summary(&ledger, 2, &results, &[ReplayStatus::Replayed, ReplayStatus::Replayed]);

        let decision = summary.proof_grade_release_gate();

        assert!(decision.rejected());
        assert!(decision.rejections.iter().any(|reason| {
            matches!(
                reason,
                BinaryReleaseGateRejection::NonProvedVerificationConditions {
                    vc_count: 2,
                    total_results: 2,
                    proved: 1,
                    unproved_vcs: 1,
                    non_proved_results: 1,
                }
            )
        }));
    }

    #[test]
    fn proof_grade_gate_rejects_proved_vcs_without_proof_certificates() {
        let ledger = UnsupportedLedger::default();
        let results = vec![proved(), proved_without_certificate()];
        let summary = summary(&ledger, 2, &results, &[ReplayStatus::Replayed]);

        let decision = summary.proof_grade_release_gate();

        assert!(decision.rejected());
        assert!(decision.rejections.iter().any(|reason| {
            matches!(
                reason,
                BinaryReleaseGateRejection::MissingProofCertificates {
                    vc_count: 2,
                    proved: 2,
                    proved_with_certificates: 0,
                    missing_certificates: 2,
                }
            )
        }));
    }
}
